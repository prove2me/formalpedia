-- Prove2me | solution 1 for DegreeSequences.eg_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:42:57.862736+00:00
-- url     : https://prove2.me/submissions/690255fa-08c0-4f43-b813-f28aae5b3b67

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_bot_isGraphic
public import Theorems.Thm_DegreeSequences_augment
public import Theorems.Thm_DegreeSequences_egReduce_add
public import Theorems.Thm_DegreeSequences_egReduce_antitone
public import Theorems.Thm_DegreeSequences_egReduce_sum_lt
public import Theorems.Thm_DegreeSequences_egReduce_EG

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {n : ℕ} (s : ℕ) : ∀ (d : Fin n → ℕ), ∑ i, d i = s → Antitone d →
    Even (∑ i, d i) →
    (∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k) →
    IsGraphic d := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro d hs hd hev hEG
  by_cases hz : ∀ i, d i = 0
  · exact bot_isGraphic d hz
  push Not at hz
  obtain ⟨i0, hi0⟩ := hz
  set P : Finset (Fin n) := univ.filter (fun i => 1 ≤ d i) with hPdef
  have hPne : P.Nonempty := ⟨i0, by simp [hPdef]; omega⟩
  set p := P.max' hPne with hpdef
  have hp1 : 1 ≤ d p := by
    have := P.max'_mem hPne
    rw [← hpdef, hPdef, mem_filter] at this
    exact this.2
  have hpz : ∀ i, p < i → d i = 0 := by
    intro i hi
    by_contra h
    have : i ∈ P := by simp [hPdef]; omega
    exact absurd (P.le_max' i this) (not_le.mpr hi)
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) p.isLt
  set z : Fin n := ⟨0, hn⟩ with hz
  -- Erdős–Gallai at `k = 1`
  have hE1 := hEG 1 (by omega)
  have hL1 : ∑ i with i.val < 1, d i = d z := by
    have : (univ.filter fun i : Fin n => i.val < 1) = {z} := by
      ext i; simp [hz, Fin.ext_iff]
    rw [this, sum_singleton]
  have hcount : ∑ i with 1 ≤ i.val, min (d i) 1 ≤ p.val := by
    calc ∑ i with 1 ≤ i.val, min (d i) 1 ≤ ∑ i with 1 ≤ i.val, (if i ≤ p then 1 else 0) := by
          refine sum_le_sum fun i _ => ?_
          split_ifs with h
          · exact min_le_right _ _
          · rw [hpz i (not_le.mp h)]; simp
      _ = #((univ.filter fun i : Fin n => 1 ≤ i.val).filter (· ≤ p)) := by
          rw [sum_boole]; simp
      _ ≤ #(Ioc z p) := by
          refine card_le_card fun i hi => ?_
          simp only [mem_filter, mem_univ, true_and] at hi
          rw [mem_Ioc, Fin.lt_def]
          exact ⟨by simp [hz]; omega, hi.2⟩
      _ = p.val := by rw [Fin.card_Ioc]; simp [hz]
  rw [hL1] at hE1
  simp only [Nat.sub_self, mul_zero, zero_add] at hE1
  have hzle : ∀ j : Fin n, z ≤ j := fun j => Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
  have hzp : d p ≤ d z := hd (hzle p)
  have hp0 : 0 < p.val := by omega
  -- choose `t`
  set T : Finset (Fin n) := univ.filter (fun i => i < p ∧ ∀ j ≤ i, d j = d i) with hTdef
  have hzT : z ∈ T := by
    simp only [hTdef, mem_filter, mem_univ, true_and]
    refine ⟨by rw [Fin.lt_def]; simpa [hz] using hp0, fun j hj => ?_⟩
    rw [le_antisymm hj (hzle j)]
  set t := T.max' ⟨z, hzT⟩ with htdef
  have htT : t ∈ T := T.max'_mem _
  simp only [hTdef, mem_filter, mem_univ, true_and] at htT
  obtain ⟨htp, htop⟩ := htT
  have hzt : z ≤ t := T.le_max' z hzT
  have hdzt : d z = d t := htop z hzt
  have htmax : ∀ i, t < i → i < p → d i < d t := by
    intro i hti hip
    by_contra h
    have hdi : d i = d t := le_antisymm (hd hti.le) (not_lt.mp h)
    have : i ∈ T := by
      simp only [hTdef, mem_filter, mem_univ, true_and]
      refine ⟨hip, fun j hj => le_antisymm ?_ (hd hj)⟩
      rw [hdi, ← hdzt]
      exact hd (hzle j)
    exact absurd (T.le_max' i this) (not_le.mpr hti)
  have ht1 : 1 ≤ d t := le_trans hp1 (hd htp.le)
  have hQ : d t ≤ #(univ.filter fun x : Fin n => x ≠ t ∧ d p ≤ d x) := by
    calc d t = d z := hdzt.symm
      _ ≤ p.val := le_trans hE1 hcount
      _ = #((Iic p).erase t) := by
          rw [card_erase_of_mem (mem_Iic.mpr htp.le), Fin.card_Iic]; simp
      _ ≤ _ := by
          refine card_le_card fun x hx => ?_
          simp only [mem_erase, mem_Iic] at hx
          simp only [mem_filter, mem_univ, true_and]
          exact ⟨hx.1, hd hx.2⟩
  -- the reduced sequence
  have hsum := egReduce_sum_lt d t p htp.ne ht1 hp1 univ
  simp only [mem_univ, ite_true] at hsum
  have hG' := ih (∑ i, egReduce d t p i) (by omega) (egReduce d t p) rfl
    (egReduce_antitone d hd t p htp hp1 hpz htmax)
    (by rw [hsum] at hev; obtain ⟨v, hv⟩ := hev; exact ⟨v - 1, by omega⟩)
    (egReduce_EG d hd hev hEG t p htp hp1 htop)
  obtain ⟨G', _, hG'⟩ := hG'
  obtain ⟨G, inst, hG⟩ := augment G' d t p htp.ne hp1 (fun v => by
    rw [hG', egReduce_add d t p htp.ne ht1 hp1 v]) hQ
  exact ⟨G, inst, hG⟩
end DegreeSequences
