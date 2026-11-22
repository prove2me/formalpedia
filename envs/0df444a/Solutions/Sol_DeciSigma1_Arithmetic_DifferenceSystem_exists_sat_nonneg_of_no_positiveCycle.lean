-- Prove2me | solution 1 for DeciSigma1.Arithmetic.DifferenceSystem.exists_sat_nonneg_of_no_positiveCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:00.448901+00:00
-- url     : https://prove2.me/submissions/a908a8b4-3947-4248-9880-0ff36db2484c

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_append_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_snoc_snoc
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_le_maxNonnegativeWeight
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_isWalk_append_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
open DeciSigma1.Arithmetic.DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
variable {D}
open Classical
namespace DeciSigma1.Arithmetic.DifferenceSystem
theorem _root_.solution [Fintype ι]
    (h : ¬ D.HasPositiveCycle) :
    ∃ x, D.Sat x ∧ ∀ i, 0 ≤ x i ∧ x i ≤ ((Fintype.card ι - 1 : ℕ) : ℤ) *
        D.maxNonnegativeWeight := by
  set n := Fintype.card ι
  -- candidate simple paths ending at `i`
  let P : ι → Finset (List ι) := fun i =>
    (Automata.wordsUpTo n).filter (fun q => q.Nodup ∧ q.getLast? = some i ∧ D.IsWalk q)
  have mem_P : ∀ i q, q ∈ P i ↔ q.Nodup ∧ q.getLast? = some i ∧ D.IsWalk q := by
    intro i q
    simp only [P, Finset.mem_filter, Automata.mem_wordsUpTo, and_iff_right_iff_imp]
    exact fun h => h.1.length_le_card
  have single : ∀ i, [i] ∈ P i := fun i => (mem_P i [i]).mpr
    ⟨List.nodup_singleton i, rfl, List.isChain_singleton i⟩
  let x : ι → ℤ := fun i => ((P i).sup (fun q => (D.weight q).toNat) : ℕ)
  have le_x : ∀ i q, q ∈ P i → D.weight q ≤ x i := by
    intro i q hq
    have : (D.weight q).toNat ≤ (P i).sup (fun q => (D.weight q).toNat) :=
      Finset.le_sup (f := fun q => (D.weight q).toNat) hq
    simp only [x]
    omega
  have attained : ∀ i, ∃ q ∈ P i, D.weight q = x i := by
    intro i
    obtain ⟨q, hq, hqx⟩ := Finset.exists_mem_eq_sup (P i) ⟨[i], single i⟩
      (fun q => (D.weight q).toNat)
    by_cases hneg : 0 ≤ D.weight q
    · refine ⟨q, hq, ?_⟩
      simp only [x, hqx]; omega
    · refine ⟨[i], single i, ?_⟩
      simp only [x, hqx, weight_singleton]; omega
  refine ⟨x, ?_, fun i => ⟨by simp [x], ?_⟩⟩
  · intro i j c hc
    obtain ⟨q, hq, hqx⟩ := attained i
    obtain ⟨hnd, hlast, hw⟩ := (mem_P i q).mp hq
    have hqne : q ≠ [] := by rintro rfl; simp at hlast
    by_cases hj : j ∈ q
    · -- the extension would close a cycle: cut it off
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hj
      have hsplit := List.isChain_split.mp hw
      have hcyc : D.IsWalk (j :: t ++ [j]) := by
        refine isWalk_append_singleton hsplit.2 ?_ (by rw [hc]; rfl)
        rw [← hlast, List.getLast?_append_cons]
      have hcyc_wt : D.weight (j :: t ++ [j]) = D.weight (j :: t) + c := by
        have hl : (j :: t).getLast? = some i := by rw [← hlast, List.getLast?_append_cons]
        obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp hl
        rw [hu, List.append_assoc, List.singleton_append, weight_snoc_snoc, hc, Option.getD_some]
      have hnot : ¬ 0 < D.weight (j :: t ++ [j]) := fun hpos => h ⟨j, t, hcyc, hpos⟩
      have hmem : s ++ [j] ∈ P j :=
        (mem_P j _).mpr ⟨hnd.sublist (by simp), by simp, hsplit.1⟩
      have hwq := weight_append_cons (D := D) s t j
      have := le_x j _ hmem
      rw [← hqx]
      linarith
    · have hmem : q ++ [j] ∈ P j := by
        refine (mem_P j _).mpr ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton j, ?_⟩,
          by simp, isWalk_append_singleton hw hlast (by rw [hc]; rfl)⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        exact fun hab => hj (hab ▸ ha)
      have hwq : D.weight (q ++ [j]) = D.weight q + c := by
        obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp hlast
        rw [hu, List.append_assoc, List.singleton_append, weight_snoc_snoc, hc, Option.getD_some]
      have := le_x j _ hmem
      rw [← hqx]
      linarith
  · have hsup : (P i).sup (fun q => (D.weight q).toNat) ≤ (n - 1) * D.maxNonnegativeWeight := by
      refine Finset.sup_le fun q hq => ?_
      obtain ⟨hnd, _, hw⟩ := (mem_P i q).mp hq
      have hlen : q.length ≤ n := hnd.length_le_card
      have h1 := weight_le_maxNonnegativeWeight q hw
      have h2 : ((q.length - 1 : ℕ) : ℤ) * (D.maxNonnegativeWeight : ℤ) ≤
          ((n - 1 : ℕ) : ℤ) * (D.maxNonnegativeWeight : ℤ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le_sub_right hlen 1)
          (by positivity)
      rw [Int.toNat_le]
      push_cast [Nat.cast_mul]
      linarith
    simp only [x]
    exact_mod_cast hsup
end DeciSigma1.Arithmetic.DifferenceSystem
