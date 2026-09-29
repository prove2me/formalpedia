-- Prove2me | solution 1 for AvgCompletionSched.DelayList.one_machine_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:33:21.565449+00:00
-- url     : https://prove2.me/submissions/5391208d-9fcb-444c-bc67-62bfa542a0fe

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model

namespace AvgCompletionSched.DelayList

variable {n : ℕ}

/-- Total processing time of non-overlapping jobs of one machine inside `[a, b]` is at most
`b - a`. -/
theorem aux_olb_machine {I : Instance n} {m : ℕ} (N : Schedule I m) (μ : Fin m) (a : ℝ)
    (F : Finset (Fin n)) :
    ∀ b : ℝ, (∀ k ∈ F, N.M k = μ ∧ a ≤ N.S k ∧ N.S k + I.p k ≤ b) → a ≤ b →
      ∑ k ∈ F, I.p k ≤ b - a := by
  induction F using Finset.induction_on_max_value (f := N.S) with
  | empty => intro b _ hab; simp; linarith
  | insert k s hks hmax ih =>
    intro b hF hab
    rw [Finset.sum_insert hks]
    have hk := hF k (Finset.mem_insert_self k s)
    have h1 : ∑ x ∈ s, I.p x ≤ N.S k - a := by
      apply ih (N.S k)
      · intro x hx
        have hx' := hF x (Finset.mem_insert_of_mem hx)
        refine ⟨hx'.1, hx'.2.1, ?_⟩
        have hne : x ≠ k := fun h => hks (h ▸ hx)
        rcases N.noOverlap x k (hx'.1.trans hk.1.symm) hne with h | h
        · exact h
        · have := hmax x hx
          have := I.p_pos k
          linarith
      · exact hk.2.1
    linarith [hk.2.2]

/-- Lexicographic key: completion time, then index. -/
def aux_olb_key {I : Instance n} {m : ℕ} (N : Schedule I m) (j : Fin n) : ℝ ×ₗ Fin n :=
  toLex (N.C j, j)

theorem aux_olb_key_le {I : Instance n} {m : ℕ} (N : Schedule I m) {i j : Fin n}
    (h : aux_olb_key N i ≤ aux_olb_key N j) : N.C i ≤ N.C j := by
  unfold aux_olb_key at h
  rw [Prod.Lex.toLex_le_toLex'] at h
  exact h.1

theorem aux_olb_key_inj {I : Instance n} {m : ℕ} (N : Schedule I m) {i j : Fin n}
    (h : aux_olb_key N i = aux_olb_key N j) : i = j := by
  unfold aux_olb_key at h
  have := congrArg (fun x => (ofLex x).2) h
  simpa using this

theorem aux_olb_key_lt_of_C {I : Instance n} {m : ℕ} (N : Schedule I m) {i j : Fin n}
    (h : N.C i < N.C j) : aux_olb_key N i < aux_olb_key N j := by
  unfold aux_olb_key
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

open Classical in
/-- The one-machine completion time of job `j`. -/
noncomputable def aux_olb_C1 {I : Instance n} {m : ℕ} (N : Schedule I m) (j : Fin n) : ℝ :=
  (Finset.univ.filter (fun i => aux_olb_key N i ≤ aux_olb_key N j)).sup'
    ⟨j, by simp⟩
    (fun i => I.r i + ∑ k ∈ Finset.univ.filter
      (fun k => aux_olb_key N i ≤ aux_olb_key N k ∧ aux_olb_key N k ≤ aux_olb_key N j), I.p k)

open Classical in
theorem aux_olb_le_C1 {I : Instance n} {m : ℕ} (N : Schedule I m) (i j : Fin n)
    (hij : aux_olb_key N i ≤ aux_olb_key N j) :
    I.r i + ∑ k ∈ Finset.univ.filter
      (fun k => aux_olb_key N i ≤ aux_olb_key N k ∧ aux_olb_key N k ≤ aux_olb_key N j), I.p k
      ≤ aux_olb_C1 N j := by
  unfold aux_olb_C1
  exact Finset.le_sup' (f := fun i => I.r i + ∑ k ∈ Finset.univ.filter
      (fun k => aux_olb_key N i ≤ aux_olb_key N k ∧ aux_olb_key N k ≤ aux_olb_key N j), I.p k)
    (by simpa using hij)

open Classical in
theorem aux_olb_step {I : Instance n} {m : ℕ} (N : Schedule I m) (i j : Fin n)
    (hij : aux_olb_key N i < aux_olb_key N j) :
    aux_olb_C1 N i + I.p j ≤ aux_olb_C1 N j := by
  have key : aux_olb_C1 N i ≤ aux_olb_C1 N j - I.p j := by
    unfold aux_olb_C1
    apply Finset.sup'_le
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    have hlj : aux_olb_key N l ≤ aux_olb_key N j := hl.trans hij.le
    have h2 := aux_olb_le_C1 N l j hlj
    have hsub : insert j (Finset.univ.filter
        (fun k => aux_olb_key N l ≤ aux_olb_key N k ∧ aux_olb_key N k ≤ aux_olb_key N i)) ⊆
        Finset.univ.filter
        (fun k => aux_olb_key N l ≤ aux_olb_key N k ∧ aux_olb_key N k ≤ aux_olb_key N j) := by
      intro k hk
      rw [Finset.mem_insert] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rcases hk with rfl | hk
      · exact ⟨hlj, le_rfl⟩
      · exact ⟨hk.1, hk.2.trans hij.le⟩
    have hnot : j ∉ Finset.univ.filter
        (fun k => aux_olb_key N l ≤ aux_olb_key N k ∧ aux_olb_key N k ≤ aux_olb_key N i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le]
      intro _
      exact hij
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := I.p) (fun k _ _ => (I.p_pos k).le)
    rw [Finset.sum_insert hnot] at hs
    unfold aux_olb_C1 at h2
    linarith
  linarith

open Classical in
theorem aux_olb_bound {I : Instance n} {m : ℕ} (N : Schedule I m) (i j : Fin n)
    (hij : aux_olb_key N i ≤ aux_olb_key N j) :
    I.r i + ∑ k ∈ Finset.univ.filter
      (fun k => aux_olb_key N i ≤ aux_olb_key N k ∧ aux_olb_key N k ≤ aux_olb_key N j), I.p k
      ≤ (m : ℝ) * N.C j := by
  set X := Finset.univ.filter
      (fun k => aux_olb_key N i ≤ aux_olb_key N k ∧ aux_olb_key N k ≤ aux_olb_key N j) with hX
  set T := N.C j with hTdef
  have hT : 0 < T := by
    have := N.released j
    have := I.r_nonneg j
    have := I.p_pos j
    simp only [hTdef, Schedule.C]
    linarith
  have hCiT : N.C i ≤ T := aux_olb_key_le N hij
  let a : Fin m → ℝ := fun μ => if μ = N.M i then N.S i else 0
  have hfib : ∑ μ : Fin m, ∑ k ∈ X with N.M k = μ, I.p k = ∑ k ∈ X, I.p k :=
    Finset.sum_fiberwise X N.M _
  have hμ : ∀ μ : Fin m, ∑ k ∈ X with N.M k = μ, I.p k ≤ T - a μ := by
    intro μ
    apply aux_olb_machine N μ (a μ) _ T
    · intro k hk
      simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      obtain ⟨⟨hik, hkj⟩, hkμ⟩ := hk
      refine ⟨hkμ, ?_, ?_⟩
      · simp only [a]
        split_ifs with hμi
        · by_cases hki : k = i
          · rw [hki]
          · rcases N.noOverlap k i (hkμ.trans hμi) hki with h | h
            · have h1 := aux_olb_key_le N hik
              have := I.p_pos i
              simp only [Schedule.C] at h1
              linarith
            · have := I.p_pos i
              linarith
        · exact (I.r_nonneg k).trans (N.released k)
      · exact aux_olb_key_le N hkj
    · simp only [a]
      split_ifs
      · have := I.p_pos i
        simp only [Schedule.C] at hCiT
        linarith
      · exact hT.le
  have hsum : ∑ μ : Fin m, (T - a μ) = (m : ℝ) * T - N.S i := by
    rw [Finset.sum_sub_distrib]
    simp [a]
  have h1 := Finset.sum_le_sum (fun μ (_ : μ ∈ Finset.univ) => hμ μ)
  have h2 := N.released i
  rw [hfib, hsum] at h1
  linarith

end AvgCompletionSched.DelayList

open AvgCompletionSched.DelayList

theorem solution {n m : ℕ} (I : Instance n) (N : Schedule I m) :
    ∃ S1 : Schedule I 1, S1.wct ≤ (m : ℝ) * N.wct := by
  classical
  have hC1le : ∀ j, aux_olb_C1 N j ≤ (m : ℝ) * N.C j := by
    intro j
    unfold aux_olb_C1
    apply Finset.sup'_le
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    convert aux_olb_bound N i j hi
  refine ⟨⟨fun j => aux_olb_C1 N j - I.p j, fun _ => 0, ?_, ?_, ?_⟩, ?_⟩
  · intro j
    have h := aux_olb_le_C1 N j j le_rfl
    have hs : I.p j ≤ ∑ k ∈ Finset.univ.filter
        (fun k => aux_olb_key N j ≤ aux_olb_key N k ∧ aux_olb_key N k ≤ aux_olb_key N j),
        I.p k :=
      Finset.single_le_sum (f := I.p) (fun k _ => (I.p_pos k).le) (by simp)
    show I.r j ≤ aux_olb_C1 N j - I.p j
    linarith
  · intro i j _ hij
    have hne : aux_olb_key N i ≠ aux_olb_key N j := fun h => hij (aux_olb_key_inj N h)
    rcases lt_or_gt_of_ne hne with h | h
    · left
      have := aux_olb_step N i j h
      show aux_olb_C1 N i - I.p i + I.p i ≤ aux_olb_C1 N j - I.p j
      linarith
    · right
      have := aux_olb_step N j i h
      show aux_olb_C1 N j - I.p j + I.p j ≤ aux_olb_C1 N i - I.p i
      linarith
  · intro i j hp
    have h1 := N.precedence i j hp
    have hlt : N.C i < N.C j := by
      have := I.p_pos j
      simp only [Schedule.C]
      linarith
    have := aux_olb_step N i j (aux_olb_key_lt_of_C N hlt)
    show aux_olb_C1 N i - I.p i + I.p i ≤ aux_olb_C1 N j - I.p j
    linarith
  · unfold Schedule.wct
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simp only [Schedule.C, sub_add_cancel]
    have h := hC1le j
    have hw := I.w_pos j
    simp only [Schedule.C] at h
    nlinarith
