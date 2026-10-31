-- Prove2me | solution 1 for FBMSP.lemma2b_general_menu_intervals
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:08:25.215134+00:00
-- url     : https://prove2.me/submissions/107b8387-ff1a-437b-87ee-edda6fcb45a0

import Theorems.Thm_FBMSP_mhr_revenue_tp2

open MeasureTheory
open FBMSP

namespace IntervalProof

private def IsLeastMaximizer {J : Type*} [LinearOrder J] (f : J → ℝ) (j : J) : Prop :=
  (∀ q, f q ≤ f j) ∧ (∀ q, f q = f j → j ≤ q)

/-- Every nonempty finite ordered menu has a least revenue maximizer. -/
private theorem exists_leastMaximizer {J : Type*} [Fintype J] [LinearOrder J]
    [Nonempty J] (f : J → ℝ) : ∃ j, IsLeastMaximizer f j := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  let s : Finset J := Finset.univ.filter (fun q => ∀ r, f r ≤ f q)
  have hs : s.Nonempty := by
    refine ⟨j, ?_⟩
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    intro r
    exact hj r (Finset.mem_univ r)
  have hmax : ∀ r, f r ≤ f (s.min' hs) := by
    have hm := s.min'_mem hs
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  refine ⟨s.min' hs, hmax, ?_⟩
  intro q hq
  apply Finset.min'_le
  simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
  intro r
  rw [hq]
  exact hmax r

/-- A TP2 revenue kernel with nonnegative, increasing columns has a monotone
least maximizer.  No positive-demand or distinct-price assumption is needed. -/
private theorem leastMaximizer_monotone {I J : Type*} [Preorder I] [LinearOrder J]
    (R : I → J → ℝ)
    (hR_nonneg : ∀ i j, 0 ≤ R i j)
    (hR_mono : ∀ j, Monotone (fun i => R i j))
    (hR_tp2 : ∀ i i' j j', i ≤ i' → j ≤ j' →
      R i j' * R i' j ≤ R i j * R i' j')
    (a : I → J) (ha : ∀ i, IsLeastMaximizer (R i) (a i)) :
    Monotone a := by
  intro i i' hii'
  by_contra hbad
  have hrev : a i' < a i := lt_of_not_ge hbad
  have hweak : R i (a i') ≤ R i (a i) := (ha i).1 (a i')
  have hstrict : R i (a i') < R i (a i) := by
    apply lt_of_le_of_ne hweak
    intro heq
    exact (not_le_of_gt hrev) ((ha i).2 (a i') heq)
  have hpos : 0 < R i (a i) := lt_of_le_of_lt (hR_nonneg i (a i')) hstrict
  have hcol : R i (a i) ≤ R i' (a i) := hR_mono (a i) hii'
  have hpos' : 0 < R i' (a i) := lt_of_lt_of_le hpos hcol
  have hmax' : R i' (a i) ≤ R i' (a i') := (ha i').1 (a i)
  have hprod₁ : R i (a i') * R i' (a i) < R i (a i) * R i' (a i) :=
    mul_lt_mul_of_pos_right hstrict hpos'
  have hprod₂ : R i (a i) * R i' (a i) ≤ R i (a i) * R i' (a i') :=
    mul_le_mul_of_nonneg_left hmax' (le_of_lt hpos)
  have htp := hR_tp2 i i' (a i') (a i) hii' (le_of_lt hrev)
  exact (not_lt_of_ge htp) (lt_of_lt_of_le hprod₁ hprod₂)

/-- A fixed finite menu admits a monotone assignment maximizing every row. -/
private theorem exists_monotone_rowMaximizer {I J : Type*} [Preorder I]
    [Fintype J] [LinearOrder J] [Nonempty J]
    (R : I → J → ℝ)
    (hR_nonneg : ∀ i j, 0 ≤ R i j)
    (hR_mono : ∀ j, Monotone (fun i => R i j))
    (hR_tp2 : ∀ i i' j j', i ≤ i' → j ≤ j' →
      R i j' * R i' j ≤ R i j * R i' j') :
    ∃ a : I → J, Monotone a ∧ ∀ i j, R i j ≤ R i (a i) := by
  classical
  choose a ha using (fun i => exists_leastMaximizer (R i))
  exact ⟨a, leastMaximizer_monotone R hR_nonneg hR_mono hR_tp2 a ha,
    fun i => (ha i).1⟩

end IntervalProof

open IntervalProof

theorem solution {k : ℕ}
    (hk : 0 < k) (η : MeasureTheory.Measure ℝ)
    (hη : ValidNoise η) (hMHR : HasMHR η)
    (p : Fin k → ℝ) (hp : Monotone p) (hpNonneg : ∀ j, 0 ≤ p j) :
    ∃ a : ℝ → Fin k, Monotone a ∧
      (∀ (x : ℝ) (j : Fin k), postedRevenue η x (p j) ≤
        postedRevenue η x (p (a x))) ∧
      (∀ x₁ x₂ x₃ : ℝ, x₁ ≤ x₂ → x₂ ≤ x₃ →
        a x₁ = a x₃ → a x₂ = a x₁) := by
  letI : IsProbabilityMeasure η := hη.1
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hnonneg : ∀ x j, 0 ≤ postedRevenue η x (p j) := by
    intro x j
    exact mul_nonneg (hpNonneg j) ENNReal.toReal_nonneg
  have hmono : ∀ j, Monotone (fun x => postedRevenue η x (p j)) := by
    intro j x y hxy
    unfold postedRevenue survival
    apply mul_le_mul_of_nonneg_left _ (hpNonneg j)
    apply ENNReal.toReal_mono (measure_ne_top η _)
    exact measure_mono (Set.Ici_subset_Ici.mpr (sub_le_sub_left hxy (p j)))
  have htp : ∀ x y i j, x ≤ y → i ≤ j →
      postedRevenue η x (p j) * postedRevenue η y (p i) ≤
        postedRevenue η x (p i) * postedRevenue η y (p j) := by
    intro x y i j hxy hij
    exact mhr_revenue_tp2 η hη hMHR x y (p i) (p j) hxy (hpNonneg i) (hp hij)
  obtain ⟨a, ha, hmax⟩ := exists_monotone_rowMaximizer
    (fun x j => postedRevenue η x (p j)) hnonneg hmono htp
  refine ⟨a, ha, hmax, ?_⟩
  intro x₁ x₂ x₃ h₁₂ h₂₃ heq
  apply le_antisymm
  · exact (ha h₂₃).trans_eq heq.symm
  · exact ha h₁₂
