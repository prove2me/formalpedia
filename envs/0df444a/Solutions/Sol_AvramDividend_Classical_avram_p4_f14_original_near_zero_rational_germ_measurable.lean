-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f14_original_near_zero_rational_germ_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:08:29.978711+00:00
-- url     : https://prove2.me/submissions/9345ab5e-603b-490e-af7d-2e84cacc2d00

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_DurrettProbability_Brownian
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical DurrettProbability
open scoped NNReal ENNReal
noncomputable section

/-- Countable positive rational observations can be tested at every positive germ horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    MeasurableSet[germSigma X.X] {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < X.X (q : ℝ≥0) ω} := by
  let δ (n : ℕ) : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  have hδpos (n : ℕ) : 0 < δ n := by
    dsimp [δ]
    positivity
  have hanti : Antitone δ := by
    intro a b hab
    dsimp [δ]
    gcongr
  have hsmall (ε : ℝ≥0) (hε : 0 < ε) : ∃ N : ℕ, δ N < ε := by
    simpa only [δ] using (exists_nat_one_div_lt hε)
  let A (k n : ℕ) : Set Ω :=
    ⋃ q : ℚ≥0, {ω : Ω | k ≤ n ∧ (q : ℝ≥0) < δ n ∧ 0 < X.X (q : ℝ≥0) ω}
  have heq :
      {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
        ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < X.X (q : ℝ≥0) ω} =
      (⋂ k : ℕ, ⋃ n : ℕ, A k n) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq, A]
    constructor
    · intro h k
      obtain ⟨q, hq, hpos⟩ := h (δ k) (hδpos k)
      exact ⟨k, q, le_rfl, hq, hpos⟩
    · intro h ε hε
      obtain ⟨N, hN⟩ := hsmall ε hε
      obtain ⟨n, q, hkn, hq, hpos⟩ := h N
      exact ⟨q, lt_trans hq (lt_of_le_of_lt (hanti hkn) hN), hpos⟩
  have hshift (N : ℕ) :
      (⋂ k : ℕ, ⋃ n : ℕ, A k n) =
      (⋂ k : ℕ, ⋃ n : ℕ, A (max N k) n) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq, A]
    constructor
    · intro h k
      obtain ⟨n, q, hkn, hq, hpos⟩ := h (max N k)
      exact ⟨n, q, hkn, hq, hpos⟩
    · intro h k
      obtain ⟨n, q, hkn, hq, hpos⟩ := h k
      exact ⟨n, q, le_trans (le_max_right N k) hkn, hq, hpos⟩
  have hS (s : ℝ≥0) (hs : 0 < s) :
      MeasurableSet[pastSigma X.X s]
        {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
          ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < X.X (q : ℝ≥0) ω} := by
    obtain ⟨N, hN⟩ := hsmall s hs
    rw [heq, hshift N]
    refine MeasurableSet.iInter (fun k => ?_)
    refine MeasurableSet.iUnion (fun n => ?_)
    change MeasurableSet[pastSigma X.X s]
      (⋃ q : ℚ≥0, {ω : Ω |
        max N k ≤ n ∧ (q : ℝ≥0) < δ n ∧ 0 < X.X (q : ℝ≥0) ω})
    refine MeasurableSet.iUnion (fun q => ?_)
    by_cases hn : max N k ≤ n
    · by_cases hq : (q : ℝ≥0) < δ n
      · have htime : (q : ℝ≥0) ≤ s :=
          le_trans hq.le
            (le_trans (hanti (le_trans (le_max_left N k) hn)) hN.le)
        have hcoord : Measurable[pastSigma X.X s] (X.X (q : ℝ≥0)) := by
          apply measurable_iff_comap_le.mpr
          unfold pastSigma
          exact le_iSup_of_le (q : ℝ≥0) (le_iSup_of_le htime le_rfl)
        change MeasurableSet[pastSigma X.X s]
          {ω : Ω | max N k ≤ n ∧ (q : ℝ≥0) < δ n ∧ 0 < X.X (q : ℝ≥0) ω}
        simpa only [hn, hq, true_and] using
          (measurableSet_lt
            (measurable_const : Measurable[pastSigma X.X s] (fun _ : Ω => (0 : ℝ)))
            hcoord)
      · simp [hq]
    · simp [hn]
  unfold germSigma
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro s
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro hs
  exact hS s hs
