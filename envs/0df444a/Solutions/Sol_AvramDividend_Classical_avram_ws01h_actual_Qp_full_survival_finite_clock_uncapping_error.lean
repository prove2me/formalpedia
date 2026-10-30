-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_Qp_full_survival_finite_clock_uncapping_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:56:08.997759+00:00
-- url     : https://prove2.me/submissions/70a7b918-d6d2-435c-b9a4-4b198fec3a54

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_exp_clock_finite_cap_tail_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Exact exponential-tail error for uncapping the finite-horizon genuinely
terminal-Esscher lower-survival CDF at any fixed positive rate p. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (x : ℝ) (N : ℝ≥0) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     let C : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     Qp C ≤ Qp E ∧
       Qp E ≤ Qp C + ENNReal.ofReal (Real.exp (-(p * (N : ℝ))))) := by
  intro Qp E C
  have hSub : C ⊆ E := by
    intro z hz
    exact ⟨hz.1, hz.2.2⟩
  have hCover : E ⊆ C ∪ {z : Ω × ℝ | (N : ℝ) < z.2} := by
    intro z hz
    by_cases hN : Real.toNNReal z.2 ≤ N
    · exact Or.inl ⟨hz.1, hN, hz.2⟩
    · right
      have hNN : N < Real.toNNReal z.2 := lt_of_not_ge hN
      have hr : (N : ℝ) < (Real.toNNReal z.2 : ℝ) :=
        NNReal.coe_lt_coe.mpr hNN
      change (N : ℝ) < z.2
      simpa only [Real.coe_toNNReal z.2 hz.1] using hr
  have hTail : Qp {z : Ω × ℝ | (N : ℝ) < z.2} =
      ENNReal.ofReal (Real.exp (-(p * (N : ℝ)))) := by
    simpa only [Qp] using
      (avram_ws01h_actual_Qp_exp_clock_finite_cap_tail_exact
        X θ p hθ hp N)
  constructor
  · exact measure_mono hSub
  · calc
      Qp E ≤ Qp (C ∪ {z : Ω × ℝ | (N : ℝ) < z.2}) :=
        measure_mono hCover
      _ ≤ Qp C + Qp {z : Ω × ℝ | (N : ℝ) < z.2} :=
        measure_union_le _ _
      _ = Qp C + ENNReal.ofReal (Real.exp (-(p * (N : ℝ)))) := by
        rw [hTail]
