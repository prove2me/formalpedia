-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_two_past_weights_marked_cell_covariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:08:12.333557+00:00
-- url     : https://prove2.me/submissions/2706f53e-2b7f-4e0e-9920-1bb14bfe8550

import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_one_cell_bilinear_covariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

/-- Original-space mixed mark covariance with two different predictable past weights,
derived by polarizing the same-weight marked covariance in the weight variable. -/
theorem solution {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν] (H J : Ω → ℝ) (hHm : Measurable H) (hJm : Measurable J) (hH2 : Integrable (fun ω => H ω ^ 2) μ) (hJ2 : Integrable (fun ω => J ω ^ 2) μ) (K : Ω → ℕ) (Y : ℕ → Ω → E) (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ) (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ) (hYi : iIndepFun Y μ) (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ) (hPastH : IndepFun H (fun ω => (K ω, fun n : ℕ => Y n ω)) μ) (hPastJ : IndepFun J (fun ω => (K ω, fun n : ℕ => Y n ω)) μ) (hPastSum : IndepFun (fun ω => H ω + J ω) (fun ω => (K ω, fun n : ℕ => Y n ω)) μ) (f g : E → ℝ) (hf : Measurable f) (hg : Measurable g) (hfI : Integrable f ν) (hgI : Integrable g ν) (hf2 : MemLp f 2 ν) (hg2 : MemLp g 2 ν) :
    let A : Ω → ℝ := fun ω => H ω *
      ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν)
    let B : Ω → ℝ := fun ω => J ω *
      ((∑ n ∈ Finset.range (K ω), g (Y n ω)) -
        (r : ℝ) * ∫ z, g z ∂ν)
    Integrable (fun ω => A ω * B ω) μ ∧
      (∫ ω, A ω * B ω ∂μ) =
        (∫ ω, H ω * J ω ∂μ) * (r : ℝ) * (∫ z, f z * g z ∂ν) := by
  let Df : Ω → ℝ := fun ω =>
    (∑ n ∈ Finset.range (K ω), f (Y n ω)) - (r : ℝ) * ∫ z, f z ∂ν
  let Dg : Ω → ℝ := fun ω =>
    (∑ n ∈ Finset.range (K ω), g (Y n ω)) - (r : ℝ) * ∫ z, g z ∂ν
  let A : Ω → ℝ := fun ω => H ω * Df ω
  let B : Ω → ℝ := fun ω => J ω * Dg ω
  change Integrable (fun ω => A ω * B ω) μ ∧
    (∫ ω, A ω * B ω ∂μ) =
      (∫ ω, H ω * J ω ∂μ) * (r : ℝ) * (∫ z, f z * g z ∂ν)
  have hHLp : MemLp H 2 μ :=
    (memLp_two_iff_integrable_sq hHm.aestronglyMeasurable).2 hH2
  have hJLp : MemLp J 2 μ :=
    (memLp_two_iff_integrable_sq hJm.aestronglyMeasurable).2 hJ2
  have hHJ : Integrable (fun ω => H ω * J ω) μ := by
    have h := hHLp.integrable_mul hJLp
    have hEq : (fun ω => H ω * J ω) = H * J := by
      funext ω
      rfl
    rw [hEq]
    exact h
  have hSum2 : Integrable (fun ω => (H ω + J ω) ^ 2) μ := by
    have hSqPoint :
        (fun ω => (H ω + J ω) ^ 2) =
          (fun ω => (H ω ^ 2 + 2 * (H ω * J ω)) + J ω ^ 2) := by
      funext ω
      ring
    rw [hSqPoint]
    exact (hH2.add (hHJ.const_mul 2)).add hJ2
  have hOneH := avram_wave4_p1_predictable_marked_one_cell_bilinear_covariance
    μ ν H hHm hH2 K Y hKm r hKlaw hYm hYL hYi
      hCountMarks hPastH f g hf hg hfI hgI hf2 hg2
  have hOneJ := avram_wave4_p1_predictable_marked_one_cell_bilinear_covariance
    μ ν J hJm hJ2 K Y hKm r hKlaw hYm hYL hYi
      hCountMarks hPastJ f g hf hg hfI hgI hf2 hg2
  have hOneSum := avram_wave4_p1_predictable_marked_one_cell_bilinear_covariance
    μ ν (fun ω => H ω + J ω) (hHm.add hJm) hSum2
      K Y hKm r hKlaw hYm hYL hYi
      hCountMarks hPastSum f g hf hg hfI hgI hf2 hg2
  let P : (Ω → ℝ) → Ω → ℝ := fun C ω => (C ω * Df ω) * (C ω * Dg ω)
  have hP :
      Integrable (P H) μ ∧
        (∫ ω, P H ω ∂μ) =
          (∫ ω, H ω ^ 2 ∂μ) * (r : ℝ) *
            (∫ z, f z * g z ∂ν) := hOneH
  have hQ :
      Integrable (P J) μ ∧
        (∫ ω, P J ω ∂μ) =
          (∫ ω, J ω ^ 2 ∂μ) * (r : ℝ) *
            (∫ z, f z * g z ∂ν) := hOneJ
  have hR :
      Integrable (P (fun ω => H ω + J ω)) μ ∧
        (∫ ω, P (fun ω => H ω + J ω) ω ∂μ) =
          (∫ ω, (H ω + J ω) ^ 2 ∂μ) * (r : ℝ) *
            (∫ z, f z * g z ∂ν) := hOneSum
  have hProductPoint :
      (fun ω => A ω * B ω) =
        (fun ω => (1 / 2 : ℝ) *
          (P (fun ω => H ω + J ω) ω - P H ω - P J ω)) := by
    funext ω
    dsimp [A, B, P]
    ring
  have hProd : Integrable (fun ω => A ω * B ω) μ := by
    rw [hProductPoint]
    exact ((hR.1.sub hP.1).sub hQ.1).const_mul (1 / 2 : ℝ)
  have hWeightEnergy :
      (∫ ω, (H ω + J ω) ^ 2 ∂μ) -
          (∫ ω, H ω ^ 2 ∂μ) -
            (∫ ω, J ω ^ 2 ∂μ) =
        2 * (∫ ω, H ω * J ω ∂μ) := by
    have hSqPoint :
        (fun ω => (H ω + J ω) ^ 2) =
          (fun ω => (H ω ^ 2 + 2 * (H ω * J ω)) + J ω ^ 2) := by
      funext ω
      ring
    have hOuter :
        (∫ ω, (H ω ^ 2 + 2 * (H ω * J ω)) + J ω ^ 2 ∂μ) =
          (∫ ω, H ω ^ 2 + 2 * (H ω * J ω) ∂μ) +
            (∫ ω, J ω ^ 2 ∂μ) := by
      simpa only [Pi.add_apply] using integral_add (hH2.add (hHJ.const_mul 2)) hJ2
    have hInner :
        (∫ ω, H ω ^ 2 + 2 * (H ω * J ω) ∂μ) =
          (∫ ω, H ω ^ 2 ∂μ) +
            (∫ ω, (2 : ℝ) * (H ω * J ω) ∂μ) := by
      simpa only [Pi.add_apply] using integral_add hH2 (hHJ.const_mul 2)
    rw [hSqPoint, hOuter, hInner, integral_const_mul]
    ring
  constructor
  · exact hProd
  · have hPolar :
        (∫ ω, A ω * B ω ∂μ) =
          (1 / 2 : ℝ) *
            ((∫ ω, P (fun ω => H ω + J ω) ω ∂μ) -
              (∫ ω, P H ω ∂μ) -
                (∫ ω, P J ω ∂μ)) := by
      have hOuterSub :
          (∫ ω, (P (fun ω => H ω + J ω) ω - P H ω) - P J ω ∂μ) =
            (∫ ω, P (fun ω => H ω + J ω) ω - P H ω ∂μ) -
              (∫ ω, P J ω ∂μ) := by
        simpa only [Pi.sub_apply] using integral_sub (hR.1.sub hP.1) hQ.1
      have hInnerSub :
          (∫ ω, P (fun ω => H ω + J ω) ω - P H ω ∂μ) =
            (∫ ω, P (fun ω => H ω + J ω) ω ∂μ) -
              (∫ ω, P H ω ∂μ) := by
        simpa only [Pi.sub_apply] using integral_sub hR.1 hP.1
      rw [hProductPoint, integral_const_mul, hOuterSub, hInnerSub]
    rw [hPolar, hR.2, hP.2, hQ.2]
    calc
      (1 / 2 : ℝ) *
          ((∫ ω, (H ω + J ω) ^ 2 ∂μ) * (r : ℝ) *
              (∫ z, f z * g z ∂ν) -
            (∫ ω, H ω ^ 2 ∂μ) * (r : ℝ) *
              (∫ z, f z * g z ∂ν) -
            (∫ ω, J ω ^ 2 ∂μ) * (r : ℝ) *
              (∫ z, f z * g z ∂ν)) =
          (1 / 2 : ℝ) *
            ((∫ ω, (H ω + J ω) ^ 2 ∂μ) -
              (∫ ω, H ω ^ 2 ∂μ) -
                (∫ ω, J ω ^ 2 ∂μ)) *
              (r : ℝ) * (∫ z, f z * g z ∂ν) := by ring
      _ = (∫ ω, H ω * J ω ∂μ) * (r : ℝ) *
          (∫ z, f z * g z ∂ν) := by
            rw [hWeightEnergy]
            ring