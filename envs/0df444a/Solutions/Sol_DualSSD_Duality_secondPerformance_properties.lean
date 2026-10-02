-- Prove2me | solution 1 for DualSSD.Duality.secondPerformance_properties
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:09:25.952694+00:00
-- url     : https://prove2.me/submissions/4367d710-42b5-44d1-b204-aba54a937e93

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem dssd_shift (c : ℝ) (f : ℝ → ℝ) (S : Set ℝ) :
    ∫ u in S, f u = ∫ t in (fun t : ℝ => t + c) ⁻¹' S, f (t + c) := by
  have A : MeasurableEmbedding (fun t : ℝ => t + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have h := A.setIntegral_map (μ := volume) f S
  rw [map_add_right_eq_self] at h
  exact h

open MeasureTheory Filter in
/-- Layer cake: the second performance function is the expected shortfall `E (η - X)⁺`. -/
theorem dssd_perf_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (x : ℝ) :
    DualSSD.Shared.secondPerformance μ X x = ∫ ω, max (x - X ω) 0 ∂μ := by
  have hi : Integrable (fun ω => max (x - X ω) 0) μ := ((integrable_const x).sub hX).pos_part
  rw [DualSSD.Shared.secondPerformance,
    hi.integral_eq_integral_meas_le (Eventually.of_forall fun ω => le_max_right _ _),
    dssd_shift x (DualSSD.Shared.distFun μ X) (Set.Iic x), Set.preimage_add_const_Iic, sub_self]
  have h2 := integral_comp_neg_Ioi (0 : ℝ) (fun s => DualSSD.Shared.distFun μ X (s + x))
  rw [neg_zero] at h2
  rw [← h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [DualSSD.Shared.distFun, measureReal_def]
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, le_max_iff]
  have ht' : 0 < t := ht
  constructor
  · intro h; left; linarith
  · rintro (h | h)
    · linarith
    · linarith

open MeasureTheory in
theorem dssd_pp_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (x : ℝ) :
    Integrable (fun ω => max (x - X ω) 0) μ := ((integrable_const x).sub hX).pos_part

open MeasureTheory DualSSD in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) :
    Continuous (Shared.secondPerformance P X) ∧ ConvexOn ℝ Set.univ (Shared.secondPerformance P X) ∧
      (∀ η : ℝ, 0 ≤ Shared.secondPerformance P X η) ∧ Monotone (Shared.secondPerformance P X) := by
  have hF : Shared.secondPerformance P X = fun x => ∫ ω, max (x - X ω) 0 ∂P :=
    funext (dssd_perf_eq P X hX)
  rw [hF]
  have hI := dssd_pp_int P X hX
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq, ← integral_sub (hI x) (hI y)]
    have h := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => max (x - X ω) 0 - max (y - X ω) 0) (C := |x - y|)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
        congr 1; ring)
    simpa [Real.norm_eq_abs] using h
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hI x).const_mul a) ((hI y).const_mul b)]
    refine integral_mono (hI _) (((hI x).const_mul a).add ((hI y).const_mul b)) fun ω => ?_
    simp only
    have e : a * x + b * y - X ω = a * (x - X ω) + b * (y - X ω) := by
      linear_combination X ω * hab
    rw [e]
    refine max_le ?_ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
  · intro η
    exact integral_nonneg fun ω => le_max_right _ _
  · intro x y hxy
    exact integral_mono (hI x) (hI y) fun ω => max_le_max (by linarith) le_rfl

