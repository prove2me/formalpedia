-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_esscher_excursion_integrated_scale_representation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:53:04.544058+00:00
-- url     : https://prove2.me/submissions/2d58442d-ecc0-4012-8041-e9c0abd4ce09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_ratio_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_positive_monotone_of_given_root
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_absolute_continuity
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_log_concavity
import Theorems.Thm_AvramDividend_Classical_continuous_log_derivative_of_positive_C1
import Theorems.Thm_AvramDividend_Classical_log_derivative_antitone_of_concave_log
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_log_derivative_flatness
import Theorems.Thm_AvramDividend_Classical_nonnegative_of_positive_axis_antitone_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_atomless_positive_tail_measure_of_antitone_continuous
import Theorems.Thm_AvramDividend_Classical_interval_exponential_of_positive_log_derivative
import Theorems.Thm_AvramDividend_Classical_esscher_interval_representation_transfer

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Integrate the genuine tilted-scale C1 theorem with the accepted
    log-concave excursion-tail construction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t))) := by
  obtain ⟨φ, hφ, hroot, _⟩ :=
    unbounded_esscher_ratio_bound X q hq W hW hnbv
  have hWpos : ∀ x : ℝ, 0 < x → 0 < W x :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x
  have hVpos : ∀ x : ℝ, 0 < x → 0 < V x := by
    intro x hx
    exact mul_pos (Real.exp_pos _) (hWpos x hx)
  have hVeq : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x := by
    intro x hx
    rfl
  have hVmono : MonotoneOn V (Ioi 0) := by
    simpa only [V, neg_mul] using
      unbounded_tilted_positive_monotone_of_given_root
        X q hq W hW hnbv φ hφ hroot
  have hVone : ContDiffOn ℝ 1 V (Ioi 0) :=
    unbounded_tilted_scale_absolute_continuity
      X q hq W hW hnbv φ hφ hroot V hVeq
  have hVdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ V x := by
    intro x hx
    exact (hVone.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  let g : ℝ → ℝ := fun x => deriv (fun y : ℝ => Real.log (V y)) x
  have hgcont : ContinuousOn g (Ioi 0) :=
    continuous_log_derivative_of_positive_C1 V hVpos hVone
  have hVderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (V x * g x) x := by
    intro x hx
    have hv : V x ≠ 0 := (hVpos x hx).ne'
    have hlog : g x = deriv V x / V x := by
      change deriv (fun y : ℝ => Real.log (V y)) x = deriv V x / V x
      exact ((hVdiff x hx).hasDerivAt.log hv).deriv
    have hmul : V x * g x = deriv V x := by
      rw [hlog]
      field_simp [hv]
    simpa only [hmul] using (hVdiff x hx).hasDerivAt
  have hconcave : ConcaveOn ℝ (Ioi 0) (fun x : ℝ => Real.log (V x)) :=
    unbounded_tilted_scale_log_concavity
      X q hq W hW hnbv φ hφ hroot V hVeq
      (fun x hx => (hVdiff x hx).hasDerivAt)
  have hganti : AntitoneOn g (Ioi 0) :=
    log_derivative_antitone_of_concave_log V g hVpos hconcave hVderiv
  have hglim : Tendsto g atTop (nhds 0) :=
    unbounded_esscher_log_derivative_flatness
      X q hq W hW hnbv φ hφ hroot V hVeq hVpos hVdiff hVmono hganti
  have hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x :=
    nonnegative_of_positive_axis_antitone_tendsto_zero g hganti hglim
  obtain ⟨μ, hμnull, hμfin, hμeq⟩ :=
    atomless_positive_tail_measure_of_antitone_continuous
      g hgcont hganti hgnonneg hglim
  have hμcont : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0) :=
    hgcont.congr (fun x hx => hμeq x hx)
  have hVinterval : ∀ a b : ℝ, 0 < a → a ≤ b →
      V b = V a * Real.exp (∫ t in a..b, μ.real (Ici t)) := by
    intro a b ha hab
    have hraw :=
      interval_exponential_of_positive_log_derivative
        V g hVpos hgcont hVderiv a b ha hab
    have hintegral : (∫ t in a..b, g t) =
        ∫ t in a..b, μ.real (Ici t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le ha
        (Set.mem_Icc.mp (by simpa [uIcc_of_le hab] using ht)).1
      exact (hμeq t htpos).symm
    rwa [hintegral] at hraw
  have hWscale : ∀ x : ℝ, 0 < x →
      W x = Real.exp (φ * x) * V x := by
    intro x hx
    simp only [V, ← mul_assoc, ← Real.exp_add]
    have hh : φ * x + -(φ * x) = 0 := by ring
    rw [hh, Real.exp_zero, one_mul]
  exact ⟨φ, μ, hφ, hμnull, hμfin, hμcont,
    esscher_interval_representation_transfer
      W V φ μ hμcont hWscale hVinterval⟩
