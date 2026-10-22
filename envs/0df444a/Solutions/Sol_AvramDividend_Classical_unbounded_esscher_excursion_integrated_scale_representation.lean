-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_esscher_excursion_integrated_scale_representation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T22:33:41.976357+00:00
-- url     : https://prove2.me/submissions/72b193db-5cab-4abd-b286-08a6b279bfff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_ratio_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
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

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-!
Reduce the unbounded-variation excursion-integral theorem to the independent
Esscher ratio, tilted regularity, log-concavity and flat-tail obligations.
The flat-tail theorem is undergoing coordinator-owned publication.
-/
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
  obtain ⟨φ, hφ, hroot, hratio⟩ :=
    unbounded_esscher_ratio_bound X q hq W hW hnbv
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x
  have hVeq : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x :=
    fun _ _ => rfl
  have hWpos : ∀ x : ℝ, 0 < x → 0 < W x :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  have hVpos : ∀ x : ℝ, 0 < x → 0 < V x := by
    intro x hx
    exact mul_pos (Real.exp_pos _) (hWpos x hx)
  have hVone : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) :=
    unbounded_tilted_scale_absolute_continuity X q hq W hW hnbv φ hφ hroot V hVeq
  have hVdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ V x :=
    fun x hx => (hVone.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt_one
  have hdecay : ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp ((-φ) * (y - x)) * W y := by
    intro x y hx hxy
    simpa only [neg_mul] using
      (div_le_iff₀ (hWpos y (lt_of_lt_of_le hx hxy))).mp (hratio x y hx hxy)
  have hVmono : MonotoneOn V (Ioi (0 : ℝ)) := by
    simpa only [V, neg_mul] using
      (exit_decay_implies_tilted_monotone W φ hdecay)
  let g : ℝ → ℝ := fun x => deriv (fun y : ℝ => Real.log (V y)) x
  have hgcont : ContinuousOn g (Ioi (0 : ℝ)) :=
    continuous_log_derivative_of_positive_C1 V hVpos hVone
  have hVderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (V x * g x) x := by
    intro x hx
    have hv : V x ≠ 0 := (hVpos x hx).ne'
    have hd := (hVdiff x hx).hasDerivAt
    have hlog : deriv (fun y : ℝ => Real.log (V y)) x = deriv V x / V x :=
      (hd.log hv).deriv
    have heq : deriv V x = V x * g x := by
      calc
        deriv V x = V x * (deriv V x / V x) := by field_simp [hv]
        _ = V x * g x := by rw [← hlog]
    rw [← heq]
    exact hd
  have hconcave : ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) :=
    unbounded_tilted_scale_log_concavity X q hq W hW hnbv φ hφ hroot
      V hVeq (fun x hx => (hVdiff x hx).hasDerivAt)
  have hganti : AntitoneOn g (Ioi (0 : ℝ)) :=
    log_derivative_antitone_of_concave_log V g hVpos hconcave hVderiv
  have hglim : Tendsto g atTop (nhds (0 : ℝ)) :=
    unbounded_esscher_log_derivative_flatness X q hq W hW hnbv φ hφ hroot
      V hVeq hVpos hVdiff hVmono hganti
  have hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x :=
    nonnegative_of_positive_axis_antitone_tendsto_zero g hganti hglim
  obtain ⟨μ, hμnull, hμfin, hμeq⟩ :=
    atomless_positive_tail_measure_of_antitone_continuous
      g hgcont hganti hgnonneg hglim
  have hμcont : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0) := by
    exact hgcont.congr (fun x hx => hμeq x hx)
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
      have htIcc : t ∈ Icc a b := by
        simpa [uIcc_of_le hab] using ht
      exact (hμeq t (lt_of_lt_of_le ha htIcc.1)).symm
    rw [hintegral] at hraw
    exact hraw
  have hWscale : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x := by
    intro x hx
    simp [V, ← mul_assoc, ← Real.exp_add]
  have hWinterval :=
    esscher_interval_representation_transfer W V φ μ hμcont hWscale hVinterval
  exact ⟨φ, μ, hφ, hμnull, hμfin, hμcont, hWinterval⟩
