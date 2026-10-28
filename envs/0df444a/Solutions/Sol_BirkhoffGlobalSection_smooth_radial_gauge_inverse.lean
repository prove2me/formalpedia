-- Prove2me | solution 1 for BirkhoffGlobalSection.smooth_radial_gauge_inverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:22:58.485448+00:00
-- url     : https://prove2.me/submissions/5cf4ab9e-734b-4311-a38c-f2ebc8a441c1

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff

import Theorems.Thm_ImplicitCalculus_contDiffAt_continuous_solution
import Theorems.Thm_ConvexAnalysis_gauge_radius_frontier
import Theorems.Thm_ConvexAnalysis_gauge_radius_frontier
open scoped ContDiff Topology
open BirkhoffGlobalSection Filter Set


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    (B : Set Phase) (hc : Convex ℝ B) (h0 : B ∈ 𝓝 (0 : Phase))
    (hb : Bornology.IsVonNBounded ℝ B) (F : Phase → ℝ)
    (hzero : ∀ y ∈ frontier B, F y = 0)
    (hsmooth : ∀ y ∈ frontier B, ContDiffAt ℝ ∞ F y)
    (hrad : ∀ y ∈ frontier B, fderiv ℝ F y y ≠ 0)
    (u : Phase) (hu : u ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u := by
  set r : Phase → ℝ := fun x => (gauge B x)⁻¹ with hr_def
  have hfr : ∀ x : Phase, x ≠ 0 → r x • x ∈ frontier B := fun x hx =>
    ConvexAnalysis.gauge_radius_frontier B hc h0 hb x hx
  have hp := hfr u hu
  set p : Phase := r u • u with hp_def
  let f : Phase × ℝ → ℝ := fun q => F (q.2 • q.1)
  have hgu : gauge B u ≠ 0 := by
    intro h
    have : p = 0 := by simp [hp_def, hr_def, h]
    rw [this] at hp
    have hi : (0 : Phase) ∈ interior B := mem_interior_iff_mem_nhds.mpr h0
    exact hp.2 hi
  have hf : ContDiffAt ℝ ∞ f (u, r u) := by
    have h1 : ContDiffAt ℝ ∞ (fun q : Phase × ℝ => q.2 • q.1) (u, r u) :=
      contDiffAt_snd.smul contDiffAt_fst
    exact (hsmooth p hp).comp (u, r u) h1
  have hrc : ContinuousAt r u :=
    ((continuous_gauge hc h0).continuousAt).inv₀ hgu
  have hD : HasFDerivAt f ((fderiv ℝ F p).comp
      ((r u) • ContinuousLinearMap.fst ℝ Phase ℝ +
        (ContinuousLinearMap.snd ℝ Phase ℝ).smulRight u)) (u, r u) := by
    have h1 : HasFDerivAt (fun q : Phase × ℝ => q.2 • q.1)
        ((r u) • ContinuousLinearMap.fst ℝ Phase ℝ +
          (ContinuousLinearMap.snd ℝ Phase ℝ).smulRight u) (u, r u) :=
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (u, r u)) (E := Phase) (F := ℝ)).smul
        (hasFDerivAt_fst (𝕜 := ℝ) (p := (u, r u)) (E := Phase) (F := ℝ))
    exact ((hsmooth p hp).differentiableAt (by simp)).hasFDerivAt.comp (u, r u) h1
  have hc0 : fderiv ℝ F p u ≠ 0 := by
    intro h
    apply hrad p hp
    rw [hp_def, map_smul, h, smul_zero]
  have hi : ((fderiv ℝ f (u, r u)).comp
      (ContinuousLinearMap.inr ℝ Phase ℝ)).IsInvertible := by
    rw [hD.fderiv]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hc0), ?_⟩
    apply ContinuousLinearMap.ext_ring
    simp
  have heq : ∀ᶠ x in 𝓝 u, f (x, r x) = f (u, r u) := by
    filter_upwards [eventually_ne_nhds hu] with x hx
    show F (r x • x) = F (r u • u)
    rw [hzero _ (hfr x hx), hzero _ hp]
  have hR : ContDiffAt ℝ ∞ r u :=
    ImplicitCalculus.contDiffAt_continuous_solution (𝕜 := ℝ) ∞ (by simp) f r u hf hrc hi heq
  exact hR.smul contDiffAt_id
