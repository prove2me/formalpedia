-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_contact_transverse_angle_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T19:45:37.452977+00:00
-- url     : https://prove2.me/submissions/dc49ad65-fdce-443a-8335-bf8b252aec70

import Theorems.Thm_BirkhoffGlobalSection_canonical_transverse_coordinates_of_variation
import Theorems.Thm_BirkhoffGlobalSection_closed_positive_cross_gauge_conjugacy
import Theorems.Thm_BirkhoffGlobalSection_radial_gradient_frame_comparison
import Theorems.Thm_BirkhoffGlobalSection_strict_convex_orbit_positive_canonical_model
import Mathlib.Tactic
open BirkhoffGlobalSection HryniewiczCriterion
open scoped ContDiff

theorem solution
    (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn G {y | IsStrictlyConvexStarShapedAt G y} x T)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G) (x t)).comp (Y t)) t)
    (v : Phase) (hv : fderiv ℝ G (x 0) v = 0)
    (hvne : transverseFrameCoordinates (TangentialHessian.grad G (x 0)) v ≠ 0)
    (θ : ℝ → ℝ) (hθc : Continuous θ)
    (hθ : ∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
      transverseFrameCoordinates (TangentialHessian.grad G (x t)) (Y t v) =
        ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)]) :
    ∃ (s : ℝ) (β a : ℝ → ℝ),
      s ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧
      IsAngleLift (canonicalTransversePath G x T Y) s β ∧
      StrictMono a ∧
      (∀ u : ℝ, a (u + 2 * Real.pi) = a u + 2 * Real.pi) ∧
      θ T - θ 0 = a (β 1) - a s := by
  have model := BirkhoffGlobalSection.strict_convex_orbit_positive_canonical_model G x T hx Y hY0 hY
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hx.2.2.1 t).continuousAt
  have hG : ∀ t, ContDiffAt ℝ 2 G (x t) := fun t => (hx.2.1 t).1.1 (x t) (by simp)
  have hr : ∀ t, 0 < fderiv ℝ G (x t) (x t) := fun t => (hx.2.1 t).2
  obtain ⟨A, hAc, hAend, hApos, hcompare⟩ :=
    BirkhoffGlobalSection.radial_gradient_frame_comparison G x T hxc hG hr hx.2.2.2
      model.symplectic model.continuous
  let φ := canonicalTransversePath G x T Y
  let z₀ : Fin 2 → ℝ := fun i => ((canonicalRadialFrame G x 0)⁻¹.mulVec (toHryn v)) i.succ.succ
  let w : ℝ → ℂ := fun t => ⟨((φ t).mulVec z₀) 0, ((φ t).mulVec z₀) 1⟩
  have hcoord : ∀ t, A (t * T) (w t) =
      (⟨transverseFrameCoordinates (TangentialHessian.grad G (x (t * T))) (Y (t * T) v) 0,
        transverseFrameCoordinates (TangentialHessian.grad G (x (t * T))) (Y (t * T) v) 1⟩ : ℂ) := by
    intro t
    have hq := BirkhoffGlobalSection.canonical_transverse_coordinates_of_variation
      G x T hx Y hY0 hY v hv model.symplectic t
    have h0 := congrFun hq.2 0
    have h1 := congrFun hq.2 1
    change ((canonicalRadialFrame G x (t * T))⁻¹.mulVec (toHryn (Y (t * T) v))) 2 = ((φ t).mulVec z₀) 0 at h0
    change ((canonicalRadialFrame G x (t * T))⁻¹.mulVec (toHryn (Y (t * T) v))) 3 = ((φ t).mulVec z₀) 1 at h1
    have he := hcompare (t * T) (Y (t * T) v) hq.1
    rw [h0, h1] at he
    exact he.symm
  have hw : ContinuousOn w (Set.Icc 0 1) := by
    have hφc : ∀ i j, ContinuousOn (fun t => φ t i j) (Set.Icc 0 1) := model.transverse_continuous
    simp only [w, Complex.mk_eq_add_mul_I, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fun_prop
  have hθ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ ρ : ℝ, 0 < ρ ∧
      A (t * T) (w t) = (ρ : ℂ) * Complex.exp ((θ (t * T) : ℂ) * Complex.I) := by
    intro t _
    obtain ⟨ρ, hρ, he⟩ := hθ (t * T)
    refine ⟨ρ, hρ, ?_⟩
    rw [hcoord t, he]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hwne : ∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≠ 0 := by
    intro t ht hz
    obtain ⟨ρ, hρ, he⟩ := hθ' t ht
    rw [hz, map_zero] at he
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne') (Complex.exp_ne_zero _)) he.symm
  have hAp : ContinuousOn (fun t => A (t * T)) (Set.Icc 0 1) :=
    (hAc.comp (continuous_id.mul_const T)).continuousOn
  have hθp : ContinuousOn (fun t => θ (t * T)) (Set.Icc 0 1) :=
    (hθc.comp (continuous_id.mul_const T)).continuousOn
  obtain ⟨s, β, a, hs, hβc, hβ0, hpolar, ha, haper, hend⟩ :=
    BirkhoffGlobalSection.closed_positive_cross_gauge_conjugacy
      (fun t => A (t * T)) hAp (by simpa using hAend)
      (fun t _ => hApos (t * T)) w hw hwne (fun t => θ (t * T)) hθp hθ'
  have hpolarR : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧
      (φ t).mulVec z₀ = r • rotationVector (β t) := by
    intro t ht
    obtain ⟨r, hr, he⟩ := hpolar t ht
    refine ⟨r, hr, ?_⟩
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    ext i; fin_cases i
    · simpa [w, rotationVector] using hre
    · simpa [w, rotationVector] using him
  obtain ⟨r₀, hr₀, hzero⟩ := hpolarR 0 ⟨le_rfl, zero_le_one⟩
  have hz₀ : z₀ = r₀ • rotationVector s := by
    simpa only [φ, model.transverse_zero, Matrix.one_mulVec, hβ0] using hzero
  refine ⟨s, β, a, hs, ⟨hβc.continuousOn, hβ0, ?_⟩, ha, haper, ?_⟩
  · intro t ht
    obtain ⟨r, hr, he⟩ := hpolarR t ht
    refine ⟨r / r₀, div_pos hr hr₀, ?_⟩
    rw [hz₀, Matrix.mulVec_smul] at he
    have he' := congrArg (fun u : Fin 2 → ℝ => r₀⁻¹ • u) he
    simpa only [smul_smul, inv_mul_cancel₀ hr₀.ne', one_smul,
      div_eq_mul_inv, mul_comm r₀⁻¹ r] using he'
  · simpa only [one_mul, zero_mul] using hend
