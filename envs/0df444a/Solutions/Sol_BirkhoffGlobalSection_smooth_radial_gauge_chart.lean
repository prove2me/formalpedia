-- Prove2me | solution 1 for BirkhoffGlobalSection.smooth_radial_gauge_chart
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T18:01:37.594804+00:00
-- url     : https://prove2.me/submissions/0a6b8288-05d8-46ac-bf13-6e10d532f4ed

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff

open scoped ContDiff Topology
open BirkhoffGlobalSection Filter Set

private theorem smoothContinuousImplicitSolution
    (f : Phase × ℝ → ℝ) (r : Phase → ℝ) (u : Phase)
    (hf : ContDiffAt ℝ ∞ f (u, r u)) (hr : ContinuousAt r u)
    (hi : ((fderiv ℝ f (u, r u)).comp
      (ContinuousLinearMap.inr ℝ Phase ℝ)).IsInvertible)
    (heq : ∀ᶠ x in 𝓝 u, f (x, r x) = f (u, r u)) :
    ContDiffAt ℝ ∞ r u := by
  let ψ := hf.implicitFunction (by simp) hi
  have hψ : ContDiffAt ℝ ∞ ψ u := hf.contDiffAt_implicitFunction (by simp) hi
  have hlocal := hf.eventually_apply_eq_iff_implicitFunction (by simp) hi
  have ht : Tendsto (fun x => (x, r x)) (𝓝 u) (𝓝 (u, r u)) :=
    continuousAt_id.prodMk hr
  have hevent : r =ᶠ[𝓝 u] ψ := by
    filter_upwards [ht.eventually hlocal, heq] with x hx hroot
    exact (hx.mp hroot).symm
  exact hψ.congr_of_eventuallyEq hevent

private theorem gaugeInverse_frontier
    (B : Set Phase) (hc : Convex ℝ B) (h0 : B ∈ 𝓝 (0 : Phase))
    (hb : Bornology.IsVonNBounded ℝ B) (x : Phase) (hx : x ≠ 0) :
    (gauge B x)⁻¹ • x ∈ frontier B := by
  have hg : 0 < gauge B x := (gauge_pos (absorbent_nhds_zero h0) hb).2 hx
  apply (gauge_eq_one_iff_mem_frontier hc h0).mp
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr hg.le), smul_eq_mul,
    inv_mul_cancel₀ hg.ne']

/-- Smoothness of the gauge-radius inverse, with explicit radial transversality.
The zero-set hypothesis is only imposed on the frontier, not on the entire
Hamiltonian zero set. -/
private theorem smooth_radial_gauge_inverse
    (B : Set Phase) (hc : Convex ℝ B) (h0 : B ∈ 𝓝 (0 : Phase))
    (hb : Bornology.IsVonNBounded ℝ B) (F : Phase → ℝ)
    (hzero : ∀ y ∈ frontier B, F y = 0)
    (hsmooth : ∀ y ∈ frontier B, ContDiffAt ℝ ∞ F y)
    (hrad : ∀ y ∈ frontier B, fderiv ℝ F y y ≠ 0)
    (u : Phase) (hu : u ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u := by
  let r : Phase → ℝ := fun x => (gauge B x)⁻¹
  let y : Phase := r u • u
  have hg : 0 < gauge B u := (gauge_pos (absorbent_nhds_zero h0) hb).2 hu
  have hrpos : 0 < r u := inv_pos.mpr hg
  have hy : y ∈ frontier B := gaugeInverse_frontier B hc h0 hb u hu
  have hr : ContinuousAt r u := (continuousAt_gauge hc h0).inv₀ hg.ne'
  have hF : ContDiffAt ℝ ∞ F y := hsmooth y hy
  let f : Phase × ℝ → ℝ := fun p => F (p.2 • p.1)
  have hscale : ContDiffAt ℝ ∞ (fun p : Phase × ℝ => p.2 • p.1) (u, r u) :=
    contDiffAt_snd.smul contDiffAt_fst
  have hf : ContDiffAt ℝ ∞ f (u, r u) := hF.comp (u, r u) hscale
  have hnonzero : fderiv ℝ F y u ≠ 0 := by
    intro hz
    have := hrad y hy
    apply this
    change fderiv ℝ F y (r u • u) = 0
    simp [hz]
  have hdscale := (hasFDerivAt_snd (𝕜 := ℝ) (p := (u, r u))).smul
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (u, r u)))
  have hdf := (hF.differentiableAt (by simp)).hasFDerivAt.comp (u, r u) hdscale
  change HasFDerivAt f _ (u, r u) at hdf
  have hrestrict : (fderiv ℝ f (u, r u)).comp (ContinuousLinearMap.inr ℝ Phase ℝ) =
      (fderiv ℝ F y u) • ContinuousLinearMap.id ℝ ℝ := by
    rw [hdf.fderiv]
    ext
    simp [mul_comm]
  have hi : ((fderiv ℝ f (u, r u)).comp
      (ContinuousLinearMap.inr ℝ Phase ℝ)).IsInvertible := by
    rw [hrestrict]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (fderiv ℝ F y u)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [hnonzero]
    · ext
      simp [hnonzero]
  have heq : ∀ᶠ x in 𝓝 u, f (x, r x) = f (u, r u) := by
    have hne : ∀ᶠ x in 𝓝 u, x ≠ 0 := isOpen_compl_singleton.mem_nhds hu
    filter_upwards [hne] with x hx
    change F ((gauge B x)⁻¹ • x) = F y
    rw [hzero _ (gaugeInverse_frontier B hc h0 hb x hx), hzero y hy]
  have hrsmooth : ContDiffAt ℝ ∞ r u := smoothContinuousImplicitSolution f r u hf hr hi heq
  exact hrsmooth.smul contDiffAt_id

private theorem squaredRadius_pos (y : Phase) (hy : y ≠ 0) :
    0 < zNormSq y + wNormSq y := by
  by_contra hn
  have hle : zNormSq y + wNormSq y ≤ 0 := le_of_not_gt hn
  unfold zNormSq wNormSq at hle
  apply hy
  ext i
  fin_cases i <;> dsimp <;>
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg (y 3)]

private theorem squaredRadius_smul (a : ℝ) (y : Phase) :
    zNormSq (a • y) + wNormSq (a • y) = a ^ 2 * (zNormSq y + wNormSq y) := by
  simp [zNormSq, wNormSq]
  ring

/-- Full smooth radial chart between a convex body's frontier and the coordinate
Euclidean sphere, assuming a smooth frontier-defining Hamiltonian with nonzero
radial derivative. The inverse is the explicit gauge-radius map. -/
theorem solution
    (B : Set Phase) (hc : Convex ℝ B) (h0 : B ∈ 𝓝 (0 : Phase))
    (hb : Bornology.IsVonNBounded ℝ B) (F : Phase → ℝ)
    (hzero : ∀ y ∈ frontier B, F y = 0)
    (hsmooth : ∀ y ∈ frontier B, ContDiffAt ℝ ∞ F y)
    (hrad : ∀ y ∈ frontier B, fderiv ℝ F y y ≠ 0) :
    let G : Phase → Phase := fun u => (gauge B u)⁻¹ • u
    (∀ y ∈ frontier B,
      ContDiffAt ℝ ∞ radialNormalize y ∧ radialNormalize y ∈ unitThreeSphere ∧
        G (radialNormalize y) = y) ∧
    (∀ u ∈ unitThreeSphere,
      ContDiffAt ℝ ∞ G u ∧ G u ∈ frontier B ∧ radialNormalize (G u) = u) := by
  dsimp only
  constructor
  · intro y hy
    have hgy : gauge B y = 1 := (gauge_eq_one_iff_mem_frontier hc h0).mpr hy
    have hyne : y ≠ 0 := by
      intro h
      simp [h] at hgy
    have hQ := squaredRadius_pos y hyne
    obtain ⟨hs, hn, _, _⟩ := radial_normalization_contact_identity y hQ
    refine ⟨hs, hn, ?_⟩
    have hsqrt : Real.sqrt (zNormSq y + wNormSq y) ≠ 0 :=
      (Real.sqrt_pos.mpr hQ).ne'
    unfold radialNormalize
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), smul_eq_mul,
      hgy, mul_one, inv_inv, smul_smul, mul_inv_cancel₀ hsqrt, one_smul]
  · intro u hu
    have huQ : zNormSq u + wNormSq u = 1 := hu
    have hune : u ≠ 0 := by
      intro h
      simp [h, zNormSq, wNormSq] at huQ
    have hg : 0 < gauge B u := (gauge_pos (absorbent_nhds_zero h0) hb).mpr hune
    refine ⟨smooth_radial_gauge_inverse B hc h0 hb F hzero hsmooth hrad u hune,
      gaugeInverse_frontier B hc h0 hb u hune, ?_⟩
    unfold radialNormalize
    rw [squaredRadius_smul, huQ, mul_one, Real.sqrt_sq (inv_nonneg.mpr hg.le),
      smul_smul, inv_mul_cancel₀ (inv_ne_zero hg.ne'), one_smul]
