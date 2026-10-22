-- Prove2me | solution 1 for ConvexAnalysis.convex_frontier_radial_derivative_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T00:11:45.113187+00:00
-- url     : https://prove2.me/submissions/a05a0cb6-9eb9-4499-99ba-1390d197d79f

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation

open BirkhoffGlobalSection Filter Set
open scoped ContDiff Topology

private theorem supporting_functional_positive (K : Set Phase)
    (h0 : (0 : Phase) ∈ interior K) (L : Phase →L[ℝ] ℝ) (hL : L ≠ 0)
    (y : Phase) (hsupport : ∀ x ∈ K, L x ≤ L y) : 0 < L y := by
  have hnonneg : 0 ≤ L y := by simpa using hsupport 0 (interior_subset h0)
  have hne : L y ≠ 0 := by
    intro heq
    have hmax : IsLocalMax L 0 := by
      filter_upwards [mem_interior_iff_mem_nhds.mp h0] with x hx
      simpa only [map_zero, heq] using hsupport x hx
    exact hL (hmax.hasFDerivAt_eq_zero L.hasFDerivAt)
  exact lt_of_le_of_ne hnonneg hne.symm

private theorem gauge_radius_frontier (K : Set Phase) (hK : Convex ℝ K)
    (h0 : K ∈ nhds (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ K)
    (x : Phase) (hx : x ≠ 0) : (gauge K x)⁻¹ • x ∈ frontier K := by
  have hg : 0 < gauge K x := (gauge_pos (absorbent_nhds_zero h0) hb).2 hx
  apply (gauge_eq_one_iff_mem_frontier hK h0).mp
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr hg.le), smul_eq_mul,
    inv_mul_cancel₀ hg.ne']

private theorem smooth_gauge_radius_at (K : Set Phase) (hK : Convex ℝ K)
    (h0 : K ∈ nhds (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ K)
    (F : Phase → ℝ) (hzero : ∀ x ∈ frontier K, F x = 0)
    (u : Phase) (hu : u ∈ frontier K) (hc : ContDiffAt ℝ ∞ F u)
    (hrad : fderiv ℝ F u u ≠ 0) :
    ContDiffAt ℝ ∞ (fun x => (gauge K x)⁻¹) u := by
  let r : Phase → ℝ := fun x => (gauge K x)⁻¹
  have hgu : gauge K u = 1 := (gauge_eq_one_iff_mem_frontier hK h0).mpr hu
  have hru : r u = 1 := by simp [r, hgu]
  have hune : u ≠ 0 := by
    intro heq
    exact hrad (by simp [heq])
  have hr : ContinuousAt r u := (continuousAt_gauge hK h0).inv₀ (by simp [hgu])
  let f : Phase × ℝ → ℝ := fun p => F (p.2 • p.1)
  have hcscale : ContDiffAt ℝ ∞ F (r u • u) := by simpa [hru] using hc
  have hf : ContDiffAt ℝ ∞ f (u, r u) := by
    exact hcscale.comp (u, r u) (contDiffAt_snd.smul contDiffAt_fst)
  have hdscale := (hasFDerivAt_snd (𝕜 := ℝ) (p := (u, r u))).smul
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (u, r u)))
  have hc' : DifferentiableAt ℝ F (r u • u) := by
    simpa only [hru, one_smul] using hc.differentiableAt (by simp)
  have hdf := hc'.hasFDerivAt.comp (u, r u) hdscale
  change HasFDerivAt f _ (u, r u) at hdf
  have hrestrict : (fderiv ℝ f (u, r u)).comp
      (ContinuousLinearMap.inr ℝ Phase ℝ) =
      (fderiv ℝ F u u) • ContinuousLinearMap.id ℝ ℝ := by
    rw [hdf.fderiv]
    ext
    simp [hru, mul_comm]
  have hi : ((fderiv ℝ f (u, r u)).comp
      (ContinuousLinearMap.inr ℝ Phase ℝ)).IsInvertible := by
    rw [hrestrict]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (fderiv ℝ F u u)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [hrad]
    · ext
      simp [hrad]
  let ψ := hf.implicitFunction (by simp) hi
  have hψ : ContDiffAt ℝ ∞ ψ u := hf.contDiffAt_implicitFunction (by simp) hi
  have hlocal := hf.eventually_apply_eq_iff_implicitFunction (by simp) hi
  have ht : Tendsto (fun x => (x, r x)) (nhds u) (nhds (u, r u)) :=
    continuousAt_id.prodMk hr
  have heq : r =ᶠ[nhds u] ψ := by
    filter_upwards [ht.eventually hlocal, isOpen_compl_singleton.mem_nhds hune] with x hx hxne
    apply (hx.mp ?_).symm
    change F ((gauge K x)⁻¹ • x) = F (r u • u)
    rw [hzero _ (gauge_radius_frontier K hK h0 hb x hxne), hru, one_smul, hzero u hu]
  exact hψ.congr_of_eventuallyEq heq

private theorem frontier_tangent_kernel_le_support_kernel (K : Set Phase)
    (hK : Convex ℝ K) (h0 : (0 : Phase) ∈ interior K)
    (hb : Bornology.IsVonNBounded ℝ K) (F : Phase → ℝ)
    (hzero : ∀ x ∈ frontier K, F x = 0) (u : Phase) (hu : u ∈ frontier K)
    (hc : ContDiffAt ℝ ∞ F u) (hrad : fderiv ℝ F u u ≠ 0)
    (L : Phase →L[ℝ] ℝ) (hsupport : ∀ x ∈ frontier K, L x ≤ L u) :
    ∀ v : Phase, fderiv ℝ F u v = 0 → L v = 0 := by
  let r : Phase → ℝ := fun x => (gauge K x)⁻¹
  have h0n := mem_interior_iff_mem_nhds.mp h0
  have hru : r u = 1 := by
    simp [r, (gauge_eq_one_iff_mem_frontier hK h0n).mpr hu]
  have hune : u ≠ 0 := by
    intro heq
    exact hrad (by simp [heq])
  have hr : DifferentiableAt ℝ r u :=
    (smooth_gauge_radius_at K hK h0n hb F hzero u hu hc hrad).differentiableAt (by simp)
  have hG := hr.hasFDerivAt.smul (hasFDerivAt_id (𝕜 := ℝ) u)
  change HasFDerivAt (fun x : Phase => r x • x) _ u at hG
  have hFdiff : DifferentiableAt ℝ F (r u • u) := by
    simpa [hru] using hc.differentiableAt (by simp)
  have hroot : (fun x => F (r x • x)) =ᶠ[nhds u] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hune] with x hx
    exact hzero _ (gauge_radius_frontier K hK h0n hb x hx)
  have hH := (hFdiff.hasFDerivAt.comp u (f := fun x : Phase => r x • x) hG).unique
    ((hasFDerivAt_const (0 : ℝ) u).congr_of_eventuallyEq hroot)
  have hmax : IsLocalMax (fun x => L (r x • x)) u := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hune] with x hx
    simpa [hru] using hsupport _ (gauge_radius_frontier K hK h0n hb x hx)
  have hL := hmax.hasFDerivAt_eq_zero
    (L.hasFDerivAt.comp u (f := fun x : Phase => r x • x) hG)
  intro v hv
  have hfirst : (fderiv ℝ r u v) * (fderiv ℝ F u u) = 0 := by
    simpa [hru, hv] using DFunLike.congr_fun hH v
  have ha : fderiv ℝ r u v = 0 := (mul_eq_zero.mp hfirst).resolve_right hrad
  simpa [hru, ha] using DFunLike.congr_fun hL v

private theorem exists_transverse_interior_center (K : Set Phase)
    (h0 : (0 : Phase) ∈ interior K) (H : Phase →L[ℝ] ℝ) (hH : H ≠ 0)
    (y : Phase) : ∃ z ∈ interior K, H (y - z) ≠ 0 := by
  by_contra! hn
  have hyzero : H y = 0 := by simpa using hn 0 h0
  have hmax : IsLocalMax H 0 := by
    filter_upwards [isOpen_interior.mem_nhds h0] with z hz
    have hz0 : H z = 0 := by
      have h := hn z hz
      rw [map_sub, hyzero] at h
      linarith
    simp only [hz0, map_zero, le_refl]
  exact hH (hmax.hasFDerivAt_eq_zero H.hasFDerivAt)

theorem solution (K : Set Phase)
    (hcompact : IsCompact K) (hK : Convex ℝ K) (h0 : (0 : Phase) ∈ interior K)
    (F : Phase → ℝ) (hzero : ∀ x ∈ frontier K, F x = 0)
    (y : Phase) (hy : y ∈ frontier K) (hc : ContDiffAt ℝ ∞ F y)
    (hregular : fderiv ℝ F y ≠ 0) : fderiv ℝ F y y ≠ 0 := by
  obtain ⟨L, hL, hs⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hK hy.2 ⟨0, h0⟩
  have hLy : 0 < L y := supporting_functional_positive K h0 L hL y hs
  obtain ⟨z, hz, htransverse⟩ := exists_transverse_interior_center K h0
    (fderiv ℝ F y) hregular y
  let e : Phase ≃ₜ Phase := Homeomorph.addLeft z
  let B : Set Phase := e ⁻¹' K
  let u : Phase := y - z
  let G : Phase → ℝ := fun x => F (z + x)
  have hBconvex : Convex ℝ B := hK.translate_preimage_right z
  have hBcompact : IsCompact B := e.isCompact_preimage.mpr hcompact
  have hB0 : (0 : Phase) ∈ interior B := by
    rw [show B = e ⁻¹' K from rfl, ← e.preimage_interior]
    simpa [e] using hz
  have hu : u ∈ frontier B := by
    rw [show B = e ⁻¹' K from rfl, ← e.preimage_frontier]
    simpa [e, u] using hy
  have hGzero : ∀ x ∈ frontier B, G x = 0 := by
    intro x hx
    apply hzero
    have hx' : x ∈ e ⁻¹' frontier K := by
      rwa [e.preimage_frontier]
    exact hx'
  have hGsmooth : ContDiffAt ℝ ∞ G u := by
    have hFy : ContDiffAt ℝ ∞ F (z + u) := by simpa [u] using hc
    exact hFy.comp u (contDiffAt_const.add contDiffAt_id)
  have hdadd : HasFDerivAt (fun x : Phase => z + x) (ContinuousLinearMap.id ℝ Phase) u := by
    simpa using (hasFDerivAt_const z u).add (hasFDerivAt_id (𝕜 := ℝ) u)
  have hGderiv : fderiv ℝ G u = fderiv ℝ F y := by
    have hFd : DifferentiableAt ℝ F (z + u) := by
      simpa [u] using hc.differentiableAt (by simp)
    simpa [G, u, Function.comp_def] using
      (hFd.hasFDerivAt.comp u (f := fun x : Phase => z + x) hdadd).fderiv
  have hBsupport : ∀ x ∈ frontier B, L x ≤ L u := by
    intro x hx
    have hx' : z + x ∈ K := by
      have hx' : x ∈ e ⁻¹' frontier K := by rwa [e.preimage_frontier]
      exact hcompact.isClosed.closure_subset hx'.1
    have h := hs (z + x) hx'
    simp only [map_add, u, map_sub] at h ⊢
    linarith
  have hker := frontier_tangent_kernel_le_support_kernel B hBconvex hB0
    (hBcompact.isVonNBounded ℝ) G hGzero u hu hGsmooth
    (by simpa only [hGderiv, u] using htransverse) L hBsupport
  intro hrad
  have hLy0 : L y = 0 := hker y (by simpa only [hGderiv] using hrad)
  linarith
