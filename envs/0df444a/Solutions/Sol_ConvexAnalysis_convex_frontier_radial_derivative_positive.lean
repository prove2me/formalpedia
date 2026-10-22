-- Prove2me | solution 1 for ConvexAnalysis.convex_frontier_radial_derivative_positive
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T00:25:17.122361+00:00
-- url     : https://prove2.me/submissions/6336e31f-a0d3-4a40-a270-05017a192259

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Theorems.Thm_ConvexAnalysis_convex_frontier_radial_derivative_ne_zero
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open BirkhoffGlobalSection ConvexAnalysis Filter Set
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

private theorem local_max_second_derivative_nonpositive (f : ℝ → ℝ) (x : ℝ)
    (hmax : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hp hmax.deriv_eq_zero hc
  have heq : f =ᶠ[nhds x] (fun _ => f x) := by
    filter_upwards [hmax, hmin] with t htmax htmin
    exact le_antisymm htmax htmin
  have hz : deriv (deriv f) x = 0 := by simpa using heq.deriv.deriv_eq
  linarith

private theorem second_derivative_along_smooth_curve (F : Phase → ℝ) (γ : ℝ → Phase)
    (y v : Phase) (hγ : ContDiffAt ℝ ∞ γ 0) (hc : ContDiffAt ℝ ∞ F y)
    (hγ0 : γ 0 = y) (hγ1 : deriv γ 0 = v) :
    deriv (deriv (F ∘ γ)) 0 =
      fderiv ℝ (fun x => fderiv ℝ F x v) y v + fderiv ℝ F y (deriv (deriv γ) 0) := by
  have hdγ := (hγ.differentiableAt (by simp)).hasDerivAt
  have hdDγ := ((hγ.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hc.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hD := hDF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hdγ hγ0.symm
  have hpair := hD.clm_apply hdDγ
  have heq : deriv (F ∘ γ) =ᶠ[nhds (0 : ℝ)]
      (fun t => fderiv ℝ F (γ t) (deriv γ t)) := by
    have ht : Tendsto γ (nhds 0) (nhds y) := by simpa [hγ0] using hγ.continuousAt.tendsto
    have hγone : ContDiffAt ℝ 1 γ 0 := hγ.of_le (mod_cast le_top)
    have hFone : ContDiffAt ℝ 1 F y := hc.of_le (mod_cast le_top)
    filter_upwards [hγone.eventually (by norm_num),
      ht.eventually (hFone.eventually (by norm_num))] with t htγ htF
    exact htF.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t
      (htγ.differentiableAt_one.hasDerivAt) |>.deriv
  have hhess : fderiv ℝ (fun x => fderiv ℝ F x v) y v =
      (fderiv ℝ (fderiv ℝ F) y v) v := by
    have h := (hDF.hasFDerivAt.clm_apply (hasFDerivAt_const v y)).fderiv
    simpa using DFunLike.congr_fun h v
  simpa only [Function.comp_apply, hγ0, hγ1, hhess] using (hpair.congr_of_eventuallyEq heq).deriv

private theorem phase_has_nonzero_tangent (H : Phase →L[ℝ] ℝ) :
    ∃ v : Phase, v ≠ 0 ∧ H v = 0 := by
  let e0 : Phase := Pi.single 0 1
  let e1 : Phase := Pi.single 1 1
  by_cases h0 : H e0 = 0
  · refine ⟨e0, ?_, h0⟩
    intro hz
    have h := congrArg (fun w : Phase => w 0) hz
    simp [e0] at h
  · let v : Phase := H e0 • e1 - H e1 • e0
    refine ⟨v, ?_, ?_⟩
    · intro hz
      have h := congrArg (fun w : Phase => w 1) hz
      simp [v, e0, e1] at h
      exact h0 h
    · simp only [v, map_sub, map_smul, smul_eq_mul]
      ring

theorem solution (K : Set Phase)
    (hcompact : IsCompact K) (hK : Convex ℝ K) (h0 : (0 : Phase) ∈ interior K)
    (F : Phase → ℝ) (hzero : ∀ x ∈ frontier K, F x = 0)
    (y : Phase) (hy : y ∈ frontier K) (hc : ContDiffAt ℝ ∞ F y)
    (hregular : fderiv ℝ F y ≠ 0)
    (hcurv : ∀ v : Phase, v ≠ 0 → fderiv ℝ F y v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) y v) : 0 < fderiv ℝ F y y := by
  have hrad := convex_frontier_radial_derivative_ne_zero K hcompact hK h0 F hzero y hy hc hregular
  obtain ⟨L, hL, hs⟩ := geometric_hahn_banach_of_nonempty_interior_point hK hy.2 ⟨0, h0⟩
  have hLy := supporting_functional_positive K h0 L hL y hs
  obtain ⟨v, hvne, hv⟩ := phase_has_nonzero_tangent (fderiv ℝ F y)
  have hLv : L v = 0 := frontier_tangent_kernel_le_support_kernel K hK h0
    (hcompact.isVonNBounded ℝ) F hzero y hy hc hrad L
    (fun x hx => hs x (hcompact.isClosed.closure_subset hx.1)) v hv
  let q : ℝ → Phase := fun t => y + t • v
  let r : ℝ → ℝ := fun t => (gauge K (q t))⁻¹
  let γ : ℝ → Phase := fun t => r t • q t
  have h0n := mem_interior_iff_mem_nhds.mp h0
  have hq0 : q 0 = y := by simp [q]
  have hq (t : ℝ) : HasDerivAt q v t := by
    convert (hasDerivAt_const t y).add ((hasDerivAt_id t).smul_const v) using 1 <;>
      first | rfl | simp only [zero_add, one_smul]
  have hqc : ContDiff ℝ ∞ q := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hrc : ContDiffAt ℝ ∞ r 0 := by
    have hb : ContDiffAt ℝ ∞ (fun x => (gauge K x)⁻¹) (q 0) := by
      simpa only [hq0] using smooth_gauge_radius_at K hK h0n
        (hcompact.isVonNBounded ℝ) F hzero y hy hc hrad
    exact hb.comp 0 hqc.contDiffAt
  have hr0 : r 0 = 1 := by
    simp [r, hq0, (gauge_eq_one_iff_mem_frontier hK h0n).mpr hy]
  have hγc : ContDiffAt ℝ ∞ γ 0 := hrc.smul hqc.contDiffAt
  have hγ0 : γ 0 = y := by simp [γ, hr0, hq0]
  have hyne : y ≠ 0 := by intro hz; exact hrad (by simp [hz])
  have hqne : ∀ᶠ t in nhds (0 : ℝ), q t ≠ 0 := by
    have ht : Tendsto q (nhds 0) (nhds y) := by
      simpa only [hq0] using hqc.continuous.continuousAt.tendsto (x := (0 : ℝ))
    exact ht.eventually (isOpen_compl_singleton.mem_nhds hyne)
  have hroot : (F ∘ γ) =ᶠ[nhds (0 : ℝ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hqne] with t ht
    exact hzero _ (gauge_radius_frontier K hK h0n (hcompact.isVonNBounded ℝ) (q t) ht)
  have hrfirst := (hrc.differentiableAt (by simp)).hasDerivAt
  have hγfirst := hrfirst.smul (hq 0)
  change HasDerivAt γ _ 0 at hγfirst
  have hFpoint : DifferentiableAt ℝ F (γ 0) := by simpa [hγ0] using hc.differentiableAt (by simp)
  have hfirstzero : deriv (F ∘ γ) 0 = 0 := by simpa using hroot.deriv_eq
  have hr1 : deriv r 0 = 0 := by
    have h := (hFpoint.hasFDerivAt.comp_hasDerivAt 0 hγfirst).deriv
    simp only [hfirstzero, hγ0, hq0, hr0, one_smul, map_add, map_smul, hv,
      smul_eq_mul, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hrad
  have hγ1 : deriv γ 0 = v := by simpa [hq0, hr0, hr1] using hγfirst.deriv
  have hrmax : IsLocalMax r 0 := by
    filter_upwards [hqne] with t ht
    have h := hs (γ t)
      (hcompact.isClosed.closure_subset
        (gauge_radius_frontier K hK h0n (hcompact.isVonNBounded ℝ) (q t) ht).1)
    have he : L (γ t) = r t * L y := by simp [γ, q, map_smul, map_add, hLv]
    rw [he] at h
    change r t ≤ r 0
    rw [hr0]
    nlinarith
  have hr2 : deriv (deriv r) 0 ≤ 0 := local_max_second_derivative_nonpositive r 0 hrmax hrc.continuousAt
  have hdDr := ((hrc.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hγderiv : deriv γ =ᶠ[nhds (0 : ℝ)]
      (fun t => deriv r t • q t + r t • v) := by
    have hrone : ContDiffAt ℝ 1 r 0 := hrc.of_le (mod_cast le_top)
    filter_upwards [hrone.eventually (by norm_num)] with t ht
    change deriv (r • q) t = _
    simpa only [add_comm] using (ht.differentiableAt_one.hasDerivAt.smul (hq t)).deriv
  have hγ2 : deriv (deriv γ) 0 = deriv (deriv r) 0 • y := by
    have h := ((hdDr.smul (hq 0)).add (hrfirst.smul_const v)).congr_of_eventuallyEq hγderiv
    simpa [hr1, hq0] using h.deriv
  have hsecondzero : deriv (deriv (F ∘ γ)) 0 = 0 := by simpa using hroot.deriv.deriv_eq
  have hsecond := second_derivative_along_smooth_curve F γ y v hγc hc hγ0 hγ1
  rw [hsecondzero, hγ2, map_smul, smul_eq_mul] at hsecond
  have hpos := hcurv v hvne hv
  by_contra hn
  have hnonpos : fderiv ℝ F y y ≤ 0 := le_of_not_gt hn
  have hp : 0 ≤ deriv (deriv r) 0 * fderiv ℝ F y y := mul_nonneg_of_nonpos_of_nonpos hr2 hnonpos
  linarith
