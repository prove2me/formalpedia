-- Prove2me | solution 1 for FiniteEnergyPlane.charField_div_eq_omega0
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T21:22:08.925219+00:00
-- url     : https://prove2.me/submissions/929f84d1-0a9a-45ce-9df9-2dd4dfa91ac9

import Definitions.Def_FiniteEnergyPlane_SpanningDisk
import Mathlib



/-! Child C of P c5a21fab: `charField_div_eq_omega0`. -/

namespace FiniteEnergyPlane

open scoped ContDiff

theorem olpc_j0_add (x y : V 1) : j0 (x + y) = j0 x + j0 y := by
  funext k; simp only [j0, Pi.add_apply]; split_ifs <;> ring

theorem olpc_j0_smul (a : ℝ) (x : V 1) : j0 (a • x) = a • j0 x := by
  funext k; simp only [j0, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

theorem olpc_om_add_left (x y v : V 1) : omega0 (x + y) v = omega0 x v + omega0 y v := by
  simp only [omega0, olpc_j0_add, dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem olpc_om_smul_left (a : ℝ) (x v : V 1) : omega0 (a • x) v = a * omega0 x v := by
  simp only [omega0, olpc_j0_smul, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem olpc_om_add_right (x v w : V 1) : omega0 x (v + w) = omega0 x v + omega0 x w := by
  simp only [omega0, dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem olpc_om_smul_right (a : ℝ) (x v : V 1) : omega0 x (a • v) = a * omega0 x v := by
  simp only [omega0, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem olpc_om_anti (u v : V 1) : omega0 u v = -omega0 v u := by
  simp only [omega0, dot, j0, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  ring

/-- `v ↦ omega0 x v` as a continuous linear functional. -/
noncomputable def olpcOmR (x : V 1) : V 1 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => omega0 x v
      map_add' := fun v w => olpc_om_add_right x v w
      map_smul' := fun a v => olpc_om_smul_right a x v }

/-- `x ↦ (v ↦ omega0 x v)` as a continuous linear map. -/
noncomputable def olpcOm : V 1 →L[ℝ] V 1 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := olpcOmR
      map_add' := fun x y => by
        ext v; simp [olpcOmR, olpc_om_add_left]
      map_smul' := fun a x => by
        ext v; simp [olpcOmR, olpc_om_smul_left] }

theorem olpcOm_apply (x v : V 1) : olpcOm x v = omega0 x v := rfl

theorem olpc_hasFDerivAt_liou (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (w z : ℂ) :
    HasFDerivAt (fun z => omega0 (e z) (fderiv ℝ e z w))
      ((olpcOm (e z)).comp ((fderiv ℝ (fderiv ℝ e) z).flip w) +
        (olpcOm.comp (fderiv ℝ e z)).flip (fderiv ℝ e z w)) z := by
  have hd1 : Differentiable ℝ e := he.differentiable (by simp)
  have hd2 : Differentiable ℝ (fderiv ℝ e) :=
    (he.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have hc : HasFDerivAt (fun z => olpcOm (e z)) (olpcOm.comp (fderiv ℝ e z)) z :=
    olpcOm.hasFDerivAt.comp z (hd1 z).hasFDerivAt
  have hu : HasFDerivAt (fun z => fderiv ℝ e z w) ((fderiv ℝ (fderiv ℝ e) z).flip w) z := by
    have := (hd2 z).hasFDerivAt.clm_apply (hasFDerivAt_const w z)
    refine this.congr_fderiv ?_
    ext v; simp
  exact hc.clm_apply hu

theorem charField_div_eq_omega0_aux (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z : ℂ) :
    (fderiv ℝ (charField e) z 1).re + (fderiv ℝ (charField e) z Complex.I).im =
      omega0 (ds e z) (dt e z) := by
  have hdiff : Differentiable ℝ (charField e) := by
    have h : charField e = fun z => ((liouville (e z) (fderiv ℝ e z Complex.I) : ℝ) : ℂ) +
        ((-liouville (e z) (fderiv ℝ e z 1) : ℝ) : ℂ) * Complex.I := by
      funext z; apply Complex.ext <;> simp [charField, ds, dt]
    rw [h]
    have hl : ∀ w, Differentiable ℝ (fun z => liouville (e z) (fderiv ℝ e z w)) := by
      intro w z
      have h := (olpc_hasFDerivAt_liou e he w z).differentiableAt
      have h2 := h.mul_const (2⁻¹ : ℝ)
      unfold liouville
      simpa [div_eq_mul_inv] using h2
    exact ((Complex.ofRealCLM.differentiable.comp (hl _))).add
      ((Complex.ofRealCLM.differentiable.comp (hl _).neg).mul (differentiable_const _))
  have hre : HasFDerivAt (fun z => (charField e z).re)
      (Complex.reCLM.comp (fderiv ℝ (charField e) z)) z :=
    Complex.reCLM.hasFDerivAt.comp z (hdiff z).hasFDerivAt
  have him : HasFDerivAt (fun z => (charField e z).im)
      (Complex.imCLM.comp (fderiv ℝ (charField e) z)) z :=
    Complex.imCLM.hasFDerivAt.comp z (hdiff z).hasFDerivAt
  have hre' : HasFDerivAt (fun z => (charField e z).re)
      ((1 / 2 : ℝ) • ((olpcOm (e z)).comp ((fderiv ℝ (fderiv ℝ e) z).flip Complex.I) +
        (olpcOm.comp (fderiv ℝ e z)).flip (fderiv ℝ e z Complex.I))) z := by
    have hfe : (fun z => (charField e z).re) =
        fun z => (1 / 2 : ℝ) • omega0 (e z) (fderiv ℝ e z Complex.I) := by
      funext z; simp [charField, liouville, dt]; ring
    rw [hfe]
    exact (olpc_hasFDerivAt_liou e he Complex.I z).const_smul (1 / 2 : ℝ)
  have him' : HasFDerivAt (fun z => (charField e z).im)
      (-((1 / 2 : ℝ) • ((olpcOm (e z)).comp ((fderiv ℝ (fderiv ℝ e) z).flip 1) +
        (olpcOm.comp (fderiv ℝ e z)).flip (fderiv ℝ e z 1)))) z := by
    have hfe : (fun z => (charField e z).im) =
        fun z => -((1 / 2 : ℝ) • omega0 (e z) (fderiv ℝ e z 1)) := by
      funext z; simp [charField, liouville, ds]; ring
    rw [hfe]
    exact ((olpc_hasFDerivAt_liou e he 1 z).const_smul (1 / 2 : ℝ)).neg
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) (hre.unique hre')
  have h2 := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) (him.unique him')
  change (fderiv ℝ (charField e) z 1).re = _ at h1
  change (fderiv ℝ (charField e) z Complex.I).im = _ at h2
  rw [h1, h2]
  have hsymm : fderiv ℝ (fderiv ℝ e) z 1 Complex.I = fderiv ℝ (fderiv ℝ e) z Complex.I 1 :=
    (he.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) 1 Complex.I
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.neg_apply,
    olpcOm_apply, smul_eq_mul, hsymm]
  rw [olpc_om_anti (fderiv ℝ e z Complex.I) (fderiv ℝ e z 1)]
  simp only [ds, dt]
  ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z : ℂ) :
    (fderiv ℝ (charField e) z 1).re + (fderiv ℝ (charField e) z Complex.I).im =
      omega0 (ds e z) (dt e z) :=
  charField_div_eq_omega0_aux e he z
