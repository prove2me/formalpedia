-- Prove2me | solution 1 for ContactTopology.simultaneous_global_extension_of_local_invariant_contact_forms
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T21:36:02.926801+00:00
-- url     : https://prove2.me/submissions/e8db770c-f97c-457f-96d0-4eb3b4068eaf

import Theorems.Thm_ContactCalculus_exterior_pairing_pullback

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ContactTopology.LocalExtension
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev P := Fin 2 → ℝ

def sq (x : P) : ℝ := x 0^2+x 1^2

lemma sq_smooth : ContDiff ℝ ∞ sq := by unfold sq; fun_prop
lemma sq_nonneg (x : P) : 0 ≤ sq x := by unfold sq; positivity

def radialCutoff (a b s : ℝ) : ℝ := Real.smoothTransition ((s-a^2)/(b^2-a^2))
def radialModel (R c s : ℝ) : ℝ := R/Real.sqrt (s+c)
def radialFactor (R a b c s : ℝ) : ℝ :=
  1-radialCutoff a b s+radialCutoff a b s*radialModel R c s

lemma radialCutoff_smooth (a b : ℝ) : ContDiff ℝ ∞ (radialCutoff a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma radialCutoff_range (a b s : ℝ) : 0 ≤ radialCutoff a b s ∧ radialCutoff a b s ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma radialCutoff_zero (a b s : ℝ) (hab : a^2 < b^2) (hs : s ≤ a^2) :
    radialCutoff a b s = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

lemma radialCutoff_one (a b s : ℝ) (hab : a^2 < b^2) (hs : b^2 ≤ s) :
    radialCutoff a b s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by linarith : 0 < b^2-a^2)).mpr
  linarith

lemma radialCutoff_monotone (a b : ℝ) (hab : a^2 < b^2) : Monotone (radialCutoff a b) := by
  intro s t hst
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (sub_le_sub_right hst _) (by linarith)

lemma radialCutoff_deriv_zero (a b s : ℝ) (hab : a^2 < b^2) (hs : b^2 < s) :
    deriv (radialCutoff a b) s = 0 := by
  have he : radialCutoff a b =ᶠ[𝓝 s] (fun _ => (1:ℝ)) := by
    filter_upwards [isOpen_lt continuous_const continuous_id |>.mem_nhds hs] with t ht
    exact radialCutoff_one a b t hab ht.le
  rw [he.deriv_eq]
  simp

lemma radialModel_smoothAt (R c s : ℝ) (hs : 0 < s+c) : ContDiffAt ℝ ∞ (radialModel R c) s := by
  exact contDiffAt_const.div ((contDiffAt_id.add contDiffAt_const).sqrt hs.ne')
    (Real.sqrt_pos.mpr hs).ne'

lemma radialModel_hasDerivAt (R c s : ℝ) (hs : 0 < s+c) :
    HasDerivAt (radialModel R c) (-R/(2*Real.sqrt (s+c)^3)) s := by
  have ht : Real.sqrt (s+c) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := (hasDerivAt_const s R).div
    ((Real.hasDerivAt_sqrt hs.ne').comp s ((hasDerivAt_id s).add_const c)) ht
  change HasDerivAt (radialModel R c)
    ((0*Real.sqrt (s+c)-R*(1/(2*Real.sqrt (s+c))*1))/Real.sqrt (s+c)^2) s at hd
  convert hd using 1
  field_simp [ht]
  ring

lemma radialFactor_smoothAt (R a b c s : ℝ) (hs : 0 < s+c) :
    ContDiffAt ℝ ∞ (radialFactor R a b c) s :=
  (contDiffAt_const.sub (radialCutoff_smooth a b).contDiffAt).add
    ((radialCutoff_smooth a b).contDiffAt.mul (radialModel_smoothAt R c s hs))

lemma radialFactor_hasDerivAt (R a b c s : ℝ) (hs : 0 < s+c) :
    HasDerivAt (radialFactor R a b c)
      (deriv (radialCutoff a b) s*(radialModel R c s-1)+
        radialCutoff a b s*(-R/(2*Real.sqrt (s+c)^3))) s := by
  have hdχ := ((radialCutoff_smooth a b).differentiable (by simp) s).hasDerivAt
  have hd := ((hasDerivAt_const s (1:ℝ)).sub hdχ).add
    (hdχ.mul (radialModel_hasDerivAt R c s hs))
  change HasDerivAt (radialFactor R a b c) _ s at hd
  convert hd using 1 <;> ring

lemma radialFactor_pos (R a b c s : ℝ) (hR : 0 < R) (hs : 0 < s+c) :
    0 < radialFactor R a b c s := by
  have hχ := radialCutoff_range a b s
  have hk : 0 < radialModel R c s := div_pos hR (Real.sqrt_pos.mpr hs)
  rcases eq_or_lt_of_le hχ.1 with he | hp
  · simp [radialFactor,← he]
  · exact add_pos_of_nonneg_of_pos (by linarith) (mul_pos hp hk)

lemma radialModel_ge_one (R b c s : ℝ) (hR : 0 < R) (hc : 0 < c) (hs : 0 ≤ s)
    (hsb : s ≤ b^2) (hbound : b^2+c ≤ R^2) : 1 ≤ radialModel R c s := by
  have hsc : 0 < s+c := by linarith
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hsc)).mpr
  simp only [one_mul]
  exact (Real.sqrt_le_iff).mpr ⟨hR.le,by linarith⟩

lemma radialFactor_normal_pos (R a b c s : ℝ) (hR : 0 < R) (hc : 0 < c)
    (hab : a^2 < b^2) (hbound : b^2+c ≤ R^2) (hs : 0 ≤ s) :
    0 < radialFactor R a b c s+2*s*deriv (radialFactor R a b c) s := by
  have hsc : 0 < s+c := by linarith
  have ht : 0 < Real.sqrt (s+c) := Real.sqrt_pos.mpr hsc
  have ht2 := Real.sq_sqrt hsc.le
  have hid : radialModel R c s+2*s*(-R/(2*Real.sqrt (s+c)^3)) =
      R*c/Real.sqrt (s+c)^3 := by
    unfold radialModel
    field_simp
    nlinarith [congrArg (fun z : ℝ => R*z) ht2]
  have hχ := radialCutoff_range a b s
  have hdχ : 0 ≤ deriv (radialCutoff a b) s := (radialCutoff_monotone a b hab).deriv_nonneg
  have herror : 0 ≤ 2*s*deriv (radialCutoff a b) s*(radialModel R c s-1) := by
    by_cases hsb : s ≤ b^2
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) hdχ)
        (sub_nonneg.mpr (radialModel_ge_one R b c s hR hc hs hsb hbound))
    · rw [radialCutoff_deriv_zero a b s hab (lt_of_not_ge hsb)]
      simp
  have hcore : 0 < 1-radialCutoff a b s+radialCutoff a b s*(R*c/Real.sqrt (s+c)^3) := by
    have hk : 0 < R*c/Real.sqrt (s+c)^3 := div_pos (mul_pos hR hc) (pow_pos ht 3)
    rcases eq_or_lt_of_le hχ.1 with he | hp
    · simp [← he]
    · exact add_pos_of_nonneg_of_pos (by linarith) (mul_pos hp hk)
  rw [(radialFactor_hasDerivAt R a b c s hsc).deriv]
  have heq : radialFactor R a b c s+2*s*(deriv (radialCutoff a b) s*(radialModel R c s-1)+
        radialCutoff a b s*(-R/(2*Real.sqrt (s+c)^3))) =
      (1-radialCutoff a b s+radialCutoff a b s*(R*c/Real.sqrt (s+c)^3))+
        2*s*deriv (radialCutoff a b) s*(radialModel R c s-1) := by
    rw [← hid]
    unfold radialFactor
    ring
  rw [heq]
  linarith


lemma radialFactor_inner (R a b c s : ℝ) (hab : a^2 < b^2) (hs : s ≤ a^2) :
    radialFactor R a b c s = 1 := by simp [radialFactor,radialCutoff_zero a b s hab hs]

lemma radialModel_radius_lt (R c s : ℝ) (hR : 0 < R) (hc : 0 < c) (hs : 0 ≤ s) :
    radialModel R c s*Real.sqrt s < R := by
  have ht : 0 < Real.sqrt (s+c) := Real.sqrt_pos.mpr (by linarith)
  have hlt : Real.sqrt s < Real.sqrt (s+c) := Real.sqrt_lt_sqrt hs (by linarith)
  unfold radialModel
  apply (div_mul_eq_mul_div _ _ _).trans_lt
  exact (div_lt_iff₀ ht).mpr (mul_lt_mul_of_pos_left hlt hR)

lemma radialFactor_radius_lt (R a b c s : ℝ) (hR : 0 < R) (hc : 0 < c)
    (hb : 0 ≤ b) (hbR : b < R) (hab : a^2 < b^2) (hs : 0 ≤ s) :
    radialFactor R a b c s*Real.sqrt s < R := by
  have hmodel := radialModel_radius_lt R c s hR hc hs
  by_cases hsb : s ≤ b^2
  · have hr : Real.sqrt s < R := lt_of_le_of_lt ((Real.sqrt_le_iff).mpr ⟨hb,hsb⟩) hbR
    have hχ := radialCutoff_range a b s
    have hleft : 0 ≤ (1-radialCutoff a b s)*(R-Real.sqrt s) := mul_nonneg (by linarith) (by linarith)
    have hright : 0 ≤ radialCutoff a b s*(R-radialModel R c s*Real.sqrt s) :=
      mul_nonneg hχ.1 (by linarith)
    have hsum : 0 < (1-radialCutoff a b s)*(R-Real.sqrt s)+
        radialCutoff a b s*(R-radialModel R c s*Real.sqrt s) := by
      rcases eq_or_lt_of_le hχ.1 with he | hp
      · simp only [← he,sub_zero,one_mul,zero_mul,add_zero]
        linarith
      · exact add_pos_of_nonneg_of_pos hleft (mul_pos hp (by linarith))
    unfold radialFactor
    nlinarith
  · simpa [radialFactor,radialCutoff_one a b s hab (le_of_not_ge hsb)] using hmodel

lemma radialFactor_ge_one_inner (R a b c s : ℝ) (hR : 0 < R) (hc : 0 < c)
    (hs : 0 ≤ s) (hsb : s ≤ b^2) (hbound : b^2+c ≤ R^2) :
    1 ≤ radialFactor R a b c s := by
  have hχ := (radialCutoff_range a b s).1
  have hk := radialModel_ge_one R b c s hR hc hs hsb hbound
  have hh := mul_nonneg hχ (sub_nonneg.mpr hk)
  unfold radialFactor
  nlinarith

lemma radialFactor_outside_unit (R a b c s : ℝ) (hR : 1 < R) (hb : 1 < b)
    (hab : a^2 < b^2) (hc : 0 < c) (hbound : b^2+c ≤ R^2) (hs : 1 < s) :
    1 < radialFactor R a b c s^2*s := by
  have hR0 : 0 < R := by linarith
  have hb0 : 0 < b := by linarith
  have hs0 : 0 ≤ s := by linarith
  by_cases hsb : s ≤ b^2
  · have hh := radialFactor_ge_one_inner R a b c s hR0 hc hs0 hsb hbound
    have hh2 : 1 ≤ radialFactor R a b c s^2 := by nlinarith
    nlinarith
  · have hsb' : b^2 < s := lt_of_not_ge hsb
    have ht : 0 < Real.sqrt (s+c) := Real.sqrt_pos.mpr (by linarith)
    have ht2 := Real.sq_sqrt (show 0 ≤ s+c by linarith)
    rw [radialFactor,radialCutoff_one a b s hab hsb'.le]
    simp only [sub_self,one_mul,zero_add,radialModel,div_pow]
    rw [ht2]
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ (by linarith : 0 < s+c)).mpr
    nlinarith [mul_nonneg (show 0 ≤ R^2-1 by nlinarith) (show 0 ≤ s-1 by linarith)]

def radialMap (R a b c : ℝ) (x : P) : P := radialFactor R a b c (sq x) • x

lemma radialMap_smooth (R a b c : ℝ) (hc : 0 < c) : ContDiff ℝ ∞ (radialMap R a b c) := by
  have hl : ContDiff ℝ ∞ (fun x : P => radialFactor R a b c (sq x)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (radialFactor_smoothAt R a b c (sq x) (by linarith [sq_nonneg x])).comp x sq_smooth.contDiffAt
  exact hl.smul contDiff_id

lemma sq_hasFDerivAt (x : P) :
    HasFDerivAt sq ((2*x 0) • (ContinuousLinearMap.proj (0:Fin 2) : P →L[ℝ] ℝ)+
      (2*x 1) • (ContinuousLinearMap.proj (1:Fin 2) : P →L[ℝ] ℝ)) x := by
  have h0 : HasFDerivAt (fun y : P => y 0) (ContinuousLinearMap.proj 0) x :=
    (ContinuousLinearMap.proj (0:Fin 2) : P →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun y : P => y 1) (ContinuousLinearMap.proj 1) x :=
    (ContinuousLinearMap.proj (1:Fin 2) : P →L[ℝ] ℝ).hasFDerivAt
  have hd := (h0.mul h0).add (h1.mul h1)
  have heq : (((fun y : P => y 0)*(fun y : P => y 0))+
      (fun y : P => y 1)*(fun y : P => y 1)) = sq := by
    funext y
    simp [sq,pow_two]
  rw [heq] at hd
  apply hd.congr_fderiv
  ext v
  simp
  ring

lemma radialMap_fderiv (R a b c : ℝ) (hc : 0 < c) (x v : P) :
    fderiv ℝ (radialMap R a b c) x v = radialFactor R a b c (sq x) • v+
      (2*deriv (radialFactor R a b c) (sq x)*(x 0*v 0+x 1*v 1)) • x := by
  have hl := (radialFactor_smoothAt R a b c (sq x) (by linarith [sq_nonneg x])).differentiableAt (by simp)
  have hd := (hl.hasDerivAt.comp_hasFDerivAt x (sq_hasFDerivAt x)).smul (hasFDerivAt_id x)
  change HasFDerivAt (radialMap R a b c) _ x at hd
  rw [hd.fderiv]
  ext i
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.proj_apply,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,Function.comp_apply,id_eq]
  ring

def det2 (D : P →L[ℝ] P) : ℝ := D (Pi.single 0 1) 0*D (Pi.single 1 1) 1-
  D (Pi.single 1 1) 0*D (Pi.single 0 1) 1

lemma radialMap_det (R a b c : ℝ) (hc : 0 < c) (x : P) :
    det2 (fderiv ℝ (radialMap R a b c) x) =
      radialFactor R a b c (sq x)*(radialFactor R a b c (sq x)+
        2*sq x*deriv (radialFactor R a b c) (sq x)) := by
  simp [det2,radialMap_fderiv R a b c hc,sq]
  ring

lemma radialMap_det_pos (R a b c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (hab : a^2 < b^2) (hbound : b^2+c ≤ R^2) (x : P) :
    0 < det2 (fderiv ℝ (radialMap R a b c) x) := by
  rw [radialMap_det R a b c hc]
  exact mul_pos (radialFactor_pos R a b c _ hR (by linarith [sq_nonneg x]))
    (radialFactor_normal_pos R a b c _ hR hc hab hbound (sq_nonneg x))

lemma sq_radialMap (R a b c : ℝ) (x : P) :
    sq (radialMap R a b c x) = radialFactor R a b c (sq x)^2*sq x := by
  simp [radialMap,sq]
  ring

lemma radialMap_range (R a b c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (hb : 0 ≤ b) (hbR : b < R) (hab : a^2 < b^2) (x : P) :
    sq (radialMap R a b c x) < R^2 := by
  have hl := radialFactor_pos R a b c (sq x) hR (by linarith [sq_nonneg x])
  have hh := radialFactor_radius_lt R a b c (sq x) hR hc hb hbR hab (sq_nonneg x)
  have hs := (sq_lt_sq₀ (mul_nonneg hl.le (Real.sqrt_nonneg _)) hR.le).mpr hh
  rw [sq_radialMap]
  simpa only [mul_pow,Real.sq_sqrt (sq_nonneg x)] using hs

lemma radialMap_identity (R a b c : ℝ) (hab : a^2 < b^2) (x : P) (hx : sq x ≤ a^2) :
    radialMap R a b c x = x := by simp [radialMap,radialFactor_inner R a b c _ hab hx]

lemma radialMap_reflects_unit (R a b c : ℝ) (hR : 1 < R) (ha : 1 < a) (hb : a < b)
    (hc : 0 < c) (hbound : b^2+c ≤ R^2) (x : P) :
    sq (radialMap R a b c x) ≤ 1 → sq x ≤ 1 := by
  intro hx
  by_contra hn
  have hab : a^2 < b^2 := by nlinarith
  have hh := radialFactor_outside_unit R a b c (sq x) hR (by linarith) hab hc hbound (lt_of_not_ge hn)
  rw [sq_radialMap] at hx
  linarith

end
end ContactTopology.LocalExtension


namespace ContactTopology.LocalExtension
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def pair (a v : P) : ℝ := a 0*v 0+a 1*v 1
def covector : P →L[ℝ] (P →L[ℝ] ℝ) :=
  (ContinuousLinearMap.proj 0 : P →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 0 : P →L[ℝ] ℝ)+
  (ContinuousLinearMap.proj 1 : P →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 1 : P →L[ℝ] ℝ)

lemma covector_apply (a v : P) : covector a v = pair a v := by simp [covector,pair]

lemma vector_expansion (v : P) : v = v 0 • Pi.single 0 1+v 1 • Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp

lemma exterior_pair_algebra (D : P →L[ℝ] P) (v w : P) :
    pair (D v) w-pair (D w) v =
      (v 0*w 1-v 1*w 0)*(D (Pi.single 0 1) 1-D (Pi.single 1 1) 0) := by
  have hv : D v = v 0 • D (Pi.single 0 1)+v 1 • D (Pi.single 1 1) := by
    conv_lhs => rw [vector_expansion v]
    simp only [map_add,map_smul]
  have hw : D w = w 0 • D (Pi.single 0 1)+w 1 • D (Pi.single 1 1) := by
    conv_lhs => rw [vector_expansion w]
    simp only [map_add,map_smul]
  rw [hv,hw]
  simp [pair]
  ring

lemma wedge_pair_algebra (a : P) (D : P →L[ℝ] ℝ) (v w : P) :
    pair a v*D w-pair a w*D v =
      (v 0*w 1-v 1*w 0)*(a 0*D (Pi.single 1 1)-a 1*D (Pi.single 0 1)) := by
  have hv : D v = v 0*D (Pi.single 0 1)+v 1*D (Pi.single 1 1) := by
    conv_lhs => rw [vector_expansion v]
    simp
  have hw : D w = w 0*D (Pi.single 0 1)+w 1*D (Pi.single 1 1) := by
    conv_lhs => rw [vector_expansion w]
    simp
  rw [hv,hw]
  unfold pair
  ring

def volume (u : P → ℝ) (β : P → P) (x : P) : ℝ :=
  β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
    u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)

def pullBeta (F : P → P) (β : P → P) (x : P) : P :=
  ![covector (β (F x)) (fderiv ℝ F x (Pi.single 0 1)),
    covector (β (F x)) (fderiv ℝ F x (Pi.single 1 1))]

lemma pullBeta_pair (F : P → P) (β : P → P) (x v : P) :
    covector (pullBeta F β x) v = covector (β (F x)) (fderiv ℝ F x v) := by
  have hh : fderiv ℝ F x v = v 0 • fderiv ℝ F x (Pi.single 0 1)+
      v 1 • fderiv ℝ F x (Pi.single 1 1) := by
    conv_lhs => rw [vector_expansion v]
    simp only [map_add,map_smul]
  rw [hh]
  simp [pullBeta,covector_apply,pair]
  ring

lemma pullBeta_smoothAt (F : P → P) (β : P → P) (hF : ContDiff ℝ ∞ F) (x : P)
    (hβ : ContDiffAt ℝ ∞ β (F x)) : ContDiffAt ℝ ∞ (pullBeta F β) x := by
  have ha := covector.contDiff.contDiffAt.comp x (hβ.comp x hF.contDiffAt)
  have hd : ContDiffAt ℝ ∞ (fun z => fderiv ℝ F z) x := (hF.fderiv_right (by simp)).contDiffAt
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [pullBeta] <;> exact ha.clm_apply (hd.clm_apply contDiffAt_const)

lemma coefficient_form_fderiv (β : P → P) (x v w : P) (hβ : DifferentiableAt ℝ β x) :
    fderiv ℝ (fun y => covector (β y)) x v w = pair (fderiv ℝ β x v) w := by
  have hd := covector.hasFDerivAt.comp x hβ.hasFDerivAt
  change HasFDerivAt (fun y => covector (β y)) _ x at hd
  rw [hd.fderiv]
  exact covector_apply _ _

lemma pullBeta_curl (F : P → P) (β : P → P) (hF : ContDiff ℝ ∞ F) (x : P)
    (hβ : ContDiffAt ℝ ∞ β (F x)) :
    fderiv ℝ (pullBeta F β) x (Pi.single 0 1) 1-
      fderiv ℝ (pullBeta F β) x (Pi.single 1 1) 0 =
    det2 (fderiv ℝ F x)*(fderiv ℝ β (F x) (Pi.single 0 1) 1-
      fderiv ℝ β (F x) (Pi.single 1 1) 0) := by
  have hα : DifferentiableAt ℝ (fun y => covector (β y)) (F x) :=
    covector.differentiableAt.comp (F x) (hβ.differentiableAt (by simp))
  have hp := ContactCalculus.exterior_pairing_pullback (fun y => covector (β y)) F x
    (Pi.single 0 1) (Pi.single 1 1) hα
    (hF.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have he : (fun z => (covector (β (F z))).comp (fderiv ℝ F z)) =
      (fun z => covector (pullBeta F β z)) := by
    funext z
    ext v
    exact (pullBeta_pair F β z v).symm
  rw [he,coefficient_form_fderiv _ _ _ _ ((pullBeta_smoothAt F β hF x hβ).differentiableAt (by simp)),
    coefficient_form_fderiv _ _ _ _ ((pullBeta_smoothAt F β hF x hβ).differentiableAt (by simp)),
    coefficient_form_fderiv _ _ _ _ (hβ.differentiableAt (by simp)),
    coefficient_form_fderiv _ _ _ _ (hβ.differentiableAt (by simp))] at hp
  rw [exterior_pair_algebra (fderiv ℝ β (F x))] at hp
  simpa [pair,det2,mul_comm] using hp

lemma volume_pullback (F : P → P) (u : P → ℝ) (β : P → P) (hF : ContDiff ℝ ∞ F)
    (x : P) (hu : DifferentiableAt ℝ u (F x)) (hβ : ContDiffAt ℝ ∞ β (F x)) :
    volume (u ∘ F) (pullBeta F β) x = det2 (fderiv ℝ F x)*volume u β (F x) := by
  have hdu : ∀ v, fderiv ℝ (u ∘ F) x v = fderiv ℝ u (F x) (fderiv ℝ F x v) := by
    intro v
    rw [fderiv_comp x hu (hF.differentiable (by simp) x)]
    rfl
  unfold volume
  rw [pullBeta_curl F β hF x hβ,hdu,hdu]
  have hw := wedge_pair_algebra (β (F x)) (fderiv ℝ u (F x))
    (fderiv ℝ F x (Pi.single 0 1)) (fderiv ℝ F x (Pi.single 1 1))
  change covector (β (F x)) (fderiv ℝ F x (Pi.single 0 1))*
      fderiv ℝ u (F x) (fderiv ℝ F x (Pi.single 1 1))-
    covector (β (F x)) (fderiv ℝ F x (Pi.single 1 1))*
      fderiv ℝ u (F x) (fderiv ℝ F x (Pi.single 0 1))+
    u (F x)*(det2 (fderiv ℝ F x)*_) = _
  rw [covector_apply,covector_apply,hw]
  unfold det2
  ring

end
end ContactTopology.LocalExtension


namespace ContactTopology.LocalExtension
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma closed_disk_compact : IsCompact {x : P | sq x ≤ 1} := by
  apply (isCompact_Icc : IsCompact (Icc (![-1,-1] : P) ![1,1])).of_isClosed_subset
    (isClosed_le sq_smooth.continuous continuous_const)
  intro x hx
  have h : x 0^2+x 1^2 ≤ 1 := hx
  have h₀ : -1 ≤ x 0 ∧ x 0 ≤ 1 := by constructor <;> nlinarith [_root_.sq_nonneg (x 1)]
  have h₁ : -1 ≤ x 1 ∧ x 1 ≤ 1 := by constructor <;> nlinarith [_root_.sq_nonneg (x 0)]
  constructor <;> intro i <;> fin_cases i
  · exact h₀.1
  · exact h₁.1
  · exact h₀.2
  · exact h₁.2

lemma exists_larger_disk (N : Set P) (hN : IsOpen N) (hDN : ∀ x, sq x ≤ 1 → x ∈ N) :
    ∃ R : ℝ, 1 < R ∧ ∀ x, sq x ≤ R^2 → x ∈ N := by
  let join : P × ℝ → P := fun p => p.2 • p.1
  have hj : Continuous join := continuous_snd.smul continuous_fst
  have hs : {x : P | sq x ≤ 1} ×ˢ ({1} : Set ℝ) ⊆ join ⁻¹' N := by
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    have ht1 : t = 1 := ht
    subst t
    simpa [join] using hDN x hx
  obtain ⟨A,B,hA,hB,hDA,h1B,hAB⟩ := generalized_tube_lemma closed_disk_compact
    isCompact_singleton (hN.preimage hj) hs
  have hone : (1:ℝ) ∈ B := h1B (by simp)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hone)
  let R : ℝ := 1+ε/2
  have hR : 1 < R := by dsimp [R]; linarith
  have hR0 : 0 < R := by linarith
  have hRB : R ∈ B := hball (by
    change dist R 1 < ε
    rw [Real.dist_eq,abs_of_pos (by dsimp [R]; linarith : 0 < R-1)]
    dsimp [R]
    linarith)
  refine ⟨R,hR,?_⟩
  intro x hx
  have hsq : sq (R⁻¹ • x) = sq x/R^2 := by simp [sq,div_eq_mul_inv]; ring
  have hy : sq (R⁻¹ • x) ≤ 1 := by
    rw [hsq]
    exact (div_le_one (pow_pos hR0 2)).mpr hx
  have hh := hAB (show (R⁻¹ • x,R) ∈ A ×ˢ B from ⟨hDA hy,hRB⟩)
  change R • (R⁻¹ • x) ∈ N at hh
  simpa only [smul_smul,mul_inv_cancel₀ hR0.ne',one_smul] using hh

theorem exists_relative_radial_compression (N : Set P) (hN : IsOpen N)
    (hDN : ∀ x, sq x ≤ 1 → x ∈ N) :
    ∃ F : P → P, ∃ W : Set P, ContDiff ℝ ∞ F ∧ IsOpen W ∧
      (∀ x, sq x ≤ 1 → x ∈ W) ∧ W ⊆ N ∧ EqOn F id W ∧
      (∀ x, F x ∈ N) ∧ (∀ x, 0 < det2 (fderiv ℝ F x)) ∧
      ∀ x, sq (F x) ≤ 1 → sq x ≤ 1 := by
  obtain ⟨R,hR,hRN⟩ := exists_larger_disk N hN hDN
  let a : ℝ := (2+R)/3
  let b : ℝ := (1+2*R)/3
  let c : ℝ := (R^2-b^2)/2
  have ha : 1 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hbR : b < R := by dsimp [b]; linarith
  have hR0 : 0 < R := by linarith
  have hb0 : 0 < b := by linarith
  have hab2 : a^2 < b^2 := by nlinarith
  have hbR2 : b^2 < R^2 := by nlinarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hbound : b^2+c ≤ R^2 := by dsimp [c]; linarith
  let F := radialMap R a b c
  let W : Set P := {x | sq x < a^2}
  have hFI : EqOn F id W := fun x hx => radialMap_identity R a b c hab2 x hx.le
  have hFN : ∀ x, F x ∈ N := fun x => hRN _
    (radialMap_range R a b c hR0 hc hb0.le hbR hab2 x).le
  refine ⟨F,W,radialMap_smooth R a b c hc,isOpen_lt sq_smooth.continuous continuous_const,
    ?_,?_,hFI,hFN,radialMap_det_pos R a b c hR0 hc hab2 hbound,?_⟩
  · intro x hx
    change sq x < a^2
    nlinarith
  · intro x hx
    have hh := hFN x
    rw [hFI hx] at hh
    exact hh
  · exact radialMap_reflects_unit R a b c hR ha hab hc hbound

end
end ContactTopology.LocalExtension


namespace ContactTopology.LocalExtension
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma pullBeta_on_identity (F : P → P) (β : P → P) (W : Set P) (hW : IsOpen W)
    (heq : EqOn F id W) : EqOn (pullBeta F β) β W := by
  intro x hx
  have he : F =ᶠ[𝓝 x] id := by filter_upwards [hW.mem_nhds hx] with z hz; exact heq hz
  have hd : fderiv ℝ F x = ContinuousLinearMap.id ℝ P := by rw [he.fderiv_eq,fderiv_id]
  unfold pullBeta
  rw [heq hx,hd]
  ext i
  fin_cases i <;> simp [covector_apply,pair]

lemma pullBeta_smooth (F : P → P) (β : P → P) (hF : ContDiff ℝ ∞ F)
    (N : Set P) (hN : IsOpen N) (hFN : ∀ x, F x ∈ N) (hβ : ContDiffOn ℝ ∞ β N) :
    ContDiff ℝ ∞ (pullBeta F β) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact pullBeta_smoothAt F β hF x (hβ.contDiffAt (hN.mem_nhds (hFN x)))

lemma compose_smooth (F : P → P) (u : P → ℝ) (hF : ContDiff ℝ ∞ F)
    (N : Set P) (hN : IsOpen N) (hFN : ∀ x, F x ∈ N) (hu : ContDiffOn ℝ ∞ u N) :
    ContDiff ℝ ∞ (u ∘ F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (hu.contDiffAt (hN.mem_nhds (hFN x))).comp x hF.contDiffAt

/-- Simultaneous positive extension of local invariant contact coefficients,
with actual equality on a neighborhood of the closed disk and relative fixing. -/
theorem simultaneous_positive_extension
    (N : Set P) (hN : IsOpen N) (hDN : ∀ x, sq x ≤ 1 → x ∈ N)
    (u₀ u₁ : P → ℝ) (β₀ β₁ : P → P)
    (hu₀ : ContDiffOn ℝ ∞ u₀ N) (hu₁ : ContDiffOn ℝ ∞ u₁ N)
    (hβ₀ : ContDiffOn ℝ ∞ β₀ N) (hβ₁ : ContDiffOn ℝ ∞ β₁ N)
    (hpos₀ : ∀ x ∈ N, 0 < volume u₀ β₀ x) (hpos₁ : ∀ x ∈ N, 0 < volume u₁ β₁ x)
    (hzero : ∀ x ∈ N, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x ∈ N, u₁ x ≠ 0 → 0 < u₀ x*u₁ x)
    (K : Set P) (hKD : K ⊆ {x | sq x < 1})
    (heq : ∀ x ∈ N, x ∉ K → u₀ x = u₁ x ∧ β₁ x = β₀ x) :
    ∃ U₀ U₁ : P → ℝ, ∃ B₀ B₁ : P → P, ∃ W : Set P,
      ContDiff ℝ ∞ U₀ ∧ ContDiff ℝ ∞ U₁ ∧ ContDiff ℝ ∞ B₀ ∧ ContDiff ℝ ∞ B₁ ∧
      (∀ x, 0 < volume U₀ B₀ x) ∧ (∀ x, 0 < volume U₁ B₁ x) ∧
      (∀ x, U₀ x = 0 ↔ U₁ x = 0) ∧ (∀ x, U₁ x ≠ 0 → 0 < U₀ x*U₁ x) ∧
      (∀ x, x ∉ K → U₀ x = U₁ x ∧ B₁ x = B₀ x) ∧
      IsOpen W ∧ (∀ x, sq x ≤ 1 → x ∈ W) ∧ W ⊆ N ∧
      EqOn U₀ u₀ W ∧ EqOn U₁ u₁ W ∧ EqOn B₀ β₀ W ∧ EqOn B₁ β₁ W := by
  obtain ⟨F,W,hF,hW,hDW,hWN,hFI,hFN,hdet,hreflect⟩ := exists_relative_radial_compression N hN hDN
  have hFK : ∀ x, x ∉ K → F x ∉ K := by
    intro x hx hFx
    have hd : sq x ≤ 1 := hreflect x (hKD hFx).le
    have hh : F x = x := hFI (hDW x hd)
    rw [hh] at hFx
    exact hx hFx
  refine ⟨u₀ ∘ F,u₁ ∘ F,pullBeta F β₀,pullBeta F β₁,W,
    compose_smooth F u₀ hF N hN hFN hu₀,compose_smooth F u₁ hF N hN hFN hu₁,
    pullBeta_smooth F β₀ hF N hN hFN hβ₀,pullBeta_smooth F β₁ hF N hN hFN hβ₁,
    ?_,?_,?_,?_,?_,hW,hDW,hWN,?_,?_,pullBeta_on_identity F β₀ W hW hFI,
    pullBeta_on_identity F β₁ W hW hFI⟩
  · intro x
    rw [volume_pullback F u₀ β₀ hF x
      ((hu₀.contDiffAt (hN.mem_nhds (hFN x))).differentiableAt (by simp))
      (hβ₀.contDiffAt (hN.mem_nhds (hFN x)))]
    exact mul_pos (hdet x) (hpos₀ _ (hFN x))
  · intro x
    rw [volume_pullback F u₁ β₁ hF x
      ((hu₁.contDiffAt (hN.mem_nhds (hFN x))).differentiableAt (by simp))
      (hβ₁.contDiffAt (hN.mem_nhds (hFN x)))]
    exact mul_pos (hdet x) (hpos₁ _ (hFN x))
  · exact fun x => hzero _ (hFN x)
  · exact fun x hx => hsign _ (hFN x) hx
  · intro x hx
    have hh := heq (F x) (hFN x) (hFK x hx)
    refine ⟨hh.1,?_⟩
    unfold pullBeta
    rw [hh.2]
  · intro x hx
    change u₀ (F x) = u₀ x
    rw [hFI hx]
    rfl
  · intro x hx
    change u₁ (F x) = u₁ x
    rw [hFI hx]
    rfl

end
end ContactTopology.LocalExtension


open Set
open scoped ContDiff

theorem solution
    (N : Set (Fin 2 → ℝ)) (hN : IsOpen N) (hDN : ∀ x, (x 0^2+x 1^2) ≤ 1 → x ∈ N)
    (u₀ u₁ : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu₀ : ContDiffOn ℝ ∞ u₀ N) (hu₁ : ContDiffOn ℝ ∞ u₁ N)
    (hβ₀ : ContDiffOn ℝ ∞ β₀ N) (hβ₁ : ContDiffOn ℝ ∞ β₁ N)
    (hzero : ∀ x ∈ N, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x ∈ N, u₁ x ≠ 0 → 0 < u₀ x*u₁ x)
    (K : Set (Fin 2 → ℝ)) (hKD : K ⊆ {x | (x 0^2+x 1^2) < 1})
    (heq : ∀ x ∈ N, x ∉ K → u₀ x = u₁ x ∧ β₁ x = β₀ x) :
    let Q : ((Fin 2 → ℝ) → ℝ) → ((Fin 2 → ℝ) → (Fin 2 → ℝ)) → (Fin 2 → ℝ) → ℝ := fun u β x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    (∀ x ∈ N, 0 < Q u₀ β₀ x) → (∀ x ∈ N, 0 < Q u₁ β₁ x) →
    ∃ U₀ U₁ : (Fin 2 → ℝ) → ℝ, ∃ B₀ B₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ), ∃ W : Set (Fin 2 → ℝ),
      ContDiff ℝ ∞ U₀ ∧ ContDiff ℝ ∞ U₁ ∧ ContDiff ℝ ∞ B₀ ∧ ContDiff ℝ ∞ B₁ ∧
      (∀ x, 0 < Q U₀ B₀ x) ∧ (∀ x, 0 < Q U₁ B₁ x) ∧
      (∀ x, U₀ x = 0 ↔ U₁ x = 0) ∧ (∀ x, U₁ x ≠ 0 → 0 < U₀ x*U₁ x) ∧
      (∀ x, x ∉ K → U₀ x = U₁ x ∧ B₁ x = B₀ x) ∧
      IsOpen W ∧ (∀ x, (x 0^2+x 1^2) ≤ 1 → x ∈ W) ∧ W ⊆ N ∧
      EqOn U₀ u₀ W ∧ EqOn U₁ u₁ W ∧ EqOn B₀ β₀ W ∧ EqOn B₁ β₁ W := by
  dsimp only
  intro hpos₀ hpos₁
  exact ContactTopology.LocalExtension.simultaneous_positive_extension
    N hN hDN u₀ u₁ β₀ β₁ hu₀ hu₁ hβ₀ hβ₁ hpos₀ hpos₁ hzero hsign K hKD heq
