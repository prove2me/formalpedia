-- Prove2me | solution 1 for ContactTopology.relative_contact_representative_from_signed_dividing_data
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T21:59:39.019838+00:00
-- url     : https://prove2.me/submissions/ad928994-a5d1-472b-84a2-3452c71ab08b

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact
import Theorems.Thm_ContactCalculus_exterior_pairing_pullback
import Theorems.Thm_ContactTopology_positive_invariant_contact_representative_of_signed_dividing_data



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



namespace ContactTopology.NormalMatching
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma transition_deriv_compact : HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.intro' (K := Icc (0:ℝ) 1) isCompact_Icc isClosed_Icc
  intro s hs
  by_cases hn : s < 0
  · have he : Real.smoothTransition =ᶠ[𝓝 s] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_lt continuous_id continuous_const |>.mem_nhds hn] with t ht
      exact Real.smoothTransition.zero_of_nonpos ht.le
    rw [he.deriv_eq]
    simp
  · have hp : 1 < s := by
      by_contra hh
      exact hs ⟨le_of_not_gt hn,le_of_not_gt hh⟩
    have he : Real.smoothTransition =ᶠ[𝓝 s] (fun _ => (1:ℝ)) := by
      filter_upwards [isOpen_lt continuous_const continuous_id |>.mem_nhds hp] with t ht
      exact Real.smoothTransition.one_of_one_le ht.le
    rw [he.deriv_eq]
    simp

lemma transition_deriv_bound : ∃ M > 0, ∀ s, |deriv Real.smoothTransition s| ≤ M := by
  obtain ⟨B,hB⟩ := ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_deriv
    (by simp)).abs.bddAbove_range_of_hasCompactSupport transition_deriv_compact.abs
  refine ⟨|B|+1,by positivity,?_⟩
  intro s
  have hb := hB ⟨s,rfl⟩
  linarith [le_abs_self B]

def logCutoff (η L s : ℝ) : ℝ :=
  if 0 < s then Real.smoothTransition (1+(Real.log s-Real.log η)/L) else 0

lemma logCutoff_range (η L s : ℝ) : 0 ≤ logCutoff η L s ∧ logCutoff η L s ≤ 1 := by
  unfold logCutoff
  split_ifs
  · exact ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  · norm_num

lemma logCutoff_zero (η L s : ℝ) (hL : 0 < L)
    (hs : s ≤ Real.exp (Real.log η-L)) : logCutoff η L s = 0 := by
  unfold logCutoff
  split_ifs with hp
  · apply Real.smoothTransition.zero_of_nonpos
    have hh : Real.log s ≤ Real.log η-L := by
      have hl := Real.log_le_log hp hs
      simpa only [Real.log_exp] using hl
    have hd : (Real.log s-Real.log η)/L ≤ -1 := (div_le_iff₀ hL).mpr (by linarith)
    linarith
  · rfl

lemma logCutoff_one (η L s : ℝ) (hη : 0 < η) (hL : 0 < L) (hs : η ≤ s) :
    logCutoff η L s = 1 := by
  unfold logCutoff
  rw [if_pos (lt_of_lt_of_le hη hs)]
  apply Real.smoothTransition.one_of_one_le
  have hh : 0 ≤ (Real.log s-Real.log η)/L :=
    div_nonneg (sub_nonneg.mpr (Real.log_le_log hη hs)) hL.le
  linarith

lemma logCutoff_smooth (η L : ℝ) (hL : 0 < L) : ContDiff ℝ ∞ (logCutoff η L) := by
  apply contDiff_iff_contDiffAt.mpr
  intro s
  by_cases hs : 0 < s
  · have he : logCutoff η L =ᶠ[𝓝 s]
        (fun t => Real.smoothTransition (1+(Real.log t-Real.log η)/L)) := by
      filter_upwards [isOpen_lt continuous_const continuous_id |>.mem_nhds hs] with t ht
      exact if_pos ht
    have hc : ContDiffAt ℝ ∞ (fun t => Real.smoothTransition (1+(Real.log t-Real.log η)/L)) s :=
      Real.smoothTransition.contDiff.contDiffAt.comp s
        (contDiffAt_const.add (((contDiffAt_id.log hs.ne').sub contDiffAt_const).div_const L))
    exact hc.congr_of_eventuallyEq he
  · have hρ : 0 < Real.exp (Real.log η-L) := Real.exp_pos _
    have he : logCutoff η L =ᶠ[𝓝 s] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_lt continuous_id continuous_const |>.mem_nhds
        (lt_of_le_of_lt (le_of_not_gt hs) hρ)] with t ht
      exact logCutoff_zero η L t hL ht.le
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma logCutoff_hasDerivAt (η L s : ℝ) (hs : 0 < s) :
    HasDerivAt (logCutoff η L)
      (deriv Real.smoothTransition (1+(Real.log s-Real.log η)/L)*(s⁻¹/L)) s := by
  have hi := (hasDerivAt_const s (1:ℝ)).add
    (((Real.hasDerivAt_log hs.ne').sub_const (Real.log η)).div_const L)
  have hd := ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
    (by simp) _).hasDerivAt.comp s hi
  have he : logCutoff η L =ᶠ[𝓝 s]
      (fun t => Real.smoothTransition (1+(Real.log t-Real.log η)/L)) := by
    filter_upwards [isOpen_lt continuous_const continuous_id |>.mem_nhds hs] with t ht
    exact if_pos ht
  have hh := hd.congr_of_eventuallyEq he
  convert! hh using 1 <;> simp

lemma logCutoff_deriv_zero_nonpos (η L s : ℝ) (hL : 0 < L) (hs : s ≤ 0) :
    deriv (logCutoff η L) s = 0 := by
  have he : logCutoff η L =ᶠ[𝓝 s] (fun _ => (0:ℝ)) := by
    filter_upwards [isOpen_lt continuous_id continuous_const |>.mem_nhds
      (lt_of_le_of_lt hs (Real.exp_pos (Real.log η-L)))] with t ht
    exact logCutoff_zero η L t hL ht.le
  rw [he.deriv_eq]
  simp

theorem exists_weighted_small_cutoff (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ χ : ℝ → ℝ, ∃ ρ : ℝ, ContDiff ℝ ∞ χ ∧ 0 < ρ ∧ ρ < η ∧
      (∀ s, 0 ≤ χ s ∧ χ s ≤ 1) ∧ (∀ s, s ≤ ρ → χ s = 0) ∧
      (∀ s, η ≤ s → χ s = 1) ∧ ∀ s, |s*deriv χ s| < ε := by
  obtain ⟨M,hM,hbound⟩ := transition_deriv_bound
  let L : ℝ := M/ε+1
  have hL : 0 < L := by dsimp [L]; positivity
  have hML : M/L < ε := by
    apply (div_lt_iff₀ hL).mpr
    have hh : ε*(M/ε) = M := by field_simp
    dsimp [L]
    nlinarith
  refine ⟨logCutoff η L,Real.exp (Real.log η-L),logCutoff_smooth η L hL,Real.exp_pos _,?_,
    logCutoff_range η L,fun s hs => logCutoff_zero η L s hL hs,
    fun s hs => logCutoff_one η L s hη hL hs,?_⟩
  · calc
      Real.exp (Real.log η-L) < Real.exp (Real.log η) := Real.exp_lt_exp.mpr (by linarith)
      _ = η := Real.exp_log hη
  · intro s
    by_cases hs : 0 < s
    · rw [(logCutoff_hasDerivAt η L s hs).deriv]
      have he : s*(deriv Real.smoothTransition (1+(Real.log s-Real.log η)/L)*(s⁻¹/L)) =
          deriv Real.smoothTransition (1+(Real.log s-Real.log η)/L)/L := by
        field_simp
      rw [he,abs_div,abs_of_pos hL]
      exact (div_le_div_of_nonneg_right (hbound _) hL.le).trans_lt hML
    · rw [logCutoff_deriv_zero_nonpos η L s hL (le_of_not_gt hs),mul_zero,abs_zero]
      exact hε

end
end ContactTopology.NormalMatching


namespace ContactTopology.NormalMatching
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev P := Fin 2 → ℝ
def sq (x : P) : ℝ := x 0^2+x 1^2
def q (x : P) : ℝ := 1-sq x

lemma sq_smooth : ContDiff ℝ ∞ sq := by unfold sq; fun_prop
lemma q_smooth : ContDiff ℝ ∞ q := contDiff_const.sub sq_smooth
lemma sq_nonneg (x : P) : 0 ≤ sq x := by unfold sq; positivity

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

lemma q_fderiv (x v : P) : fderiv ℝ q x v = -2*(x 0*v 0+x 1*v 1) := by
  have h0 : HasFDerivAt (fun y : P => y 0) (ContinuousLinearMap.proj 0) x :=
    (ContinuousLinearMap.proj (0:Fin 2) : P →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun y : P => y 1) (ContinuousLinearMap.proj 1) x :=
    (ContinuousLinearMap.proj (1:Fin 2) : P →L[ℝ] ℝ).hasFDerivAt
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) x).sub ((h0.mul h0).add (h1.mul h1))
  have heq : (fun y : P => 1-(y 0*y 0+y 1*y 1)) = q := by funext y; simp [q,sq,pow_two]
  change HasFDerivAt (𝕜 := ℝ) (fun y : P => 1-(y 0*y 0+y 1*y 1)) _ x at hd
  rw [heq] at hd
  rw [hd.fderiv]
  simp
  ring

lemma boundary_vanishing_estimate (g : P → ℝ) (hg : ContDiff ℝ ∞ g)
    (hzero : ∀ x, sq x = 1 → g x = 0) :
    ∃ C > 0, ∀ x, sq x ≤ 1 → (1/4:ℝ) ≤ sq x → |g x| ≤ C*|q x| := by
  let B : Set P := Icc (![-2,-2]:P) ![2,2]
  obtain ⟨K,hK⟩ := hg.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_Icc (![-2,-2]:P) ![2,2]) isCompact_Icc
  have hbox : ∀ x : P, sq x ≤ 1 → x ∈ B := by
    intro x hx
    have hh : x 0^2+x 1^2 ≤ 1 := hx
    have h₀ : -2 ≤ x 0 ∧ x 0 ≤ 2 := by constructor <;> nlinarith [_root_.sq_nonneg (x 1)]
    have h₁ : -2 ≤ x 1 ∧ x 1 ≤ 2 := by constructor <;> nlinarith [_root_.sq_nonneg (x 0)]
    constructor <;> intro i <;> fin_cases i
    · exact h₀.1
    · exact h₁.1
    · exact h₀.2
    · exact h₁.2
  refine ⟨(K:ℝ)+1,by positivity,?_⟩
  intro x hx hinner
  let t := Real.sqrt (sq x)
  have ht : 0 < t := Real.sqrt_pos.mpr (by linarith)
  have ht1 : t ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by simpa using hx⟩
  have ht2 : t^2 = sq x := Real.sq_sqrt (sq_nonneg x)
  let p : P := t⁻¹ • x
  have hp : sq p = 1 := by
    have he : sq p = sq x/t^2 := by dsimp [p]; simp [sq,div_eq_mul_inv]; ring
    rw [he,ht2,div_self (show sq x ≠ 0 by linarith)]
  have hq : 0 ≤ q x := by dsimp [q]; linarith
  have hnorm : ‖x-p‖ ≤ q x := by
    apply (pi_norm_le_iff_of_nonneg hq).mpr
    intro i
    have hcomp : x i^2 ≤ sq x := by
      fin_cases i <;> simp [sq] <;> positivity
    have hxi : |x i| ≤ t := abs_le.mpr ⟨by nlinarith,by nlinarith⟩
    have he : x i-p i = x i*(t-1)/t := by
      change x i-t⁻¹*x i = x i*(t-1)/t
      field_simp [ht.ne']
    change |x i-p i| ≤ q x
    rw [he,abs_div,abs_mul,abs_of_pos ht,abs_of_nonpos (by linarith : t-1 ≤ 0)]
    apply (div_le_iff₀ ht).mpr
    have htq : 1-t ≤ q x := by
      dsimp [q]
      nlinarith [mul_nonneg ht.le (show 0 ≤ 1-t by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxi) (show 0 ≤ 1-t by linarith),
      mul_nonneg ht.le (sub_nonneg.mpr htq)]
  have hlip := hK.dist_le_mul x (hbox x hx) p (hbox p hp.le)
  rw [hzero p hp,Real.dist_eq,sub_zero,dist_eq_norm] at hlip
  rw [abs_of_nonneg hq]
  calc
    |g x| ≤ (K:ℝ)*‖x-p‖ := hlip
    _ ≤ (K:ℝ)*q x := mul_le_mul_of_nonneg_left hnorm K.coe_nonneg
    _ ≤ ((K:ℝ)+1)*q x := by nlinarith

def characteristic (β : P → P) (x : P) : P := ![β x 1,-β x 0]
def boundaryVelocity (β : P → P) (x : P) : ℝ := fderiv ℝ q x (characteristic β x)

lemma characteristic_smooth (β : P → P) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (characteristic β) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [characteristic] <;> fun_prop

lemma boundaryVelocity_smooth (β : P → P) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (boundaryVelocity β) :=
  (q_smooth.fderiv_right (by simp)).clm_apply (characteristic_smooth β hβ)

lemma legendrian_boundary_velocity_estimate (β : P → P) (hβ : ContDiff ℝ ∞ β)
    (hLegendrian : ∀ x, sq x = 1 → β x 0*(-x 1)+β x 1*x 0 = 0) :
    ∃ C > 0, ∀ x, sq x ≤ 1 → (1/4:ℝ) ≤ sq x → |boundaryVelocity β x| ≤ C*|q x| := by
  apply boundary_vanishing_estimate (boundaryVelocity β) (boundaryVelocity_smooth β hβ)
  intro x hx
  have hh := hLegendrian x hx
  unfold boundaryVelocity
  rw [q_fderiv]
  simp only [characteristic,Matrix.cons_val_zero,Matrix.cons_val_one]
  nlinarith

end
end ContactTopology.NormalMatching

namespace ContactTopology.NormalMatching
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def curl (β : P → P) (x : P) : ℝ :=
  fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0

def volume (u : P → ℝ) (β : P → P) (x : P) : ℝ :=
  β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+u x*curl β x

lemma volume_eq_operator (u : P → ℝ) (β : P → P) (x : P) :
    volume u β x = u x*curl β x-fderiv ℝ u x (characteristic β x) := by
  have he : characteristic β x = β x 1 • (Pi.single 0 1 : P)-β x 0 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [characteristic]
  rw [he,map_sub,map_smul,map_smul]
  unfold volume
  simp only [smul_eq_mul]
  ring

lemma curl_smooth (β : P → P) (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (curl β) :=
  ((contDiff_apply ℝ ℝ 1).comp ((hβ.fderiv_right (by simp)).clm_apply contDiff_const)).sub
    ((contDiff_apply ℝ ℝ 0).comp ((hβ.fderiv_right (by simp)).clm_apply contDiff_const))

lemma volume_smooth (u : P → ℝ) (β : P → P) (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (volume u β) := by
  have he : volume u β = fun x => u x*curl β x-fderiv ℝ u x (characteristic β x) :=
    funext (volume_eq_operator u β)
  rw [he]
  exact (hu.mul (curl_smooth β hβ)).sub
    ((hu.fderiv_right (by simp)).clm_apply (characteristic_smooth β hβ))

def mixNormal (χ : ℝ → ℝ) (u₀ u₁ : P → ℝ) (x : P) : ℝ :=
  (1-χ (q x))*u₀ x+χ (q x)*u₁ x

lemma mixNormal_smooth (χ : ℝ → ℝ) (u₀ u₁ : P → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (h₀ : ContDiff ℝ ∞ u₀) (h₁ : ContDiff ℝ ∞ u₁) :
    ContDiff ℝ ∞ (mixNormal χ u₀ u₁) :=
  ((contDiff_const.sub (hχ.comp q_smooth)).mul h₀).add ((hχ.comp q_smooth).mul h₁)

lemma mixNormal_fderiv (χ : ℝ → ℝ) (u₀ u₁ : P → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (h₀ : ContDiff ℝ ∞ u₀) (h₁ : ContDiff ℝ ∞ u₁) (x v : P) :
    fderiv ℝ (mixNormal χ u₀ u₁) x v =
      (1-χ (q x))*fderiv ℝ u₀ x v+χ (q x)*fderiv ℝ u₁ x v+
        deriv χ (q x)*fderiv ℝ q x v*(u₁ x-u₀ x) := by
  have hdχ := (hχ.differentiable (by simp) (q x)).hasDerivAt.comp_hasFDerivAt x
    (q_smooth.differentiable (by simp) x).hasFDerivAt
  have hd := (((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) x).sub hdχ).mul
    (h₀.differentiable (by simp) x).hasFDerivAt).add
    (hdχ.mul (h₁.differentiable (by simp) x).hasFDerivAt)
  change HasFDerivAt (𝕜 := ℝ) (mixNormal χ u₀ u₁) _ x at hd
  rw [hd.fderiv]
  simp
  ring

lemma mixNormal_volume (χ : ℝ → ℝ) (u₀ u₁ : P → ℝ) (β : P → P)
    (hχ : ContDiff ℝ ∞ χ) (h₀ : ContDiff ℝ ∞ u₀) (h₁ : ContDiff ℝ ∞ u₁) (x : P) :
    volume (mixNormal χ u₀ u₁) β x = (1-χ (q x))*volume u₀ β x+χ (q x)*volume u₁ β x-
      deriv χ (q x)*boundaryVelocity β x*(u₁ x-u₀ x) := by
  rw [volume_eq_operator,mixNormal_fderiv χ u₀ u₁ hχ h₀ h₁,volume_eq_operator,volume_eq_operator]
  unfold mixNormal boundaryVelocity
  ring

lemma convex_mix_product (a b t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (ha : a ≠ 0) (hb : 0 < b*a) :
    0 < ((1-t)*a+t*b)*a := by
  have hsq : 0 < a^2 := sq_pos_of_ne_zero ha
  by_cases he : t = 1
  · simpa [he] using hb
  · have hp : 0 < 1-t := by linarith [lt_of_le_of_ne ht.2 he]
    nlinarith [mul_pos hp hsq,mul_nonneg ht.1 hb.le]

theorem relative_positive_normal_gluing (u₀ u₁ : P → ℝ) (β : P → P)
    (h₀ : ContDiff ℝ ∞ u₀) (h₁ : ContDiff ℝ ∞ u₁) (hβ : ContDiff ℝ ∞ β)
    (hzero : ∀ x, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x, u₀ x ≠ 0 → 0 < u₁ x*u₀ x)
    (hLegendrian : ∀ x, sq x = 1 → β x 0*(-x 1)+β x 1*x 0 = 0)
    (η : ℝ) (hη : 0 < η) (hηsmall : η ≤ 1/2)
    (hpos₀ : ∀ x, sq x ≤ 1 → q x ≤ η → 0 < volume u₀ β x)
    (hpos₁ : ∀ x, sq x ≤ 1 → 0 < volume u₁ β x) :
    ∃ v : P → ℝ, ∃ ρ : ℝ, ContDiff ℝ ∞ v ∧ 0 < ρ ∧ ρ < η ∧
      (∀ x, v x = 0 ↔ u₀ x = 0) ∧ (∀ x, u₀ x ≠ 0 → 0 < v x*u₀ x) ∧
      (∀ x, q x ≤ ρ → v x = u₀ x) ∧ (∀ x, η ≤ q x → v x = u₁ x) ∧
      ∃ O : Set P, IsOpen O ∧ (∀ x, sq x ≤ 1 → x ∈ O) ∧ ∀ x ∈ O, 0 < volume v β x := by
  let A : Set P := {x | sq x ≤ 1 ∧ q x ≤ η}
  have hA : IsCompact A := closed_disk_compact.inter_right (isClosed_le q_smooth.continuous continuous_const)
  obtain ⟨m₀,hm₀,hb₀⟩ := hA.exists_forall_le' (volume_smooth u₀ β h₀ hβ).continuous.continuousOn
    (fun x hx => hpos₀ x hx.1 hx.2)
  obtain ⟨m₁,hm₁,hb₁⟩ := closed_disk_compact.exists_forall_le'
    (volume_smooth u₁ β h₁ hβ).continuous.continuousOn hpos₁
  let m := min m₀ m₁
  have hm : 0 < m := lt_min hm₀ hm₁
  obtain ⟨B,hB⟩ := closed_disk_compact.bddAbove_image (h₁.sub h₀).continuous.abs.continuousOn
  let M : ℝ := |B|+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hdiff : ∀ x, sq x ≤ 1 → |u₁ x-u₀ x| ≤ M := by
    intro x hx
    have hh := hB ⟨x,hx,rfl⟩
    dsimp [M]
    linarith [le_abs_self B]
  obtain ⟨C,hC,hvel⟩ := legendrian_boundary_velocity_estimate β hβ hLegendrian
  let ε : ℝ := m/(2*C*M)
  have hε : 0 < ε := div_pos hm (by positivity)
  obtain ⟨χ,ρ,hχ,hρ,hρη,hrange,hcut₀,hcut₁,hcutd⟩ := exists_weighted_small_cutoff η ε hη hε
  let v := mixNormal χ u₀ u₁
  have hv : ContDiff ℝ ∞ v := mixNormal_smooth χ u₀ u₁ hχ h₀ h₁
  have hsgn : ∀ x, u₀ x ≠ 0 → 0 < v x*u₀ x := by
    intro x hx
    exact convex_mix_product _ _ _ (hrange _) hx (hsign x hx)
  have hpositive : ∀ x, sq x ≤ 1 → 0 < volume v β x := by
    intro x hx
    rw [show v = mixNormal χ u₀ u₁ from rfl,mixNormal_volume χ u₀ u₁ β hχ h₀ h₁]
    by_cases hinner : η ≤ q x
    · have hχ1 := hcut₁ (q x) hinner
      have hmax : IsLocalMax χ (q x) := Eventually.of_forall fun s => by rw [hχ1]; exact (hrange s).2
      rw [hχ1,hmax.deriv_eq_zero]
      simpa using hpos₁ x hx
    · have hqx : q x ≤ η := le_of_not_ge hinner
      have hq0 : 0 ≤ q x := by dsimp [q]; linarith
      have hxinner : (1/4:ℝ) ≤ sq x := by dsimp [q] at hqx; linarith
      have hg := hvel x hx hxinner
      have hb0 : m ≤ volume u₀ β x := (min_le_left _ _).trans (hb₀ x ⟨hx,hqx⟩)
      have hb1 : m ≤ volume u₁ β x := (min_le_right _ _).trans (hb₁ x hx)
      have hbase : m ≤ (1-χ (q x))*volume u₀ β x+χ (q x)*volume u₁ β x := by
        nlinarith [mul_nonneg (show 0 ≤ 1-χ (q x) by linarith [(hrange (q x)).2]) (sub_nonneg.mpr hb0),
          mul_nonneg (hrange (q x)).1 (sub_nonneg.mpr hb1)]
      have herr : |deriv χ (q x)*boundaryVelocity β x*(u₁ x-u₀ x)| < m/2 := by
        have h1 : |deriv χ (q x)| * |boundaryVelocity β x| * |u₁ x-u₀ x| ≤
            |deriv χ (q x)| * (C * |q x|)*M := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hg (abs_nonneg _)) (hdiff x hx)
            (abs_nonneg _) (mul_nonneg (abs_nonneg _) (mul_nonneg hC.le (abs_nonneg _)))
        have he : |deriv χ (q x)| * (C * |q x|)*M = (C*M) * |q x*deriv χ (q x)| := by
          rw [abs_mul]
          ring
        rw [abs_mul,abs_mul]
        have h2 : |deriv χ (q x)| * (C * |q x|)*M < (C*M)*ε := by
          rw [he]
          exact mul_lt_mul_of_pos_left (hcutd (q x)) (mul_pos hC hM)
        have hh := h1.trans_lt h2
        have hcancel : (C*M)*ε = m/2 := by dsimp [ε]; field_simp [hC.ne',hM.ne'] <;> ring
        rwa [hcancel] at hh
      linarith [(le_abs_self (deriv χ (q x)*boundaryVelocity β x*(u₁ x-u₀ x))).trans herr.le]
  let O : Set P := {x | 0 < volume v β x}
  have hO : IsOpen O := isOpen_lt continuous_const (volume_smooth v β hv hβ).continuous
  refine ⟨v,ρ,hv,hρ,hρη,?_,hsgn,?_,?_,O,hO,hpositive,fun _ hx => hx⟩
  · intro x
    constructor
    · intro hx
      by_contra hn
      have hh := hsgn x hn
      rw [hx,zero_mul] at hh
      exact lt_irrefl 0 hh
    · intro hx
      have hu1 := (hzero x).mp hx
      simp [v,mixNormal,hx,hu1]
  · intro x hx
    simp [v,mixNormal,hcut₀ (q x) hx]
  · intro x hx
    simp [v,mixNormal,hcut₁ (q x) hx]

end
end ContactTopology.NormalMatching


namespace ContactTopology.NormalMatching
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma compact_inner_radius (K : Set P) (hK : IsCompact K) (hKD : K ⊆ {x | sq x < 1}) :
    ∃ η > 0, η ≤ (1/2:ℝ) ∧ ∀ x, q x ≤ η → x ∉ K := by
  obtain ⟨m,hm,hbound⟩ := hK.exists_forall_le' (a := (0:ℝ)) q_smooth.continuous.continuousOn
    (fun x hx => by have hh : sq x < 1 := hKD hx; dsimp [q]; linarith)
  let η := min (m/2) (1/2)
  have hη : 0 < η := lt_min (half_pos hm) (by norm_num)
  refine ⟨η,hη,min_le_right _ _,?_⟩
  intro x hx hmem
  have hh := hbound x hmem
  have he : η ≤ m/2 := min_le_left _ _
  linarith

/-- Relative target representative from signed dividing data: no target normal
coefficient and no normal agreement near the boundary are assumed. -/
theorem relative_representative_of_signed_data (u₀ : P → ℝ) (β₀ β₁ : P → P)
    (hu₀ : ContDiff ℝ ∞ u₀) (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, sq x ≤ 1 → 0 < volume u₀ β₀ x)
    (hdiv : ∀ x, sq x ≤ 1 → u₀ x ≠ 0 → 0 < u₀ x*curl β₁ x)
    (hcross : ∀ x, sq x ≤ 1 → u₀ x = 0 → fderiv ℝ u₀ x (characteristic β₁ x) < 0)
    (hLegendrian : ∀ x, sq x = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set P) (hK : IsCompact K) (hKD : K ⊆ {x | sq x < 1})
    (heq : ∀ x, x ∉ K → β₁ x = β₀ x) :
    ∃ v : P → ℝ, ∃ K' : Set P, ContDiff ℝ ∞ v ∧ IsCompact K' ∧
      K ⊆ K' ∧ K' ⊆ {x | sq x < 1} ∧
      (∀ x, v x = 0 ↔ u₀ x = 0) ∧ (∀ x, u₀ x ≠ 0 → 0 < v x*u₀ x) ∧
      (∀ x, x ∉ K' → v x = u₀ x ∧ β₁ x = β₀ x) ∧
      ∃ O : Set P, IsOpen O ∧ (∀ x, sq x ≤ 1 → x ∈ O) ∧ ∀ x ∈ O, 0 < volume v β₁ x := by
  obtain ⟨u₁,hu₁,hzero,hsign,N,hN,hDN,hpositive⟩ :=
    ContactTopology.positive_invariant_contact_representative_of_signed_dividing_data
      {x : P | sq x ≤ 1} closed_disk_compact u₀ β₁ hu₀ hβ₁ hdiv hcross
  obtain ⟨η,hη,hηsmall,hηK⟩ := compact_inner_radius K hK hKD
  have hLeg₁ : ∀ x, sq x = 1 → β₁ x 0*(-x 1)+β₁ x 1*x 0 = 0 := by
    intro x hx
    have hnot : x ∉ K := fun h => (hKD h).ne hx
    rw [heq x hnot]
    exact hLegendrian x hx
  have hcollar : ∀ x, sq x ≤ 1 → q x ≤ η → 0 < volume u₀ β₁ x := by
    intro x hx hqx
    have hnot := hηK x hqx
    have hgerm : β₁ =ᶠ[𝓝 x] β₀ := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hnot] with y hy
      exact heq y hy
    unfold volume curl
    rw [hgerm.eq_of_nhds,hgerm.fderiv_eq]
    exact hpos₀ x hx
  obtain ⟨v,ρ,hv,hρ,hρη,hvz,hvs,hvfix,hvinner,O,hO,hDO,hvpos⟩ :=
    relative_positive_normal_gluing u₀ u₁ β₁ hu₀ hu₁ hβ₁ (fun x => (hzero x).symm) hsign
      hLeg₁ η hη hηsmall hcollar (fun x hx => hpositive x (hDN hx))
  let K' : Set P := {x | sq x ≤ 1-ρ}
  have hK'D : K' ⊆ {x | sq x < 1} := by intro x hx; change sq x ≤ 1-ρ at hx; dsimp; linarith
  have hK' : IsCompact K' := closed_disk_compact.of_isClosed_subset
    (isClosed_le sq_smooth.continuous continuous_const) (fun x hx => le_of_lt (show sq x < 1 from hK'D hx))
  have hKK' : K ⊆ K' := by
    intro x hx
    by_contra hn
    have hqx : q x ≤ η := by change ¬sq x ≤ 1-ρ at hn; dsimp [q]; linarith
    exact hηK x hqx hx
  refine ⟨v,K',hv,hK',hKK',hK'D,hvz,hvs,?_,O,hO,hDO,hvpos⟩
  intro x hx
  have hqx : q x ≤ ρ := by change ¬sq x ≤ 1-ρ at hx; dsimp [q]; linarith
  exact ⟨hvfix x hqx,heq x (fun h => hx (hKK' h))⟩

end
end ContactTopology.NormalMatching

namespace ContactTopology.NormalMatching
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma volume_eq_germs (u v : P → ℝ) (β γ : P → P) (x : P)
    (hu : u =ᶠ[𝓝 x] v) (hβ : β =ᶠ[𝓝 x] γ) : volume u β x = volume v γ x := by
  unfold volume curl
  rw [hu.eq_of_nhds,hu.fderiv_eq,hβ.eq_of_nhds,hβ.fderiv_eq]

theorem local_relative_representative_of_signed_data
    (N : Set P) (hN : IsOpen N) (hDN : ∀ x, sq x ≤ 1 → x ∈ N)
    (u₀ : P → ℝ) (β₀ β₁ : P → P)
    (hu₀ : ContDiffOn ℝ ∞ u₀ N) (hβ₀ : ContDiffOn ℝ ∞ β₀ N) (hβ₁ : ContDiffOn ℝ ∞ β₁ N)
    (hpos₀ : ∀ x, sq x ≤ 1 → 0 < volume u₀ β₀ x)
    (hdiv : ∀ x, sq x ≤ 1 → u₀ x ≠ 0 → 0 < u₀ x*curl β₁ x)
    (hcross : ∀ x, sq x ≤ 1 → u₀ x = 0 → fderiv ℝ u₀ x (characteristic β₁ x) < 0)
    (hLegendrian : ∀ x, sq x = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set P) (hK : IsCompact K) (hKD : K ⊆ {x | sq x < 1})
    (heq : ∀ x ∈ N, x ∉ K → β₁ x = β₀ x) :
    ∃ v : P → ℝ, ∃ K' : Set P, ∃ O : Set P,
      ContDiff ℝ ∞ v ∧ IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ {x | sq x < 1} ∧
      IsOpen O ∧ (∀ x, sq x ≤ 1 → x ∈ O) ∧ O ⊆ N ∧
      (∀ x ∈ O, u₀ x = 0 ↔ v x = 0) ∧
      (∀ x ∈ O, v x ≠ 0 → 0 < u₀ x*v x) ∧
      (∀ x ∈ O, x ∉ K' → u₀ x = v x ∧ β₁ x = β₀ x) ∧
      (∀ x ∈ O, 0 < volume u₀ β₀ x) ∧ ∀ x ∈ O, 0 < volume v β₁ x := by
  obtain ⟨F,W,hF,hW,hDW,hWN,hFI,hFN,hdet,hreflect⟩ :=
    ContactTopology.LocalExtension.exists_relative_radial_compression N hN hDN
  let U₀ := u₀ ∘ F
  let B₀ := ContactTopology.LocalExtension.pullBeta F β₀
  let B₁ := ContactTopology.LocalExtension.pullBeta F β₁
  have hU₀ : ContDiff ℝ ∞ U₀ := ContactTopology.LocalExtension.compose_smooth F u₀ hF N hN hFN hu₀
  have hB₀ : ContDiff ℝ ∞ B₀ := ContactTopology.LocalExtension.pullBeta_smooth F β₀ hF N hN hFN hβ₀
  have hB₁ : ContDiff ℝ ∞ B₁ := ContactTopology.LocalExtension.pullBeta_smooth F β₁ hF N hN hFN hβ₁
  have hUeq : EqOn U₀ u₀ W := by intro x hx; change u₀ (F x) = u₀ x; rw [hFI hx]; rfl
  have hB₀eq : EqOn B₀ β₀ W := ContactTopology.LocalExtension.pullBeta_on_identity F β₀ W hW hFI
  have hB₁eq : EqOn B₁ β₁ W := ContactTopology.LocalExtension.pullBeta_on_identity F β₁ W hW hFI
  have hUgerm : ∀ x ∈ W, U₀ =ᶠ[𝓝 x] u₀ := by
    intro x hx
    filter_upwards [hW.mem_nhds hx] with y hy
    exact hUeq hy
  have hB₀germ : ∀ x ∈ W, B₀ =ᶠ[𝓝 x] β₀ := by
    intro x hx
    filter_upwards [hW.mem_nhds hx] with y hy
    exact hB₀eq hy
  have hB₁germ : ∀ x ∈ W, B₁ =ᶠ[𝓝 x] β₁ := by
    intro x hx
    filter_upwards [hW.mem_nhds hx] with y hy
    exact hB₁eq hy
  have hFK : ∀ x, x ∉ K → F x ∉ K := by
    intro x hx hFx
    have hd : ContactTopology.LocalExtension.sq x ≤ 1 :=
      hreflect x (le_of_lt (show ContactTopology.LocalExtension.sq (F x) < 1 from hKD hFx))
    have hh : F x = x := hFI (hDW x hd)
    rw [hh] at hFx
    exact hx hFx
  have hBE : ∀ x, x ∉ K → B₁ x = B₀ x := by
    intro x hx
    have hh := heq (F x) (hFN x) (hFK x hx)
    dsimp only [B₀,B₁,ContactTopology.LocalExtension.pullBeta]
    rw [hh]
  have hpE : ∀ x, sq x ≤ 1 → 0 < volume U₀ B₀ x := by
    intro x hx
    rw [volume_eq_germs U₀ u₀ B₀ β₀ x (hUgerm x (hDW x hx)) (hB₀germ x (hDW x hx))]
    exact hpos₀ x hx
  have hdE : ∀ x, sq x ≤ 1 → U₀ x ≠ 0 → 0 < U₀ x*curl B₁ x := by
    intro x hx hz
    have hw := hDW x hx
    have he : fderiv ℝ B₁ x = fderiv ℝ β₁ x := (hB₁germ x hw).fderiv_eq
    unfold curl
    rw [he,hUeq hw]
    exact hdiv x hx (by simpa only [hUeq hw] using hz)
  have hcE : ∀ x, sq x ≤ 1 → U₀ x = 0 → fderiv ℝ U₀ x (characteristic B₁ x) < 0 := by
    intro x hx hz
    have hw := hDW x hx
    rw [(hUgerm x hw).fderiv_eq]
    unfold characteristic
    rw [hB₁eq hw]
    exact hcross x hx (by simpa only [hUeq hw] using hz)
  have hLegE : ∀ x, sq x = 1 → B₀ x 0*(-x 1)+B₀ x 1*x 0 = 0 := by
    intro x hx
    rw [hB₀eq (hDW x hx.le)]
    exact hLegendrian x hx
  obtain ⟨v,K',hv,hK',hKK',hKD',hvzero,hvsign,hvfix,O₁,hO₁,hDO₁,hvpositive⟩ :=
    relative_representative_of_signed_data U₀ B₀ B₁ hU₀ hB₀ hB₁ hpE hdE hcE hLegE K hK hKD hBE
  let E₀ : Set P := {x | 0 < volume U₀ B₀ x}
  have hE₀ : IsOpen E₀ := isOpen_lt continuous_const (volume_smooth U₀ B₀ hU₀ hB₀).continuous
  let O := W ∩ (E₀ ∩ O₁)
  have hO : IsOpen O := hW.inter (hE₀.inter hO₁)
  refine ⟨v,K',O,hv,hK',hKK',hKD',hO,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    exact ⟨hDW x hx,hpE x hx,hDO₁ x hx⟩
  · exact fun x hx => hWN hx.1
  · intro x hx
    have hh := (hvzero x).symm
    rwa [hUeq hx.1] at hh
  · intro x hx hz
    have hn : U₀ x ≠ 0 := fun he => hz ((hvzero x).mpr he)
    have hh := hvsign x hn
    rw [hUeq hx.1] at hh
    simpa only [mul_comm] using hh
  · intro x hx hnot
    have hh := (hvfix x hnot).1
    rw [hUeq hx.1] at hh
    exact ⟨hh.symm,heq x (hWN hx.1) (fun hk => hnot (hKK' hk))⟩
  · intro x hx
    rw [← volume_eq_germs U₀ u₀ B₀ β₀ x (hUgerm x hx.1) (hB₀germ x hx.1)]
    exact hx.2.1
  · intro x hx
    rw [← volume_eq_germs v v B₁ β₁ x Filter.EventuallyEq.rfl (hB₁germ x hx.1)]
    exact hvpositive x hx.2.2

end
end ContactTopology.NormalMatching

open Set
open scoped ContDiff

theorem solution
    (N : Set (Fin 2 → ℝ)) (hN : IsOpen N) (hDN : ∀ x, (x 0^2+x 1^2) ≤ 1 → x ∈ N)
    (u₀ : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu₀ : ContDiffOn ℝ ∞ u₀ N) (hβ₀ : ContDiffOn ℝ ∞ β₀ N) (hβ₁ : ContDiffOn ℝ ∞ β₁ N)
    (hdiv : ∀ x, (x 0^2+x 1^2) ≤ 1 → u₀ x ≠ 0 → 0 < u₀ x*(fderiv ℝ β₁ x (Pi.single 0 1) 1-fderiv ℝ β₁ x (Pi.single 1 1) 0))
    (hcross : ∀ x, (x 0^2+x 1^2) ≤ 1 → u₀ x = 0 → fderiv ℝ u₀ x (![β₁ x 1,-β₁ x 0] : (Fin 2 → ℝ)) < 0)
    (hLegendrian : ∀ x, (x 0^2+x 1^2) = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKD : K ⊆ {x | (x 0^2+x 1^2) < 1})
    (heq : ∀ x ∈ N, x ∉ K → β₁ x = β₀ x) :
    let Q : ((Fin 2 → ℝ) → ℝ) → ((Fin 2 → ℝ) → (Fin 2 → ℝ)) → (Fin 2 → ℝ) → ℝ := fun u β x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    (∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → 0 < Q u₀ β₀ x) →
    ∃ v : (Fin 2 → ℝ) → ℝ, ∃ K' : Set (Fin 2 → ℝ), ∃ O : Set (Fin 2 → ℝ),
      ContDiff ℝ ∞ v ∧ IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ {x | (x 0^2+x 1^2) < 1} ∧
      IsOpen O ∧ (∀ x, (x 0^2+x 1^2) ≤ 1 → x ∈ O) ∧ O ⊆ N ∧
      (∀ x ∈ O, u₀ x = 0 ↔ v x = 0) ∧
      (∀ x ∈ O, v x ≠ 0 → 0 < u₀ x*v x) ∧
      (∀ x ∈ O, x ∉ K' → u₀ x = v x ∧ β₁ x = β₀ x) ∧
      (∀ x ∈ O, 0 < Q u₀ β₀ x) ∧ ∀ x ∈ O, 0 < Q v β₁ x := by
  dsimp only
  intro hpos₀
  exact ContactTopology.NormalMatching.local_relative_representative_of_signed_data
    N hN hDN u₀ β₀ β₁ hu₀ hβ₀ hβ₁ hpos₀ hdiv hcross hLegendrian K hK hKD heq
