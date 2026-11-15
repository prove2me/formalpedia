-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_fderiv_qMember_le_of_norm_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T11:34:58.904214+00:00
-- url     : https://prove2.me/submissions/5d642fbf-1bb4-4507-a597-dca00b7f2580

import Definitions.Def_FiniteEnergyPlane_QMember
import Theorems.Thm_CauchyRiemannIndex_exists_continuous_representative_of_mem_W1p
import Theorems.Thm_CauchyRiemannIndex_eq_of_continuous_periodic_ae_eq
import Theorems.Thm_JHolomorphic_bounded_iteratedFDeriv_of_sobolevNorm_le
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib
import Theorems.Thm_Nemytskii_exists_contDiff_superposition
import Theorems.Thm_Nemytskii_iteratedFDeriv_bounds_of_comp_compact
import Theorems.Thm_Nemytskii_iteratedFDeriv_bounds_of_partial
import Theorems.Thm_FiniteEnergyPlane_norm_iteratedFDeriv_intervalIntegral_le
import Theorems.Thm_FiniteEnergyPlane_exists_clm_boundedContinuous_rep
import Theorems.Thm_FiniteEnergyPlane_cylJ_iteratedFDeriv_bdd
import Theorems.Thm_FiniteEnergyPlane_memLp_four_of_exp_bound
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Theorems.Thm_CauchyRiemannIndex_finrank_quotient_eq_finrank_annihilator
import Theorems.Thm_CauchyRiemannIndex_memW1p_of_weak_solution
import Theorems.Thm_CauchyRiemannIndex_semiFredholm
import Theorems.Thm_CauchyRiemannIndex_crOp_formalAdjoint
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_contDiffOn_of_isWeakJHolomorphicOn
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_prodMk
import Theorems.Thm_JHolomorphic_memLp_of_continuousOn_compact
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq
import Theorems.Thm_FiniteEnergyPlane_exists_smooth_qPoint_rep
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_ball_of_energy_lt_top
import Theorems.Thm_FiniteEnergyPlane_hadamard_integral_fderiv
import Theorems.Thm_FiniteEnergyPlane_contDiff_qMember_of_qMap_eq_zero
import Theorems.Thm_FiniteEnergyPlane_exists_norm_qMember_le
import Definitions.Def_FiniteEnergyPlane_TubeFamily

open Metric Set Filter Topology BoundedContinuousFunction
open Metric Set Filter Topology MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open MeasureTheory Metric Set Filter Topology BoundedContinuousFunction
open scoped ENNReal ContDiff
open Metric Set Filter Topology
open scoped ContDiff

-- FILE: _imports_RSK_RP4N.lean


-- FILE: QSlope.lean
/-!
# Slope weights (local helper definition, not published as a definition)

`IsSlopeWeight χ a b`: `χ` is smooth, with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`.
-/

namespace FiniteEnergyPlane

open scoped ContDiff

/-! ### Slope weights are affine near the ends -/

theorem IsSlopeWeight.eq_right {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : 1 ≤ s) : χ s = χ 1 + b * (s - 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have hb : deriv χ c = b := h.2.2 c hc.1.le
  rw [hb, eq_div_iff (by linarith)] at hc'
  linarith

theorem IsSlopeWeight.eq_left {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : s ≤ -1) : χ s = χ (-1) + a * (s + 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have ha : deriv χ c = a := h.2.1 c hc.2.le
  rw [ha, eq_div_iff (by linarith)] at hc'
  linarith


end FiniteEnergyPlane

-- FILE: JWQ_S1.lean
/-!
# Q-S, part 1: matrices of real-linear maps `ℂ → ℂ`, the normal coefficient as such a matrix,
smoothness, periodicity, and the plane form (from `Jbar² = -1`).
-/

namespace FiniteEnergyPlane.QS

open Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

/-! ### smoothness of partial `w`-derivatives -/

theorem contDiff_cyl : ContDiff ℝ ∞ (fun q : ℝ × ℝ => cylInf q.1 q.2) := by
  unfold cylInf ccwLoop
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => ((Real.exp (2 * π * q.1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst))
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => ((2 * π * q.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd)
  exact h1.mul (Complex.contDiff_exp.comp (h2.mul contDiff_const))

/-! ### antilinearity of `∂_w Jbar(z, 0)` in the tangential slot -/

/-! ### plane form -/

/-! ### smoothness and periodicity of the entries -/

end

end FiniteEnergyPlane.QS

-- FILE: JWQ_N6.lean
/-!
# Q-N, layer 6 (local, NOT published): `qMap 0 = 0` and the derivative of `qMap` at `0`

Decoupled from the smoothness proof: assuming only that `qMap` is differentiable at `0` and that
its components are the `L⁴` classes of the pointwise formula near `0`, the derivative in the
directions `(ζ, 0, 0)` and `(0, 0, ζ)` is identified a.e. through difference quotients along
`r_n = 1/(n+1)` (an `L⁴`-convergent sequence has an a.e.-convergent subsequence).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

namespace QN

/-! ### `ℂ ↔ ℝ²` and `toLpOrZero` -/

lemma cToVec_vecToC (a : Vec 1) : cToVec (vecToC a) = a := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [cToVec, vecToC]

lemma cToVec_add (a b : ℂ) : cToVec (a + b) = cToVec a + cToVec b := by
  ext i; rcases i with i | i <;> simp [cToVec]

lemma cToVec_smul (r : ℝ) (a : ℂ) : cToVec ((r : ℂ) * a) = r • cToVec a := by
  ext i; rcases i with i | i <;> simp [cToVec]

/-! ### The pointwise formula in terms of values -/

lemma jStd_apply (a b : ℂ) : jStd (a, b) = (Complex.I * a, Complex.I * b) := by
  simp [jStd]

/-! ### The a.e. limit of difference quotients -/

/-! ### Values of scaled unknowns -/

end QN

namespace QN18

/-! ### `ℂ → ℝ²` as a continuous linear map -/

/-- `vecToC` as a continuous linear map. -/
def vL : Vec 1 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := vecToC
      map_add' := fun a b => by apply Complex.ext <;> simp [vecToC]
      map_smul' := fun c a => by apply Complex.ext <;> simp [vecToC] }

@[simp] lemma vL_apply (a : Vec 1) : vL a = vecToC a := rfl

/-- `cToVec` as a continuous linear map. -/
def cL : ℂ →L[ℝ] Vec 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := cToVec
      map_add' := QN.cToVec_add
      map_smul' := fun r a => by
        have := QN.cToVec_smul r a
        simpa [Complex.real_smul] using this }

@[simp] lemma cL_apply (a : ℂ) : cL a = cToVec a := rfl

end QN18

end

end FiniteEnergyPlane

-- FILE: RSK_N19.lean
/-!
# Q-N, layer 19 (local, NOT published): the value map `U : QDom →L C_b(ℝ × ℝ, ℂ³)`

`U x = (vecToC ∘ T̃, vecToC ∘ Ñ, c)`, with `T̃`, `Ñ` the continuous periodic representatives of the
first components (abcf43a8); linear by uniqueness of continuous periodic representatives.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal BoundedContinuousFunction

noncomputable section

namespace QN19W

open QN QN18

lemma rep_spec : ∃ C : ℝ, ∀ w ∈ W1p 4 1,
      (∃ g : ℝ × ℝ → Vec 1, Continuous g ∧ (∀ s t, g (s, t + 1) = g (s, t)) ∧
        (w.1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] g) ∧
      ∀ g : ℝ × ℝ → Vec 1, Continuous g → (∀ s t, g (s, t + 1) = g (s, t)) →
        (w.1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] g →
        (∀ x, ‖g x‖ ≤ C * ‖w‖) ∧ ∀ ε > 0, ∃ R : ℝ, ∀ s t, R < |s| → ‖g (s, t)‖ < ε :=
  exists_continuous_representative_of_mem_W1p 4 (by norm_num) (by simp) 1

/-- The representative constant. -/
def wC : ℝ := Classical.choose rep_spec

/-- The continuous periodic representative of the first component. -/
def wrep (w : ↥(W1p 4 1)) : ℝ × ℝ → Vec 1 := Classical.choose ((Classical.choose_spec rep_spec w w.2).1)

lemma wrep_prop (w : ↥(W1p 4 1)) : Continuous (wrep w) ∧ (∀ s t, wrep w (s, t + 1) = wrep w (s, t)) ∧
    (((w : Triple 1 4).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] wrep w) :=
  Classical.choose_spec ((Classical.choose_spec rep_spec w w.2).1)

lemma wrep_bound (w : ↥(W1p 4 1)) (q : ℝ × ℝ) : ‖wrep w q‖ ≤ wC * ‖w‖ :=
  ((Classical.choose_spec rep_spec w w.2).2 (wrep w) (wrep_prop w).1 (wrep_prop w).2.1 (wrep_prop w).2.2).1 q

lemma wrep_add (w w' : ↥(W1p 4 1)) : wrep (w + w') = wrep w + wrep w' := by
  refine eq_of_continuous_periodic_ae_eq (wrep_prop _).1 ((wrep_prop w).1.add (wrep_prop w').1)
    (wrep_prop _).2.1 (fun s t => by simp [(wrep_prop w).2.1, (wrep_prop w').2.1]) ?_
  have h1 := (wrep_prop (w + w')).2.2
  have h2 : (((w + w' : ↥(W1p 4 1)) : Triple 1 4).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure]
      (((w : Triple 1 4).1 : ℝ × ℝ → Vec 1) + ((w' : Triple 1 4).1 : ℝ × ℝ → Vec 1)) :=
    Lp.coeFn_add _ _
  filter_upwards [h1, h2, (wrep_prop w).2.2, (wrep_prop w').2.2] with q a b c d
  rw [← a, b, Pi.add_apply, c, d]; rfl

lemma wrep_smul (r : ℝ) (w : ↥(W1p 4 1)) : wrep (r • w) = r • wrep w := by
  refine eq_of_continuous_periodic_ae_eq (wrep_prop _).1 ((wrep_prop w).1.const_smul r)
    (wrep_prop _).2.1 (fun s t => by simp [(wrep_prop w).2.1]) ?_
  have h1 := (wrep_prop (r • w)).2.2
  have h2 : (((r • w : ↥(W1p 4 1)) : Triple 1 4).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure]
      r • ((w : Triple 1 4).1 : ℝ × ℝ → Vec 1) :=
    Lp.coeFn_smul _ _
  filter_upwards [h1, h2, (wrep_prop w).2.2] with q a b c
  rw [← a, b, Pi.smul_apply, c]; rfl

/-- The operator constant of `U`. -/
def UK : ℝ := ‖vL‖ * max wC 0 + 1

lemma UK_pos : 0 < UK := by unfold UK; positivity

lemma comp_bound (w : ↥(W1p 4 1)) (x : QDom) (hw : ‖w‖ ≤ ‖x‖) (q : ℝ × ℝ) :
    ‖vL (wrep w q)‖ ≤ UK * ‖x‖ := by
  calc ‖vL (wrep w q)‖ ≤ ‖vL‖ * ‖wrep w q‖ := vL.le_opNorm _
    _ ≤ ‖vL‖ * (max wC 0 * ‖x‖) := by
        refine mul_le_mul_of_nonneg_left ((wrep_bound w q).trans ?_) (norm_nonneg _)
        exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hw (le_max_right _ _))
    _ ≤ UK * ‖x‖ := by
        rw [← mul_assoc]; unfold UK
        nlinarith [norm_nonneg x, norm_nonneg vL, le_max_right wC 0]

/-- The pointwise values. -/
def Uv (x : QDom) (q : ℝ × ℝ) : ℂ × ℂ × ℂ := (vL (wrep x.1 q), vL (wrep x.2.2 q), x.2.1)

lemma Uv_continuous (x : QDom) : Continuous (Uv x) :=
  (vL.continuous.comp (wrep_prop x.1).1).prodMk
    ((vL.continuous.comp (wrep_prop x.2.2).1).prodMk continuous_const)

lemma Uv_bound (x : QDom) (q : ℝ × ℝ) : ‖Uv x q‖ ≤ UK * ‖x‖ := by
  have h1 : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
  have h3 : ‖x.2.2‖ ≤ ‖x‖ := (norm_snd_le x.2).trans (norm_snd_le x)
  have h2 : ‖x.2.1‖ ≤ ‖x‖ := (norm_fst_le x.2).trans (norm_snd_le x)
  have hK : ‖x‖ ≤ UK * ‖x‖ := by
    have : 1 ≤ UK := by unfold UK; nlinarith [norm_nonneg vL, le_max_right wC 0]
    nlinarith [norm_nonneg x]
  refine norm_prod_le_iff.2 ⟨comp_bound _ x h1 q, norm_prod_le_iff.2 ⟨comp_bound _ x h3 q, h2.trans hK⟩⟩

/-- `U x` as a bounded continuous function. -/
def Uf (x : QDom) : ℝ × ℝ →ᵇ ℂ × ℂ × ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (Uv x) (Uv_continuous x) (UK * ‖x‖) (Uv_bound x)

@[simp] lemma Uf_apply (x : QDom) (q : ℝ × ℝ) : Uf x q = Uv x q := rfl

/-- `U` as a linear map. -/
def Ul : QDom →ₗ[ℝ] (ℝ × ℝ →ᵇ ℂ × ℂ × ℂ) where
  toFun := Uf
  map_add' := fun x y => by
    ext q <;> simp [Uv, wrep_add, -vL_apply]
  map_smul' := fun r x => by
    ext q <;> simp [Uv, wrep_smul, -vL_apply]

lemma Ul_bound (x : QDom) : ‖Ul x‖ ≤ UK * ‖x‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by
    have := UK_pos; positivity) (Uv_bound x)

/-- **The value map.** -/
def U : QDom →L[ℝ] (ℝ × ℝ →ᵇ ℂ × ℂ × ℂ) :=
  ⟨Ul, (Ul.mkContinuous UK Ul_bound).continuous⟩

lemma U_apply (x : QDom) (q : ℝ × ℝ) : U x q = Uv x q := rfl

end QN19W

end

end FiniteEnergyPlane

-- FILE: RSK_R0.lean
/-!
# Q-R, layer 0 (local, NOT published): the plane family of a curve in `QDom`

For `y ∈ QDom` and `z = cylInf s t ≠ 0`, the linear part is
`pLc z y = (e^{χT(s)} ũT(s,t), β(s) c + e^{χN(s)} ũN(s,t))`, with `ũ` the continuous periodic
representatives (`QN19W.U`); at `z = 0` it is `(0, c)`. The member of `x` is `pG x z = (z, 0) + pLc z x`,
and the family of a curve `γ` is `fam γ (z, t) = pG (γ t) z`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal BoundedContinuousFunction

noncomputable section

namespace QR

open QN19W

/-- Cylinder coordinates of `z ≠ 0`. -/
def zc (z : ℂ) : ℝ × ℝ := (Real.log ‖z‖ / (2 * π), Complex.arg z / (2 * π))

/-- Evaluation of `U` at a point of the cylinder. -/
def evU (q : ℝ × ℝ) : QDom →L[ℝ] ℂ × ℂ × ℂ :=
  (BoundedContinuousFunction.evalCLM ℝ q).comp U

@[simp] lemma evU_apply (q : ℝ × ℝ) (y : QDom) : evU q y = U y q := rfl

/-- The constant coordinate. -/
def cP : QDom →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℂ (↥(W1p 4 1))).comp (ContinuousLinearMap.snd ℝ (↥(W1p 4 1)) _)

@[simp] lemma cP_apply (y : QDom) : cP y = y.2.1 := rfl

/-- The weighted value map at the cylinder point `q`. -/
def wV (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) : QDom →L[ℝ] ℂ × ℂ :=
  (((Real.exp (χT q.1) : ℂ) • ContinuousLinearMap.fst ℝ ℂ (ℂ × ℂ)).prod
    ((β q.1 : ℂ) • ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp (ContinuousLinearMap.snd ℝ ℂ (ℂ × ℂ))) +
      (Real.exp (χN q.1) : ℂ) • ((ContinuousLinearMap.fst ℝ ℂ ℂ).comp
        (ContinuousLinearMap.snd ℝ ℂ (ℂ × ℂ))))).comp (evU q)

lemma wV_apply (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (y : QDom) :
    wV χT χN β q y = ((Real.exp (χT q.1) : ℂ) * (U y q).1,
      (β q.1 : ℂ) * (U y q).2.2 + (Real.exp (χN q.1) : ℂ) * (U y q).2.1) := rfl

open Classical in
/-- The linear part of a member, as a CLM in `y` for fixed `z`. -/
def pLc (χT χN β : ℝ → ℝ) (z : ℂ) : QDom →L[ℝ] ℂ × ℂ :=
  if z = 0 then (ContinuousLinearMap.inr ℝ ℂ ℂ).comp cP else wV χT χN β (zc z)

lemma pLc_zero (χT χN β : ℝ → ℝ) (y : QDom) : pLc χT χN β 0 y = (0, y.2.1) := by
  simp [pLc]

lemma pLc_ne (χT χN β : ℝ → ℝ) {z : ℂ} (hz : z ≠ 0) (y : QDom) :
    pLc χT χN β z y = wV χT χN β (zc z) y := by
  simp [pLc, hz]

/-- The member of `x`. -/
def pG (χT χN β : ℝ → ℝ) (x : QDom) (z : ℂ) : ℂ × ℂ := (z, 0) + pLc χT χN β z x

@[simp] lemma pG_zero (χT χN β : ℝ → ℝ) (z : ℂ) : pG χT χN β 0 z = (z, 0) := by
  simp [pG]

end QR

end

end FiniteEnergyPlane

-- FILE: RSK_RB.lean
/-!
# Q-R bridge (local, NOT published): the local plane maps `pG`/`fam` are the published
`qMember`/`qFamily`
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QRB

open QR QN18 QN19W

lemma qRep_eq_wrep (w : ↥(W1p 4 1)) : qRep w = wrep w := by
  have hex : ∃ g : ℝ × ℝ → Vec 1, Continuous g ∧ (∀ s t, g (s, t + 1) = g (s, t)) ∧
      (((w : Triple 1 4).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] g) := ⟨wrep w, wrep_prop w⟩
  have hs := Classical.choose_spec hex
  unfold qRep
  rw [dif_pos hex]
  exact eq_of_continuous_periodic_ae_eq hs.1 (wrep_prop w).1 hs.2.1 (wrep_prop w).2.1
    (hs.2.2.symm.trans (wrep_prop w).2.2)

lemma pG_eq_qMember (χT χN β : ℝ → ℝ) : pG χT χN β = qMember χT χN β := by
  funext x z
  by_cases hz : z = 0
  · subst hz
    simp [pG, pLc_zero, qMember]
  · rw [pG, pLc_ne χT χN β hz, wV_apply]
    simp only [qMember, if_neg hz, U_apply, Uv, vL_apply, qRep_eq_wrep, zc, cylCoord]
    ext <;> simp

end QRB

end

end FiniteEnergyPlane

-- FILE: RSK_R11.lean
/-!
# Q-R, layer 11 (local, NOT published): variable-fibre graph structures and uniform bounds

* `vgJ Jf m`: on `ℂ × F × ℂ` (base, fibre, parameters),
  `J̃(e)(a, v, p) = (i a, Jf(e) v + Re a · Jf(e) m(e) + Im a · m(e), i p)`.
  It squares to `-1` wherever `Jf(e)` does, it is smooth when `Jf` and `m` are, and the graph
  `ζ ↦ (c + ζ, v ζ, p₀)` is `J̃`-holomorphic iff `∂ₛv + Jf ∂ₜv + m = 0`.
  The parameter block (`i` on the last factor) lets constants that range over a compact set
  enter `Jf` and `m` as target coordinates.
* `bound_const`: for one fixed almost complex structure, Thm 2.22(2a) gives a uniform `C¹` bound
  on a compact subset of the unit disc for all `W^{1,4}`-bounded holomorphic maps into a compact.
* `sobolevNorm_one_le`, `eLpNorm_fderiv_graph_le`: the `W^{1,p}` bound of a graph.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology JHolomorphic DbarRegularity
open scoped ContDiff ENNReal NNReal

noncomputable section

namespace QR11

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The variable-fibre graph structure on `ℂ × F × ℂ`. -/
def vgJ (Jf : ℂ × F × ℂ → F →L[ℝ] F) (m : ℂ × F × ℂ → F) (e : ℂ × F × ℂ) :
    (ℂ × F × ℂ) →L[ℝ] (ℂ × F × ℂ) :=
  ((Complex.I • ContinuousLinearMap.id ℝ ℂ).comp (ContinuousLinearMap.fst ℝ ℂ (F × ℂ))).prod
    (((Jf e).comp ((ContinuousLinearMap.fst ℝ F ℂ).comp (ContinuousLinearMap.snd ℝ ℂ (F × ℂ))) +
      (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ (F × ℂ))).smulRight (Jf e (m e)) +
      (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ (F × ℂ))).smulRight (m e)).prod
    ((Complex.I • ContinuousLinearMap.id ℝ ℂ).comp
      ((ContinuousLinearMap.snd ℝ F ℂ).comp (ContinuousLinearMap.snd ℝ ℂ (F × ℂ)))))

lemma vgJ_apply (Jf : ℂ × F × ℂ → F →L[ℝ] F) (m : ℂ × F × ℂ → F) (e y : ℂ × F × ℂ) :
    vgJ Jf m e y = (Complex.I * y.1,
      Jf e y.2.1 + y.1.re • Jf e (m e) + y.1.im • m e, Complex.I * y.2.2) := by
  simp [vgJ]

lemma vgJ_sq (Jf : ℂ × F × ℂ → F →L[ℝ] F) (m : ℂ × F × ℂ → F) (e : ℂ × F × ℂ)
    (hJ : ∀ v, Jf e (Jf e v) = -v) :
    (vgJ Jf m e).comp (vgJ Jf m e) = -ContinuousLinearMap.id ℝ (ℂ × F × ℂ) := by
  refine ContinuousLinearMap.ext fun y => ?_
  rw [ContinuousLinearMap.comp_apply, vgJ_apply, vgJ_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.fst_neg]
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.snd_neg,
      Prod.fst_neg, map_add, map_smul, hJ, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_sub, add_zero, smul_neg, neg_smul]
    abel
  · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.snd_neg]
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

variable [FiniteDimensional ℝ F]

lemma contDiff_vgJ {Jf : ℂ × F × ℂ → F →L[ℝ] F} {m : ℂ × F × ℂ → F}
    (hJ : ContDiff ℝ ∞ Jf) (hm : ContDiff ℝ ∞ m) : ContDiff ℝ ∞ (vgJ Jf m) := by
  rw [contDiff_clm_apply_iff]
  intro y
  simp only [vgJ_apply]
  exact contDiff_const.prodMk ((((hJ.clm_apply contDiff_const).add
    ((hJ.clm_apply hm).const_smul _)).add (hm.const_smul _)).prodMk contDiff_const)

/-- `vgJ` is an almost complex structure on the whole space. -/
lemma isAlmostComplexOn_vgJ {Jf : ℂ × F × ℂ → F →L[ℝ] F} {m : ℂ × F × ℂ → F}
    (hJ : ContDiff ℝ ∞ Jf) (hm : ContDiff ℝ ∞ m) (hsq : ∀ e v, Jf e (Jf e v) = -v) :
    IsAlmostComplexOn (vgJ Jf m) univ :=
  ⟨isOpen_univ, (contDiff_vgJ hJ hm).contDiffOn, fun e _ => vgJ_sq Jf m e (hsq e)⟩

/-! ### Graphs -/

/-- The graph of `v` over the translate `c + ζ`, with constant parameter `p₀`. -/
def graph (c : ℂ) (v : ℂ → F) (p₀ : ℂ) (ζ : ℂ) : ℂ × F × ℂ := (c + ζ, v ζ, p₀)

lemma hasFDerivAt_graph (c : ℂ) {v : ℂ → F} (p₀ : ℂ) {ζ : ℂ} (hv : DifferentiableAt ℝ v ζ) :
    HasFDerivAt (graph c v p₀) ((ContinuousLinearMap.id ℝ ℂ).prod
      ((fderiv ℝ v ζ).prod (0 : ℂ →L[ℝ] ℂ))) ζ :=
  ((hasFDerivAt_id ζ).const_add c).prodMk (hv.hasFDerivAt.prodMk (hasFDerivAt_const p₀ ζ))

lemma fderiv_graph_apply (c : ℂ) {v : ℂ → F} (p₀ : ℂ) {ζ : ℂ} (hv : DifferentiableAt ℝ v ζ)
    (h : ℂ) : fderiv ℝ (graph c v p₀) ζ h = (h, fderiv ℝ v ζ h, 0) := by
  rw [(hasFDerivAt_graph c p₀ hv).fderiv]; rfl

lemma dbarJ_graph (Jf : ℂ × F × ℂ → F →L[ℝ] F) (m : ℂ × F × ℂ → F) (c : ℂ) {v : ℂ → F}
    (p₀ : ℂ) {ζ : ℂ} (hv : DifferentiableAt ℝ v ζ) :
    dbarJ (vgJ Jf m) (graph c v p₀) ζ = (0, fderiv ℝ v ζ 1 +
      Jf (graph c v p₀ ζ) (fderiv ℝ v ζ Complex.I) + m (graph c v p₀ ζ), 0) := by
  rw [dbarJ, fderiv_graph_apply c p₀ hv, fderiv_graph_apply c p₀ hv, vgJ_apply]
  simp only [Complex.I_re, Complex.I_im, zero_smul, add_zero, one_smul, mul_zero]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp
  · simp only [Prod.snd_add, Prod.fst_add]; abel
  · simp

/-- The graph of a solution of `∂ₛv + Jf ∂ₜv + m = 0` is `vgJ`-holomorphic. -/
lemma isJHolomorphicOn_graph (Jf : ℂ × F × ℂ → F →L[ℝ] F) (m : ℂ × F × ℂ → F) (c : ℂ)
    {v : ℂ → F} (p₀ : ℂ) {U : Set ℂ} (hv : ∀ ζ ∈ U, DifferentiableAt ℝ v ζ)
    (heq : ∀ ζ ∈ U, fderiv ℝ v ζ 1 + Jf (graph c v p₀ ζ) (fderiv ℝ v ζ Complex.I) +
      m (graph c v p₀ ζ) = 0) :
    IsJHolomorphicOn (vgJ Jf m) U (graph c v p₀) := by
  intro ζ hζ
  refine ⟨(hasFDerivAt_graph c p₀ (hv ζ hζ)).differentiableAt, ?_⟩
  rw [dbarJ_graph Jf m c p₀ (hv ζ hζ), heq ζ hζ]
  rfl

lemma norm_fderiv_le_graph (c : ℂ) {v : ℂ → F} (p₀ : ℂ) {ζ : ℂ} (hv : DifferentiableAt ℝ v ζ) :
    ‖fderiv ℝ v ζ‖ ≤ ‖fderiv ℝ (graph c v p₀) ζ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h => ?_
  have e : fderiv ℝ v ζ h = (fderiv ℝ (graph c v p₀) ζ h).2.1 := by
    rw [fderiv_graph_apply c p₀ hv]
  rw [e]
  exact ((norm_fst_le _).trans (norm_snd_le _)).trans ((fderiv ℝ (graph c v p₀) ζ).le_opNorm h)

lemma norm_fderiv_graph_le (c : ℂ) {v : ℂ → F} (p₀ : ℂ) {ζ : ℂ} (hv : DifferentiableAt ℝ v ζ) :
    ‖fderiv ℝ (graph c v p₀) ζ‖ ≤ 1 + ‖fderiv ℝ v ζ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [fderiv_graph_apply c p₀ hv]
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · nlinarith [norm_nonneg h, norm_nonneg (fderiv ℝ v ζ)]
  · have := (fderiv ℝ v ζ).le_opNorm h
    nlinarith [norm_nonneg h]
  · rw [norm_zero]; positivity

lemma norm_graph_le (c : ℂ) (v : ℂ → F) (p₀ : ℂ) (ζ : ℂ) :
    ‖graph c v p₀ ζ‖ ≤ ‖c + ζ‖ + ‖v ζ‖ + ‖p₀‖ := by
  have h1 := norm_nonneg (c + ζ)
  have h2 := norm_nonneg (v ζ)
  have h3 := norm_nonneg p₀
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · show ‖c + ζ‖ ≤ _; linarith
  · show ‖v ζ‖ ≤ _; linarith
  · show ‖p₀‖ ≤ _; linarith

/-! ### Sobolev norms -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sobolevNorm_one_eq (p : ℝ≥0∞) (U : Set ℂ) (φ : ℂ → E) :
    sobolevNorm 1 p U φ = eLpNorm φ p (volume.restrict U) +
      eLpNorm (fderiv ℝ φ) p (volume.restrict U) := by
  rw [sobolevNorm, Finset.sum_range_succ, Finset.sum_range_one]
  congr 1
  · exact eLpNorm_congr_norm_ae (Eventually.of_forall fun z => norm_iteratedFDeriv_zero)
  · exact eLpNorm_congr_norm_ae (Eventually.of_forall fun z => norm_iteratedFDeriv_one φ)

/-- The `W^{1,p}` norm of a bounded map with an `L^p` bound of its derivative. -/
lemma sobolevNorm_one_le {p : ℝ≥0∞} {U : Set ℂ} {φ : ℂ → E} {A : ℝ}
    (hA : ∀ z ∈ U, ‖φ z‖ ≤ A) (hU : MeasurableSet U) :
    sobolevNorm 1 p U φ ≤ eLpNorm (fun _ : ℂ => A) p (volume.restrict U) +
      eLpNorm (fderiv ℝ φ) p (volume.restrict U) := by
  rw [sobolevNorm_one_eq]
  gcongr
  exact eLpNorm_mono_ae_real ((ae_restrict_iff' hU).2 (Eventually.of_forall hA))

/-- The derivative of a graph in `L^p`. -/
lemma eLpNorm_fderiv_graph_le {p : ℝ≥0∞} (hp : 1 ≤ p) {U : Set ℂ} (hU : IsOpen U) (c : ℂ)
    {v : ℂ → F} (p₀ : ℂ) (hv : ContDiffOn ℝ 1 v U) :
    eLpNorm (fderiv ℝ (graph c v p₀)) p (volume.restrict U) ≤
      eLpNorm (fun _ : ℂ => (1 : ℝ)) p (volume.restrict U) +
        eLpNorm (fderiv ℝ v) p (volume.restrict U) := by
  have hd : ∀ ζ ∈ U, DifferentiableAt ℝ v ζ := fun ζ hζ =>
    (hv.differentiableOn one_ne_zero ζ hζ).differentiableAt (hU.mem_nhds hζ)
  have hc : ContinuousOn (fderiv ℝ v) U := hv.continuousOn_fderiv_of_isOpen hU le_rfl
  have h1 : eLpNorm (fderiv ℝ (graph c v p₀)) p (volume.restrict U) ≤
      eLpNorm ((fun _ : ℂ => (1 : ℝ)) + fun ζ => ‖fderiv ℝ v ζ‖) p (volume.restrict U) := by
    refine eLpNorm_mono_ae_real ((ae_restrict_iff' hU.measurableSet).2
      (Eventually.of_forall fun ζ hζ => ?_))
    exact norm_fderiv_graph_le c p₀ (hd ζ hζ)
  refine h1.trans ((eLpNorm_add_le aestronglyMeasurable_const
    (hc.norm.aestronglyMeasurable hU.measurableSet) hp).trans ?_)
  gcongr
  exact (eLpNorm_norm _).le

/-! ### The uniform bound for one structure -/

variable [FiniteDimensional ℝ E]

/-- Thm 2.22(2a) for a constant sequence of structures, as a uniform bound. -/
theorem bound_const (J : E → E →L[ℝ] E) (O K₀ : Set E) (hJ : IsAlmostComplexOn J O)
    (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O) (K : Set ℂ) (hK : K ⊆ ball (0 : ℂ) 1)
    (hKc : IsCompact K) (C : ℝ≥0) :
    ∃ M : ℝ, ∀ u : ℂ → E, ContDiffOn ℝ ∞ u (ball 0 1) → IsJHolomorphicOn J (ball 0 1) u →
      MapsTo u (ball 0 1) K₀ → sobolevNorm 1 (ENNReal.ofReal 4) (ball 0 1) u ≤ C →
      ∀ z ∈ K, ‖fderiv ℝ u z‖ ≤ M := by
  by_contra hne
  push_neg at hne
  choose u hu hhol hmaps hC z hz hbig using fun ν : ℕ => hne ν
  have hconv : TendstoCInftyLocOn (fun _ : ℕ => J) J O := fun K' _ _ m =>
    Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun _ x _ => by
      simpa using hε
  obtain ⟨M, hM⟩ := bounded_iteratedFDeriv_of_sobolevNorm_le 4 (by norm_num) J (fun _ => J) O K₀
    hJ (fun _ => hJ) hconv hK₀ hK₀O u hu hhol hmaps C hC K hK hKc 1
  obtain ⟨ν, hν⟩ := exists_nat_gt M
  have h1 := hM ν (z ν) (hz ν)
  rw [norm_iteratedFDeriv_one] at h1
  linarith [hbig ν]

end QR11

end

end FiniteEnergyPlane

-- FILE: NEM_Base.lean
/-!
# Nemytskii operators on bounded continuous functions: base layer (spike (e))

`nem Φ u = (x ↦ Φ x (u x))` on `X →ᵇ E`, its continuity, and the pointwise-application
operator `pmul : (X →ᵇ (E →L F)) →L (X →ᵇ E) →L (X →ᵇ F)`.
-/


noncomputable section

namespace NEM

universe u v

variable {X : Type u} [TopologicalSpace X]
  {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]

end NEM

-- FILE: NSK_Nem.lean
/-!
# Q-N sketch: the Nemytskii interface over the published children

The class `UC` is the derivative-bound hypothesis of `Nemytskii.exists_contDiff_superposition`
(the index `n` is kept so the later layers read unchanged). Smoothness of the Nemytskii operator,
and the two ways of producing such integrands, come from the published children
`Nemytskii.exists_contDiff_superposition`, `Nemytskii.iteratedFDeriv_bounds_of_comp_compact` and
`Nemytskii.iteratedFDeriv_bounds_of_partial`. The value map `QN19.U` is the published
`exists_clm_boundedContinuous_rep`.
-/


noncomputable section

namespace NEM

universe u v

variable {X : Type u} [TopologicalSpace X] {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

end NEM

namespace FiniteEnergyPlane

open CauchyRiemannIndex

namespace QN19

/-- The value map (published child `exists_clm_boundedContinuous_rep`). -/
def U : QDom →L[ℝ] (ℝ × ℝ →ᵇ ℂ × ℂ × ℂ) := Classical.choose exists_clm_boundedContinuous_rep

def UK : ℝ := ‖U‖ + 1

lemma UK_pos : 0 < UK := by unfold UK; positivity

end QN19

end FiniteEnergyPlane

-- FILE: NSK_Lp.lean
/-!
# Spike (e), milestone 3 piece: multiplication `C_b × Lᵖ → Lᵖ`

For a continuous bilinear `B : G →L E →L F`, `(f, g) ↦ (x ↦ B (f x) (g x))` is a continuous
bilinear map `(X →ᵇ G) →L (Lp E p μ →L Lp F p μ)`. Composed with `NEM.nem`, this gives the
smoothness of `u ↦ Φ(·, u) · g` into `Lᵖ`, which is the shape of the `Jbar(G) ∂ₜG` term of `qMap`.
-/


noncomputable section

namespace NEM

universe u v

variable {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [SecondCountableTopology X] {μ : Measure X}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E F G : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

end NEM

-- FILE: NSK_N9.lean
/-!
# Q-N, layer 9 (local, NOT published): Nemytskii integrands from derivative bounds

* `NEM.partial_of_bdd`: for `Ψ` jointly `C^∞` on `P × E` with derivative bounds on
  `range p × closedBall 0 R`, the partial maps `a ↦ Ψ (p x, a)` satisfy the hypotheses of
  `uc_of_iteratedFDeriv` / `uc_of_comp_clm` (no compactness).
* `BddDerivOn`, `BddDeriv1On`: smooth maps with bounded derivatives (of order `≥ 1`) on a set;
  closed under bilinear products, composition, sums; CLMs and constants.
-/


noncomputable section



namespace QN9

variable {Y Z W : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

end QN9

-- FILE: NSK_N2.lean
/-!
# Q-N, layer 2: the worked `-∞` instance of the `c`-term shortcut (local, NOT published)

The zero-order term `e^{-χ}(Jbar(ψ, v) - jStd)(2πi z, 0)` near `s = -∞`, cut off to `s ≤ 1`, equals
`B(Ψ(p(x), u(x)), m(x))` with
* `m = κ₀(s) e^{-χ(s)} z`, a FIXED function in `L⁴` (independent of `x`'s values and of `c`),
* `Ψ` jointly `C^∞` and `p` continuous with bounded range, so `Ψ(p(·), ·)` lies in every `UC n`,
* `B(G, m) = G(2πi m, 0)` continuous bilinear.
The constant `c` rides in the value variable on the `C_b` side. Hence `u ↦ mulLp B (nem Φ u) m` is
`C^∞` (no weighted Nemytskii operator needed).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex BoundedContinuousFunction
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Cut-offs and the value retraction -/

/-- A smooth map `ℂ → ℂ`, the identity on `ball 0 (ρ/4)`, with values in `ball 0 ρ`. -/
def rtr (ρ : ℝ) (v : ℂ) : ℂ :=
  ((1 - Real.smoothTransition (Complex.normSq v / (ρ / 4) ^ 2 - 1) : ℝ) : ℂ) * v

lemma rtr_contDiff (ρ : ℝ) : ContDiff ℝ ∞ (rtr ρ) := by
  have hn : ContDiff ℝ ∞ (fun v : ℂ => Complex.normSq v) := by
    have : (fun v : ℂ => Complex.normSq v) = fun v => v.re * v.re + v.im * v.im := by
      funext v; rw [Complex.normSq_apply]
    rw [this]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hs : ContDiff ℝ ∞ (fun v : ℂ =>
      1 - Real.smoothTransition (Complex.normSq v / (ρ / 4) ^ 2 - 1)) :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((hn.div_const _).sub contDiff_const))
  exact (Complex.ofRealCLM.contDiff.comp hs).mul contDiff_id

lemma rtr_eq {ρ : ℝ} (hρ : 0 < ρ) {v : ℂ} (hv : ‖v‖ < ρ / 4) : rtr ρ v = v := by
  have h1 : Complex.normSq v < (ρ / 4) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_lt_pow_left₀ hv (norm_nonneg _) two_ne_zero
  have h2 : Complex.normSq v / (ρ / 4) ^ 2 - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one (by positivity)]; exact h1.le
  simp [rtr, Real.smoothTransition.zero_of_nonpos h2]

lemma norm_rtr_lt {ρ : ℝ} (hρ : 0 < ρ) (v : ℂ) : ‖rtr ρ v‖ < ρ := by
  set σ := 1 - Real.smoothTransition (Complex.normSq v / (ρ / 4) ^ 2 - 1)
  have hσ0 : 0 ≤ σ := by simp [σ, Real.smoothTransition.le_one]
  have hσ1 : σ ≤ 1 := by simp [σ, Real.smoothTransition.nonneg]
  have hnorm : ‖rtr ρ v‖ = σ * ‖v‖ := by
    simp only [rtr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ0, σ]
  rw [hnorm]
  by_cases hv : Complex.normSq v / (ρ / 4) ^ 2 - 1 < 1
  · have h2 : ‖v‖ ^ 2 < ρ ^ 2 := by
      have h3 : Complex.normSq v < 2 * (ρ / 4) ^ 2 := by
        have := (div_lt_iff₀ (by positivity : (0 : ℝ) < (ρ / 4) ^ 2)).1 (by linarith : _ < (2 : ℝ))
        linarith
      rw [← Complex.normSq_eq_norm_sq]; nlinarith
    have h4 : ‖v‖ < ρ := lt_of_pow_lt_pow_left₀ 2 hρ.le h2
    calc σ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hσ1 (norm_nonneg _)
      _ < ρ := by linarith
  · have : σ = 0 := by
      simp [σ, Real.smoothTransition.one_of_one_le (not_lt.1 hv)]
    rw [this, zero_mul]; exact hρ

/-! ### Bounds for functions of `s` -/

/-- `e^{χ}` is bounded on `(-∞, -1]` for a weight with slope `π` there. -/
lemma exp_le_left {χ : ℝ → ℝ} {b : ℝ} (h : IsSlopeWeight χ π b) {s : ℝ} (hs : s ≤ -1) :
    Real.exp (χ s) ≤ Real.exp (χ (-1)) := by
  rw [h.eq_left hs]; exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])

/-! ### The worked instance -/

end

end FiniteEnergyPlane

-- FILE: NSK_N3.lean
/-!
# Q-N, layer 3: the `+∞` Lipschitz bound `‖cylJ(s, t, w) - jStd‖ ≤ C ‖w‖` (local, NOT published)
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

lemma cylInf_ne_zero (s t : ℝ) : cylInf s t ≠ 0 := by
  unfold cylInf ccwLoop
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne') (Complex.exp_ne_zero _)

end

end FiniteEnergyPlane

-- FILE: NSK_N5.lean
/-!
# Q-N, layer 5 (local, NOT published): log coordinates of `ψ` at `+∞`

`ψ = z (1 + ζ)` with `z = cylInf s t` and `‖ζ‖ < 1` is again a cylinder point:
`ψ = cylInf (s + (logChart ζ).re) (t + (logChart ζ).im)`, with `logChart ζ = log(1 + ζ)/(2π)`
smooth on `ball 0 1`, and all its derivatives bounded on `closedBall 0 (1/2)`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Real

noncomputable section

/-- `log(1 + ζ) / (2π)`. -/
def logChart (ζ : ℂ) : ℂ := Complex.log (1 + ζ) * (((2 * π : ℝ) : ℂ))⁻¹

lemma one_add_mem_slitPlane {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 1 + ζ ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have := Complex.abs_re_le_norm ζ
  rw [Complex.add_re, Complex.one_re]
  linarith [neg_abs_le ζ.re]

/-- `cylInf s t (1 + ζ)` in log coordinates. -/
lemma cylInf_mul_one_add (s t : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    cylInf s t * (1 + ζ) = cylInf (s + (logChart ζ).re) (t + (logChart ζ).im) := by
  have hne : 1 + ζ ≠ 0 := Complex.slitPlane_ne_zero (one_add_mem_slitPlane hζ)
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hre : 2 * π * (logChart ζ).re = (Complex.log (1 + ζ)).re := by
    simp only [logChart, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    field_simp
  have him : 2 * π * (logChart ζ).im = (Complex.log (1 + ζ)).im := by
    simp only [logChart, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
    field_simp
  unfold cylInf ccwLoop
  rw [← Complex.exp_log hne]
  simp only [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_mul]
    push_cast
    linarith [hre]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_mul, zero_add]
    push_cast
    linarith [him]

end

end FiniteEnergyPlane

-- FILE: NSK_N18.lean
/-!
# Q-N, layer 18 (local, NOT published): the pointwise split of `qPt` and global bounds

`qPt = Lin + W·A(2πiz, 0) + W·A(eT a3, eN b3)` with `A = Jbar(ψ, v) - jStd`, the partition
`lcut 0 + smoothTransition = 1`, the left zero-order recombination, and the bounded coefficients
used by the assembly.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN18

open QN

/-! ### The partition and the left zero-order recombination -/

/-! ### Bounds -/

lemma bdd_mid (g : ℝ → ℝ) (hg : Continuous g) (D : ℝ) (h : ∀ s, (s ≤ -1 ∨ 1 ≤ s) → |g s| ≤ D) :
    ∃ M, 0 ≤ M ∧ ∀ s, |g s| ≤ M := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max (max B D) 0, le_max_right _ _, fun s => ?_⟩
  rcases le_or_gt s (-1) with h1 | h1
  · exact (h s (Or.inl h1)).trans ((le_max_right _ _).trans (le_max_left _ _))
  rcases le_or_gt 1 s with h2 | h2
  · exact (h s (Or.inr h2)).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (hB s ⟨h1.le, h2.le⟩).trans ((le_max_left _ _).trans (le_max_left _ _))

lemma expN_bdd {χN : ℝ → ℝ} {δ : ℝ} (hδ : δ < 0) (hχN : IsSlopeWeight χN π δ) :
    ∃ M, 0 ≤ M ∧ ∀ s, |Real.exp (χN s)| ≤ M := by
  refine bdd_mid _ (Real.continuous_exp.comp hχN.1.continuous)
    (max (Real.exp (χN (-1))) (Real.exp (χN 1))) fun s hs => ?_
  rw [abs_of_pos (Real.exp_pos _)]
  rcases hs with hs | hs
  · exact (exp_le_left hχN hs).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    rw [hχN.eq_right hs]
    exact Real.exp_le_exp.2 (by nlinarith)

lemma beta_bdd {β : ℝ → ℝ} (hβ : IsLeftCutoff β) : ∃ M, 0 ≤ M ∧ ∀ s, |β s| ≤ M := by
  refine bdd_mid _ hβ.1.continuous 1 fun s hs => ?_
  rcases hs with hs | hs
  · rw [hβ.2.1 s hs]; simp
  · rw [hβ.2.2 s (by linarith)]; simp

end QN18

end

end FiniteEnergyPlane

-- FILE: CokerPair.lean
namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

noncomputable section

section Pairing

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

lemma cka_integrable (f : Lp E p μ) (g : Lp E q μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  have h := MemLp.of_bilin (r := 1) (fun a b => inner ℝ a b) 1 (Lp.memLp f) (Lp.memLp g)
    ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g))
    (Filter.Eventually.of_forall fun x => by
      rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
      exact norm_inner_le_norm _ _)
  exact memLp_one_iff_integrable.1 h

/-- The pairing `∫ ⟨f, g⟩` as a bilinear map. -/
def ckaPair : Lp E p μ →ₗ[ℝ] Lp E q μ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => ∫ x, inner ℝ (f x) (g x) ∂μ)
    (fun f f' g => by
      rw [← integral_add (cka_integrable f g) (cka_integrable f' g)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add f f'] with x hx
      rw [hx, Pi.add_apply, inner_add_left])
    (fun c f g => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c f] with x hx
      rw [hx, Pi.smul_apply, real_inner_smul_left])
    (fun f g g' => by
      rw [← integral_add (cka_integrable f g) (cka_integrable f g')]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add g g'] with x hx
      rw [hx, Pi.add_apply, inner_add_right])
    (fun c f g => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c g] with x hx
      rw [hx, Pi.smul_apply, real_inner_smul_right])

lemma ckaPair_apply (f : Lp E p μ) (g : Lp E q μ) :
    ckaPair f g = ∫ x, inner ℝ (f x) (g x) ∂μ := rfl

/-- Hölder's inequality for the pairing. -/
lemma cka_bound (f : Lp E p μ) (g : Lp E q μ) : ‖ckaPair f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [ckaPair_apply]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hb := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := p) (q := q) (r := 1) (Lp.aestronglyMeasurable f)
    (Lp.aestronglyMeasurable g) (fun a b => inner ℝ a b) 1
    (Filter.Eventually.of_forall fun x => by
      rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
      exact norm_inner_le_norm _ _)
  simp only [ENNReal.coe_one, one_mul] at hb
  have hi := cka_integrable f g
  rw [integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable, ← eLpNorm_one_eq_lintegral_enorm,
    Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)) hb

/-- The pairing as a continuous bilinear map. -/
def ckaPairL : Lp E p μ →L[ℝ] Lp E q μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ ckaPair 1 fun f g => by
    rw [one_mul, Real.norm_eq_abs, ← Real.norm_eq_abs]; exact cka_bound f g

lemma ckaPairL_apply (f : Lp E p μ) (g : Lp E q μ) :
    ckaPairL f g = ∫ x, inner ℝ (f x) (g x) ∂μ := rfl

end Pairing

end

end CauchyRiemannIndex

-- FILE: CR411Bridge.lean
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous map on `ℝ × ℝ` vanishing for large `|s|` is in `L^p` of the strip. -/
lemma memLp_of_vanish {E : Type*} [NormedAddCommGroup E] (g : ℝ × ℝ → E) (hg : Continuous g)
    (R : ℝ) (hR : ∀ s t, R < |s| → g (s, t) = 0) : MemLp g p cylMeasure := by
  set K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc 0 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hae : K.indicator g =ᵐ[cylMeasure] g := by
    unfold cylMeasure
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Ico) ?_
    rintro ⟨s, t⟩ ⟨-, ht⟩
    by_cases hx : (s, t) ∈ K
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have : R < |s| := by
        by_contra h
        push_neg at h
        exact hx ⟨abs_le.1 h, Set.Ico_subset_Icc_self ht⟩
      exact (hR s t this).symm
  refine (memLp_congr_ae hae).1 ((memLp_indicator_iff_restrict hKm).2 ?_)
  haveI : IsFiniteMeasure (cylMeasure.restrict K) := by
    refine isFiniteMeasure_restrict.2 (ne_of_lt (lt_of_le_of_lt ?_ (hKc.measure_lt_top (μ := (volume : Measure (ℝ × ℝ))))))
    exact Measure.le_iff'.1 Measure.restrict_le_self K
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C (ae_restrict_of_forall_mem hKm hC)

lemma IsTestSection.continuous {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : Continuous u :=
  hu.1.continuous

lemma IsTestSection.memLp {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : MemLp u p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish u hu.continuous R hR

lemma IsTestSection.sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u - v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.sub hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u + v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.add hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    IsTestSection (c • u) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  refine ⟨ContDiff.const_smul c hu.1, fun s t => by simp [hu.2.1], R₁, fun s t hs => ?_⟩
  simp [h₁ s t hs]

end

end CauchyRiemannIndex

-- FILE: CokerMat.lean
/-!
# Complex conjugation and the conjugated coefficient `S̄ = -C Sᵀ C`
-/

namespace CauchyRiemannIndex

open Matrix

noncomputable section

variable {n : ℕ}

end

end CauchyRiemannIndex

-- FILE: CR411Core.lean
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

end

end CauchyRiemannIndex

-- FILE: CRCylCalc.lean
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

end

end CauchyRiemannIndex

-- FILE: CokerP.lean
/-!
# Wendl, Lemma 4.17 / Proposition 4.18 / Theorem 4.20 on the cylinder

The `L^q` annihilator of `im D_S` is `C · ker D_{S̄}`, and the codimension of the closed range
equals the dimension of that annihilator.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-! ### Pointwise algebra -/

/-! ### Conjugated test sections -/

/-! ### Test triples -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous linear functional on triples vanishing on test triples vanishes on `W^{1,p}`. -/
lemma ckp_W1p_le_ker (Λ : Triple n p →L[ℝ] ℝ)
    (h : ∀ u : ℝ × ℝ → Vec n, ∀ hu : IsTestSection u, ∀ w ∈ testTriples n p,
      (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u →
      (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u →
      (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u → Λ w = 0) :
    ∀ w ∈ W1p p n, Λ w = 0 := by
  have hle : W1p p n ≤ LinearMap.ker (Λ : Triple n p →ₗ[ℝ] ℝ) := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · refine Submodule.span_le.2 fun w hw => ?_
      obtain ⟨u, hu, h1, h2, h3⟩ := id hw
      exact h u hu w hw h1 h2 h3
    · exact Λ.isClosed_ker
  exact fun w hw => hle hw

end

end CauchyRiemannIndex

-- FILE: JWQ_L1.lean
/-!
# Q-L, layer L1: `W^{1,p}` triples give weak partials on the plane

For `w ∈ W1p p n` with a continuous periodic representative `g` of `w.1`, the map
`z ↦ g(Re z, Im z)` has weak partials `perF w.2.1`, `perF w.2.2` (the `t`-periodic extensions) on
the strip `stripU = {|Im z| < 1}` of `ℂ`.
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal

noncomputable section

/-- `ℂ → ℝ × ℝ`, `z ↦ (Re z, Im z)`. -/
def cplx (z : ℂ) : ℝ × ℝ := Complex.equivRealProdCLM z

/-- `ℝ × ℝ → ℂ`. -/
def toC (x : ℝ × ℝ) : ℂ := Complex.equivRealProdCLM.symm x

@[simp] lemma cplx_toC (x : ℝ × ℝ) : cplx (toC x) = x :=
  Complex.equivRealProdCLM.apply_symm_apply x

@[simp] lemma toC_cplx (z : ℂ) : toC (cplx z) = z :=
  Complex.equivRealProdCLM.symm_apply_apply z

@[simp] lemma cplx_apply (z : ℂ) : cplx z = (z.re, z.im) := by
  simp [cplx]

/-- The strip `|Im z| < 1`. -/
def stripU : Set ℂ := {z | |z.im| < 1}

lemma isOpen_stripU : IsOpen stripU :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

/-- The `t`-periodic extension of a function on the strip `ℝ × [0, 1)`. -/
def perF {E : Type*} (f : ℝ × ℝ → E) (x : ℝ × ℝ) : E := f (x.1, Int.fract x.2)

/-- Shift down by one in `t`. -/
def tdn : ℝ × ℝ := (0, -1)

lemma perF_of_mem {E : Type*} (f : ℝ × ℝ → E) {x : ℝ × ℝ} (hx : x ∈ (univ : Set ℝ) ×ˢ Ico 0 1) :
    perF f x = f x := by
  simp only [perF, Int.fract_eq_self.2 hx.2]

lemma perF_add_tdn {E : Type*} (f : ℝ × ℝ → E) (x : ℝ × ℝ) : perF f (x + tdn) = perF f x := by
  simp only [perF, tdn, Prod.fst_add, Prod.snd_add, add_zero, ← sub_eq_add_neg, Int.fract_sub_one]

lemma per_add_tdn {E : Type*} {f : ℝ × ℝ → E} (hf : ∀ s t : ℝ, f (s, t + 1) = f (s, t))
    (x : ℝ × ℝ) : f (x + tdn) = f x := by
  obtain ⟨s, t⟩ := x
  have := hf s (t - 1)
  simp only [sub_add_cancel] at this
  simp only [tdn, Prod.mk_add_mk, add_zero, ← sub_eq_add_neg]
  exact this.symm

lemma fderiv_per {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ × ℝ → E}
    (hf : ∀ s t : ℝ, f (s, t + 1) = f (s, t)) (s t : ℝ) :
    fderiv ℝ f (s, t + 1) = fderiv ℝ f (s, t) := by
  have e : f = fun x => f (x + ((0 : ℝ), (1 : ℝ))) := by
    funext x
    obtain ⟨a, b⟩ := x
    rw [Prod.mk_add_mk, add_zero, hf]
  conv_rhs => rw [e]
  rw [fderiv_comp_add_right]
  simp

lemma measurePreserving_tdn : MeasurePreserving (fun x : ℝ × ℝ => x + tdn) volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_add_right (volume : Measure ℝ) (-1))
  have e : Prod.map id (fun t : ℝ => t + -1) = fun x : ℝ × ℝ => x + tdn := by
    funext x; obtain ⟨a, b⟩ := x; simp [tdn, Prod.map]
  rw [e] at h
  exact h

lemma measurableEmbedding_tdn : MeasurableEmbedding (fun x : ℝ × ℝ => x + tdn) :=
  (MeasurableEquiv.addRight tdn).measurableEmbedding

lemma preimage_tdn_lower :
    (fun x : ℝ × ℝ => x + tdn) ⁻¹' ((univ : Set ℝ) ×ˢ Ico (-1) 0) = univ ×ˢ Ico 0 1 := by
  ext ⟨s, t⟩
  simp only [tdn, mem_preimage, Prod.mk_add_mk, add_zero, mem_prod, mem_univ, true_and, mem_Ico]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Splitting `ℝ × [-1, 1)` into two period strips. -/
lemma integral_eq_cyl_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × ℝ → E) (h1 : Integrable F cylMeasure)
    (h2 : Integrable (fun x => F (x + tdn)) cylMeasure)
    (h0 : ∀ x : ℝ × ℝ, x.2 ∉ Ico (-1 : ℝ) 1 → F x = 0) :
    Integrable F ∧ ∫ x, F x = ∫ x, (F x + F (x + tdn)) ∂cylMeasure := by
  have hlowI : IntegrableOn F ((univ : Set ℝ) ×ˢ Ico (-1) 0) := by
    rw [← (measurePreserving_tdn.integrableOn_comp_preimage measurableEmbedding_tdn),
      preimage_tdn_lower]
    exact h2
  have hupI : IntegrableOn F ((univ : Set ℝ) ×ˢ Ico 0 1) := h1
  have hsplit : (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1 = univ ×ˢ Ico (-1) 0 ∪ univ ×ˢ Ico 0 1 := by
    rw [← prod_union, Ico_union_Ico_eq_Ico (by norm_num) (by norm_num)]
  have hI : Integrable F := by
    have hon : IntegrableOn F ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1) := by
      rw [hsplit]; exact hlowI.union hupI
    refine (integrableOn_iff_integrable_of_support_subset
      (s := (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1) ?_).1 hon
    intro x hx
    exact Set.mem_prod.2 ⟨mem_univ _, by_contra fun h => hx (h0 x h)⟩
  refine ⟨hI, ?_⟩
  have hA : ∫ x, F x = ∫ x in (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1, F x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (s := (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1)
      fun x hx => h0 x fun h => hx (Set.mem_prod.2 ⟨mem_univ _, h⟩)).symm
  have hdisj : Disjoint ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 0) (univ ×ˢ Ico 0 1) :=
    Set.disjoint_prod.2 (Or.inr (Ico_disjoint_Ico_same))
  have hlow : ∫ x in (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 0, F x =
      ∫ x in (univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1, F (x + tdn) := by
    rw [← preimage_tdn_lower]
    exact (measurePreserving_tdn.setIntegral_preimage_emb measurableEmbedding_tdn F _).symm
  rw [hA, hsplit, setIntegral_union hdisj (MeasurableSet.univ.prod measurableSet_Ico) hlowI hupI,
    hlow]
  rw [show ∫ x, (F x + F (x + tdn)) ∂cylMeasure =
      (∫ x, F x ∂cylMeasure) + ∫ x, F (x + tdn) ∂cylMeasure from integral_add h1 h2, add_comm]
  rfl

/-! ### Test functions on the strip -/

section TestFn

variable (φ : ℂ → ℝ)

lemma exists_vanish_of_hasCompactSupport (hφc : HasCompactSupport φ) :
    ∃ R : ℝ, ∀ z : ℂ, R < |z.re| → φ z = 0 ∧ fderiv ℝ φ z = 0 := by
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun z hz => ?_⟩
  have hz' : z ∉ tsupport φ := by
    intro h
    have := hR h
    rw [mem_closedBall, dist_zero_right] at this
    have := Complex.abs_re_le_norm z
    linarith
  refine ⟨image_eq_zero_of_notMem_tsupport hz', ?_⟩
  by_contra h
  exact hz' (support_fderiv_subset ℝ h)

lemma vanish_of_tsupport (hφU : tsupport φ ⊆ stripU) {z : ℂ} (hz : 1 ≤ |z.im|) :
    φ z = 0 ∧ fderiv ℝ φ z = 0 := by
  have hz' : z ∉ tsupport φ := fun h => absurd (hφU h) (by simp [stripU]; linarith)
  refine ⟨image_eq_zero_of_notMem_tsupport hz', ?_⟩
  by_contra h
  exact hz' (support_fderiv_subset ℝ h)

lemma not_mem_Ico_abs {t : ℝ} (ht : t ∉ Ico (-1 : ℝ) 1) : 1 ≤ |t| := by
  rw [mem_Ico, not_and_or, not_le, not_lt] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

end TestFn

/-- Products of a continuous function vanishing for large `|s|` with an `L^p` function are
integrable on the strip. -/
lemma integrable_smul_cyl {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (R : ℝ) (hR : ∀ s t, R < |s| → f (s, t) = 0) (h : ℝ × ℝ → Vec n)
    (hh : MemLp h p cylMeasure) : Integrable (fun x => f x • h x) cylMeasure := by
  haveI : Fact (1 ≤ p.conjExponent) := ⟨le_self_add⟩
  have hf' : MemLp f p.conjExponent cylMeasure := memLp_of_vanish f hf R hR
  have := hh.smul (p := p.conjExponent) (q := p) (r := 1) hf'
  exact memLp_one_iff_integrable.1 this

end

end QL

end FiniteEnergyPlane

-- FILE: JWQ_L1b.lean
/-!
# Q-L, layer L1b: the weak identity for `W^{1,p}` triples on the plane strip
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma integral_cplx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ × ℝ → E) :
    ∫ z : ℂ, F (cplx z) = ∫ x, F x :=
  Complex.volume_preserving_equiv_real_prod.integral_comp' F

lemma toC_re (x : ℝ × ℝ) : (toC x).re = x.1 := by simp [toC]

lemma toC_im (x : ℝ × ℝ) : (toC x).im = x.2 := by simp [toC]

/-- Pairing with `f • e` is the inner product of the integral. -/
lemma integral_inner_smul (f : ℝ × ℝ → ℝ) (hf : Continuous f) (R : ℝ)
    (hR : ∀ s t, R < |s| → f (s, t) = 0) (h : ℝ × ℝ → Vec n) (hh : MemLp h p cylMeasure)
    (e : Vec n) :
    ∫ x, inner ℝ (h x) (f x • e) ∂cylMeasure = inner ℝ (∫ x, f x • h x ∂cylMeasure) e := by
  rw [real_inner_comm, ← integral_inner (integrable_smul_cyl f hf R hR h hh) e]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_comm]

/-- Plane integral of `f • G` for a periodic `G` as a cylinder integral. -/
lemma integral_plane_eq_cyl (f : ℝ × ℝ → ℝ) (hf : Continuous f) (R : ℝ)
    (hR : ∀ x : ℝ × ℝ, R < |x.1| → f x = 0)
    (h0 : ∀ x : ℝ × ℝ, x.2 ∉ Ico (-1 : ℝ) 1 → f x = 0)
    (G : ℝ × ℝ → Vec n) (hG : ∀ x, G (x + tdn) = G x) (hGm : MemLp G p cylMeasure) :
    ∫ x, f x • G x = ∫ x, (f x + f (x + tdn)) • G x ∂cylMeasure := by
  have hf2 : Continuous fun x : ℝ × ℝ => f (x + tdn) := hf.comp (continuous_id.add continuous_const)
  have i1 := integrable_smul_cyl f hf R (fun s t h => hR (s, t) h) G hGm
  have i2 := integrable_smul_cyl (fun x => f (x + tdn)) hf2 R
    (fun s t h => hR _ (by simpa [tdn] using h)) G hGm
  obtain ⟨-, hI⟩ := integral_eq_cyl_add (fun x => f x • G x) i1
    (by simpa only [hG] using i2) (fun x hx => by simp [h0 x hx])
  rw [hI]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hG, add_smul]

/-- The weak identity in direction `dir ∈ {1, i}`. -/
theorem weak_identity (dir : ℂ) (hdir : dir = 1 ∨ dir = Complex.I)
    (pd : (ℝ × ℝ → Vec n) → ℝ × ℝ → Vec n)
    (hpd : ∀ u : ℝ × ℝ → Vec n, ∀ x, fderiv ℝ u x (cplx dir) = pd u x)
    (sel : Triple n p →L[ℝ] LpCyl n p)
    (hsel : ∀ u : ℝ × ℝ → Vec n, IsTestSection u → ∀ v : Triple n p,
      (v.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u →
      (v.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u →
      (v.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u →
      (sel v : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] pd u)
    (w : Triple n p) (hw : w ∈ W1p p n) (g : ℝ × ℝ → Vec n) (hgc : Continuous g)
    (hgper : ∀ s t : ℝ, g (s, t + 1) = g (s, t))
    (hwg : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ stripU) :
    ∫ z, fderiv ℝ φ z dir • g (cplx z) = -∫ z, φ z • perF (sel w) (cplx z) := by
  haveI : Fact (1 ≤ p.conjExponent) := ⟨le_self_add⟩
  -- the coefficient functions
  set D : ℝ × ℝ → ℝ := fun x => fderiv ℝ φ (toC x) dir with hDdef
  set φr : ℝ × ℝ → ℝ := fun x => φ (toC x) with hφrdef
  have hcC : Continuous toC := Complex.equivRealProdCLM.symm.continuous
  have hDc : Continuous D :=
    ((hφ.continuous_fderiv (by simp)).comp hcC).clm_apply continuous_const
  have hφrc : Continuous φr := hφ.continuous.comp hcC
  obtain ⟨R, hR⟩ := exists_vanish_of_hasCompactSupport φ hφc
  have hDR : ∀ x : ℝ × ℝ, R < |x.1| → D x = 0 := fun x hx => by
    simp only [hDdef, (hR (toC x) (by rwa [toC_re])).2, ContinuousLinearMap.zero_apply]
  have hφrR : ∀ x : ℝ × ℝ, R < |x.1| → φr x = 0 := fun x hx =>
    (hR (toC x) (by rwa [toC_re])).1
  have hD0 : ∀ x : ℝ × ℝ, x.2 ∉ Ico (-1 : ℝ) 1 → D x = 0 := fun x hx => by
    simp only [hDdef, (vanish_of_tsupport φ hφU (by rw [toC_im]; exact not_mem_Ico_abs hx)).2,
      ContinuousLinearMap.zero_apply]
  have hφr0 : ∀ x : ℝ × ℝ, x.2 ∉ Ico (-1 : ℝ) 1 → φr x = 0 := fun x hx =>
    (vanish_of_tsupport φ hφU (by rw [toC_im]; exact not_mem_Ico_abs hx)).1
  set DΦ : ℝ × ℝ → ℝ := fun x => D x + D (x + tdn) with hDΦdef
  set Φ : ℝ × ℝ → ℝ := fun x => φr x + φr (x + tdn) with hΦdef
  have hsh : Continuous fun x : ℝ × ℝ => x + tdn := continuous_id.add continuous_const
  have hDΦc : Continuous DΦ := hDc.add (hDc.comp hsh)
  have hΦc : Continuous Φ := hφrc.add (hφrc.comp hsh)
  have hDΦR : ∀ s t, R < |s| → DΦ (s, t) = 0 := fun s t h => by
    simp only [hDΦdef, hDR (s, t) h, hDR ((s, t) + tdn) (by simpa [tdn] using h), add_zero]
  have hΦR : ∀ s t, R < |s| → Φ (s, t) = 0 := fun s t h => by
    simp only [hΦdef, hφrR (s, t) h, hφrR ((s, t) + tdn) (by simpa [tdn] using h), add_zero]
  -- plane integrals as cylinder integrals
  have hplaneD : ∀ G : ℝ × ℝ → Vec n, (∀ x, G (x + tdn) = G x) → MemLp G p cylMeasure →
      ∫ z, fderiv ℝ φ z dir • G (cplx z) = ∫ x, DΦ x • G x ∂cylMeasure := by
    intro G hG hGm
    rw [← integral_plane_eq_cyl D hDc R hDR hD0 G hG hGm, ← integral_cplx]
    simp only [hDdef, toC_cplx]
  have hplaneφ : ∀ G : ℝ × ℝ → Vec n, (∀ x, G (x + tdn) = G x) → MemLp G p cylMeasure →
      ∫ z, φ z • G (cplx z) = ∫ x, Φ x • G x ∂cylMeasure := by
    intro G hG hGm
    rw [← integral_plane_eq_cyl φr hφrc R hφrR hφr0 G hG hGm, ← integral_cplx]
    simp only [hφrdef, toC_cplx]
  -- the functional
  set P := ckaPairL (μ := cylMeasure) (E := Vec n) (p := p) (q := p.conjExponent)
  have hm1 : ∀ e : Vec n, MemLp (fun x => DΦ x • e) p.conjExponent cylMeasure := fun e =>
    memLp_of_vanish _ (hDΦc.smul continuous_const) R fun s t h => by simp [hDΦR s t h]
  have hm2 : ∀ e : Vec n, MemLp (fun x => Φ x • e) p.conjExponent cylMeasure := fun e =>
    memLp_of_vanish _ (hΦc.smul continuous_const) R fun s t h => by simp [hΦR s t h]
  let Λ : Vec n → Triple n p →L[ℝ] ℝ := fun e =>
    (P.flip ((hm1 e).toLp _)).comp (ContinuousLinearMap.fst ℝ _ _) + (P.flip ((hm2 e).toLp _)).comp sel
  have hΛ : ∀ e (v : Triple n p), Λ e v =
      inner ℝ (∫ x, DΦ x • v.1 x ∂cylMeasure + ∫ x, Φ x • sel v x ∂cylMeasure) e := by
    intro e v
    simp only [Λ, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst', P, ckaPairL_apply]
    rw [inner_add_left, ← integral_inner_smul DΦ hDΦc R hDΦR _ (Lp.memLp v.1) e,
      ← integral_inner_smul Φ hΦc R hΦR _ (Lp.memLp (sel v)) e]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [(hm1 e).coeFn_toLp] with x hx
      rw [hx]
    · refine integral_congr_ae ?_
      filter_upwards [(hm2 e).coeFn_toLp] with x hx
      rw [hx]
  -- vanishing on test triples
  have htest : ∀ u : ℝ × ℝ → Vec n, ∀ hu : IsTestSection u, ∀ v ∈ testTriples n p,
      (v.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u →
      (v.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u →
      (v.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u → ∀ e, Λ e v = 0 := by
    intro u hu v _ h1 h2 h3 e
    have hs := hsel u hu v h1 h2 h3
    have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
    have hupd : ∀ x, pd u (x + tdn) = pd u x := by
      intro x
      rw [← hpd, ← hpd]
      obtain ⟨s, t⟩ := x
      have := fderiv_per hu.2.1 s (t - 1)
      simp only [sub_add_cancel] at this
      simp only [tdn, Prod.mk_add_mk, add_zero, ← sub_eq_add_neg, this]
    have hupm : MemLp (pd u) p cylMeasure := (Lp.memLp (sel v)).ae_eq hs
    have hum : MemLp u p cylMeasure := hu.memLp
    have hu_per : ∀ x, u (x + tdn) = u x := per_add_tdn hu.2.1
    rw [hΛ]
    have e1 : ∫ x, DΦ x • v.1 x ∂cylMeasure = ∫ z, fderiv ℝ φ z dir • u (cplx z) := by
      rw [hplaneD u hu_per hum]
      refine integral_congr_ae ?_
      filter_upwards [h1] with x hx
      rw [hx]
    have e2 : ∫ x, Φ x • sel v x ∂cylMeasure = ∫ z, φ z • pd u (cplx z) := by
      rw [hplaneφ (pd u) hupd hupm]
      refine integral_congr_ae ?_
      filter_upwards [hs] with x hx
      rw [hx]
    -- the plane identity for the smooth map `u ∘ cplx`
    have hcomp : ContDiffOn ℝ 1 (fun z => u (cplx z)) univ :=
      ((hu.1.of_le (by simp)).comp Complex.equivRealProdCLM.contDiff).contDiffOn
    have hW := JHolomorphic.HasWeakPartialsOn.of_contDiffOn isOpen_univ hcomp φ hφ hφc
      (subset_univ _)
    have hfd : ∀ z (a : ℂ), fderiv ℝ (fun z => u (cplx z)) z a = fderiv ℝ u (cplx z) (cplx a) := by
      intro z a
      have : (fun z => u (cplx z)) = u ∘ Complex.equivRealProdCLM := rfl
      rw [this, ContinuousLinearEquiv.comp_right_fderiv]
      rfl
    have e3 : ∫ z, fderiv ℝ φ z dir • u (cplx z) = -∫ z, φ z • pd u (cplx z) := by
      rcases hdir with rfl | rfl
      · rw [hW.1]
        simp only [hfd, hpd]
      · rw [hW.2]
        simp only [hfd, hpd]
    rw [e1, e2, e3, neg_add_cancel, inner_zero_left]
  -- vanishing on `W^{1,p}`
  have hall : ∀ e, Λ e w = 0 := fun e =>
    ckp_W1p_le_ker (Λ e) (fun u hu v hv h1 h2 h3 => htest u hu v hv h1 h2 h3 e) w hw
  have hI : ∫ x, DΦ x • w.1 x ∂cylMeasure + ∫ x, Φ x • sel w x ∂cylMeasure = 0 := by
    have := hall (∫ x, DΦ x • w.1 x ∂cylMeasure + ∫ x, Φ x • sel w x ∂cylMeasure)
    rw [hΛ] at this
    exact inner_self_eq_zero.1 this
  -- back to the plane
  have hgm : MemLp g p cylMeasure := (Lp.memLp w.1).ae_eq hwg
  have hpm : MemLp (perF (sel w : ℝ × ℝ → Vec n)) p cylMeasure := by
    refine (Lp.memLp (sel w)).ae_eq ?_
    unfold cylMeasure
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with x hx
    rw [perF_of_mem _ hx]
  have e1 : ∫ z, fderiv ℝ φ z dir • g (cplx z) = ∫ x, DΦ x • w.1 x ∂cylMeasure := by
    rw [hplaneD g (per_add_tdn hgper) hgm]
    refine integral_congr_ae ?_
    filter_upwards [hwg] with x hx
    rw [hx]
  have e2 : ∫ z, φ z • perF (sel w : ℝ × ℝ → Vec n) (cplx z) = ∫ x, Φ x • sel w x ∂cylMeasure := by
    rw [hplaneφ _ (perF_add_tdn _) hpm]
    refine integral_congr_ae ?_
    unfold cylMeasure
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with x hx
    rw [perF_of_mem _ hx]
  rw [e1, e2]
  exact eq_neg_of_add_eq_zero_left hI

end

end QL

end FiniteEnergyPlane

-- FILE: JWQ_L1c.lean
/-!
# Q-L, layer L1c: `W^{1,p}` triples as `W^{1,p}_loc` maps on the plane strip
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Shift up by one in `t`. -/
def tup : ℝ × ℝ := (0, 1)

lemma measurePreserving_tup : MeasurePreserving (fun x : ℝ × ℝ => x + tup) volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_add_right (volume : Measure ℝ) 1)
  have e : Prod.map id (fun t : ℝ => t + 1) = fun x : ℝ × ℝ => x + tup := by
    funext x; obtain ⟨a, b⟩ := x; simp [tup, Prod.map]
  rw [e] at h
  exact h

/-- The lower strip `ℝ × [-1, 0)`. -/
abbrev lowS : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ Ico (-1) 0

/-- The period strip `ℝ × [0, 1)`. -/
abbrev upS : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ Ico 0 1

lemma preimage_tup_upS : (fun x : ℝ × ℝ => x + tup) ⁻¹' upS = lowS := by
  ext ⟨s, t⟩
  simp only [tup, mem_preimage, Prod.mk_add_mk, add_zero, mem_prod, mem_univ, true_and, mem_Ico]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma measurePreserving_tup_restrict :
    MeasurePreserving (fun x : ℝ × ℝ => x + tup) (volume.restrict lowS) cylMeasure := by
  have := measurePreserving_tup.restrict_preimage (MeasurableSet.univ.prod measurableSet_Ico)
    (s := upS)
  rwa [preimage_tup_upS] at this

lemma perF_of_mem_lowS {E : Type*} (f : ℝ × ℝ → E) {x : ℝ × ℝ} (hx : x ∈ lowS) :
    perF f x = f (x + tup) := by
  obtain ⟨s, t⟩ := x
  have ht := hx.2
  simp only [perF, tup, Prod.mk_add_mk, add_zero]
  congr 2
  rw [← Int.fract_add_one, Int.fract_eq_self.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩]

lemma lowS_union_upS : lowS ∪ upS = (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1 := by
  rw [← prod_union, Ico_union_Ico_eq_Ico (by norm_num) (by norm_num)]

/-- `perF f` is `L^p` on `ℝ × [-1, 1)`. -/
lemma memLp_perF (f : LpCyl n p) :
    MemLp (perF (f : ℝ × ℝ → Vec n)) p (volume.restrict ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1)) := by
  have hmL : MeasurableSet lowS := MeasurableSet.univ.prod measurableSet_Ico
  have hmU : MeasurableSet upS := MeasurableSet.univ.prod measurableSet_Ico
  have hU : MemLp (perF (f : ℝ × ℝ → Vec n)) p (volume.restrict upS) := by
    refine (Lp.memLp f).ae_eq ?_
    filter_upwards [ae_restrict_mem hmU] with x hx
    rw [perF_of_mem _ hx]
  have hL : MemLp (perF (f : ℝ × ℝ → Vec n)) p (volume.restrict lowS) := by
    refine ((Lp.memLp f).comp_measurePreserving measurePreserving_tup_restrict).ae_eq ?_
    filter_upwards [ae_restrict_mem hmL] with x hx
    rw [perF_of_mem_lowS _ hx]
    rfl
  rw [← lowS_union_upS, ← memLp_indicator_iff_restrict (hmL.union hmU),
    indicator_union_of_disjoint (Set.disjoint_prod.2 (Or.inr Ico_disjoint_Ico_same))]
  exact ((memLp_indicator_iff_restrict hmL).2 hL).add ((memLp_indicator_iff_restrict hmU).2 hU)

lemma measurePreserving_cplx : MeasurePreserving cplx volume volume :=
  Complex.volume_preserving_equiv_real_prod

/-- `L^p` on `ℝ × [-1, 1)` gives `L^p` on compact subsets of the plane strip. -/
lemma memLp_comp_cplx_of_compact {E : Type*} [NormedAddCommGroup E] {F : ℝ × ℝ → E}
    (hF : MemLp F p (volume.restrict ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1)))
    (K : Set ℂ) (hK : K ⊆ stripU) :
    MemLp (fun z => F (cplx z)) p (volume.restrict K) := by
  have hm : MeasurableSet ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1) :=
    MeasurableSet.univ.prod measurableSet_Ico
  have h := hF.comp_measurePreserving (measurePreserving_cplx.restrict_preimage hm)
  refine h.mono_measure (Measure.restrict_mono ?_ le_rfl)
  intro z hz
  have := hK hz
  simp only [stripU, mem_setOf_eq, abs_lt] at this
  simp [cplx_apply, this.1.le, this.2]

/-- L1. A `W^{1,p}` triple with a continuous periodic representative is a `W^{1,p}_loc` map on
the plane strip, and the equation `D_M w = 0` holds a.e. there. -/
theorem isWeak_of_mem_W1p (w : Triple n p) (hw : w ∈ W1p p n) (g : ℝ × ℝ → Vec n)
    (hgc : Continuous g) (hgper : ∀ s t : ℝ, g (s, t + 1) = g (s, t))
    (hwg : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g) :
    JHolomorphic.HasWeakPartialsOn stripU (fun z => g (cplx z))
        (fun z => perF (w.2.1 : ℝ × ℝ → Vec n) (cplx z))
        (fun z => perF (w.2.2 : ℝ × ℝ → Vec n) (cplx z)) ∧
      ∀ K ⊆ stripU, MemLp (fun z => perF (w.2.1 : ℝ × ℝ → Vec n) (cplx z)) p (volume.restrict K) ∧
        MemLp (fun z => perF (w.2.2 : ℝ × ℝ → Vec n) (cplx z)) p (volume.restrict K) := by
  refine ⟨fun φ hφ hφc hφU => ⟨?_, ?_⟩, fun K hK =>
    ⟨memLp_comp_cplx_of_compact (memLp_perF _) K hK,
      memLp_comp_cplx_of_compact (memLp_perF _) K hK⟩⟩
  · exact weak_identity 1 (Or.inl rfl) partialS
      (fun u x => by simp [cplx_apply, partialS])
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
      (fun u _ v _ h2 _ => h2) w hw g hgc hgper hwg φ hφ hφc hφU
  · exact weak_identity Complex.I (Or.inr rfl) partialT
      (fun u x => by simp [cplx_apply, partialT])
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
      (fun u _ v _ _ h3 => h3) w hw g hgc hgper hwg φ hφ hφc hφU

end

end QL

end FiniteEnergyPlane

-- FILE: JWQ_L2.lean
/-!
# Q-L, layer L2: regularity of weak solutions of `∂ₛu + J₀ ∂ₜu + m(z, u) = 0`

Graph trick: `z ↦ (z, u z)` is weakly `J`-holomorphic for the smooth almost complex structure
`J(z, y)(a, b) = (i a, J₀ b + Re a · J₀ m(z, y) + Im a · m(z, y))` on `ℂ × F`.
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Set JHolomorphic
open scoped ContDiff ENNReal

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

end

end QL

end FiniteEnergyPlane

-- FILE: JWQ_L3.lean
/-!
# Q-L, layer L3: kernel elements of `D_M` on `W^{1,p}` are smooth (L-K)
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal

noncomputable section

lemma fderiv_comp_cplx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : ℝ × ℝ → E)
    (z a : ℂ) : fderiv ℝ (fun z => u (cplx z)) z a = fderiv ℝ u (cplx z) (cplx a) := by
  have : (fun z => u (cplx z)) = u ∘ Complex.equivRealProdCLM := rfl
  rw [this, ContinuousLinearEquiv.comp_right_fderiv]
  rfl

lemma measurePreserving_toC : MeasurePreserving toC volume volume :=
  Complex.volume_preserving_equiv_real_prod.symm

lemma per_int {E : Type*} {g : ℝ × ℝ → E} (hg : ∀ s t : ℝ, g (s, t + 1) = g (s, t))
    (x : ℝ × ℝ) (k : ℤ) : g (x - ((0 : ℝ), (k : ℝ))) = g x := by
  obtain ⟨s, t⟩ := x
  have hp : Function.Periodic (fun t => g (s, t)) 1 := fun t => hg s t
  have := (hp.int_mul k) (t - k)
  simp only [mul_one, sub_add_cancel] at this
  simp only [Prod.mk_sub_mk, sub_zero]
  exact this.symm

end

end QL

end FiniteEnergyPlane

-- FILE: JWQ_L4.lean
/-!
# Q-L, layer L4: the plane function of a cylinder solution

For a smooth `t`-periodic `v`, `pf v z = vecToC (v (s, t))` at `z = cylInf s t` (and `0` at `z = 0`).
It is smooth on `ℂ \ {0}`, and if `∂ₛv + J₀ ∂ₜv + S v = 0` with `IsPlaneCoeff S` (coefficient `A`),
then `∂ₓζ + i ∂ᵧζ = -2 A(z) ζ` on `ℂ \ {0}`.
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### `vecToC` -/

/-! ### `cylInf` -/

lemma cylInf_eq_exp (s t : ℝ) :
    cylInf s t = Complex.exp (((2 * π : ℝ) : ℂ) * ((s : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold cylInf ccwLoop
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast; ring

lemma cylInf_ne_zero (s t : ℝ) : cylInf s t ≠ 0 := by
  rw [cylInf_eq_exp]; exact Complex.exp_ne_zero _

lemma norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma cylInf_log_arg {z : ℂ} (hz : z ≠ 0) :
    cylInf (Real.log ‖z‖ / (2 * π)) (Complex.arg z / (2 * π)) = z := by
  unfold cylInf ccwLoop
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hπ, Real.exp_log (norm_pos_iff.2 hz), mul_div_cancel₀ _ hπ]
  exact Complex.norm_mul_exp_arg_mul_I z

lemma arg_cylInf (s t : ℝ) : ∃ k : ℤ, Complex.arg (cylInf s t) / (2 * π) = t - k := by
  unfold cylInf ccwLoop
  rw [Complex.arg_real_mul _ (Real.exp_pos _), Complex.arg_exp_mul_I]
  refine ⟨toIocDiv Real.two_pi_pos (-π) (2 * π * t), ?_⟩
  rw [← self_sub_toIocDiv_zsmul, zsmul_eq_mul]
  field_simp

/-! ### The log chart (copy of `JWQ_N5`, renamed) -/

/-- `log(1 + ζ) / (2π)`. -/
def lchart (ζ : ℂ) : ℂ := Complex.log (1 + ζ) * (((2 * π : ℝ) : ℂ))⁻¹

lemma one_add_mem_slitPlane' {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 1 + ζ ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have := Complex.abs_re_le_norm ζ
  rw [Complex.add_re, Complex.one_re]
  linarith [neg_abs_le ζ.re]

lemma lchart_contDiffAt {ζ : ℂ} (hζ : ‖ζ‖ < 1) : ContDiffAt ℝ ∞ lchart ζ := by
  have hlog : ContDiffAt ℝ ∞ Complex.log (1 + ζ) :=
    (Complex.contDiffAt_log (one_add_mem_slitPlane' hζ)).restrict_scalars ℝ
  exact (hlog.comp ζ (contDiffAt_const.add contDiffAt_id)).mul contDiffAt_const

/-- `cylInf s t (1 + ζ)` in log coordinates. -/
lemma cylInf_mul_one_add (s t : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    cylInf s t * (1 + ζ) = cylInf (s + (lchart ζ).re) (t + (lchart ζ).im) := by
  have hne : 1 + ζ ≠ 0 := Complex.slitPlane_ne_zero (one_add_mem_slitPlane' hζ)
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hre : 2 * π * (lchart ζ).re = (Complex.log (1 + ζ)).re := by
    simp only [lchart, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    field_simp
  have him : 2 * π * (lchart ζ).im = (Complex.log (1 + ζ)).im := by
    simp only [lchart, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
    field_simp
  unfold cylInf ccwLoop
  rw [← Complex.exp_log hne]
  simp only [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_mul]
    push_cast
    linarith [hre]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_mul, zero_add]
    push_cast
    linarith [him]

/-! ### The plane function -/

variable {v : ℝ × ℝ → Vec 1}

/-! ### Derivatives through the exponential chart -/

/-- `cylInf` on `ℝ × ℝ`. -/
def Ecyl (x : ℝ × ℝ) : ℂ := cylInf x.1 x.2

lemma toC_eq (x : ℝ × ℝ) : toC x = (x.1 : ℂ) + (x.2 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [toC]

lemma Ecyl_eq (x : ℝ × ℝ) : Ecyl x = Complex.exp (((2 * π : ℝ) : ℂ) * toC x) := by
  rw [Ecyl, cylInf_eq_exp, toC_eq]

lemma hasFDerivAt_Ecyl (x : ℝ × ℝ) :
    HasFDerivAt Ecyl ((((2 * π : ℝ) : ℂ) * Ecyl x) • (Complex.equivRealProdCLM.symm :
      ℝ × ℝ →L[ℝ] ℂ)) x := by
  have e : Ecyl = fun x => Complex.exp (((2 * π : ℝ) : ℂ) * toC x) := funext Ecyl_eq
  have hL : HasFDerivAt (fun x : ℝ × ℝ => ((2 * π : ℝ) : ℂ) * toC x)
      (((2 * π : ℝ) : ℂ) • (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)) x := by
    have := (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ).hasFDerivAt (x := x)
    exact this.const_smul (((2 * π : ℝ) : ℂ))
  have h := ((Complex.hasDerivAt_exp (((2 * π : ℝ) : ℂ) * toC x)).hasFDerivAt.restrictScalars ℝ).comp
    x hL
  rw [e]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun y => ?_)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul,
    ContinuousLinearMap.toSpanSingleton_apply, Ecyl_eq]
  rw [show (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) y = toC y from rfl]
  ring

/-! ### Decay at `0` -/

end

end QL

end FiniteEnergyPlane

-- FILE: JWQ_L5a.lean
/-!
# Q-L, layer L5a: the unweighted solution `v = e^χ g` and its energy near `s = -∞`
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Weights -/

/-- An exponential weight bound on a half-line from affinity beyond `1` (resp. `-1`). -/
lemma exists_exp_bound_right (χ : ℝ → ℝ) (hc : Continuous χ) (b : ℝ)
    (hχ : ∀ s ≥ 1, χ s = χ 1 + b * (s - 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ≥ 0, Real.exp (χ s) ≤ K * Real.exp (b * s) := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((Real.continuous_exp.comp (hc.sub (continuous_const.mul continuous_id)))).continuousOn
  refine ⟨max (max K₀ 1) (Real.exp (χ 1 - b)), lt_max_of_lt_left (lt_max_of_lt_right one_pos),
    fun s hs => ?_⟩
  have hsplit : Real.exp (χ s) = Real.exp (χ s - b * s) * Real.exp (b * s) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rcases le_or_gt s 1 with h1 | h1
  · have := hK₀ s ⟨hs, h1⟩
    simp only [Function.comp, Real.norm_eq_abs, Real.abs_exp, id] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [hχ s h1.le]
    exact le_of_eq_of_le (by ring_nf) (le_max_right _ _)

lemma exists_exp_bound_left (χ : ℝ → ℝ) (hc : Continuous χ) (a : ℝ)
    (hχ : ∀ s ≤ -1, χ s = χ (-1) + a * (s + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ≤ 0, Real.exp (χ s) ≤ K * Real.exp (a * s) := by
  obtain ⟨K, hK, h⟩ := exists_exp_bound_right (fun s => χ (-s)) (hc.comp continuous_neg) (-a)
    (fun s hs => by rw [hχ (-s) (by linarith)]; ring_nf)
  refine ⟨K, hK, fun s hs => ?_⟩
  have := h (-s) (by linarith)
  simpa using this

/-! ### `v = e^χ g` -/

variable {g : ℝ × ℝ → Vec 1} {χ : ℝ → ℝ}

/-- The unweighted section. -/
def vOf (χ : ℝ → ℝ) (g : ℝ × ℝ → Vec 1) (x : ℝ × ℝ) : Vec 1 := Real.exp (χ x.1) • g x

lemma hasFDerivAt_expχ (hχ : ContDiff ℝ ∞ χ) (x : ℝ × ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => Real.exp (χ x.1))
      ((Real.exp (χ x.1) * deriv χ x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
  have hd : HasDerivAt χ (deriv χ x.1) x.1 :=
    ((hχ.differentiable (by simp)) x.1).hasDerivAt
  have h := ((Real.hasDerivAt_exp (χ x.1)).comp x.1 hd).hasFDerivAt.comp x
    (hasFDerivAt_fst (p := x))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun y => ?_)
  simp [mul_comm]

lemma hasFDerivAt_vOf (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ) :
    HasFDerivAt (vOf χ g) (Real.exp (χ x.1) • fderiv ℝ g x +
      ((Real.exp (χ x.1) * deriv χ x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (g x)) x :=
  (hasFDerivAt_expχ hχ x).smul ((hg.differentiable (by simp)) x).hasFDerivAt

lemma vOf_contDiff (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (vOf χ g) :=
  (Real.contDiff_exp.comp (hχ.comp contDiff_fst)).smul hg

/-- A continuous linear map on `ℝ × ℝ` is bounded by its two partials. -/
lemma norm_clm_prod_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ × ℝ →L[ℝ] E) : ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have hy : y = y.1 • ((1 : ℝ), (0 : ℝ)) + y.2 • ((0 : ℝ), (1 : ℝ)) := by
    obtain ⟨a, b⟩ := y; simp
  have h1 : |y.1| ≤ ‖y‖ := by
    rw [← Real.norm_eq_abs]; exact norm_fst_le y
  have h2 : |y.2| ≤ ‖y‖ := by
    rw [← Real.norm_eq_abs]; exact norm_snd_le y
  calc ‖L y‖ = ‖y.1 • L (1, 0) + y.2 • L (0, 1)‖ := by
        conv_lhs => rw [hy]
        rw [map_add, map_smul, map_smul]
    _ ≤ |y.1| * ‖L (1, 0)‖ + |y.2| * ‖L (0, 1)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖y‖ * ‖L (1, 0)‖ + ‖y‖ * ‖L (0, 1)‖ := by gcongr
    _ = (‖L (1, 0)‖ + ‖L (0, 1)‖) * ‖y‖ := by ring

lemma norm_fderiv_vOf_le (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ) :
    ‖fderiv ℝ (vOf χ g) x‖ ≤
      Real.exp (χ x.1) * (|deriv χ x.1| * ‖g x‖ + ‖partialS g x‖ + ‖partialT g x‖) := by
  rw [(hasFDerivAt_vOf hχ hg x).fderiv]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hf : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
  have hD := norm_clm_prod_le (fderiv ℝ g x)
  have e1 : ‖fderiv ℝ g x‖ ≤ ‖partialS g x‖ + ‖partialT g x‖ := hD
  have : |deriv χ x.1| * ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ * ‖g x‖ ≤ |deriv χ x.1| * ‖g x‖ := by
    have := mul_le_mul_of_nonneg_left hf (abs_nonneg (deriv χ x.1))
    nlinarith [norm_nonneg (g x)]
  have he := (Real.exp_pos (χ x.1)).le
  nlinarith [mul_le_mul_of_nonneg_left e1 he, mul_le_mul_of_nonneg_left this he]

end

end QL

end FiniteEnergyPlane

-- FILE: RSK_R3.lean
/-!
# Q-R, layer 3 (local, NOT published): the pointwise equation of a small zero of `qMap`

`qMap x = 0` with `x` small gives, a.e. on the cylinder, the unweighted equation
`(ψs, vs) + Jbar(ψ, v)(ψt, vt) = 0`, with the first components replaced by the continuous
periodic representatives `wrep`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QR3

open QN QN19W

end QR3

end

end FiniteEnergyPlane

-- FILE: RSK_R2.lean
/-!
# Q-R, layer 2 (local, NOT published): calculus of weak partial derivatives

Sums, products with smooth real functions and continuous linear images of weak partials
(`JHolomorphic.HasWeakPartialsOn`), under local integrability on compact subsets.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff

noncomputable section

namespace QR2

open JHolomorphic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {U : Set ℂ}

section test

variable {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
include hφ hφc hφU

end test

end QR2

end

end FiniteEnergyPlane

-- FILE: JWQ_L5b.lean
/-!
# Q-L, layer L5b: finite energy of `v = e^χ g` on the negative half of the period strip
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-- The negative half of the period strip. -/
abbrev negS : Set (ℝ × ℝ) := Iio 0 ×ˢ Ico 0 1

lemma measurableSet_negS : MeasurableSet negS := measurableSet_Iio.prod measurableSet_Ico

lemma integrableOn_exp_negS : IntegrableOn (fun x : ℝ × ℝ => Real.exp (2 * π * x.1)) negS := by
  have hf : IntegrableOn (fun s : ℝ => Real.exp (2 * π * s)) (Iio 0) :=
    (integrableOn_exp_mul_Iic (by positivity) 0).mono_set Iio_subset_Iic_self
  have hg : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico 0 1) := integrableOn_const (by simp)
  have h := hf.mul_prod hg
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  simp only [mul_one] at h
  exact h

variable {g : ℝ × ℝ → Vec 1} {χ : ℝ → ℝ}

end

end QL

end FiniteEnergyPlane

-- FILE: JWQ_L5c.lean
/-!
# Q-L, layer L5c: finite energy of the plane function on the punctured unit disc

Change of variables `ξ ↦ exp(2πξ)` from `{Re ξ < 0, Im ξ ∈ [0, 1)}` onto `ball 0 1 \ {0}`.
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

lemma det_mul_restrict (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det =
      Complex.normSq c := by
  rw [ContinuousLinearMap.det]
  have : (((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ : ℂ →L[ℝ] ℂ) :
      ℂ →ₗ[ℝ] ℂ) = ((LinearMap.mulLeft ℂ c : ℂ →ₗ[ℂ] ℂ).restrictScalars ℝ) := by
    ext x <;> simp [mul_comm]
  rw [this, LinearMap.det_restrictScalars, ← Algebra.norm_complex_apply]
  congr 1
  exact LinearMap.det_mulLeft c

/-- The exponential chart. -/
def Eexp (ξ : ℂ) : ℂ := Complex.exp (((2 * π : ℝ) : ℂ) * ξ)

/-- The negative half strip in `ℂ`. -/
def negC : Set ℂ := cplx ⁻¹' negS

lemma measurableSet_negC : MeasurableSet negC :=
  measurableSet_negS.preimage Complex.equivRealProdCLM.continuous.measurable

lemma Ecyl_cplx (ξ : ℂ) : Ecyl (cplx ξ) = Eexp ξ := by
  rw [Ecyl_eq, toC_cplx, Eexp]

lemma cylInf_add_one (s t : ℝ) : cylInf s (t + 1) = cylInf s t := by
  rw [cylInf_eq_exp, cylInf_eq_exp]
  have : ((2 * π : ℝ) : ℂ) * ((s : ℂ) + ((t + 1 : ℝ) : ℂ) * Complex.I) =
      ((2 * π : ℝ) : ℂ) * ((s : ℂ) + (t : ℂ) * Complex.I) + 2 * π * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma subset_image_negC : ball (0 : ℂ) 1 \ {0} ⊆ Eexp '' negC := by
  intro z hz
  have hz0 : z ≠ 0 := hz.2
  have hz1 : ‖z‖ < 1 := by simpa using hz.1
  set s := Real.log ‖z‖ / (2 * π)
  set t := Complex.arg z / (2 * π)
  have hs : s < 0 :=
    div_neg_of_neg_of_pos (Real.log_neg (norm_pos_iff.2 hz0) hz1) (by positivity)
  have ht1 : t ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith [Complex.arg_le_pi z]
  have ht0 : -(1 / 2) < t := by
    rw [lt_div_iff₀ (by positivity)]; linarith [Complex.neg_pi_lt_arg z]
  have hE : ∀ t' : ℝ, cylInf s t' = z → (0 ≤ t' ∧ t' < 1) → z ∈ Eexp '' negC := by
    intro t' ht' hm
    refine ⟨toC (s, t'), ?_, ?_⟩
    · show cplx (toC (s, t')) ∈ negS
      rw [cplx_toC]; exact ⟨hs, hm⟩
    · rw [← Ecyl_cplx, cplx_toC]; exact ht'
  rcases le_or_gt 0 t with h | h
  · exact hE t (cylInf_log_arg hz0) ⟨h, by linarith⟩
  · exact hE (t + 1) (by rw [cylInf_add_one]; exact cylInf_log_arg hz0) ⟨by linarith, by linarith⟩

lemma injOn_Eexp : InjOn Eexp negC := by
  intro ξ hξ η hη h
  have hξ' : cplx ξ ∈ negS := hξ
  have hη' : cplx η ∈ negS := hη
  simp only [negS, mem_prod, mem_Iio, mem_Ico, cplx_apply] at hξ' hη'
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hx : ξ = η + n * Complex.I := by
    apply mul_left_cancel₀ hπ
    rw [hn]; push_cast; ring
  have him : ξ.im = η.im + n := by rw [hx]; simp
  have hn0 : n = 0 := by
    have h1 : (n : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < n := by linarith
    have h1' : n < 1 := by exact_mod_cast h1
    have h2' : -1 < n := by exact_mod_cast h2
    omega
  rw [hx, hn0]; simp

lemma hasFDerivAt_Eexp (ξ : ℂ) :
    HasFDerivAt Eexp ((ContinuousLinearMap.toSpanSingleton ℂ
      (Eexp ξ * ((2 * π : ℝ) : ℂ))).restrictScalars ℝ) ξ := by
  have h : HasDerivAt Eexp (Eexp ξ * ((2 * π : ℝ) : ℂ)) ξ := by
    have := ((hasDerivAt_id ξ).const_mul (((2 * π : ℝ) : ℂ))).cexp
    simp only [id, mul_one] at this
    exact this
  exact h.hasFDerivAt.restrictScalars ℝ

lemma norm_cplx_le (h : ℂ) : ‖cplx h‖ ≤ ‖h‖ := by
  rw [cplx_apply, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)

variable {v : ℝ × ℝ → Vec 1}

end

end QL

end FiniteEnergyPlane

-- FILE: RSK_R4.lean
/-!
# Q-R, layer 4 (local, NOT published): small zeros of `qMap` are smooth on the cylinder

The cylinder map `gC x q = (cylInf q + e^{χT} ũT(q), β c + e^{χN} ũN(q))` of a small zero `x`
is a weak `Jbar`-holomorphic map on the plane strip `|Im ζ| < 1` (`ζ = s + it`), hence smooth
(Thm 2.22(1) `contDiffOn_of_isWeakJHolomorphicOn`), hence smooth on `ℝ × ℝ` by periodicity.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QR4

open QL QR2 QR3 QN19W QN18 JHolomorphic

variable (χT χN β : ℝ → ℝ)

/-- The cylinder map of `x`. -/
def gC (x : QDom) (q : ℝ × ℝ) : ℂ × ℂ :=
  (cylInf q.1 q.2 + Real.exp (χT q.1) • vL (wrep x.1 q),
    β q.1 • x.2.1 + Real.exp (χN q.1) • vL (wrep x.2.2 q))

variable {χT χN β}

lemma gC_per (x : QDom) (s t : ℝ) : gC χT χN β x (s, t + 1) = gC χT χN β x (s, t) := by
  simp only [gC, cylInf_add_one, (wrep_prop x.1).2.1, (wrep_prop x.2.2).2.1]

/-! ### Smooth pieces on the plane -/

lemma cylInf_cplx (ζ : ℂ) : cylInf (cplx ζ).1 (cplx ζ).2 = Complex.exp (((2 * π : ℝ) : ℂ) * ζ) := by
  rw [cylInf_eq_exp]
  congr 2
  simp only [cplx_apply]
  exact Complex.re_add_im ζ

lemma contDiff_cyl : ContDiff ℝ ∞ (fun ζ : ℂ => cylInf (cplx ζ).1 (cplx ζ).2) := by
  have e : (fun ζ : ℂ => cylInf (cplx ζ).1 (cplx ζ).2) =
      fun ζ => Complex.exp (((2 * π : ℝ) : ℂ) * ζ) := funext cylInf_cplx
  rw [e]
  have h : ContDiff ℂ ∞ (fun ζ : ℂ => Complex.exp (((2 * π : ℝ) : ℂ) * ζ)) :=
    Complex.contDiff_exp.comp ((contDiff_const (𝕜 := ℂ)).mul contDiff_id)
  exact h.restrict_scalars ℝ

/-! ### `L^p` on compact sets -/

end QR4

end

end FiniteEnergyPlane

-- FILE: RSK_R5.lean
/-!
# Q-R, layer 5 (local, NOT published): weak partials of the cylinder map on the plane strip

R2 step 1: `ζ ↦ gC x (cplx ζ)` has weak partials `Ps x`, `Pt x` on `stripU`, all three locally
integrable (in `L⁴` on compacts).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QR5

open QL QR2 QR3 QR4 QN19W QN18 JHolomorphic

variable {χT χN β : ℝ → ℝ}

end QR5

end

end FiniteEnergyPlane

-- FILE: RSK_R6.lean
/-!
# Q-R, layer 6 (local, NOT published): small zeros of `qMap` give smooth cylinder maps

R2 steps 2–4: the a.e. equation `Ps + Jbar(gC) Pt = 0` on the plane strip, `L⁴` on compacts,
values in `ℂ × ball 0 ρ` for small `x`, and smoothness of `gC x` on `ℝ × ℝ` via Thm 2.22(1).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QR6

open QL QR2 QR3 QR4 QR5 QN19W QN18 JHolomorphic

variable {χT χN β : ℝ → ℝ}

/-! ### `L⁴` on compacts -/

/-! ### Values in the tube -/

lemma exists_mapsTo {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : δ < 0) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∀ x : QDom, ‖x‖ < ε → ∀ q : ℝ × ℝ, (gC χT χN β x q).2 ∈ ball (0 : ℂ) ρ := by
  obtain ⟨Mβ, hMβ0, hMβ⟩ := beta_bdd hβ
  obtain ⟨ME, hME0, hME⟩ := expN_bdd hδ hχN
  set K := Mβ + ME * UK + 1 with hK
  have hKp : 0 < K := by have := UK_pos; positivity
  refine ⟨ρ / K, div_pos hρ hKp, fun x hx q => ?_⟩
  rw [mem_ball_zero_iff]
  have hc : ‖x.2.1‖ ≤ ‖x‖ := (norm_fst_le x.2).trans (norm_snd_le x)
  have hw := comp_bound x.2.2 x ((norm_snd_le x.2).trans (norm_snd_le x)) q
  have hb := hMβ q.1
  have he := hME q.1
  calc ‖(gC χT χN β x q).2‖ ≤ |β q.1| * ‖x.2.1‖ + |Real.exp (χN q.1)| * ‖vL (wrep x.2.2 q)‖ := by
        simp only [gC]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ Mβ * ‖x‖ + ME * (UK * ‖x‖) := by
        gcongr
    _ ≤ K * ‖x‖ := by rw [hK]; nlinarith [norm_nonneg x]
    _ < K * (ρ / K) := by gcongr
    _ = ρ := by field_simp

/-! ### Smoothness -/

end QR6

end

end FiniteEnergyPlane

-- FILE: RSK_R7.lean
/-!
# Q-R, layer 7 (local, NOT published): classical consequences of a smooth `gC`

R2 step 5: if `gC x` is smooth, then the representatives `wrep x.1`, `wrep x.2.2` are smooth with
`L⁴` classical partials, and `∂ₛ gC + Jbar(gC) ∂ₜ gC = 0` holds everywhere on `ℝ × ℝ`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QR7

open QL QR2 QR3 QR4 QR5 QR6 QN QN19W QN18 JHolomorphic

variable {χT χN β : ℝ → ℝ}

lemma contDiff_cylP : ContDiff ℝ ∞ (fun q : ℝ × ℝ => cylInf q.1 q.2) := by
  have e : (fun q : ℝ × ℝ => cylInf q.1 q.2) =
      (fun ζ : ℂ => cylInf (cplx ζ).1 (cplx ζ).2) ∘ toC := by
    funext q; simp [toC_re, toC_im]
  rw [e]; exact contDiff_cyl.comp Complex.equivRealProdCLM.symm.contDiff

lemma contDiff_wrep1 (hχT : ContDiff ℝ ∞ χT) (x : QDom) (h : ContDiff ℝ ∞ (gC χT χN β x)) :
    ContDiff ℝ ∞ (wrep x.1) := by
  have e : wrep x.1 = fun q => cL (Real.exp (-χT q.1) • ((gC χT χN β x q).1 - cylInf q.1 q.2)) := by
    funext q
    simp only [gC, add_sub_cancel_left, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_smul, cL_apply, vL_apply, cToVec_vecToC]
  rw [e]
  exact cL.contDiff.comp (((Real.contDiff_exp.comp (hχT.neg.comp contDiff_fst))).smul
    ((contDiff_fst.comp h).sub contDiff_cylP))

lemma contDiff_wrep2 (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β) (x : QDom)
    (h : ContDiff ℝ ∞ (gC χT χN β x)) : ContDiff ℝ ∞ (wrep x.2.2) := by
  have e : wrep x.2.2 = fun q =>
      cL (Real.exp (-χN q.1) • ((gC χT χN β x q).2 - β q.1 • x.2.1)) := by
    funext q
    simp only [gC, add_sub_cancel_left, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_smul, cL_apply, vL_apply, cToVec_vecToC]
  rw [e]
  exact cL.contDiff.comp (((Real.contDiff_exp.comp (hχN.neg.comp contDiff_fst))).smul
    ((contDiff_snd.comp h).sub ((hβ.comp contDiff_fst).smul contDiff_const)))

/-- The pointwise operator of a map on `ℝ × ℝ`. -/
def dbarC (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (g : ℝ × ℝ → ℂ × ℂ) (q : ℝ × ℝ) : ℂ × ℂ :=
  fderiv ℝ g q (1, 0) + Jbar (g q) (fderiv ℝ g q (0, 1))

end QR7

end

end FiniteEnergyPlane

-- FILE: RSK_R8.lean
/-!
# Q-R, layer 8 (local, NOT published): the plane map of a smooth periodic cylinder map

Generic version of `QL.pf` (L4/L5c) with values in any normed space and a prescribed value `c₀`
at `0`: `pfG c₀ G (cylInf s t) = G (s, t)`. It is smooth on `ℂ \ {0}`, the chain rule through the
exponential chart holds, and finite cylinder energy on `negS` gives finite energy on the
punctured unit disc.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QR8

open QL QR

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The plane map of `G`. -/
def pfG (c₀ : E) (G : ℝ × ℝ → E) (z : ℂ) : E := if z = 0 then c₀ else G (zc z)

variable {c₀ : E} {G : ℝ × ℝ → E}

lemma pfG_zero : pfG c₀ G 0 = c₀ := by simp [pfG]

lemma pfG_ne {z : ℂ} (hz : z ≠ 0) : pfG c₀ G z = G (zc z) := by simp [pfG, hz]

lemma pfG_cylInf (hper : ∀ s t : ℝ, G (s, t + 1) = G (s, t)) (s t : ℝ) :
    pfG c₀ G (cylInf s t) = G (s, t) := by
  rw [pfG, if_neg (cylInf_ne_zero s t), zc, norm_cylInf, Real.log_exp,
    mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]
  obtain ⟨k, hk⟩ := arg_cylInf s t
  rw [hk]
  simpa using per_int hper (s, t) k

lemma pfG_local (hper : ∀ s t : ℝ, G (s, t + 1) = G (s, t)) (s₀ t₀ : ℝ) {z : ℂ}
    (hz : z ∈ ball (cylInf s₀ t₀) ‖cylInf s₀ t₀‖) :
    pfG c₀ G z = G (s₀ + (lchart (z / cylInf s₀ t₀ - 1)).re,
      t₀ + (lchart (z / cylInf s₀ t₀ - 1)).im) := by
  have h0 := cylInf_ne_zero s₀ t₀
  have hlt : ‖z / cylInf s₀ t₀ - 1‖ < 1 := by
    rw [div_sub_one h0, norm_div, div_lt_one (norm_pos_iff.2 h0)]
    rwa [mem_ball, dist_eq_norm] at hz
  rw [← pfG_cylInf (c₀ := c₀) hper, ← QL.cylInf_mul_one_add s₀ t₀ hlt, add_sub_cancel,
    mul_div_cancel₀ _ h0]

lemma pfG_contDiffAt (hG : ContDiff ℝ ∞ G) (hper : ∀ s t : ℝ, G (s, t + 1) = G (s, t))
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) : ContDiffAt ℝ ∞ (pfG c₀ G) z₀ := by
  set s₀ := Real.log ‖z₀‖ / (2 * π)
  set t₀ := Complex.arg z₀ / (2 * π)
  have he : cylInf s₀ t₀ = z₀ := cylInf_log_arg hz₀
  have hr : 0 < ‖cylInf s₀ t₀‖ := norm_pos_iff.2 (cylInf_ne_zero _ _)
  have hloc : pfG c₀ G =ᶠ[𝓝 z₀] fun z => G (s₀ + (lchart (z / cylInf s₀ t₀ - 1)).re,
      t₀ + (lchart (z / cylInf s₀ t₀ - 1)).im) := by
    have : ball (cylInf s₀ t₀) ‖cylInf s₀ t₀‖ ∈ 𝓝 z₀ := by
      rw [he] at hr ⊢; exact ball_mem_nhds _ hr
    filter_upwards [this] with z hz
    exact pfG_local hper s₀ t₀ hz
  refine ContDiffAt.congr_of_eventuallyEq ?_ hloc
  have hq : ContDiffAt ℝ ∞ (fun z => z / cylInf s₀ t₀ - 1) z₀ :=
    (contDiffAt_id.div_const _).sub contDiffAt_const
  have hq0 : ‖z₀ / cylInf s₀ t₀ - 1‖ < 1 := by
    rw [he, div_self hz₀, sub_self, norm_zero]; norm_num
  have hl : ContDiffAt ℝ ∞ (fun z => lchart (z / cylInf s₀ t₀ - 1)) z₀ :=
    ContDiffAt.comp (g := lchart) (f := fun z => z / cylInf s₀ t₀ - 1) z₀
      (lchart_contDiffAt hq0) hq
  have hpair : ContDiffAt ℝ ∞ (fun z => (s₀ + (lchart (z / cylInf s₀ t₀ - 1)).re,
      t₀ + (lchart (z / cylInf s₀ t₀ - 1)).im)) z₀ :=
    (contDiffAt_const.add (Complex.reCLM.contDiff.contDiffAt.comp z₀ hl)).prodMk
      (contDiffAt_const.add (Complex.imCLM.contDiff.contDiffAt.comp z₀ hl))
  exact hG.contDiffAt.comp z₀ hpair

/-- The chain rule through `Ecyl`. -/
lemma fderiv_pfG_cylInf (hG : ContDiff ℝ ∞ G) (hper : ∀ s t : ℝ, G (s, t + 1) = G (s, t))
    (x : ℝ × ℝ) (h : ℂ) :
    fderiv ℝ (pfG c₀ G) (Ecyl x) (((2 * π : ℝ) : ℂ) * Ecyl x * h) = fderiv ℝ G x (cplx h) := by
  have hcomp : (pfG c₀ G) ∘ Ecyl = G := by
    funext x; simp [Ecyl, pfG_cylInf hper]
  have hdz : DifferentiableAt ℝ (pfG c₀ G) (Ecyl x) :=
    (pfG_contDiffAt hG hper (cylInf_ne_zero _ _)).differentiableAt (by simp)
  have h1 := (hdz.hasFDerivAt.comp x (hasFDerivAt_Ecyl x))
  rw [hcomp] at h1
  have h2 : HasFDerivAt G (fderiv ℝ G x) x := ((hG.differentiable (by simp)) x).hasFDerivAt
  have := congrArg (fun L : ℝ × ℝ →L[ℝ] E => L (cplx h)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_coe] at this
  rw [← this]
  congr 1

/-- The pointwise conformal bound. -/
lemma norm_mul_norm_fderiv_pfG_le (hG : ContDiff ℝ ∞ G)
    (hper : ∀ s t : ℝ, G (s, t + 1) = G (s, t)) (ξ : ℂ) :
    ‖Eexp ξ * ((2 * π : ℝ) : ℂ)‖ * ‖fderiv ℝ (pfG c₀ G) (Eexp ξ)‖ ≤ ‖fderiv ℝ G (cplx ξ)‖ := by
  set c : ℂ := Eexp ξ * ((2 * π : ℝ) : ℂ)
  have hc : c ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (Complex.ofReal_ne_zero.2 (by positivity))
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
  rw [mul_comm, ← le_div_iff₀ hcn]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun k => ?_
  have hk := fderiv_pfG_cylInf (c₀ := c₀) hG hper (cplx ξ) (k / c)
  rw [Ecyl_cplx, show ((2 * π : ℝ) : ℂ) * Eexp ξ * (k / c) = k by
    simp only [c]; field_simp; exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)] at hk
  rw [hk]
  refine ((fderiv ℝ G (cplx ξ)).le_opNorm _).trans ?_
  refine (mul_le_mul_of_nonneg_left (norm_cplx_le _) (norm_nonneg _)).trans (le_of_eq ?_)
  rw [norm_div]; ring

end QR8

end

end FiniteEnergyPlane

-- FILE: RSK_R9.lean
/-!
# Q-R, layer 9 (local, NOT published): the member as a plane map

`pG x = pfG (0, c) (gC x)`; `pG x` is continuous at `0`; and the cylinder energy of `gC x` on
`negS = (-∞, 0) × [0, 1)` is finite when the representatives are smooth.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QR9

open QL QR QR2 QR3 QR4 QR5 QR6 QR7 QR8 QN QN19W QN18 JHolomorphic

variable {χT χN β : ℝ → ℝ}

/-- The bridge. -/
theorem pG_eq_pfG (x : QDom) : pG χT χN β x = pfG ((0 : ℂ), x.2.1) (gC χT χN β x) := by
  funext z
  by_cases hz : z = 0
  · subst hz; rw [pfG_zero, pG, pLc_zero]; simp
  · rw [pfG_ne hz, pG, pLc_ne _ _ _ hz, wV_apply, U_apply]
    simp only [Uv, gC, zc]
    rw [cylInf_log_arg hz]
    refine Prod.ext ?_ ?_ <;> simp [Complex.real_smul]

/-! ### Finite cylinder energy on `negS` -/

lemma deriv_beta_eq_zero (hβ : IsLeftCutoff β) {s : ℝ} (hs : s < -1) : deriv β s = 0 := by
  have : β =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds hs] with r hr
    exact hβ.2.1 r (le_of_lt hr)
  rw [this.deriv_eq, deriv_const]

end QR9

end

end FiniteEnergyPlane

-- FILE: RSK_R10.lean
/-!
# Q-R, layer 10 (local, NOT published): R2 `member_regular`

Members of small zeros of `qMap` are smooth and `Jbar`-holomorphic on `ℂ`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QR10

open QL QR QR2 QR3 QR4 QR5 QR6 QR7 QR8 QR9 QN QN19W QN18 JHolomorphic

variable {χT χN β : ℝ → ℝ}

lemma Ecyl_zc {z : ℂ} (hz : z ≠ 0) : Ecyl (zc z) = z := cylInf_log_arg hz

end QR10

end

end FiniteEnergyPlane

-- FILE: RSK_R12.lean
/-!
# Q-R, layer 12 (local, NOT published): the single-scale rescaled graph structure of `Jbar`

`Kh q = Jbar(q.1, rtr ρ q.2)` is a global smooth almost complex structure on `ℂ × ℂ`, equal to
`Jbar` on `ℂ × ball 0 (ρ/4)` and to `jStd` along `w = 0`; `Hh` is its `w`-divided difference
(`Kh q = jStd + Hh q q.2`).

For a holomorphic base `φ` (with complex derivative `dφ`) and the rescaled perturbation
`v = λ⁻¹ (u - (φ, 0))` of a `Jbar`-holomorphic `u`, the graph `ζ ↦ (c + ζ, v(c + ζ), λ)` is
`JP φ dφ`-holomorphic, where `JP = vgJ JfP mP` with
`JfP e = Kh(φ a + λ v₁, λ v₂)` and `mP e = Hh(φ a + λ v₁, λ v₂) v₂ (i φ'(a), 0)` at
`e = (a, v, p)`, `λ = Re p`. `JP` is smooth in `λ` down to `λ = 0`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology JHolomorphic
open scoped ContDiff ENNReal NNReal

noncomputable section

namespace QR12

open QR11

variable (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)

/-- `Jbar` with the fibre coordinate retracted into `ball 0 ρ`. -/
def Kh (q : ℂ × ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ := Jbar (q.1, rtr ρ q.2)

/-- The `w`-divided difference of `Kh`. -/
def Hh (q : ℂ × ℂ) : ℂ →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ) :=
  ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun w => Kh ρ Jbar (q.1, w)) (θ • q.2)

/-- The point of the target. -/
def yP (φ : ℂ → ℂ) (e : ℂ × (ℂ × ℂ) × ℂ) : ℂ × ℂ :=
  (φ e.1 + e.2.2.re • e.2.1.1, e.2.2.re • e.2.1.2)

/-- The fibre structure. -/
def JfP (φ : ℂ → ℂ) (e : ℂ × (ℂ × ℂ) × ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ := Kh ρ Jbar (yP φ e)

/-- The inhomogeneous term. -/
def mP (φ dφ : ℂ → ℂ) (e : ℂ × (ℂ × ℂ) × ℂ) : ℂ × ℂ :=
  Hh ρ Jbar (yP φ e) e.2.1.2 (Complex.I * dφ e.1, 0)

/-- The rescaled graph structure. -/
def JP (φ dφ : ℂ → ℂ) : ℂ × (ℂ × ℂ) × ℂ → (ℂ × (ℂ × ℂ) × ℂ) →L[ℝ] (ℂ × (ℂ × ℂ) × ℂ) :=
  vgJ (JfP ρ Jbar φ) (mP ρ Jbar φ dφ)

variable {ρ Jbar}

section Props

variable (hρ : 0 < ρ) (hJs : ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ))
  (hsq : ∀ p ∈ univ ×ˢ ball (0 : ℂ) ρ, (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
  (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)

include hρ hJs in
lemma contDiff_Kh : ContDiff ℝ ∞ (Kh ρ Jbar) := by
  have h : ContDiff ℝ ∞ (fun q : ℂ × ℂ => (q.1, rtr ρ q.2)) :=
    contDiff_fst.prodMk ((rtr_contDiff ρ).comp contDiff_snd)
  exact hJs.comp_contDiff h fun q => ⟨mem_univ _, mem_ball_zero_iff.2 (norm_rtr_lt hρ _)⟩

include hρ hsq in
lemma Kh_sq (q : ℂ × ℂ) (v : ℂ × ℂ) : Kh ρ Jbar q (Kh ρ Jbar q v) = -v := by
  have := congrArg (fun L : ℂ × ℂ →L[ℝ] ℂ × ℂ => L v)
    (hsq (q.1, rtr ρ q.2) ⟨mem_univ _, mem_ball_zero_iff.2 (norm_rtr_lt hρ _)⟩)
  simpa [Kh] using this

include hρ h0 in
lemma Kh_zero (a : ℂ) : Kh ρ Jbar (a, 0) = jStd := by
  rw [Kh, rtr_eq hρ (by rw [norm_zero]; positivity : ‖(0 : ℂ)‖ < ρ / 4), h0]

include hρ in
lemma Kh_eq {q : ℂ × ℂ} (hq : ‖q.2‖ < ρ / 4) : Kh ρ Jbar q = Jbar q := by
  rw [Kh, rtr_eq hρ hq]

include hρ hJs in
lemma contDiff_Hh : ContDiff ℝ ∞ (Hh ρ Jbar) :=
  (hadamard_integral_fderiv (fun q : ℂ × ℂ => Kh ρ Jbar q) (contDiff_Kh hρ hJs)).1

include hρ hJs h0 in
lemma Kh_eq_add (q : ℂ × ℂ) : Kh ρ Jbar q = jStd + Hh ρ Jbar q q.2 := by
  have h := (hadamard_integral_fderiv (fun q : ℂ × ℂ => Kh ρ Jbar q) (contDiff_Kh hρ hJs)).2 q
  rw [Kh_zero hρ h0] at h
  exact h

include hρ hJs in
lemma contDiff_JfP {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (JfP ρ Jbar φ) := by
  have hy : ContDiff ℝ ∞ (yP φ) :=
    ((hφ.comp contDiff_fst).add ((Complex.reCLM.contDiff.comp (contDiff_snd.comp contDiff_snd)).smul
      (contDiff_fst.comp (contDiff_fst.comp contDiff_snd)))).prodMk
      ((Complex.reCLM.contDiff.comp (contDiff_snd.comp contDiff_snd)).smul
        (contDiff_snd.comp (contDiff_fst.comp contDiff_snd)))
  exact (contDiff_Kh hρ hJs).comp hy

include hρ hJs in
lemma contDiff_mP {φ dφ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hdφ : ContDiff ℝ ∞ dφ) :
    ContDiff ℝ ∞ (mP ρ Jbar φ dφ) := by
  have hy : ContDiff ℝ ∞ (yP φ) :=
    ((hφ.comp contDiff_fst).add ((Complex.reCLM.contDiff.comp (contDiff_snd.comp contDiff_snd)).smul
      (contDiff_fst.comp (contDiff_fst.comp contDiff_snd)))).prodMk
      ((Complex.reCLM.contDiff.comp (contDiff_snd.comp contDiff_snd)).smul
        (contDiff_snd.comp (contDiff_fst.comp contDiff_snd)))
  have hH := (contDiff_Hh hρ hJs).comp hy
  have hv : ContDiff ℝ ∞ (fun e : ℂ × (ℂ × ℂ) × ℂ => e.2.1.2) :=
    contDiff_snd.comp (contDiff_fst.comp contDiff_snd)
  have hw : ContDiff ℝ ∞ (fun e : ℂ × (ℂ × ℂ) × ℂ => ((Complex.I * dφ e.1, 0) : ℂ × ℂ)) :=
    (contDiff_const.mul (hdφ.comp contDiff_fst)).prodMk contDiff_const
  exact (hH.clm_apply hv).clm_apply hw

include hρ hJs hsq in
/-- The rescaled graph structure is a global smooth almost complex structure. -/
theorem isAlmostComplexOn_JP {φ dφ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hdφ : ContDiff ℝ ∞ dφ) :
    IsAlmostComplexOn (JP ρ Jbar φ dφ) univ :=
  isAlmostComplexOn_vgJ (contDiff_JfP hρ hJs hφ) (contDiff_mP hρ hJs hφ hdφ)
    fun e v => Kh_sq hρ hsq _ v

/-! ### The rescaled equation -/

lemma jStd_apply (a b : ℂ) : jStd (a, b) = (Complex.I * a, Complex.I * b) := by
  simp [jStd]

include hρ hJs h0 in
/-- The pointwise rescaled equation. -/
theorem rescaled_eq {u : ℂ → ℂ × ℂ} {φ dφ : ℂ → ℂ} {z : ℂ} {l : ℝ} (hl : l ≠ 0)
    (hu : DifferentiableAt ℝ u z) (hφ : HasDerivAt φ (dφ z) z)
    (hdbar : dbarJ Jbar u z = 0) (hsmall : ‖(u z).2‖ < ρ / 4) :
    fderiv ℝ (fun z => l⁻¹ • (u z - (φ z, 0))) z 1 +
      JfP ρ Jbar φ (z, l⁻¹ • (u z - (φ z, 0)), (l : ℂ))
        (fderiv ℝ (fun z => l⁻¹ • (u z - (φ z, 0))) z Complex.I) +
      mP ρ Jbar φ dφ (z, l⁻¹ • (u z - (φ z, 0)), (l : ℂ)) = 0 := by
  have hφr : HasFDerivAt φ ((ContinuousLinearMap.toSpanSingleton ℂ (dφ z)).restrictScalars ℝ) z :=
    hφ.hasFDerivAt.restrictScalars ℝ
  have hpair : HasFDerivAt (fun z => ((φ z, 0) : ℂ × ℂ))
      ((((ContinuousLinearMap.toSpanSingleton ℂ (dφ z)).restrictScalars ℝ)).prod 0) z :=
    hφr.prodMk (hasFDerivAt_const _ z)
  have hd : HasFDerivAt (fun z => l⁻¹ • (u z - (φ z, 0)))
      (l⁻¹ • (fderiv ℝ u z - (((ContinuousLinearMap.toSpanSingleton ℂ (dφ z)).restrictScalars ℝ)).prod 0)) z :=
    (hu.hasFDerivAt.sub hpair).const_smul l⁻¹
  rw [hd.fderiv]
  have hy : yP φ (z, l⁻¹ • (u z - (φ z, 0)), (l : ℂ)) = u z := by
    simp only [yP, Complex.ofReal_re, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
      sub_zero, smul_smul, mul_inv_cancel₀ hl, one_smul]
    ext <;> simp
  simp only [JfP, mP, hy]
  rw [Kh_eq hρ hsmall]
  have hH : Hh ρ Jbar (u z) (l⁻¹ • (u z - (φ z, 0))).2 =
      l⁻¹ • (Jbar (u z) - jStd) := by
    have e := Kh_eq_add hρ hJs h0 (u z)
    rw [Kh_eq hρ hsmall] at e
    have e2 : (l⁻¹ • (u z - (φ z, 0))).2 = l⁻¹ • (u z).2 := by simp
    rw [e2, map_smul, e]
    simp
  rw [hH]
  have hdb : fderiv ℝ u z 1 + Jbar (u z) (fderiv ℝ u z Complex.I) = 0 := hdbar
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.zero_apply, map_smul, map_sub,
    jStd_apply]
  rw [← smul_add, ← smul_add]
  have : fderiv ℝ u z 1 - ((1 : ℂ) • dφ z, (0 : ℂ)) +
      (Jbar (u z) (fderiv ℝ u z Complex.I) - Jbar (u z) (Complex.I • dφ z, 0)) +
      (Jbar (u z) (Complex.I * dφ z, 0) - (Complex.I * (Complex.I * dφ z), Complex.I * 0)) = 0 := by
    have e3 : (Complex.I • dφ z, (0 : ℂ)) = (Complex.I * dφ z, 0) := by simp
    rw [e3]
    have e4 : fderiv ℝ u z 1 = -Jbar (u z) (fderiv ℝ u z Complex.I) := eq_neg_of_add_eq_zero_left hdb
    rw [e4]
    ext <;> simp [← mul_assoc] <;> ring
  rw [this, smul_zero]

end Props

end QR12

end

end FiniteEnergyPlane

-- FILE: RSK_R13.lean
/-!
# Q-R, layer 13 (local, NOT published): the `L⁴` bound of the linear part on the unit disc

For a small zero `x` (smooth representatives), `z ↦ pLc z x = pfG (0, c) (hC x)` with the cylinder
map `hC x q = (e^{χT} ũT, β c + e^{χN} ũN)`, and
`‖D_z (pLc · x)‖_{L⁴(ball 0 1)} ≤ C ‖x‖`: change of variables `z = e^{2πξ}` (conformal factor
`e^{-4πs}`), slopes `π` of `χT`, `χN` at `-∞`, and the `W1p` norms of the components.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic
open scoped ContDiff Real ENNReal NNReal

noncomputable section

namespace QR13

open QL QR QR2 QR3 QR4 QR5 QR6 QR7 QR8 QR9 QR10 QR11 QR12 QN QN19W QN18

variable {χT χN β : ℝ → ℝ}

/-! ### The partials of `wrep` are the `W1p` components -/

theorem ae_partials_wrep (w : ↥(W1p 4 1)) (hsm : ContDiff ℝ ∞ (wrep w)) :
    ∀ᵐ x ∂cylMeasure, ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) x = partialS (wrep w) x ∧
      ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) x = partialT (wrep w) x := by
  obtain ⟨hW, hLpK⟩ := isWeak_of_mem_W1p (w : Triple 1 4) w.2 (wrep w) (wrep_prop w).1
    (wrep_prop w).2.1 (wrep_prop w).2.2
  have hcplx : Continuous cplx := Complex.equivRealProdCLM.continuous
  have hsmU1 : ContDiffOn ℝ 1 (fun z => wrep w (cplx z)) stripU :=
    ((hsm.comp Complex.equivRealProdCLM.contDiff).of_le (by simp)).contDiffOn
  have hW' := HasWeakPartialsOn.of_contDiffOn isOpen_stripU hsmU1
  have hcd : Continuous (fderiv ℝ (wrep w)) := hsm.continuous_fderiv (by simp)
  have hint : ∀ K ⊆ stripU, IsCompact K →
      IntegrableOn (fun z => perF ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z)) K ∧
      IntegrableOn (fun z => perF ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z)) K ∧
      IntegrableOn (fun z => fderiv ℝ (fun z => wrep w (cplx z)) z 1) K ∧
      IntegrableOn (fun z => fderiv ℝ (fun z => wrep w (cplx z)) z Complex.I) K := by
    intro K hKU hK
    haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    refine ⟨(hLpK K hKU).1.integrable (by norm_num), (hLpK K hKU).2.integrable (by norm_num),
      ?_, ?_⟩
    · simp only [fderiv_comp_cplx]
      exact ((hcd.comp hcplx).clm_apply continuous_const).continuousOn.integrableOn_compact hK
    · simp only [fderiv_comp_cplx]
      exact ((hcd.comp hcplx).clm_apply continuous_const).continuousOn.integrableOn_compact hK
  have heqU := HasWeakPartialsOn.ae_eq isOpen_stripU hW hW' hint
  have hsub : upS ⊆ toC ⁻¹' stripU := by
    intro x hx
    simp only [mem_preimage, stripU, mem_setOf_eq, toC_im]
    rw [abs_lt]; exact ⟨by linarith [hx.2.1], hx.2.2⟩
  have h1 := (measurePreserving_toC.restrict_preimage
    isOpen_stripU.measurableSet).quasiMeasurePreserving.ae heqU
  have h2 : ∀ᵐ x ∂(volume.restrict upS), _ := ae_restrict_of_ae_restrict_of_subset hsub h1
  have h3 : ∀ᵐ x ∂cylMeasure, x ∈ upS :=
    ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)
  filter_upwards [h2, h3] with x hx hxm
  simp only [cplx_toC, fderiv_comp_cplx, perF_of_mem _ hxm] at hx
  refine ⟨hx.1.trans ?_, hx.2.trans ?_⟩
  · simp [partialS, cplx_apply]
  · simp [partialT, cplx_apply]

/-! ### `L⁴` norms of the components on the cylinder -/

lemma eLpNorm_lp_le {f : LpCyl 1 4} {r : ℝ} (h : ‖f‖ ≤ r) :
    eLpNorm (f : ℝ × ℝ → Vec 1) 4 cylMeasure ≤ ENNReal.ofReal r := by
  rw [← Lp.enorm_def, ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal h

lemma norm_triple_le (w : ↥(W1p 4 1)) :
    ‖(w : Triple 1 4).1‖ ≤ ‖w‖ ∧ ‖(w : Triple 1 4).2.1‖ ≤ ‖w‖ ∧ ‖(w : Triple 1 4).2.2‖ ≤ ‖w‖ := by
  have e : ‖(w : Triple 1 4)‖ = ‖w‖ := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← e]; exact norm_fst_le _
  · rw [← e]; exact (norm_fst_le _).trans (norm_snd_le _)
  · rw [← e]; exact (norm_snd_le _).trans (norm_snd_le _)

lemma eLpNorm_wrep_le (w : ↥(W1p 4 1)) :
    eLpNorm (wrep w) 4 cylMeasure ≤ ENNReal.ofReal ‖w‖ := by
  rw [← eLpNorm_congr_ae (wrep_prop w).2.2]
  exact eLpNorm_lp_le (norm_triple_le w).1

lemma eLpNorm_partialS_le (w : ↥(W1p 4 1)) (hsm : ContDiff ℝ ∞ (wrep w)) :
    eLpNorm (partialS (wrep w)) 4 cylMeasure ≤ ENNReal.ofReal ‖w‖ := by
  rw [← eLpNorm_congr_ae ((ae_partials_wrep w hsm).mono fun x hx => hx.1)]
  exact eLpNorm_lp_le (norm_triple_le w).2.1

lemma eLpNorm_partialT_le (w : ↥(W1p 4 1)) (hsm : ContDiff ℝ ∞ (wrep w)) :
    eLpNorm (partialT (wrep w)) 4 cylMeasure ≤ ENNReal.ofReal ‖w‖ := by
  rw [← eLpNorm_congr_ae ((ae_partials_wrep w hsm).mono fun x hx => hx.2)]
  exact eLpNorm_lp_le (norm_triple_le w).2.2

lemma restrict_negS_le : volume.restrict negS ≤ cylMeasure :=
  Measure.restrict_mono (prod_mono (subset_univ _) le_rfl) le_rfl

/-! ### Change of variables with exponent `4` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c₀ : E} {G : ℝ × ℝ → E}

lemma norm_Eexp (ξ : ℂ) : ‖Eexp ξ‖ = Real.exp (2 * π * ξ.re) := by
  rw [Eexp, Complex.norm_exp]
  congr 1
  simp

lemma pt_four {a d D e : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (had : a * d ≤ D) (he : 0 ≤ e)
    (hae : 1 ≤ a ^ 2 * e) : a ^ 2 * d ^ 4 ≤ D ^ 4 * e := by
  have h4 : (a * d) ^ 4 ≤ D ^ 4 := pow_le_pow_left₀ (by positivity) had 4
  calc a ^ 2 * d ^ 4 ≤ a ^ 2 * d ^ 4 * (a ^ 2 * e) :=
        le_mul_of_one_le_right (by positivity) hae
    _ = (a * d) ^ 4 * e := by ring
    _ ≤ D ^ 4 * e := mul_le_mul_of_nonneg_right h4 he

/-- `∫_{|z|<1} |D(pfG G)|⁴ ≤ ∫_{s<0} (e^{-πs} |DG|)⁴`. -/
theorem lintegral_ball_pfG_le (hG : ContDiff ℝ ∞ G) (hper : ∀ s t : ℝ, G (s, t + 1) = G (s, t)) :
    ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖fderiv ℝ (pfG c₀ G) z‖ ^ 4) ≤
      ∫⁻ q in negS, ENNReal.ofReal ((Real.exp (-(π * q.1)) * ‖fderiv ℝ G q‖) ^ 4) := by
  have hd : ∀ ξ ∈ negC, HasFDerivWithinAt Eexp ((ContinuousLinearMap.toSpanSingleton ℂ
      (Eexp ξ * ((2 * π : ℝ) : ℂ))).restrictScalars ℝ) negC ξ :=
    fun ξ _ => (hasFDerivAt_Eexp ξ).hasFDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_negC hd
    injOn_Eexp (fun z => ENNReal.ofReal (‖fderiv ℝ (pfG c₀ G) z‖ ^ 4))
  have hmeas : Measurable fun ξ : ℂ =>
      ENNReal.ofReal ((Real.exp (-(π * (cplx ξ).1)) * ‖fderiv ℝ G (cplx ξ)‖) ^ 4) := by
    have hc : Continuous cplx := Complex.equivRealProdCLM.continuous
    exact ENNReal.measurable_ofReal.comp
      (((Real.continuous_exp.comp ((continuous_const.mul (continuous_fst.comp hc)).neg)).mul
        ((hG.continuous_fderiv (by simp)).comp hc).norm).pow 4).measurable
  have hmp := measurePreserving_cplx.restrict_preimage measurableSet_negS
  have hcomp : ∫⁻ ξ in negC,
      ENNReal.ofReal ((Real.exp (-(π * (cplx ξ).1)) * ‖fderiv ℝ G (cplx ξ)‖) ^ 4) =
      ∫⁻ q in negS, ENNReal.ofReal ((Real.exp (-(π * q.1)) * ‖fderiv ℝ G q‖) ^ 4) :=
    hmp.lintegral_comp (f := fun q => ENNReal.ofReal ((Real.exp (-(π * q.1)) *
      ‖fderiv ℝ G q‖) ^ 4))
      (ENNReal.measurable_ofReal.comp ((((Real.continuous_exp.comp
        ((continuous_const.mul continuous_fst).neg)).mul
        (hG.continuous_fderiv (by simp)).norm).pow 4).measurable))
  have hnull : (ball (0 : ℂ) 1 \ {0} : Set ℂ) =ᵐ[volume] ball (0 : ℂ) 1 :=
    sdiff_null_ae_eq_self (measure_singleton 0)
  calc ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖fderiv ℝ (pfG c₀ G) z‖ ^ 4)
      = ∫⁻ z in ball (0 : ℂ) 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ (pfG c₀ G) z‖ ^ 4) :=
        (setLIntegral_congr hnull).symm
    _ ≤ ∫⁻ z in Eexp '' negC, ENNReal.ofReal (‖fderiv ℝ (pfG c₀ G) z‖ ^ 4) :=
        lintegral_mono_set subset_image_negC
    _ = _ := key
    _ ≤ ∫⁻ ξ in negC,
          ENNReal.ofReal ((Real.exp (-(π * (cplx ξ).1)) * ‖fderiv ℝ G (cplx ξ)‖) ^ 4) := by
        refine setLIntegral_mono hmeas fun ξ _ => ?_
        rw [det_mul_restrict, abs_of_nonneg (Complex.normSq_nonneg _),
          ← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Complex.normSq_eq_norm_sq, mul_pow]
        have hcre : (cplx ξ).1 = ξ.re := by simp [cplx_apply]
        rw [hcre]
        have hn : ‖Eexp ξ * ((2 * π : ℝ) : ℂ)‖ = Real.exp (2 * π * ξ.re) * (2 * π) := by
          rw [norm_mul, norm_Eexp, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity)]
        have hae : 1 ≤ ‖Eexp ξ * ((2 * π : ℝ) : ℂ)‖ ^ 2 * Real.exp (-(π * ξ.re)) ^ 4 := by
          rw [hn, ← Real.exp_nat_mul, mul_pow, mul_comm, ← mul_assoc]
          have e1 : Real.exp (↑(4 : ℕ) * -(π * ξ.re)) * Real.exp (2 * π * ξ.re) ^ 2 = 1 := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf; exact Real.exp_zero
          rw [e1, one_mul]
          have : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
          nlinarith
        have h := pt_four (a := ‖Eexp ξ * ((2 * π : ℝ) : ℂ)‖)
          (d := ‖fderiv ℝ (pfG c₀ G) (Eexp ξ)‖) (D := ‖fderiv ℝ G (cplx ξ)‖)
          (e := Real.exp (-(π * ξ.re)) ^ 4) (norm_nonneg _) (norm_nonneg _)
          (norm_mul_norm_fderiv_pfG_le hG hper ξ) (by positivity) hae
        exact h.trans (le_of_eq (by ring))
    _ = _ := hcomp

end QR13

end

end FiniteEnergyPlane

-- FILE: RSK_R14.lean
/-!
# Q-R, layer 14 (local, NOT published): `‖D_z(pLc · x)‖_{L⁴(ball 0 1)} ≤ C ‖x‖`

The cylinder map of the linear part is `hC x q = (e^{χT} ũT, β c + e^{χN} ũN)`, so
`pLc · x = pfG (0, c) (hC x)`. On `s < 0`, `e^{-πs} |D hC| ≤ C (|ũ| + |∂ũ| + |c| e^{πs})`
(slopes `π` at `-∞`), and the change of variables of layer 13 gives the disc bound.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic
open scoped ContDiff Real ENNReal NNReal

noncomputable section

namespace QR14

open QL QR QR2 QR3 QR4 QR5 QR6 QR7 QR8 QR9 QR10 QR11 QR12 QR13 QN QN19W QN18

variable {χT χN β : ℝ → ℝ}

/-! ### `L⁴` helpers -/

lemma eLpNorm_four_eq {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] (f : α → F)
    (μ : Measure α) :
    eLpNorm f 4 μ = (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 4) ∂μ) ^ (1 / 4 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  norm_cast

lemma eLpNorm_smul_real {α : Type*} [MeasurableSpace α] (r : ℝ) (hr : 0 ≤ r) (f : α → ℝ)
    (μ : Measure α) : eLpNorm (r • f) 4 μ = ENNReal.ofReal r * eLpNorm f 4 μ := by
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hr]

/-- A slope-`π` weight on `s < 0`: `e^{χ} ≤ K e^{πs}` and `|χ'| ≤ c`. -/
lemma left_weight {χ : ℝ → ℝ} {a : ℝ} (hχ : IsSlopeWeight χ π a) :
    ∃ K c : ℝ, 0 < K ∧ 0 ≤ c ∧ ∀ s ≤ 0, Real.exp (χ s) ≤ K * Real.exp (π * s) ∧
      |deriv χ s| ≤ c := by
  obtain ⟨K, hK, hKb⟩ := exists_exp_bound_left χ hχ.1.continuous π fun s hs => hχ.eq_left hs
  have hcd : Continuous (deriv χ) := hχ.1.continuous_deriv (by simp)
  obtain ⟨c₀, hc₀⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 0)).exists_bound_of_continuousOn
    hcd.continuousOn
  refine ⟨K, max c₀ π, hK, le_max_of_le_right Real.pi_pos.le, fun s hs => ⟨hKb s hs, ?_⟩⟩
  rcases le_or_gt s (-1) with h1 | h1
  · rw [hχ.2.1 s h1, abs_of_pos Real.pi_pos]; exact le_max_right _ _
  · have := hc₀ s ⟨h1.le, hs⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- The weighted `L⁴(negS)` bound of `D(e^χ wrep w)`. -/
theorem eLpNorm_vOf_negS {χ : ℝ → ℝ} {a : ℝ} (hχ : IsSlopeWeight χ π a) :
    ∃ C ≥ 0, ∀ w : ↥(W1p 4 1), ContDiff ℝ ∞ (wrep w) →
      eLpNorm (fun q : ℝ × ℝ => Real.exp (-(π * q.1)) * ‖fderiv ℝ (vOf χ (wrep w)) q‖) 4
        (volume.restrict negS) ≤ ENNReal.ofReal (C * ‖w‖) := by
  obtain ⟨K, c, hK, hc, hw⟩ := left_weight hχ
  refine ⟨K * c + K + K, by positivity, fun w hsm => ?_⟩
  set g := wrep w
  have hgc : Continuous g := hsm.continuous
  have hdc : Continuous (fderiv ℝ g) := hsm.continuous_fderiv (by simp)
  have hsc : Continuous (partialS g) := hdc.clm_apply continuous_const
  have htc : Continuous (partialT g) := hdc.clm_apply continuous_const
  have hpt : ∀ q ∈ negS, ‖Real.exp (-(π * q.1)) * ‖fderiv ℝ (vOf χ g) q‖‖ ≤
      ((K * c) • (fun q => ‖g q‖) + K • (fun q => ‖partialS g q‖) +
        K • (fun q => ‖partialT g q‖)) q := by
    intro q hq
    have hs : q.1 ≤ 0 := (show q.1 < 0 from hq.1).le
    obtain ⟨h1, h2⟩ := hw q.1 hs
    have hb := norm_fderiv_vOf_le hχ.1 hsm q
    have hE : Real.exp (-(π * q.1)) * Real.exp (χ q.1) ≤ K := by
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(π * q.1))).le
      calc _ ≤ Real.exp (-(π * q.1)) * (K * Real.exp (π * q.1)) := this
        _ = K := by rw [mul_left_comm, ← Real.exp_add]; simp
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hn := norm_nonneg (g q)
    have hn1 := norm_nonneg (partialS g q)
    have hn2 := norm_nonneg (partialT g q)
    have hS : |deriv χ q.1| * ‖g q‖ + ‖partialS g q‖ + ‖partialT g q‖ ≤
        c * ‖g q‖ + ‖partialS g q‖ + ‖partialT g q‖ := by nlinarith [abs_nonneg (deriv χ q.1)]
    calc Real.exp (-(π * q.1)) * ‖fderiv ℝ (vOf χ g) q‖
        ≤ Real.exp (-(π * q.1)) * (Real.exp (χ q.1) *
            (|deriv χ q.1| * ‖g q‖ + ‖partialS g q‖ + ‖partialT g q‖)) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = (Real.exp (-(π * q.1)) * Real.exp (χ q.1)) *
            (|deriv χ q.1| * ‖g q‖ + ‖partialS g q‖ + ‖partialT g q‖) := by ring
      _ ≤ K * (c * ‖g q‖ + ‖partialS g q‖ + ‖partialT g q‖) :=
          mul_le_mul hE hS (by positivity) hK.le
      _ = _ := by ring
  have hmono := eLpNorm_mono_ae_real (μ := volume.restrict negS) (p := 4)
    ((ae_restrict_iff' measurableSet_negS).2 (Eventually.of_forall hpt))
  refine hmono.trans ?_
  have m1 : AEStronglyMeasurable ((K * c) • (fun q => ‖g q‖)) (volume.restrict negS) :=
    (hgc.norm.const_smul _).aestronglyMeasurable
  have m2 : AEStronglyMeasurable (K • (fun q => ‖partialS g q‖)) (volume.restrict negS) :=
    (hsc.norm.const_smul _).aestronglyMeasurable
  have m3 : AEStronglyMeasurable (K • (fun q => ‖partialT g q‖)) (volume.restrict negS) :=
    (htc.norm.const_smul _).aestronglyMeasurable
  refine (eLpNorm_add_le (p := 4) (m1.add m2) m3 (by norm_num)).trans ?_
  refine (add_le_add (eLpNorm_add_le (p := 4) m1 m2 (by norm_num)) le_rfl).trans ?_
  rw [eLpNorm_smul_real _ (by positivity), eLpNorm_smul_real _ hK.le, eLpNorm_smul_real _ hK.le,
    eLpNorm_norm, eLpNorm_norm, eLpNorm_norm]
  have b1 := (eLpNorm_mono_measure g restrict_negS_le).trans (eLpNorm_wrep_le w)
  have b2 := (eLpNorm_mono_measure (partialS g) restrict_negS_le).trans
    (eLpNorm_partialS_le w hsm)
  have b3 := (eLpNorm_mono_measure (partialT g) restrict_negS_le).trans
    (eLpNorm_partialT_le w hsm)
  calc ENNReal.ofReal (K * c) * eLpNorm g 4 (volume.restrict negS) +
        ENNReal.ofReal K * eLpNorm (partialS g) 4 (volume.restrict negS) +
        ENNReal.ofReal K * eLpNorm (partialT g) 4 (volume.restrict negS)
      ≤ ENNReal.ofReal (K * c) * ENNReal.ofReal ‖w‖ + ENNReal.ofReal K * ENNReal.ofReal ‖w‖ +
          ENNReal.ofReal K * ENNReal.ofReal ‖w‖ := by gcongr
    _ = ENNReal.ofReal ((K * c + K + K) * ‖w‖) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hK.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-! ### The cylinder map of the linear part -/

/-- The cylinder map of `pLc · x`. -/
def hC (χT χN β : ℝ → ℝ) (x : QDom) (q : ℝ × ℝ) : ℂ × ℂ :=
  (vL (vOf χT (wrep x.1) q), β q.1 • x.2.1 + vL (vOf χN (wrep x.2.2) q))

lemma pLc_eq_pfG (x : QDom) :
    (fun z => pLc χT χN β z x) = pfG ((0 : ℂ), x.2.1) (hC χT χN β x) := by
  funext z
  by_cases hz : z = 0
  · subst hz; rw [pLc_zero, pfG_zero]
  · rw [pfG_ne hz]
    have h1 : pLc χT χN β z x = pG χT χN β x z - (z, 0) := by simp [pG]
    rw [h1, pG_eq_pfG, pfG_ne hz]
    have hE : cylInf (zc z).1 (zc z).2 = z := QR10.Ecyl_zc hz
    simp only [gC, hC, vOf, map_smul, hE]
    ext <;> simp

lemma contDiff_hC (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)
    {x : QDom} (h1 : ContDiff ℝ ∞ (wrep x.1)) (h2 : ContDiff ℝ ∞ (wrep x.2.2)) :
    ContDiff ℝ ∞ (hC χT χN β x) :=
  (vL.contDiff.comp (vOf_contDiff hχT h1)).prodMk
    (((hβ.comp contDiff_fst).smul contDiff_const).add (vL.contDiff.comp (vOf_contDiff hχN h2)))

lemma hC_per (x : QDom) (s t : ℝ) : hC χT χN β x (s, t + 1) = hC χT χN β x (s, t) := by
  simp [hC, vOf, (wrep_prop x.1).2.1, (wrep_prop x.2.2).2.1]

lemma norm_fderiv_vL_le {g : ℝ × ℝ → Vec 1} (hg : ContDiff ℝ ∞ g) (q : ℝ × ℝ) :
    ‖fderiv ℝ (fun q => vL (g q)) q‖ ≤ ‖vL‖ * ‖fderiv ℝ g q‖ := by
  have h := (vL.hasFDerivAt.comp q ((hg.differentiable (by simp)) q).hasFDerivAt).fderiv
  have e : (fun q => vL (g q)) = vL ∘ g := rfl
  rw [e, h]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- The `β c` part on `s < 0`. -/
lemma beta_part (hβ : IsLeftCutoff β) :
    ∃ B ≥ 0, ∀ (c : ℂ) (q : ℝ × ℝ), q.1 < 0 →
      Real.exp (-(π * q.1)) * ‖fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q‖ ≤
        B * ‖c‖ * Real.exp (π * q.1) := by
  obtain ⟨Mb, hMb⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 0)).exists_bound_of_continuousOn
    (hβ.1.continuous_deriv (by simp)).continuousOn
  refine ⟨max Mb 0 * Real.exp (2 * π), by positivity, fun c q hq => ?_⟩
  have hd : HasFDerivAt (fun q : ℝ × ℝ => β q.1 • c)
      ((deriv β q.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight c) q := by
    have := (((hβ.1.differentiable (by simp)) q.1).hasDerivAt.comp_hasFDerivAt q
      (hasFDerivAt_fst (𝕜 := ℝ) (p := q))).smul_const c
    exact this
  have hn : ‖fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q‖ ≤ |deriv β q.1| * ‖c‖ := by
    rw [hd.fderiv, ContinuousLinearMap.norm_smulRight_apply]
    refine mul_le_mul_of_nonneg_right ((norm_smul_le (deriv β q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ)).trans ?_) (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  have he0 := (Real.exp_pos (-(π * q.1))).le
  rcases lt_or_ge q.1 (-1) with h | h
  · rw [deriv_beta_eq_zero hβ h, abs_zero, zero_mul] at hn
    have : ‖fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q‖ = 0 := le_antisymm hn (norm_nonneg _)
    rw [this, mul_zero]; positivity
  · have hb : |deriv β q.1| ≤ max Mb 0 := by
      have := hMb q.1 ⟨h, hq.le⟩; rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    have hexp : Real.exp (-(π * q.1)) ≤ Real.exp (2 * π) * Real.exp (π * q.1) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    calc Real.exp (-(π * q.1)) * ‖fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q‖
        ≤ (Real.exp (2 * π) * Real.exp (π * q.1)) * (max Mb 0 * ‖c‖) :=
          mul_le_mul hexp (hn.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))
            (norm_nonneg _) (by positivity)
      _ = _ := by ring

lemma eLpNorm_exp_negS_lt_top :
    eLpNorm (fun q : ℝ × ℝ => Real.exp (π * q.1)) 4 (volume.restrict negS) < ⊤ := by
  rw [eLpNorm_four_eq]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt ?_)
  refine lt_of_le_of_lt ?_ integrableOn_exp_negS.lintegral_lt_top
  refine setLIntegral_mono' measurableSet_negS fun q hq => ENNReal.ofReal_le_ofReal ?_
  have hs : q.1 < 0 := hq.1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  exact Real.exp_le_exp.2 (by push_cast; nlinarith [Real.pi_pos])

/-- The weighted derivative of `e^χ g`. -/
def FT (χ : ℝ → ℝ) (g : ℝ × ℝ → Vec 1) (q : ℝ × ℝ) : ℝ :=
  Real.exp (-(π * q.1)) * ‖fderiv ℝ (vOf χ g) q‖

/-- `e^{πs}`. -/
def Ex (q : ℝ × ℝ) : ℝ := Real.exp (π * q.1)

lemma norm_prod_add_le (A B C : ℝ × ℝ →L[ℝ] ℂ) : ‖A.prod (B + C)‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
  rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  have := norm_add_le B C
  have := norm_nonneg A
  have := norm_nonneg B
  have := norm_nonneg C
  exact max_le (by linarith) (by linarith)

lemma fderiv_hC (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)
    {x : QDom} (h1 : ContDiff ℝ ∞ (wrep x.1)) (h2 : ContDiff ℝ ∞ (wrep x.2.2)) (q : ℝ × ℝ) :
    fderiv ℝ (hC χT χN β x) q =
      (fderiv ℝ (fun q => vL (vOf χT (wrep x.1) q)) q).prod
        (fderiv ℝ (fun q : ℝ × ℝ => β q.1 • x.2.1) q +
          fderiv ℝ (fun q => vL (vOf χN (wrep x.2.2) q)) q) := by
  have d1 : ∀ {f : ℝ × ℝ → ℂ}, ContDiff ℝ ∞ f → HasFDerivAt f (fderiv ℝ f q) q :=
    fun hf => (hf.differentiable (by simp) q).hasFDerivAt
  have hA : ContDiff ℝ ∞ (fun q => vL (vOf χT (wrep x.1) q)) :=
    vL.contDiff.comp (vOf_contDiff hχT h1)
  have hBc : ContDiff ℝ ∞ (fun q : ℝ × ℝ => β q.1 • x.2.1) :=
    (hβ.comp contDiff_fst).smul contDiff_const
  have hD : ContDiff ℝ ∞ (fun q => vL (vOf χN (wrep x.2.2) q)) :=
    vL.contDiff.comp (vOf_contDiff hχN h2)
  exact ((d1 hA).prodMk ((d1 hBc).add (d1 hD))).fderiv

lemma pt_hC (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)
    {x : QDom} (h1 : ContDiff ℝ ∞ (wrep x.1)) (h2 : ContDiff ℝ ∞ (wrep x.2.2)) {B : ℝ}
    (hBb : ∀ (c : ℂ) (q : ℝ × ℝ), q.1 < 0 →
      Real.exp (-(π * q.1)) * ‖fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q‖ ≤
        B * ‖c‖ * Real.exp (π * q.1)) (q : ℝ × ℝ) (hs : q.1 < 0) :
    Real.exp (-(π * q.1)) * ‖fderiv ℝ (hC χT χN β x) q‖ ≤
      ‖vL‖ * FT χT (wrep x.1) q + B * ‖x.2.1‖ * Ex q + ‖vL‖ * FT χN (wrep x.2.2) q := by
  have hn := (le_of_eq (congrArg norm (fderiv_hC hχT hχN hβ h1 h2 q))).trans
    (norm_prod_add_le _ _ _)
  have eA := norm_fderiv_vL_le (vOf_contDiff hχT h1) q
  have eD := norm_fderiv_vL_le (vOf_contDiff hχN h2) q
  have eB := hBb x.2.1 q hs
  have he := (Real.exp_pos (-(π * q.1))).le
  have k1 := mul_le_mul_of_nonneg_left hn he
  have k2 := mul_le_mul_of_nonneg_left eA he
  have k3 := mul_le_mul_of_nonneg_left eD he
  simp only [FT, Ex]
  nlinarith

lemma final_alg {v CT B E CN n1 n2 n3 n : ℝ} (hv : 0 ≤ v) (hCT : 0 ≤ CT) (hB : 0 ≤ B)
    (hE : 0 ≤ E) (hCN : 0 ≤ CN) (h1 : 0 ≤ n1) (h2 : 0 ≤ n2) (h3 : 0 ≤ n3)
    (e1 : n1 ≤ n) (e2 : n2 ≤ n) (e3 : n3 ≤ n) :
    ENNReal.ofReal v * ENNReal.ofReal (CT * n1) + ENNReal.ofReal (B * n2) * ENNReal.ofReal E +
        ENNReal.ofReal v * ENNReal.ofReal (CN * n3) ≤
      ENNReal.ofReal ((v * CT + B * E + v * CN) * n) := by
  rw [← ENNReal.ofReal_mul hv, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hv, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_le_mul_of_nonneg_left e1 (mul_nonneg hv hCT),
    mul_le_mul_of_nonneg_left e2 (mul_nonneg hB hE),
    mul_le_mul_of_nonneg_left e3 (mul_nonneg hv hCN)]

/-- `‖D_z (pLc · x)‖_{L⁴(ball 0 1)} ≤ C ‖x‖`. -/
theorem eLpNorm_pLc_ball {aT δ : ℝ} (hχT : IsSlopeWeight χT π aT) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ C ≥ 0, ∀ x : QDom, ContDiff ℝ ∞ (wrep x.1) → ContDiff ℝ ∞ (wrep x.2.2) →
      eLpNorm (fderiv ℝ (fun z => pLc χT χN β z x)) 4 (volume.restrict (ball (0 : ℂ) 1)) ≤
        ENNReal.ofReal (C * ‖x‖) := by
  obtain ⟨CT, hCT, hT⟩ := eLpNorm_vOf_negS hχT
  obtain ⟨CN, hCN, hN⟩ := eLpNorm_vOf_negS hχN
  obtain ⟨B, hB, hBb⟩ := beta_part hβ
  obtain ⟨Eπ, hEπ0, hEπ⟩ : ∃ E : ℝ, 0 ≤ E ∧ eLpNorm Ex 4 (volume.restrict negS) = ENNReal.ofReal E :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal eLpNorm_exp_negS_lt_top.ne).symm⟩
  refine ⟨‖vL‖ * CT + B * Eπ + ‖vL‖ * CN, by positivity, fun x h1 h2 => ?_⟩
  have hsm := contDiff_hC hχT.1 hχN.1 hβ.1 h1 h2
  rw [pLc_eq_pfG]
  have hcv := lintegral_ball_pfG_le (c₀ := ((0 : ℂ), x.2.1)) hsm (hC_per x)
  have step1 : eLpNorm (fderiv ℝ (pfG ((0 : ℂ), x.2.1) (hC χT χN β x))) 4
      (volume.restrict (ball (0 : ℂ) 1)) ≤ eLpNorm (fun q : ℝ × ℝ =>
        Real.exp (-(π * q.1)) * ‖fderiv ℝ (hC χT χN β x) q‖) 4 (volume.restrict negS) := by
    rw [eLpNorm_four_eq, eLpNorm_four_eq]
    refine ENNReal.rpow_le_rpow (le_trans hcv (le_of_eq (lintegral_congr fun q => ?_)))
      (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine step1.trans ?_
  have hpt : ∀ q ∈ negS, ‖Real.exp (-(π * q.1)) * ‖fderiv ℝ (hC χT χN β x) q‖‖ ≤
      (‖vL‖ • FT χT (wrep x.1) + (B * ‖x.2.1‖) • Ex + ‖vL‖ • FT χN (wrep x.2.2)) q := by
    intro q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pt_hC hχT.1 hχN.1 hβ.1 h1 h2 hBb q hq.1
  refine (eLpNorm_mono_ae_real ((ae_restrict_iff' measurableSet_negS).2
    (Eventually.of_forall hpt))).trans ?_
  have cT : Continuous (FT χT (wrep x.1)) := (Real.continuous_exp.comp ((continuous_const.mul
    continuous_fst).neg)).mul ((vOf_contDiff hχT.1 h1).continuous_fderiv (by simp)).norm
  have cN : Continuous (FT χN (wrep x.2.2)) := (Real.continuous_exp.comp ((continuous_const.mul
    continuous_fst).neg)).mul ((vOf_contDiff hχN.1 h2).continuous_fderiv (by simp)).norm
  have cE : Continuous Ex := Real.continuous_exp.comp (continuous_const.mul continuous_fst)
  have m1 : AEStronglyMeasurable (‖vL‖ • FT χT (wrep x.1)) (volume.restrict negS) :=
    (cT.const_smul _).aestronglyMeasurable
  have m2 : AEStronglyMeasurable ((B * ‖x.2.1‖) • Ex) (volume.restrict negS) :=
    (cE.const_smul _).aestronglyMeasurable
  have m3 : AEStronglyMeasurable (‖vL‖ • FT χN (wrep x.2.2)) (volume.restrict negS) :=
    (cN.const_smul _).aestronglyMeasurable
  refine (eLpNorm_add_le (p := 4) (m1.add m2) m3 (by norm_num)).trans ?_
  refine (add_le_add (eLpNorm_add_le (p := 4) m1 m2 (by norm_num)) le_rfl).trans ?_
  rw [eLpNorm_smul_real _ (norm_nonneg _), eLpNorm_smul_real _ (by positivity),
    eLpNorm_smul_real _ (norm_nonneg _), hEπ]
  have b1 : eLpNorm (FT χT (wrep x.1)) 4 (volume.restrict negS) ≤ ENNReal.ofReal (CT * ‖x.1‖) :=
    hT x.1 h1
  have b3 : eLpNorm (FT χN (wrep x.2.2)) 4 (volume.restrict negS) ≤
      ENNReal.ofReal (CN * ‖x.2.2‖) := hN x.2.2 h2
  have n1 : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
  have n2 : ‖x.2.1‖ ≤ ‖x‖ := (norm_fst_le _).trans (norm_snd_le x)
  have n3 : ‖x.2.2‖ ≤ ‖x‖ := (norm_snd_le _).trans (norm_snd_le x)
  calc ENNReal.ofReal ‖vL‖ * eLpNorm (FT χT (wrep x.1)) 4 (volume.restrict negS) +
        ENNReal.ofReal (B * ‖x.2.1‖) * ENNReal.ofReal Eπ +
        ENNReal.ofReal ‖vL‖ * eLpNorm (FT χN (wrep x.2.2)) 4 (volume.restrict negS)
      ≤ ENNReal.ofReal ‖vL‖ * ENNReal.ofReal (CT * ‖x.1‖) +
        ENNReal.ofReal (B * ‖x.2.1‖) * ENNReal.ofReal Eπ +
        ENNReal.ofReal ‖vL‖ * ENNReal.ofReal (CN * ‖x.2.2‖) := by gcongr
    _ ≤ ENNReal.ofReal ((‖vL‖ * CT + B * Eπ + ‖vL‖ * CN) * ‖x‖) :=
        final_alg (norm_nonneg _) hCT hB hEπ0 hCN (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
          n1 n2 n3

end QR14

end

end FiniteEnergyPlane

-- FILE: RSK_R25.lean
/-!
# Q-R, layer 25 (local, NOT published): the difference structure

For an almost complex structure `J` on `E` (on all of `E`), the difference structure on
`E × E × ℂ` is
`DJ J (u, v, p) (u̇, v̇, ṗ) = (J(u) u̇, J(u + Re p • v) v̇ + Hd(u, v, p) u̇, i ṗ)`,
with `Re p • Hd(u, v, p) = J(u + Re p • v) - J(u)` (Hadamard).
* `isAlmostComplexOn_DJ`: it is smooth and squares to `-1`.
* `isJHolomorphicOn_diff`: for `J`-holomorphic `u, u'` and real `h ≠ 0`,
  `ζ ↦ (u, h⁻¹ • (u' - u), h)` is `DJ J`-holomorphic.
* `isJHolomorphicOn_comp`, `dbarJ_of_comp`: composition with holomorphic charts.
-/

namespace FiniteEnergyPlane

open Set Filter Topology Metric JHolomorphic
open scoped ContDiff

noncomputable section

namespace QR25

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

/-- A holomorphic chart condition. -/
def IsHoloAt (φ : ℂ → ℂ) (ζ : ℂ) : Prop :=
  DifferentiableAt ℝ φ ζ ∧ fderiv ℝ φ ζ Complex.I = Complex.I * fderiv ℝ φ ζ 1

end QR25

end

end FiniteEnergyPlane

namespace FiniteEnergyPlane.QR25

open Set Filter Topology Metric JHolomorphic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma cr_alg (A : ℂ →L[ℝ] F) (T : F →L[ℝ] F) (hT : ∀ v, T (T v) = -v) (a : ℂ) :
    A a + T (A (Complex.I * a)) =
      a.re • (A 1 + T (A Complex.I)) - a.im • T (A 1 + T (A Complex.I)) := by
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by apply Complex.ext <;> simp
  have hIa : Complex.I * a = a.re • Complex.I - a.im • (1 : ℂ) := by
    apply Complex.ext <;> simp
  have hA : A a = a.re • A 1 + a.im • A Complex.I := by
    conv_lhs => rw [ha]
    rw [map_add, map_smul, map_smul]
  rw [hA, hIa]
  simp only [map_add, map_sub, map_smul, hT, smul_neg]
  module

theorem isJHolomorphicOn_comp {J : F → F →L[ℝ] F} {u : ℂ → F} {φ : ℂ → ℂ} {U V : Set ℂ}
    (hu : IsJHolomorphicOn J V u) (hφ : ∀ ζ ∈ U, IsHoloAt φ ζ) (hmaps : MapsTo φ U V)
    (hJ : ∀ ζ ∈ U, ∀ v, J (u (φ ζ)) (J (u (φ ζ)) v) = -v) :
    IsJHolomorphicOn J U (fun ζ => u (φ ζ)) := by
  intro ζ hζ
  obtain ⟨hφd, hφI⟩ := hφ ζ hζ
  obtain ⟨hud, hu0⟩ := hu (φ ζ) (hmaps hζ)
  have hc : HasFDerivAt (fun ζ => u (φ ζ)) ((fderiv ℝ u (φ ζ)).comp (fderiv ℝ φ ζ)) ζ :=
    hud.hasFDerivAt.comp ζ hφd.hasFDerivAt
  refine ⟨hc.differentiableAt, ?_⟩
  rw [dbarJ, hc.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hφI,
    cr_alg _ _ (hJ ζ hζ)]
  rw [dbarJ] at hu0
  rw [hu0]; simp

end FiniteEnergyPlane.QR25

-- FILE: RSK_RF.lean
/-!
# Q-R adapter (local, NOT published): R1/R2 facts from the published siblings

The later Q-R layers use the weighted `C⁰` bound of `pLc` (R1) and the regularity facts of small
zeros (R2 and its cylinder consequences). Both are derived here from the published statements
`exists_norm_qMember_le` and `contDiff_qMember_of_qMap_eq_zero`, so the R3/R4 bundles cite them
instead of re-proving them.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic
open scoped ContDiff Real ENNReal

noncomputable section

namespace QRF

open QL QR QR4 QR6 QR7 QR8 QR9 QR10 QR25 QRB QN19W QN18 QN

/-- R1 from the published `exists_norm_qMember_le`. -/
theorem c0_bound_stub (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ K > 0, ∀ (y : QDom) (z : ℂ),
      ‖(pLc χT χN β z y).1‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(pLc χT χN β z y).2‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π)) := by
  obtain ⟨K, hK, h⟩ := exists_norm_qMember_le δ δT hδ hδT χT χN β hχT hχN hβ
  refine ⟨K, hK, fun y z => ?_⟩
  have e : qMember χT χN β y z = (z, 0) + pLc χT χN β z y := by
    rw [← pG_eq_qMember]; rfl
  obtain ⟨h1, h2⟩ := h y z
  rw [e] at h1 h2
  refine ⟨?_, ?_⟩
  · simpa using h1
  · simpa using h2

lemma holo_of_hasDerivAt {f : ℂ → ℂ} {d ζ : ℂ} (h : HasDerivAt f d ζ) : IsHoloAt f ζ := by
  have hf : HasFDerivAt f ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ) ζ :=
    h.hasFDerivAt.restrictScalars ℝ
  refine ⟨hf.differentiableAt, ?_⟩
  rw [hf.fderiv]; simp [mul_comm]

/-- The cylinder and plane facts for small zeros, from the published
`contDiff_qMember_of_qMap_eq_zero`. -/
theorem small_zero_facts_stub (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 →
      ContDiff ℝ ∞ (gC χT χN β x) ∧ (∀ q, dbarC Jbar (gC χT χN β x) q = 0) ∧
      ContDiff ℝ ∞ (wrep x.1) ∧ ContDiff ℝ ∞ (wrep x.2.2) ∧
      ContDiff ℝ ∞ (pG χT χN β x) ∧ IsJHolomorphicOn Jbar univ (pG χT χN β x) := by
  obtain ⟨ε1, hε1, hreg⟩ :=
    contDiff_qMember_of_qMap_eq_zero ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨ε2, hε2, hmap⟩ := exists_mapsTo (χT := χT) hρ hδ hχN hβ
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun x hx h0 => ?_⟩
  have hx1 : x ∈ ball (0 : QDom) ε1 := ball_subset_ball (min_le_left _ _) hx
  have hx2 : ‖x‖ < ε2 := lt_of_lt_of_le (mem_ball_zero_iff.1 hx) (min_le_right _ _)
  obtain ⟨hs, hh⟩ := hreg x hx1 h0
  rw [← pG_eq_qMember] at hs hh
  have hO := hmap x hx2
  have hg : gC χT χN β x = fun q => pG χT χN β x (cylInf q.1 q.2) := by
    funext q; rw [pG_eq_pfG, pfG_cylInf (gC_per x)]
  have hsm : ContDiff ℝ ∞ (gC χT χN β x) := by rw [hg]; exact hs.comp contDiff_cylP
  have h1 := contDiff_wrep1 (χN := χN) (β := β) hχT.1 x hsm
  have h2 := contDiff_wrep2 (χT := χT) hχN.1 hβ.1 x hsm
  refine ⟨hsm, fun q => ?_, h1, h2, hs, hh⟩
  have hFe : (fun ζ => pG χT χN β x (Complex.exp (((2 * π : ℝ) : ℂ) * ζ))) =
      fun ζ => gC χT χN β x (cplx ζ) := by
    funext ζ; rw [hg]; simp only [cylInf_cplx]
  have hF : IsJHolomorphicOn Jbar univ
      (fun ζ => pG χT χN β x (Complex.exp (((2 * π : ℝ) : ℂ) * ζ))) := by
    refine isJHolomorphicOn_comp hh (fun ζ _ => holo_of_hasDerivAt
      (((hasDerivAt_id ζ).const_mul (((2 * π : ℝ) : ℂ))).cexp)) (mapsTo_univ _ _) (fun ζ _ v => ?_)
    have hpt : pG χT χN β x (Complex.exp (((2 * π : ℝ) : ℂ) * ζ)) = gC χT χN β x (cplx ζ) :=
      congrFun hFe ζ
    rw [hpt]
    have := congrArg (fun L : ℂ × ℂ →L[ℝ] ℂ × ℂ => L v)
      (hstd.2.1 (gC χT χN β x (cplx ζ)) ⟨mem_univ _, hO _⟩)
    simpa using this
  have := (hF (toC q) (mem_univ _)).2
  rw [hFe] at this
  simp only [dbarJ, fderiv_comp_cplx, cplx_toC] at this
  simpa [dbarC, cplx_apply] using this

end QRF

end

end FiniteEnergyPlane

-- FILE: RSK_R15.lean
/-!
# Q-R, layer 15 (local, NOT published): the uniform `C¹` bound near `z = 0`

For small zeros `x`, `‖D_z (pLc · x)‖ ≤ M ‖x‖` on `closedBall 0 (1/2)`: the rescaled graph
`ζ ↦ (ζ, ‖x‖⁻¹ pLc ζ x, ‖x‖)` is `JP`-holomorphic (layer 12, base `φ = id`), lies in a fixed
compact set (R1 `c0_bound`) and is bounded in `W^{1,4}(ball 0 1)` (layer 14), so layer 11's
`bound_const` (Thm 2.22(2a)) bounds its derivative.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic DbarRegularity
open scoped ContDiff Real ENNReal NNReal

noncomputable section

namespace QR15

open QL QR QR2 QR3 QR4 QR5 QR6 QR7 QR8 QR9 QR10 QR11 QR12 QR13 QR14 QN QN19W QN18

variable {χT χN β : ℝ → ℝ}

/-- The cylinder and plane facts for small zeros. -/
theorem small_zero_facts (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 →
      ContDiff ℝ ∞ (gC χT χN β x) ∧ (∀ q, dbarC Jbar (gC χT χN β x) q = 0) ∧
      ContDiff ℝ ∞ (wrep x.1) ∧ ContDiff ℝ ∞ (wrep x.2.2) ∧
      ContDiff ℝ ∞ (pG χT χN β x) ∧ IsJHolomorphicOn Jbar univ (pG χT χN β x) :=
  QRF.small_zero_facts_stub ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ

lemma norm_fderiv_smul_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F}
    {ζ : ℂ} (hf : DifferentiableAt ℝ f ζ) (c : ℝ) :
    ‖fderiv ℝ (fun z => c • f z) ζ‖ = |c| * ‖fderiv ℝ f ζ‖ := by
  rw [fderiv_fun_const_smul hf, norm_smul, Real.norm_eq_abs]

/-- The rescaled linear part. -/
def vR (χT χN β : ℝ → ℝ) (x : QDom) (z : ℂ) : ℂ × ℂ := ‖x‖⁻¹ • pLc χT χN β z x

lemma vR_eq (x : QDom) : vR χT χN β x =
    fun z => ‖x‖⁻¹ • (pG χT χN β x z - ((id z : ℂ), (0 : ℂ))) := by
  funext z; simp [vR, pG]

lemma pLc_bdd {δ δT K₀ : ℝ} (he : δ / (2 * π) < 0) (heT : δT / (2 * π) < 0)
    (hC0 : ∀ (y : QDom) (z : ℂ),
      ‖(pLc χT χN β z y).1‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(pLc χT χN β z y).2‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π))) (hK₀ : 0 ≤ K₀)
    (x : QDom) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖pLc χT χN β z x‖ ≤ 2 * K₀ * ‖x‖ ∧ ‖(pLc χT χN β z x).2‖ ≤ K₀ * ‖x‖ := by
  obtain ⟨h1, h2⟩ := hC0 x z
  have hz2 : 1 + ‖z‖ ≤ 2 := by linarith
  have a1 : (1 + ‖z‖) ^ (1 + δT / (2 * π)) ≤ 2 :=
    ((Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (by linarith :
      1 + δT / (2 * π) ≤ 1)).trans (le_of_eq (Real.rpow_one _))).trans hz2
  have a2 : (1 + ‖z‖) ^ (δ / (2 * π)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) he.le
  have hKx : 0 ≤ K₀ * ‖x‖ := by positivity
  have b1 : ‖(pLc χT χN β z x).1‖ ≤ 2 * K₀ * ‖x‖ := by
    calc _ ≤ K₀ * ‖x‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) := h1
      _ ≤ K₀ * ‖x‖ * 2 := mul_le_mul_of_nonneg_left a1 hKx
      _ = 2 * K₀ * ‖x‖ := by ring
  have b2 : ‖(pLc χT χN β z x).2‖ ≤ K₀ * ‖x‖ := by
    calc _ ≤ K₀ * ‖x‖ * (1 + ‖z‖) ^ (δ / (2 * π)) := h2
      _ ≤ K₀ * ‖x‖ * 1 := mul_le_mul_of_nonneg_left a2 hKx
      _ = K₀ * ‖x‖ := mul_one _
  exact ⟨norm_prod_le_iff.2 ⟨b1, b2.trans (by linarith)⟩, b2⟩

set_option maxHeartbeats 1600000 in
/-- The near-zero part. -/
theorem near_zero (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ M ≥ 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 →
      ∀ z ∈ closedBall (0 : ℂ) (1 / 2),
        ‖fderiv ℝ (fun z => pLc χT χN β z x) z‖ ≤ M * ‖x‖ := by
  have hπ : 0 < 2 * π := by positivity
  have he : δ / (2 * π) < 0 := div_neg_of_neg_of_pos hδ hπ
  have heT : δT / (2 * π) < 0 := div_neg_of_neg_of_pos hδT.2 hπ
  obtain ⟨εf, hεf, hfacts⟩ :=
    small_zero_facts ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨K₀, hK₀, hC0⟩ := QRF.c0_bound_stub δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨CL, hCL, hL⟩ := eLpNorm_pLc_ball hχT hχN hβ
  have hJ := isAlmostComplexOn_JP (φ := id) (dφ := fun _ => (1 : ℂ)) hρ hstd.1 hstd.2.1
    contDiff_id contDiff_const
  set K₀' : Set (ℂ × (ℂ × ℂ) × ℂ) :=
    closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ × ℂ) (2 * K₀) ×ˢ closedBall (0 : ℂ) 1 with hK₀'
  have hK₀c : IsCompact K₀' :=
    (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  set Csob : ℝ≥0∞ := eLpNorm (fun _ : ℂ => (1 + 2 * K₀ + 1 : ℝ)) (ENNReal.ofReal 4)
      (volume.restrict (ball (0 : ℂ) 1)) +
    (eLpNorm (fun _ : ℂ => (1 : ℝ)) (ENNReal.ofReal 4) (volume.restrict (ball (0 : ℂ) 1)) +
      ENNReal.ofReal CL) with hCsob
  have hfin : ∀ r : ℝ, eLpNorm (fun _ : ℂ => r) (ENNReal.ofReal 4)
      (volume.restrict (ball (0 : ℂ) 1)) ≠ ⊤ := by
    intro r
    refine (eLpNorm_const_lt_top_iff (by norm_num) (by simp)).2 (Or.inr ?_) |>.ne
    rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top
  have hCsob_ne : Csob ≠ ⊤ := by
    simp only [hCsob]
    exact ENNReal.add_ne_top.2 ⟨hfin _, ENNReal.add_ne_top.2 ⟨hfin _, ENNReal.ofReal_ne_top⟩⟩
  obtain ⟨M, hM⟩ := bound_const (JP ρ Jbar id fun _ => (1 : ℂ)) univ K₀' hJ hK₀c (subset_univ _)
    (closedBall (0 : ℂ) (1 / 2)) (closedBall_subset_ball (by norm_num)) (isCompact_closedBall _ _)
    Csob.toNNReal
  refine ⟨min (min εf 1) (ρ / (4 * (K₀ + 1))), lt_min (lt_min hεf one_pos) (by positivity),
    max M 0, le_max_right _ _, fun x hx h0 z hz => ?_⟩
  have hxn : ‖x‖ < min (min εf 1) (ρ / (4 * (K₀ + 1))) := mem_ball_zero_iff.1 hx
  have hxf : x ∈ ball (0 : QDom) εf :=
    mem_ball_zero_iff.2 (lt_of_lt_of_le hxn ((min_le_left _ _).trans (min_le_left _ _)))
  have hx1 : ‖x‖ < 1 := lt_of_lt_of_le hxn ((min_le_left _ _).trans (min_le_right _ _))
  have hxρ : ‖x‖ < ρ / (4 * (K₀ + 1)) := lt_of_lt_of_le hxn (min_le_right _ _)
  obtain ⟨-, -, h1, h2, hpsm, hphol⟩ := hfacts x hxf h0
  rcases eq_or_ne x 0 with rfl | hx0
  · have : (fun z => pLc χT χN β z (0 : QDom)) = fun _ => 0 := by funext z; simp
    rw [this, fderiv_const_apply, norm_zero, norm_zero, mul_zero]
  set l : ℝ := ‖x‖ with hl
  have hl0 : l ≠ 0 := norm_ne_zero_iff.2 hx0
  have hlpos : 0 < l := norm_pos_iff.2 hx0
  -- smoothness of the rescaled map
  have hPsm : ContDiff ℝ ∞ (fun z => pLc χT χN β z x) := by
    have : (fun z => pLc χT χN β z x) = fun z => pG χT χN β x z - (z, 0) := by
      funext z; simp [pG]
    rw [this]; exact hpsm.sub (contDiff_id.prodMk contDiff_const)
  have hvsm : ContDiff ℝ ∞ (vR χT χN β x) := hPsm.const_smul _
  have hvd : ∀ ζ, DifferentiableAt ℝ (vR χT χN β x) ζ := fun ζ => hvsm.differentiable (by simp) ζ
  have hgsm : ContDiffOn ℝ ∞ (graph 0 (vR χT χN β x) (l : ℂ)) (ball 0 1) :=
    ((contDiff_const.add contDiff_id).prodMk (hvsm.prodMk contDiff_const)).contDiffOn
  -- holomorphicity
  have hhol : IsJHolomorphicOn (JP ρ Jbar id fun _ => (1 : ℂ)) (ball 0 1)
      (graph 0 (vR χT χN β x) (l : ℂ)) := by
    refine isJHolomorphicOn_graph _ _ 0 _ (fun ζ _ => hvd ζ) fun ζ hζ => ?_
    have hζ1 : ‖ζ‖ ≤ 1 := (mem_ball_zero_iff.1 hζ).le
    have hsmall : ‖(pG χT χN β x ζ).2‖ < ρ / 4 := by
      have e : (pG χT χN β x ζ).2 = (pLc χT χN β ζ x).2 := by simp [pG]
      rw [e]
      refine lt_of_le_of_lt (pLc_bdd he heT hC0 hK₀.le x hζ1).2 ?_
      have h4 : ‖x‖ * (4 * (K₀ + 1)) < ρ := by
        rwa [lt_div_iff₀ (by positivity)] at hxρ
      nlinarith [norm_nonneg x]
    have key := rescaled_eq (φ := id) (dφ := fun _ => (1 : ℂ)) hρ hstd.1 hstd.2.2.1 hl0
      ((hpsm.differentiable (by simp)) ζ) (hasDerivAt_id ζ) (hphol ζ (mem_univ _)).2 hsmall
    have hg : graph 0 (vR χT χN β x) (l : ℂ) ζ = (ζ, vR χT χN β x ζ, (l : ℂ)) := by
      simp [graph]
    rw [hg, vR_eq x]
    exact key
  -- values in the compact set
  have hmaps : MapsTo (graph 0 (vR χT χN β x) (l : ℂ)) (ball 0 1) K₀' := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ ≤ 1 := (mem_ball_zero_iff.1 hζ).le
    refine ⟨?_, ?_, ?_⟩
    · simpa [graph] using hζ1
    · show vR χT χN β x ζ ∈ closedBall 0 (2 * K₀)
      rw [mem_closedBall_zero_iff, vR, norm_smul, norm_inv, norm_norm]
      have := (pLc_bdd he heT hC0 hK₀.le x hζ1).1
      rw [inv_mul_le_iff₀ hlpos]
      linarith
    · show ((l : ℂ)) ∈ closedBall 0 1
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlpos]
      exact hx1.le
  -- the Sobolev bound
  have hsob : sobolevNorm 1 (ENNReal.ofReal 4) (ball 0 1) (graph 0 (vR χT χN β x) (l : ℂ)) ≤
      (Csob.toNNReal : ℝ≥0∞) := by
    rw [ENNReal.coe_toNNReal hCsob_ne]
    have hA : ∀ ζ ∈ ball (0 : ℂ) 1, ‖graph 0 (vR χT χN β x) (l : ℂ) ζ‖ ≤ 1 + 2 * K₀ + 1 := by
      intro ζ hζ
      have hm := hmaps hζ
      have a1 : ‖(0 : ℂ) + ζ‖ ≤ 1 := by simpa using (mem_ball_zero_iff.1 hζ).le
      have a2 : ‖vR χT χN β x ζ‖ ≤ 2 * K₀ := mem_closedBall_zero_iff.1 hm.2.1
      have a3 : ‖(l : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.1 hm.2.2
      exact (norm_graph_le 0 _ _ ζ).trans (by linarith)
    refine (sobolevNorm_one_le hA measurableSet_ball).trans (add_le_add le_rfl ?_)
    refine (eLpNorm_fderiv_graph_le (by norm_num) isOpen_ball 0 (l : ℂ)
      (hvsm.of_le (by simp)).contDiffOn).trans (add_le_add le_rfl ?_)
    have hpt : ∀ᵐ ζ ∂(volume.restrict (ball (0 : ℂ) 1)),
        ‖fderiv ℝ (vR χT χN β x) ζ‖ ≤ l⁻¹ * ‖fderiv ℝ (fun z => pLc χT χN β z x) ζ‖ :=
      Eventually.of_forall fun ζ => le_of_eq (by
        rw [show vR χT χN β x = fun z => l⁻¹ • pLc χT χN β z x from rfl,
          norm_fderiv_smul_eq ((hPsm.differentiable (by simp)) ζ), abs_of_pos (inv_pos.2 hlpos)])
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt _).trans ?_
    have h4 : ENNReal.ofReal 4 = 4 := by norm_num
    rw [h4]
    refine (mul_le_mul_of_nonneg_left (hL x h1 h2) (by simp)).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (inv_pos.2 hlpos).le]
    congr 1
    field_simp
    rw [← hl]; ring
  -- conclusion
  have hb := hM _ hgsm hhol hmaps hsob z hz
  have hv := (norm_fderiv_le_graph 0 (l : ℂ) (hvd z)).trans hb
  have hfz : ‖fderiv ℝ (fun z => pLc χT χN β z x) z‖ = l * ‖fderiv ℝ (vR χT χN β x) z‖ := by
    have e : (fun z => pLc χT χN β z x) = fun z => l • vR χT χN β x z := by
      funext z; simp only [vR, smul_smul, ← hl, mul_inv_cancel₀ hl0, one_smul]
    rw [e, norm_fderiv_smul_eq (hvd z), abs_of_pos hlpos]
  rw [hfz, mul_comm]
  exact mul_le_mul_of_nonneg_right (hv.trans (le_max_left _ _)) hlpos.le

end QR15

end

end FiniteEnergyPlane

-- FILE: RSK_R23N.lean
/-!
# Q-R, layer 23N (local, NOT published): the near-origin part of R4 (`‖z‖ ≤ 1/2`)
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic
open scoped ContDiff ENNReal NNReal Real

noncomputable section

namespace QR23N

open QL QR QR8 QR13 QR14 QR15 QN19W QN18

variable {χT χN β : ℝ → ℝ} {δ δT : ℝ}

lemma norm_fderiv_fst_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℂ → F × G} {ξ : ℂ}
    (hf : DifferentiableAt ℝ f ξ) :
    ‖fderiv ℝ (fun z => (f z).1) ξ‖ ≤ ‖fderiv ℝ f ξ‖ := by
  rw [hf.hasFDerivAt.fst.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  exact (norm_fst_le (fderiv ℝ f ξ v)).trans ((fderiv ℝ f ξ).le_opNorm v)

lemma norm_fderiv_snd_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℂ → F × G} {ξ : ℂ}
    (hf : DifferentiableAt ℝ f ξ) :
    ‖fderiv ℝ (fun z => (f z).2) ξ‖ ≤ ‖fderiv ℝ f ξ‖ := by
  rw [hf.hasFDerivAt.snd.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  exact (norm_snd_le (fderiv ℝ f ξ v)).trans ((fderiv ℝ f ξ).le_opNorm v)

set_option maxHeartbeats 1600000 in
theorem near_bound_proof (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ K ≥ 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      ‖fderiv ℝ (fun z => (pG χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K * ‖x‖ ∧
      (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (pG χT χN β x z).2) z‖ ≤ K * ‖x‖ := by
  have hπ : 0 < 2 * π := by positivity
  have ha1 : 1 ≤ 1 - δ / (2 * π) := by
    have : δ / (2 * π) < 0 := div_neg_of_neg_of_pos hδ hπ
    linarith
  obtain ⟨εf, hεf, hfacts⟩ :=
    small_zero_facts ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨εn, hεn, Mn, hMn, hnear⟩ :=
    near_zero ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  set a : ℝ := 1 - δ / (2 * π) with ha
  set K3 : ℝ := (3 / 2) ^ a * Mn with hK3
  have hMnK3 : Mn ≤ K3 := le_mul_of_one_le_left hMn (Real.one_le_rpow (by norm_num) (by linarith))
  have hK30 : 0 ≤ K3 := by positivity
  refine ⟨min εf εn, lt_min hεf hεn, K3, hK30, fun x hx hq z hz => ?_⟩
  have hxn : ‖x‖ < min εf εn := mem_ball_zero_iff.1 hx
  have hxf : x ∈ ball (0 : QDom) εf := mem_ball_zero_iff.2 (hxn.trans_le (min_le_left _ _))
  have hxnn : x ∈ ball (0 : QDom) εn := mem_ball_zero_iff.2 (hxn.trans_le (min_le_right _ _))
  obtain ⟨-, -, hw1, hw2, hpGs, -⟩ := hfacts x hxf hq
  have hpd : ∀ w, DifferentiableAt ℝ (pG χT χN β x) w := fun w => (hpGs.differentiable (by simp)) w
  have hf1 : DifferentiableAt ℝ (fun z => (pG χT χN β x z).1) z := (hpd z).fst
  have eL : (fun z => pLc χT χN β z x) = fun z => pG χT χN β x z - (z, 0) := by
    funext w; simp [pG]
  have hLd : DifferentiableAt ℝ (fun z => pLc χT χN β z x) z := by
    rw [eL]; exact (hpd z).sub (differentiableAt_id.prodMk (differentiableAt_const _))
  have e1 : fderiv ℝ (fun z => (pG χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ =
      fderiv ℝ (fun z => (pLc χT χN β z x).1) z := by
    have hd : HasFDerivAt (fun z => (pLc χT χN β z x).1)
        (fderiv ℝ (fun z => (pG χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ) z :=
      (hf1.hasFDerivAt.sub (hasFDerivAt_id z)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => by simp [pG])
    exact hd.fderiv.symm
  have e2 : (fun z => (pG χT χN β x z).2) = fun z => (pLc χT χN β z x).2 := by
    funext w; simp [pG]
  rw [e1, e2]
  have hN := hnear x hxnn hq z (mem_closedBall_zero_iff.2 hz)
  refine ⟨(norm_fderiv_fst_le hLd).trans (hN.trans ?_), ?_⟩
  · exact mul_le_mul_of_nonneg_right hMnK3 (norm_nonneg _)
  · have hw : (1 + ‖z‖) ^ a ≤ (3 / 2) ^ a :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    calc (1 + ‖z‖) ^ a * ‖fderiv ℝ (fun z => (pLc χT χN β z x).2) z‖
        ≤ (3 / 2) ^ a * (Mn * ‖x‖) :=
          mul_le_mul hw ((norm_fderiv_snd_le hLd).trans hN) (norm_nonneg _) (by positivity)
      _ = K3 * ‖x‖ := by rw [hK3]; ring

end QR23N

end

end FiniteEnergyPlane

-- FILE: RSK_RP4N.lean
namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QRB

theorem exists_norm_fderiv_qMember_le_of_norm_le_half_proof (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ K ≥ 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      ‖fderiv ℝ (fun z => (qMember χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K * ‖x‖ ∧
      (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (qMember χT χN β x z).2) z‖ ≤
        K * ‖x‖ := by
  rw [← pG_eq_qMember]
  exact QR23N.near_bound_proof ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ

end QRB

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ K ≥ 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      ‖fderiv ℝ (fun z => (qMember χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K * ‖x‖ ∧
      (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (qMember χT χN β x z).2) z‖ ≤
        K * ‖x‖ :=
  QRB.exists_norm_fderiv_qMember_le_of_norm_le_half_proof ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
