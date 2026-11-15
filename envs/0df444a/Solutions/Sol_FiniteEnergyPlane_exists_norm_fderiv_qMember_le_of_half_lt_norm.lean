-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_fderiv_qMember_le_of_half_lt_norm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T11:55:40.912201+00:00
-- url     : https://prove2.me/submissions/6aaf916d-1f7f-44ee-a5e4-ed9fb8106e1c

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
import Theorems.Thm_FiniteEnergyPlane_hadamard_integral_fderiv
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
import Theorems.Thm_FiniteEnergyPlane_contDiff_qMember_of_qMap_eq_zero
import Theorems.Thm_FiniteEnergyPlane_exists_norm_qMember_le
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_comp
import Definitions.Def_FiniteEnergyPlane_TubeFamily

open Metric Set Filter Topology BoundedContinuousFunction
open Metric Set Filter Topology MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open MeasureTheory Metric Set Filter Topology BoundedContinuousFunction
open scoped ENNReal ContDiff
open Metric Set Filter Topology
open scoped ContDiff

-- FILE: _imports_RSK_RP4F.lean


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

-- FILE: NSK_N10.lean
/-!
# Q-N, layer 10 (local, NOT published): bounded-derivative toolkit, part 1

* `bddDerivOn_of_outside`: smooth, derivatives bounded outside a compact set ⇒ bounded everywhere.
* `BddDerivOn.comp_contDiffOn`: composition with an outer map smooth only on an open set.
* `BddDeriv1On.comp_clm`, `BddDeriv1On.clm_comp`, `BddDerivOn.clm_comp`.
* `rtr ρ` has bounded derivatives; the smooth floor `sfl a` (`≥ a`, `= id` on `[a + 1, ∞)`).
-/

namespace FiniteEnergyPlane

open Metric Set Filter Topology
open scoped ContDiff

noncomputable section

namespace QN10

open QN9

variable {Y Z W : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-! ### The retraction and the smooth floor -/

end QN10

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

/-- `cylJ` is `jStd` along `w = 0`. -/
lemma cylJ_zero (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (s t : ℝ) : cylJ Jbar s t 0 = jStd := by
  have hz : (((2 * π : ℝ) : ℂ) * cylInf s t) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) (cylInf_ne_zero s t)
  ext x <;> simp [cylJ, cylScale, cylScaleInv, jStd, h0] <;> field_simp [cylInf_ne_zero s t]

end

end FiniteEnergyPlane

-- FILE: NSK_N11.lean
/-!
# Q-N, layer 11 (local, NOT published): `K̃` and its Hadamard quotient have bounded derivatives

* `cylJ_bdd_right`: for `a > s₀`, every derivative of `(s, t, w) ↦ cylJ Jbar s t w` is bounded on
  `[a, ∞) × ℝ × closedBall 0 (ρ/2)` (N1 at large `s`, compactness + `t`-periodicity in between).
* `Kt a`: `K̃(p) = cylJ(sfl a s, t, rtr (ρ/2) w) − jStd` on `(ℝ × ℝ) × ℂ`; `bddDerivOn_Kt`.
* `Ht a`: its Hadamard quotient in `w`; `bddDerivOn_Ht`, `Kt_eq_Ht`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN11

open QN9 QN10

variable (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
  (Sinf : ℝ → Mat 1)

/-- `cylJ` as a function on `ℝ × ℝ × ℂ`. -/
def gJ (q : ℝ × ℝ × ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ := cylJ Jbar q.1 q.2.1 q.2.2

end QN11

end

end FiniteEnergyPlane

-- FILE: NSK_N12.lean
/-!
# Q-N, layer 12 (local, NOT published): `K̃` and its Hadamard quotient `Ĥ`

* `Kt a`: `K̃(p) = cylJ(sfl a s, t, rtr (ρ/2) w) − jStd` on `(ℝ × ℝ) × ℂ`; `bddDerivOn_Kt`.
* `Ht a`: its Hadamard quotient in `w`; `Kt_eq_Ht` (`K̃ = Ĥ(·)(w)`), `bddDerivOn_Ht`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN11

open QN9 QN10

variable (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
  (Sinf : ℝ → Mat 1)

/-! ### `K̃` -/

/-! ### The Hadamard quotient `Ĥ`

Written with the full derivative of `K̃` (a 2-level CLM type); the restriction to the `w`-slot is
`(0, ·)`. (Three-level nested CLM types such as `(P →L G) →L (ℂ →L G)` do not get a `Norm`
instance in this Mathlib.) -/

end QN11

end

end FiniteEnergyPlane

-- FILE: NSK_N13.lean
/-!
# Q-N, layer 13 (local, NOT published): vector Hadamard quotients, global smoothness of `cylJ`

* `hq k`: for `k : (ℝ × ℝ) × ℂ → W`, `hq k p = ∫₀¹ Dk(x, θ w) dθ`; `eq_hq` (`k p = hq k p (0, w)` when
  `k (x, 0) = 0`), `bddDerivOn_hq`. Values of `hq k` have CLM depth 1 when `W` is a plain space.
* `gJ_contDiffOn`: `cylJ` is `C^∞` on `ℝ × ℝ × ball 0 ρ` (no `s₀`); `cylJ_bdd_right'`, `bddDerivOn_Kt'`
  for every `a`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN13

open QN9 QN10 QN11

section Hadamard

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  (k : (ℝ × ℝ) × ℂ → W)

/-- `hq k (x, w) = ∫₀¹ Dk(x, θ w) dθ`. -/
def hq (p : (ℝ × ℝ) × ℂ) : ((ℝ × ℝ) × ℂ) →L[ℝ] W :=
  ∫ θ in (0 : ℝ)..1, fderiv ℝ (k) (p.1, θ • p.2)

end Hadamard

/-! ### `cylJ` is smooth for every `s` -/

section Cyl

variable (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
  (Sinf : ℝ → Mat 1)

lemma contDiff_cylInf : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1) := by
  unfold cylInf ccwLoop
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => ((Real.exp (2 * π * q.1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst))
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => Complex.exp (((2 * π * q.2.1 : ℝ) : ℂ) * Complex.I)) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).comp ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (contDiff_fst.comp contDiff_snd))).mul contDiff_const)
  exact h1.mul h2

lemma gJ_apply (q : ℝ × ℝ × ℂ) (y : ℂ × ℂ) :
    gJ Jbar q y = ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1)⁻¹ *
        (Jbar (cylInf q.1 q.2.1, q.2.2) ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) * y.1, y.2)).1,
      (Jbar (cylInf q.1 q.2.1, q.2.2) ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) * y.1, y.2)).2) := by
  simp only [gJ, cylJ, cylScale, cylScaleInv, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]

/-- `cylJ` is `C^∞` on `ℝ × ℝ × ball 0 ρ`. -/
theorem gJ_contDiffOn (hJ : ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ)) :
    ContDiffOn ℝ ∞ (gJ Jbar) (univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) := by
  refine contDiffOn_clm_apply.2 fun y => ?_
  have hc : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => ((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) :=
    contDiff_const.mul contDiff_cylInf
  have hc0 : ∀ q : ℝ × ℝ × ℂ, ((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1 ≠ 0 := fun q =>
    mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) (cylInf_ne_zero _ _)
  have hJq : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ × ℂ => Jbar (cylInf q.1 q.2.1, q.2.2))
      (univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) :=
    hJ.comp (contDiff_cylInf.prodMk (contDiff_snd.comp contDiff_snd)).contDiffOn
      fun q hq => ⟨mem_univ _, hq.2.2⟩
  have hv : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ × ℂ =>
      Jbar (cylInf q.1 q.2.1, q.2.2) ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) * y.1, y.2))
      (univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) :=
    hJq.clm_apply ((hc.mul contDiff_const).prodMk contDiff_const).contDiffOn
  have e : (fun q => gJ Jbar q y) = fun q : ℝ × ℝ × ℂ =>
      ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1)⁻¹ *
        (Jbar (cylInf q.1 q.2.1, q.2.2) ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) * y.1, y.2)).1,
      (Jbar (cylInf q.1 q.2.1, q.2.2) ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) * y.1, y.2)).2) :=
    funext fun q => gJ_apply Jbar q y
  rw [e]
  exact ((hc.inv hc0).contDiffOn.mul (contDiff_fst.comp_contDiffOn hv)).prodMk
    (contDiff_snd.comp_contDiffOn hv)

end Cyl

end QN13

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

-- FILE: NSK_N14.lean
/-!
# Q-N, layer 14 (local, NOT published): the `+∞` integrands

* `bddDerivOn_of_isCompact`, **`bddDerivOn_frame`**: `z ↦ Φ₀(τ z, F(σ z + ℓ(τ z), m(τ z)))` has
  bounded derivatives on `τ⁻¹' C` (`C` compact, `F` with bounded derivatives on `univ`).
* `kbar`, `Fh`: the four columns of `K̃` and their Hadamard quotients (vector valued);
  `Kt_apply_eq`: `K̃(y) h = w.re • lin h F₁ + w.im • lin h F_I` with `w = y.2`.
* `phiRZ`, `phiRP`: the jointly smooth `+∞` integrands of the zero-order and the product term.

All CLM types have depth `≤ 2` (`Norm` is not synthesized at depth 3 in this Mathlib).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN14

open QN9 QN10 QN11 QN13

/-! ### Generic bounded-derivative frame -/

/-! ### Columns of `K̃` and their Hadamard quotients -/

abbrev V := ℂ × ℂ
variable (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
  (Sinf : ℝ → Mat 1)

/-! ### The jointly smooth integrands -/

end QN14

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

lemma deriv_bdd {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) :
    ∃ M, 0 ≤ M ∧ ∀ s, |deriv χ s| ≤ M := by
  refine bdd_mid _ (hχ.1.continuous_deriv (by simp)) (max |a| |b|) fun s hs => ?_
  rcases hs with hs | hs
  · rw [hχ.2.1 s hs]; exact le_max_left _ _
  · rw [hχ.2.2 s hs]; exact le_max_right _ _

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

/-- The exponential chart. -/
def Eexp (ξ : ℂ) : ℂ := Complex.exp (((2 * π : ℝ) : ℂ) * ξ)

lemma Ecyl_cplx (ξ : ℂ) : Ecyl (cplx ξ) = Eexp ξ := by
  rw [Ecyl_eq, toC_cplx, Eexp]

lemma cylInf_add_one (s t : ℝ) : cylInf s (t + 1) = cylInf s t := by
  rw [cylInf_eq_exp, cylInf_eq_exp]
  have : ((2 * π : ℝ) : ℂ) * ((s : ℂ) + ((t + 1 : ℝ) : ℂ) * Complex.I) =
      ((2 * π : ℝ) : ℂ) * ((s : ℂ) + (t : ℂ) * Complex.I) + 2 * π * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

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

variable {ρ Jbar}

section Props

variable (hρ : 0 < ρ) (hJs : ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ))
  (hsq : ∀ p ∈ univ ×ˢ ball (0 : ℂ) ρ, (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
  (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)

/-! ### The rescaled equation -/

lemma jStd_apply (a b : ℂ) : jStd (a, b) = (Complex.I * a, Complex.I * b) := by
  simp [jStd]

end Props

end QR12

end

end FiniteEnergyPlane

-- FILE: RSK_R16.lean
/-!
# Q-R, layer 16 (local, NOT published): the two-scale rescaled graph structure over a base `K`

`K : ℂ × ℂ → (ℂ × ℂ →L ℂ × ℂ)` is a global smooth almost complex structure with `K(a, 0) = jStd`
(base coordinate `a`, fibre coordinate `w`). For a `K`-holomorphic `u` and scales `μ` (base
direction) and `μ r` (fibre direction), the rescaled perturbation
`vT μ r u ξ = (μ⁻¹ (u₁ ξ - ξ), (μ r)⁻¹ u₂ ξ)` solves `∂ₛV + JfT ∂ₜV + mT = 0`, where `JfT`, `mT`
are smooth in `(μ, r)` down to `μ r = 0` (through the `w`-divided difference `Hg` of `K`).
The parameters ride in the last coordinate `p = μ + i r` of the target `TE = ℂ × (ℂ × ℂ) × ℂ`,
so the graph `ζ ↦ (c + ζ, vT (c + ζ), μ + i r)` is `TS K`-holomorphic, and `TS K` is a global
smooth almost complex structure. `TS K e = Φ (e, gT K e)` with a fixed smooth `Φ`, which is
how `C^∞_loc` convergence of the base passes to `TS`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology JHolomorphic
open scoped ContDiff ENNReal NNReal

noncomputable section

namespace QR16

open QR11 QR12

/-- Endomorphisms of `ℂ × ℂ`. -/
abbrev CL := ℂ × ℂ →L[ℝ] ℂ × ℂ

/-- The target `(base, fibre, parameters)`. -/
abbrev TE := ℂ × (ℂ × ℂ) × ℂ

/-- The `w`-divided difference of `K`. -/
def Hg (K : ℂ × ℂ → CL) (q : ℂ × ℂ) : ℂ →L[ℝ] CL :=
  ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun w => K (q.1, w)) (θ • q.2)

/-- `Hg` applied to a third coordinate. -/
def Hc (K : ℂ × ℂ → CL) (y : ℂ × ℂ × ℂ) : CL := Hg K (y.1, y.2.1) y.2.2

/-- Real diagonal scaling. -/
def dg (α β : ℝ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  ContinuousLinearMap.prodMap (α • ContinuousLinearMap.id ℝ ℂ) (β • ContinuousLinearMap.id ℝ ℂ)

@[simp] lemma dg_apply (α β : ℝ) (v : ℂ × ℂ) : dg α β v = (α • v.1, β • v.2) := rfl

lemma dg_dg {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (v : ℂ × ℂ) : dg α β (dg α⁻¹ β⁻¹ v) = v := by
  simp only [dg_apply, smul_smul, mul_inv_cancel₀ hα, mul_inv_cancel₀ hβ, one_smul, Prod.mk.eta]

lemma dg_dg' {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (v : ℂ × ℂ) : dg α⁻¹ β⁻¹ (dg α β v) = v := by
  simp only [dg_apply, smul_smul, inv_mul_cancel₀ hα, inv_mul_cancel₀ hβ, one_smul, Prod.mk.eta]

lemma jStd_dg (α β : ℝ) (v : ℂ × ℂ) : jStd (dg α β v) = dg α β (jStd v) := by
  rw [dg_apply, jStd_apply, dg_apply, jStd_apply]
  simp only [Complex.real_smul]
  ext <;> simp <;> ring

lemma dg_smul {μ r : ℝ} (hμ : μ ≠ 0) (hr : r ≠ 0) (Y : ℂ × ℂ) :
    dg μ⁻¹ (μ * r)⁻¹ ((μ * r) • Y) = dg r 1 Y := by
  have hμr : μ * r ≠ 0 := mul_ne_zero hμ hr
  have e1 : μ⁻¹ * (μ * r) = r := by field_simp
  simp only [dg_apply, Prod.smul_fst, Prod.smul_snd, smul_smul, e1, inv_mul_cancel₀ hμr]

lemma jStd_I0 : jStd (Complex.I, 0) + ((1 : ℂ), (0 : ℂ)) = 0 := by
  simp [jStd_apply]

/-- The inner point: actual point and fibre coordinate. -/
def iT (e : TE) : ℂ × ℂ × ℂ :=
  (e.1 + e.2.2.re • e.2.1.1, (e.2.2.re * e.2.2.im) • e.2.1.2, e.2.1.2)

/-- The data of `TS K` at `e`. -/
def gT (K : ℂ × ℂ → CL) (e : TE) : CL := Hc K (iT e)

/-- The fibre structure from data `X`. -/
def JfX (e : TE) (X : CL) : CL :=
  jStd + (dg e.2.2.im 1).comp (X.comp (dg e.2.2.re (e.2.2.re * e.2.2.im)))

/-- The inhomogeneous term from data `X`. -/
def mX (e : TE) (X : CL) : ℂ × ℂ := dg e.2.2.im 1 (X (Complex.I, 0))

/-- The fixed outer map. -/
def Φ (y : TE × CL) : TE →L[ℝ] TE := vgJ (fun _ => JfX y.1 y.2) (fun _ => mX y.1 y.2) y.1

/-- The fibre structure. -/
def JfT (K : ℂ × ℂ → CL) (e : TE) : CL := JfX e (gT K e)

/-- The inhomogeneous term. -/
def mT (K : ℂ × ℂ → CL) (e : TE) : ℂ × ℂ := mX e (gT K e)

/-- The two-scale graph structure. -/
def TS (K : ℂ × ℂ → CL) : TE → TE →L[ℝ] TE := vgJ (JfT K) (mT K)

lemma JfX_apply (e : TE) (X : CL) (v : ℂ × ℂ) :
    JfX e X v = jStd v + dg e.2.2.im 1 (X (dg e.2.2.re (e.2.2.re * e.2.2.im) v)) := rfl

/-! ### Smoothness -/

section Smooth

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma cd_dg {α β : Y → ℝ} {w : Y → ℂ × ℂ} (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (fun y => dg (α y) (β y) (w y)) := by
  simp only [dg_apply]
  exact (hα.smul (contDiff_fst.comp hw)).prodMk (hβ.smul (contDiff_snd.comp hw))

lemma cd_JfX {e : Y → TE} {X : Y → CL} {w : Y → ℂ × ℂ} (he : ContDiff ℝ ∞ e)
    (hX : ContDiff ℝ ∞ X) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun y => JfX (e y) (X y) (w y)) := by
  have hp : ContDiff ℝ ∞ (fun y => (e y).2.2) := contDiff_snd.comp (contDiff_snd.comp he)
  have hre : ContDiff ℝ ∞ (fun y => (e y).2.2.re) := Complex.reCLM.contDiff.comp hp
  have him : ContDiff ℝ ∞ (fun y => (e y).2.2.im) := Complex.imCLM.contDiff.comp hp
  simp only [JfX_apply]
  exact (jStd.contDiff.comp hw).add
    (cd_dg him contDiff_const (hX.clm_apply (cd_dg hre (hre.mul him) hw)))

lemma cd_mX {e : Y → TE} {X : Y → CL} (he : ContDiff ℝ ∞ e) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (fun y => mX (e y) (X y)) := by
  have hp : ContDiff ℝ ∞ (fun y => (e y).2.2) := contDiff_snd.comp (contDiff_snd.comp he)
  have him : ContDiff ℝ ∞ (fun y => (e y).2.2.im) := Complex.imCLM.contDiff.comp hp
  exact cd_dg him contDiff_const (hX.clm_apply contDiff_const)

end Smooth

lemma contDiff_Φ : ContDiff ℝ ∞ Φ := by
  rw [contDiff_clm_apply_iff]
  intro v
  simp only [Φ, vgJ_apply]
  have h1 : ContDiff ℝ ∞ (fun y : TE × CL => y.1) := contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun y : TE × CL => y.2) := contDiff_snd
  exact contDiff_const.prodMk (((cd_JfX h1 h2 contDiff_const).add
    ((cd_JfX h1 h2 (cd_mX h1 h2)).const_smul _)).add ((cd_mX h1 h2).const_smul _) |>.prodMk
    contDiff_const)

lemma contDiff_iT : ContDiff ℝ ∞ iT := by
  have hp : ContDiff ℝ ∞ (fun e : TE => e.2.2) := contDiff_snd.comp contDiff_snd
  have hre : ContDiff ℝ ∞ (fun e : TE => e.2.2.re) := Complex.reCLM.contDiff.comp hp
  have him : ContDiff ℝ ∞ (fun e : TE => e.2.2.im) := Complex.imCLM.contDiff.comp hp
  have hP : ContDiff ℝ ∞ (fun e : TE => e.2.1.1) := contDiff_fst.comp (contDiff_fst.comp contDiff_snd)
  have hW : ContDiff ℝ ∞ (fun e : TE => e.2.1.2) := contDiff_snd.comp (contDiff_fst.comp contDiff_snd)
  exact (contDiff_fst.add (hre.smul hP)).prodMk (((hre.mul him).smul hW).prodMk hW)

variable {K : ℂ × ℂ → CL}

lemma contDiff_Hg (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (Hg K) :=
  (hadamard_integral_fderiv K hK).1

lemma K_eq_add (hK : ContDiff ℝ ∞ K) (hK0 : ∀ a, K (a, 0) = jStd) (q : ℂ × ℂ) :
    K q = jStd + Hg K q q.2 := by
  have h := (hadamard_integral_fderiv K hK).2 q
  rw [hK0] at h
  exact h

lemma contDiff_Hc (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (Hc K) :=
  ((contDiff_Hg hK).comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))).clm_apply
    (contDiff_snd.comp contDiff_snd)

lemma contDiff_gT (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (gT K) :=
  (contDiff_Hc hK).comp contDiff_iT

lemma contDiff_JfT (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (JfT K) := by
  rw [contDiff_clm_apply_iff]
  intro v
  exact cd_JfX contDiff_id (contDiff_gT hK) contDiff_const

lemma contDiff_mT (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (mT K) :=
  cd_mX contDiff_id (contDiff_gT hK)

/-! ### Conjugation identities -/

/-- With `(μ r) • X = A - jStd`, the fibre structure is the conjugate of `A`. -/
lemma JfX_conj {e : TE} {X A : CL} (hμ : e.2.2.re ≠ 0) (hr : e.2.2.im ≠ 0)
    (hX : A = jStd + (e.2.2.re * e.2.2.im) • X) (v : ℂ × ℂ) :
    JfX e X v = dg e.2.2.re⁻¹ (e.2.2.re * e.2.2.im)⁻¹
      (A (dg e.2.2.re (e.2.2.re * e.2.2.im) v)) := by
  subst hX
  have hμr : e.2.2.re * e.2.2.im ≠ 0 := mul_ne_zero hμ hr
  rw [JfX_apply, ContinuousLinearMap.add_apply, map_add, jStd_dg, dg_dg' hμ hμr,
    ContinuousLinearMap.smul_apply, dg_smul hμ hr]

lemma mX_conj {e : TE} {X A : CL} (hμ : e.2.2.re ≠ 0) (hr : e.2.2.im ≠ 0)
    (hX : A = jStd + (e.2.2.re * e.2.2.im) • X) :
    mX e X = dg e.2.2.re⁻¹ (e.2.2.re * e.2.2.im)⁻¹ (A (Complex.I, 0) + (1, 0)) := by
  subst hX
  rw [mX, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, add_comm (jStd _),
    add_assoc, jStd_I0, add_zero, dg_smul hμ hr]

/-- The data identity. -/
lemma smul_gT (hK : ContDiff ℝ ∞ K) (hK0 : ∀ a, K (a, 0) = jStd) (e : TE) :
    K ((iT e).1, (iT e).2.1) = jStd + (e.2.2.re * e.2.2.im) • gT K e := by
  rw [K_eq_add hK hK0]
  congr 1
  simp only [gT, Hc, iT, map_smul]

/-! ### Almost complexity -/

lemma JfT_sq_of_ne (hK : ContDiff ℝ ∞ K) (hK0 : ∀ a, K (a, 0) = jStd)
    (hsq : ∀ y v, K y (K y v) = -v) {e : TE} (hμ : e.2.2.re ≠ 0) (hr : e.2.2.im ≠ 0)
    (v : ℂ × ℂ) : JfT K e (JfT K e v) = -v := by
  have hμr : e.2.2.re * e.2.2.im ≠ 0 := mul_ne_zero hμ hr
  have hc := fun w => JfX_conj hμ hr (smul_gT hK hK0 e) w
  simp only [JfT]
  rw [hc, hc, dg_dg hμ hμr, hsq, map_neg, dg_dg' hμ hμr]

lemma ev_ne (c : ℝ) : ∀ᶠ τ in 𝓝[>] (0 : ℝ), c + τ ≠ 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact eventually_mem_nhdsWithin.mono fun τ h => by simpa using (ne_of_gt h)
  · have : ∀ᶠ τ in 𝓝 (0 : ℝ), c + τ ≠ 0 := by
      have hcont : Continuous fun τ : ℝ => c + τ := continuous_const.add continuous_id
      exact hcont.continuousAt.eventually_ne (by simpa using hc)
    exact this.filter_mono nhdsWithin_le_nhds

lemma JfT_sq (hK : ContDiff ℝ ∞ K) (hK0 : ∀ a, K (a, 0) = jStd)
    (hsq : ∀ y v, K y (K y v) = -v) (e : TE) (v : ℂ × ℂ) : JfT K e (JfT K e v) = -v := by
  set eτ : ℝ → TE := fun τ => (e.1, e.2.1, e.2.2 + (τ : ℂ) * (1 + Complex.I)) with heτ
  have he : ContDiff ℝ ∞ eτ :=
    contDiff_const.prodMk (contDiff_const.prodMk (contDiff_const.add
      ((Complex.ofRealCLM.contDiff).mul contDiff_const)))
  have hf : Continuous fun τ => JfT K (eτ τ) (JfT K (eτ τ) v) + v := by
    have h1 : ContDiff ℝ ∞ fun τ => JfT K (eτ τ) v :=
      cd_JfX he ((contDiff_gT hK).comp he) contDiff_const
    exact ((cd_JfX he ((contDiff_gT hK).comp he) h1).add contDiff_const).continuous
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), JfT K (eτ τ) (JfT K (eτ τ) v) + v = 0 := by
    filter_upwards [ev_ne e.2.2.re, ev_ne e.2.2.im] with τ h1 h2
    have r1 : (eτ τ).2.2.re = e.2.2.re + τ := by simp [heτ]
    have r2 : (eτ τ).2.2.im = e.2.2.im + τ := by simp [heτ]
    rw [JfT_sq_of_ne hK hK0 hsq (by rw [r1]; exact h1) (by rw [r2]; exact h2), neg_add_cancel]
  have hlim : Tendsto (fun τ => JfT K (eτ τ) (JfT K (eτ τ) v) + v) (𝓝[>] (0 : ℝ))
      (𝓝 (JfT K (eτ 0) (JfT K (eτ 0) v) + v)) :=
    hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun τ h => h.symm))
  have he0 : eτ 0 = e := by simp [heτ]
  rw [he0] at h0
  exact eq_neg_of_add_eq_zero_left h0

theorem isAlmostComplexOn_TS (hK : ContDiff ℝ ∞ K) (hK0 : ∀ a, K (a, 0) = jStd)
    (hsq : ∀ y v, K y (K y v) = -v) : IsAlmostComplexOn (TS K) univ :=
  isAlmostComplexOn_vgJ (contDiff_JfT hK) (contDiff_mT hK) fun e v => JfT_sq hK hK0 hsq e v

/-! ### The rescaled equation -/

/-- The rescaled perturbation. -/
def vT (μ r : ℝ) (u : ℂ → ℂ × ℂ) (ξ : ℂ) : ℂ × ℂ := dg μ⁻¹ (μ * r)⁻¹ (u ξ - (ξ, 0))

lemma hasFDerivAt_vT {μ r : ℝ} {u : ℂ → ℂ × ℂ} {ξ : ℂ} (hu : DifferentiableAt ℝ u ξ) :
    HasFDerivAt (vT μ r u) ((dg μ⁻¹ (μ * r)⁻¹).comp
      (fderiv ℝ u ξ - (ContinuousLinearMap.id ℝ ℂ).prod 0)) ξ :=
  (dg μ⁻¹ (μ * r)⁻¹).hasFDerivAt.comp ξ
    (hu.hasFDerivAt.sub ((hasFDerivAt_id ξ).prodMk (hasFDerivAt_const (0 : ℂ) ξ)))

lemma iT_vT {μ r : ℝ} (hμ : μ ≠ 0) (hr : r ≠ 0) (u : ℂ → ℂ × ℂ) (ξ : ℂ) :
    ((iT (ξ, vT μ r u ξ, ⟨μ, r⟩)).1, (iT (ξ, vT μ r u ξ, ⟨μ, r⟩)).2.1) = u ξ := by
  have hμr : μ * r ≠ 0 := mul_ne_zero hμ hr
  simp only [iT, vT, dg_apply, smul_smul, mul_inv_cancel₀ hμ, mul_inv_cancel₀ hμr, one_smul]
  ext <;> simp

theorem two_scale_eq (hK : ContDiff ℝ ∞ K) (hK0 : ∀ a, K (a, 0) = jStd) {u : ℂ → ℂ × ℂ}
    {ξ : ℂ} {μ r : ℝ} (hμ : μ ≠ 0) (hr : r ≠ 0) (hu : DifferentiableAt ℝ u ξ)
    (hdbar : dbarJ K u ξ = 0) :
    fderiv ℝ (vT μ r u) ξ 1 + JfT K (ξ, vT μ r u ξ, ⟨μ, r⟩) (fderiv ℝ (vT μ r u) ξ Complex.I) +
      mT K (ξ, vT μ r u ξ, ⟨μ, r⟩) = 0 := by
  set e : TE := (ξ, vT μ r u ξ, ⟨μ, r⟩) with he
  have hre : e.2.2.re = μ := rfl
  have him : e.2.2.im = r := rfl
  have hμ' : e.2.2.re ≠ 0 := hμ
  have hr' : e.2.2.im ≠ 0 := hr
  have hA := smul_gT hK hK0 e
  rw [show ((iT e).1, (iT e).2.1) = u ξ from iT_vT hμ hr u ξ] at hA
  rw [(hasFDerivAt_vT hu).fderiv]
  simp only [JfT, mT, JfX_conj hμ' hr' hA, mX_conj hμ' hr' hA, hre, him]
  have hμr : μ * r ≠ 0 := mul_ne_zero hμ hr
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
    dg_dg hμ hμr]
  rw [← map_add, ← map_add]
  have hdb : fderiv ℝ u ξ 1 + K (u ξ) (fderiv ℝ u ξ Complex.I) = 0 := hdbar
  have : fderiv ℝ u ξ 1 - ((1 : ℂ), (0 : ℂ)) + K (u ξ) (fderiv ℝ u ξ Complex.I - (Complex.I, 0)) +
      (K (u ξ) (Complex.I, 0) + (1, 0)) = 0 := by
    rw [map_sub]
    have e4 : fderiv ℝ u ξ 1 = -K (u ξ) (fderiv ℝ u ξ Complex.I) :=
      eq_neg_of_add_eq_zero_left hdb
    rw [e4]; abel
  rw [this, map_zero]

lemma differentiableAt_vT {μ r : ℝ} {u : ℂ → ℂ × ℂ} {ξ : ℂ} (hu : DifferentiableAt ℝ u ξ) :
    DifferentiableAt ℝ (vT μ r u) ξ := (hasFDerivAt_vT hu).differentiableAt

/-- The graph of the rescaled perturbation is `TS K`-holomorphic. -/
theorem isJHolomorphicOn_graph_vT (hK : ContDiff ℝ ∞ K) (hK0 : ∀ a, K (a, 0) = jStd)
    {u : ℂ → ℂ × ℂ} {μ r : ℝ} (hμ : μ ≠ 0) (hr : r ≠ 0) (c : ℂ) {U : Set ℂ}
    (hu : ∀ ζ ∈ U, DifferentiableAt ℝ u (c + ζ) ∧ dbarJ K u (c + ζ) = 0) :
    IsJHolomorphicOn (TS K) U (graph c (fun ζ => vT μ r u (c + ζ)) ⟨μ, r⟩) := by
  have hd : ∀ ζ ∈ U, DifferentiableAt ℝ (fun ζ => vT μ r u (c + ζ)) ζ := fun ζ hζ =>
    (differentiableAt_vT (hu ζ hζ).1).comp ζ ((differentiableAt_id).const_add c)
  refine isJHolomorphicOn_graph _ _ c _ hd fun ζ hζ => ?_
  have hf : fderiv ℝ (fun ζ => vT μ r u (c + ζ)) ζ = fderiv ℝ (vT μ r u) (c + ζ) :=
    fderiv_comp_add_left (f := vT μ r u) c
  rw [hf]
  exact two_scale_eq hK hK0 hμ hr (hu ζ hζ).1 (hu ζ hζ).2

end QR16

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

/-! ### Change of variables with exponent `4` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c₀ : E} {G : ℝ × ℝ → E}

lemma norm_Eexp (ξ : ℂ) : ‖Eexp ξ‖ = Real.exp (2 * π * ξ.re) := by
  rw [Eexp, Complex.norm_exp]
  congr 1
  simp

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

lemma eLpNorm_smul_real {α : Type*} [MeasurableSpace α] (r : ℝ) (hr : 0 ≤ r) (f : α → ℝ)
    (μ : Measure α) : eLpNorm (r • f) 4 μ = ENNReal.ofReal r * eLpNorm f 4 μ := by
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hr]

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

/-- The Hadamard divided difference of `J` along `a`. -/
def Hg (J : E → E →L[ℝ] E) (q : E × E) : E →L[ℝ] (E →L[ℝ] E) :=
  ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => J (q.1 + a)) (θ • q.2)

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

end QR15

end

end FiniteEnergyPlane

-- FILE: RSK_R17.lean
/-!
# Q-R, layer 17 (local, NOT published): the cylinder lift of a member

* `Kc ρ Jbar σ (a, w) = cylJ Jbar (a.re + σ) a.im (rtr ρ w)`: the cylinder-coordinate structure,
  shifted by `σ` and globalized in `w`; smooth, `jStd` along `w = 0`, squares to `-1`.
* `uL x ξ = (ξ + (2π)⁻¹ log(1 + τ ξ), h₂ ξ)` with `τ = h₁ / e^{2πξ}`, where `(h₁, h₂)` is the
  perturbation `hC` of the member `x` in cylinder coordinates: `e^{2π uL₁} = e^{2πξ} + h₁`.
* `uS x σ ξ = uL x (ξ + σ) - (σ, 0)` is `Kc σ`-holomorphic where `|τ| < 1/2` and `|h₂| < ρ/4`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology JHolomorphic
open scoped ContDiff ENNReal NNReal Real

noncomputable section

namespace QR17

open QL QR QR4 QR7 QR14 QR16 QN11 QN13 QN19W QN18

/-! ### The cylinder structure -/

section Kc

variable (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)

/-- The shifted, globalized cylinder structure. -/
def Kc (σ : ℝ) (y : ℂ × ℂ) : CL := cylJ Jbar (y.1.re + σ) y.1.im (rtr ρ y.2)

variable {ρ Jbar}

lemma contDiff_Kc (hρ : 0 < ρ) (hJs : ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ)) (σ : ℝ) :
    ContDiff ℝ ∞ (Kc ρ Jbar σ) := by
  have h : ContDiff ℝ ∞ (fun y : ℂ × ℂ => ((y.1.re + σ, y.1.im, rtr ρ y.2) : ℝ × ℝ × ℂ)) :=
    ((Complex.reCLM.contDiff.comp contDiff_fst).add contDiff_const).prodMk
      ((Complex.imCLM.contDiff.comp contDiff_fst).prodMk ((rtr_contDiff ρ).comp contDiff_snd))
  have e : Kc ρ Jbar σ =
      gJ Jbar ∘ (fun y : ℂ × ℂ => ((y.1.re + σ, y.1.im, rtr ρ y.2) : ℝ × ℝ × ℂ)) := rfl
  rw [e]
  exact (gJ_contDiffOn ρ Jbar hJs).comp_contDiff h fun y =>
    ⟨mem_univ _, mem_univ _, mem_ball_zero_iff.2 (norm_rtr_lt hρ _)⟩

lemma Kc_zero (hρ : 0 < ρ) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd) (σ : ℝ) (a : ℂ) :
    Kc ρ Jbar σ (a, 0) = jStd := by
  rw [Kc, rtr_eq hρ (by rw [norm_zero]; positivity : ‖(0 : ℂ)‖ < ρ / 4), cylJ_zero Jbar h0]

lemma cylScale_cylScaleInv (s t : ℝ) (v : ℂ × ℂ) : cylScale s t (cylScaleInv s t v) = v := by
  have hz : (((2 * π : ℝ) : ℂ) * cylInf s t) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) (cylInf_ne_zero s t)
  show ((((2 * π : ℝ) : ℂ) * cylInf s t) * ((((2 * π : ℝ) : ℂ) * cylInf s t)⁻¹ * v.1), v.2) = v
  rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]

lemma cylScaleInv_cylScale (s t : ℝ) (v : ℂ × ℂ) : cylScaleInv s t (cylScale s t v) = v := by
  have hz : (((2 * π : ℝ) : ℂ) * cylInf s t) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) (cylInf_ne_zero s t)
  show (((((2 * π : ℝ) : ℂ) * cylInf s t)⁻¹ * ((((2 * π : ℝ) : ℂ) * cylInf s t) * v.1)), v.2) = v
  rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]

lemma Kc_sq (hρ : 0 < ρ)
    (hsq : ∀ p ∈ univ ×ˢ ball (0 : ℂ) ρ, (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (σ : ℝ) (y v : ℂ × ℂ) : Kc ρ Jbar σ y (Kc ρ Jbar σ y v) = -v := by
  have h := congrArg (fun L : ℂ × ℂ →L[ℝ] ℂ × ℂ => L (cylScale (y.1.re + σ) y.1.im v))
    (hsq (cylInf (y.1.re + σ) y.1.im, rtr ρ y.2)
      ⟨mem_univ _, mem_ball_zero_iff.2 (norm_rtr_lt hρ _)⟩)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply] at h
  simp only [Kc, cylJ, ContinuousLinearMap.comp_apply, cylScale_cylScaleInv, h, map_neg,
    cylScaleInv_cylScale]

lemma Kc_eq (hρ : 0 < ρ) {σ : ℝ} {y : ℂ × ℂ} (hy : ‖y.2‖ < ρ / 4) :
    Kc ρ Jbar σ y = cylJ Jbar (y.1.re + σ) y.1.im y.2 := by
  rw [Kc, rtr_eq hρ hy]

end Kc

/-! ### The lift -/

variable {χT χN β : ℝ → ℝ}

variable (χT χN β) in
/-- The tangential perturbation. -/
def h1 (x : QDom) (ξ : ℂ) : ℂ := (hC χT χN β x (cplx ξ)).1

variable (χT χN β) in
/-- The normal perturbation. -/
def h2 (x : QDom) (ξ : ℂ) : ℂ := (hC χT χN β x (cplx ξ)).2

variable (χT χN β) in
/-- The relative tangential perturbation. -/
def τL (x : QDom) (ξ : ℂ) : ℂ := h1 χT χN β x ξ / Eexp ξ

variable (χT χN β) in
/-- The cylinder lift. -/
def uL (x : QDom) (ξ : ℂ) : ℂ × ℂ :=
  (ξ + ((2 * π : ℝ) : ℂ)⁻¹ * Complex.log (1 + τL χT χN β x ξ), h2 χT χN β x ξ)

variable (χT χN β) in
/-- The shifted lift. -/
def uS (x : QDom) (σ : ℝ) (ξ : ℂ) : ℂ × ℂ :=
  ((uL χT χN β x (ξ + σ)).1 - σ, (uL χT χN β x (ξ + σ)).2)

lemma Eexp_ne (ξ : ℂ) : Eexp ξ ≠ 0 := Complex.exp_ne_zero _

lemma gC_eq_hC (x : QDom) (q : ℝ × ℝ) :
    gC χT χN β x q = (cylInf q.1 q.2 + (hC χT χN β x q).1, (hC χT χN β x q).2) := by
  simp [gC, hC, vOf, map_smul]

lemma cylInf_eq_Eexp (ξ : ℂ) : cylInf (cplx ξ).1 (cplx ξ).2 = Eexp ξ := by
  rw [cylInf_cplx]; rfl

/-- The lift identity. -/
lemma Eexp_uL (x : QDom) {ξ : ℂ} (h : 1 + τL χT χN β x ξ ≠ 0) :
    Eexp (uL χT χN β x ξ).1 = (gC χT χN β x (cplx ξ)).1 := by
  rw [gC_eq_hC, cylInf_eq_Eexp]
  simp only [uL]
  rw [Eexp, mul_add, Complex.exp_add, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2
    (by positivity : (2 * π : ℝ) ≠ 0)), one_mul, Complex.exp_log h, ← Eexp]
  simp only [τL, h1]
  field_simp [Eexp_ne ξ]

/-- `vT` of the shifted lift is `vT` of the lift, translated. -/
lemma vT_uS (x : QDom) (σ μ r : ℝ) (ξ : ℂ) :
    vT μ r (uS χT χN β x σ) ξ = vT μ r (uL χT χN β x) (ξ + σ) := by
  simp only [vT, uS]
  congr 1
  exact Prod.ext (by simp; ring) (by simp)

/-! ### Smoothness of the lift -/

variable (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)

include hχT hχN hβ in
lemma contDiff_hCc {x : QDom} (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2)) :
    ContDiff ℝ ∞ (fun ξ => hC χT χN β x (cplx ξ)) :=
  (contDiff_hC hχT hχN hβ hw1 hw2).comp Complex.equivRealProdCLM.contDiff

lemma contDiff_Eexp : ContDiff ℝ ∞ Eexp :=
  show ContDiff ℝ ∞ (fun ξ : ℂ => Complex.exp (((2 * π : ℝ) : ℂ) * ξ)) from
    (Complex.contDiff_exp.comp ((contDiff_const (c := ((2 * π : ℝ) : ℂ))).mul
      (contDiff_id (𝕜 := ℂ)))).restrict_scalars ℝ

include hχT hχN hβ in
lemma contDiff_τL {x : QDom} (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2)) :
    ContDiff ℝ ∞ (τL χT χN β x) := by
  have h := contDiff_fst.comp (contDiff_hCc hχT hχN hβ hw1 hw2)
  have he : ContDiff ℝ ∞ (fun ξ => (Eexp ξ)⁻¹) := by
    have : (fun ξ => (Eexp ξ)⁻¹) = fun ξ => Eexp (-ξ) := by
      funext ξ; rw [Eexp, Eexp, mul_neg, Complex.exp_neg]
    rw [this]; exact contDiff_Eexp.comp contDiff_neg
  have : τL χT χN β x = fun ξ => h1 χT χN β x ξ * (Eexp ξ)⁻¹ := by
    funext ξ; simp [τL, div_eq_mul_inv]
  rw [this]
  exact h.mul he

include hχT hχN hβ in
lemma contDiffAt_uL {x : QDom} (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2))
    {ξ : ℂ} (hτ : ‖τL χT χN β x ξ‖ < 1) : ContDiffAt ℝ ∞ (uL χT χN β x) ξ := by
  have hτc := contDiff_τL hχT hχN hβ hw1 hw2
  have hslit : 1 + τL χT χN β x ξ ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have h1 := Complex.abs_re_le_norm (τL χT χN β x ξ)
    simp only [Complex.add_re, Complex.one_re]
    linarith [neg_abs_le (τL χT χN β x ξ).re]
  have hlog0 : ContDiffAt ℝ ∞ Complex.log (1 + τL χT χN β x ξ) :=
    (Complex.contDiffAt_log hslit).restrict_scalars ℝ
  have hlog : ContDiffAt ℝ ∞ (fun ξ => Complex.log (1 + τL χT χN β x ξ)) ξ :=
    ContDiffAt.comp (g := Complex.log) (f := fun ξ => (1 : ℂ) + τL χT χN β x ξ) ξ hlog0
      ((contDiff_const (c := (1 : ℂ))).add hτc).contDiffAt
  exact (contDiffAt_id.add (contDiffAt_const.mul hlog)).prodMk
    (contDiff_snd.comp (contDiff_hCc hχT hχN hβ hw1 hw2)).contDiffAt

lemma cylInf_re_add (a : ℂ) (σ : ℝ) : cylInf (a.re + σ) a.im = Eexp (a + σ) := by
  have := cylInf_eq_Eexp (a + σ)
  simpa using this

lemma cylScale_apply' (a : ℂ) (σ : ℝ) (w : ℂ × ℂ) :
    cylScale (a.re + σ) a.im w = (w.1 * (Eexp (a + σ) * ((2 * π : ℝ) : ℂ)), w.2) := by
  show ((((2 * π : ℝ) : ℂ) * cylInf (a.re + σ) a.im) * w.1, w.2) = _
  rw [cylInf_re_add]; ring_nf

include hχT hχN hβ in
lemma contDiffAt_uS {x : QDom} (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2))
    {σ : ℝ} {ξ : ℂ} (hτ : ‖τL χT χN β x (ξ + σ)‖ < 1) : ContDiffAt ℝ ∞ (uS χT χN β x σ) ξ := by
  have h := (contDiffAt_uL hχT hχN hβ hw1 hw2 hτ).comp ξ
    ((contDiffAt_id (𝕜 := ℝ)).add (contDiffAt_const (c := (σ : ℂ))))
  exact ((contDiff_fst.contDiffAt.comp ξ h).sub contDiffAt_const).prodMk
    (contDiff_snd.contDiffAt.comp ξ h)

include hχT hχN hβ in
/-- The shifted lift is `Kc σ`-holomorphic where the perturbation is small. -/
theorem dbarJ_uS {ρ : ℝ} (hρ : 0 < ρ) {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {x : QDom}
    (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2))
    (hgsm : ContDiff ℝ ∞ (gC χT χN β x)) (hdb : ∀ q, dbarC Jbar (gC χT χN β x) q = 0)
    {σ : ℝ} {ξ : ℂ} (hτ : ‖τL χT χN β x (ξ + σ)‖ < 1)
    (hsmall : ‖h2 χT χN β x (ξ + σ)‖ < ρ / 4) :
    DifferentiableAt ℝ (uS χT χN β x σ) ξ ∧ dbarJ (Kc ρ Jbar σ) (uS χT χN β x σ) ξ = 0 := by
  have hcd := contDiffAt_uS hχT hχN hβ hw1 hw2 hτ
  have hd : DifferentiableAt ℝ (uS χT χN β x σ) ξ := hcd.differentiableAt (by simp)
  refine ⟨hd, ?_⟩
  set a := (uS χT χN β x σ ξ).1 with ha
  set L := fderiv ℝ (uS χT χN β x σ) ξ with hL
  -- the map `Ψ`
  set Ψ : ℂ × ℂ → ℂ × ℂ := fun y => (Eexp (y.1 + σ), y.2) with hΨ
  set DΨ : ℂ × ℂ →L[ℝ] ℂ × ℂ := (((ContinuousLinearMap.toSpanSingleton ℂ
      (Eexp (a + σ) * ((2 * π : ℝ) : ℂ))).restrictScalars ℝ).comp
        (ContinuousLinearMap.fst ℝ ℂ ℂ)).prod (ContinuousLinearMap.snd ℝ ℂ ℂ) with hDΨ
  have hΨd : HasFDerivAt Ψ DΨ (uS χT χN β x σ ξ) := by
    have h1 : HasFDerivAt (fun y : ℂ × ℂ => y.1 + (σ : ℂ)) (ContinuousLinearMap.fst ℝ ℂ ℂ)
        (uS χT χN β x σ ξ) := hasFDerivAt_fst.add_const _
    have h2 := (hasFDerivAt_Eexp (a + σ)).comp (uS χT χN β x σ ξ) h1
    exact h2.prodMk hasFDerivAt_snd
  -- `F = Ψ ∘ uS` near `ξ`
  have hτc := contDiff_τL hχT hχN hβ hw1 hw2
  have hev : ∀ᶠ ξ' in 𝓝 ξ, ‖τL χT χN β x (ξ' + σ)‖ < 1 :=
    ((hτc.continuous.comp (continuous_id.add continuous_const)).norm.continuousAt).eventually
      (gt_mem_nhds hτ)
  have hFeq : (fun ξ' => gC χT χN β x (cplx (ξ' + σ))) =ᶠ[𝓝 ξ] Ψ ∘ uS χT χN β x σ := by
    filter_upwards [hev] with ξ' h'
    have hne : 1 + τL χT χN β x (ξ' + σ) ≠ 0 := by
      intro h0
      have : τL χT χN β x (ξ' + σ) = -1 := by linear_combination h0
      rw [this, norm_neg, norm_one] at h'
      exact lt_irrefl _ h'
    simp only [Function.comp, hΨ, uS, sub_add_cancel]
    refine Prod.ext ?_ ?_
    · exact (Eexp_uL x hne).symm
    · simp [gC_eq_hC, uL, h2]
  have hF : HasFDerivAt (fun ξ' => gC χT χN β x (cplx (ξ' + σ))) (DΨ.comp L) ξ :=
    (hΨd.comp ξ hd.hasFDerivAt).congr_of_eventuallyEq hFeq
  have hFv : ∀ v : ℂ, fderiv ℝ (gC χT χN β x) (cplx (ξ + σ)) (cplx v) = DΨ (L v) := by
    intro v
    have e1 : fderiv ℝ (fun ξ' => gC χT χN β x (cplx (ξ' + σ))) ξ v =
        fderiv ℝ (gC χT χN β x) (cplx (ξ + σ)) (cplx v) := by
      rw [fderiv_comp_add_right (f := fun z => gC χT χN β x (cplx z)), fderiv_comp_cplx]
    rw [← e1, hF.fderiv]; rfl
  have hq := hdb (cplx (ξ + σ))
  simp only [dbarC] at hq
  have c1 : cplx 1 = ((1 : ℝ), (0 : ℝ)) := by simp
  have cI : cplx Complex.I = ((0 : ℝ), (1 : ℝ)) := by simp
  rw [← c1, ← cI, hFv, hFv] at hq
  have hpt : gC χT χN β x (cplx (ξ + σ)) = (cylInf (a.re + σ) a.im, (uS χT χN β x σ ξ).2) := by
    have := hFeq.eq_of_nhds
    simp only [Function.comp, hΨ] at this
    rw [this, cylInf_re_add]
  rw [hpt] at hq
  have hDΨv : ∀ w : ℂ × ℂ, DΨ w = cylScale (a.re + σ) a.im w := by
    intro w; rw [cylScale_apply']; simp [hDΨ]
  rw [hDΨv, hDΨv] at hq
  have hsm2 : ‖(uS χT χN β x σ ξ).2‖ < ρ / 4 := by simpa [uS, uL] using hsmall
  rw [dbarJ, ← hL, Kc_eq hρ hsm2, ← ha]
  have := congrArg (cylScaleInv (a.re + σ) a.im) hq
  rw [map_add, cylScaleInv_cylScale, map_zero] at this
  simpa [cylJ] using this

end QR17

end

end FiniteEnergyPlane

-- FILE: RSK_R18.lean
/-!
# Q-R, layer 18 (local, NOT published): unit windows and slope-weight bounds

* `lintegral_window_le`: for `F ≥ 0` measurable and `1`-periodic in `t`, the integral of
  `F ∘ cplx` over a unit disc centred at `ξ₀` with `|Im ξ₀| ≤ 1/2` is at most `4 ∫ F dcylMeasure`.
* `eLpNorm_window_le`: the same for `L⁴` norms (factor `2`).
* Slope weights: bounded derivative, Lipschitz, and upper bounds on half-lines of functions that
  are affine with nonpositive slope on `[1, ∞)`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal NNReal Real

noncomputable section

namespace QR18

open QL QR16 QR17

/-! ### Windows -/

lemma lintegral_strip_eq {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (hper : ∀ s t : ℝ, F (s, t + 1) = F (s, t)) (k : ℤ) :
    ∫⁻ q in univ ×ˢ Ico (k : ℝ) (k + 1), F q = ∫⁻ q, F q ∂cylMeasure := by
  have hmp0 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_add_right (volume : Measure ℝ) (k : ℝ))
  have e : Prod.map id (fun t : ℝ => t + k) = fun q : ℝ × ℝ => q + ((0 : ℝ), (k : ℝ)) := by
    funext q; obtain ⟨a, b⟩ := q; simp [Prod.map]
  rw [e] at hmp0
  have hmp : MeasurePreserving (fun q : ℝ × ℝ => q + ((0 : ℝ), (k : ℝ))) volume volume := hmp0
  have hpre : (fun q : ℝ × ℝ => q + ((0 : ℝ), (k : ℝ))) ⁻¹' (univ ×ˢ Ico (k : ℝ) (k + 1)) =
      univ ×ˢ Ico 0 1 := by
    ext ⟨a, t⟩
    simp only [mem_preimage, Prod.mk_add_mk, add_zero, mem_prod, mem_univ, true_and, mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have h := hmp.setLIntegral_comp_preimage
    ((MeasurableSet.univ (α := ℝ)).prod (measurableSet_Ico (a := (k : ℝ)) (b := k + 1))) hF
  rw [hpre] at h
  rw [← h]
  have hpk : ∀ q : ℝ × ℝ, F (q + ((0 : ℝ), (k : ℝ))) = F q := by
    intro q
    have hp : Function.Periodic (fun t => F (q.1, t)) 1 := fun t => hper q.1 t
    have := (hp.int_mul k) q.2
    simp only [mul_one] at this
    obtain ⟨a, t⟩ := q
    simpa using this
  simp only [hpk]
  rfl

/-- Unit discs in cylinder coordinates. -/
theorem lintegral_window_le {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (hper : ∀ s t : ℝ, F (s, t + 1) = F (s, t)) {ξ₀ : ℂ} (ht : |ξ₀.im| ≤ 1 / 2) :
    ∫⁻ ζ in ball (0 : ℂ) 1, F (cplx (ξ₀ + ζ)) ≤ 4 * ∫⁻ q, F q ∂cylMeasure := by
  set g : ℝ × ℝ → ℂ := fun q => toC q - ξ₀ with hg
  have hmp : MeasurePreserving g volume volume :=
    (measurePreserving_sub_right (volume : Measure ℂ) ξ₀).comp QL.measurePreserving_toC
  have hFc : Measurable fun ζ : ℂ => F (cplx (ξ₀ + ζ)) :=
    hF.comp (Complex.equivRealProdCLM.continuous.measurable.comp (measurable_const.add measurable_id))
  have h := hmp.setLIntegral_comp_preimage (measurableSet_ball (x := (0 : ℂ)) (ε := 1)) hFc
  rw [← h]
  have hgq : ∀ q, F (cplx (ξ₀ + g q)) = F q := by
    intro q; simp only [hg, add_sub_cancel, cplx_toC]
  simp only [hgq]
  have hsub : g ⁻¹' ball (0 : ℂ) 1 ⊆
      (univ ×ˢ Ico ((-2 : ℤ) : ℝ) ((-2 : ℤ) + 1) ∪ univ ×ˢ Ico ((-1 : ℤ) : ℝ) ((-1 : ℤ) + 1)) ∪
        (univ ×ˢ Ico ((0 : ℤ) : ℝ) ((0 : ℤ) + 1) ∪ univ ×ˢ Ico ((1 : ℤ) : ℝ) ((1 : ℤ) + 1)) := by
    intro q hq
    simp only [mem_preimage, mem_ball_zero_iff, hg] at hq
    have him : |q.2 - ξ₀.im| < 1 := by
      have := Complex.abs_im_le_norm (toC q - ξ₀)
      have e : (toC q - ξ₀).im = q.2 - ξ₀.im := by simp [toC]
      rw [e] at this; linarith
    rw [abs_lt] at him
    rw [abs_le] at ht
    simp only [mem_union, mem_prod, mem_univ, true_and, mem_Ico, Int.cast_neg, Int.cast_ofNat,
      Int.cast_zero, Int.cast_one]
    rcases lt_or_ge q.2 (-1) with h1 | h1
    · left; left; constructor <;> linarith
    rcases lt_or_ge q.2 0 with h2 | h2
    · left; right; constructor <;> linarith
    rcases lt_or_ge q.2 1 with h3 | h3
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith
  refine (lintegral_mono_set hsub).trans ?_
  refine (lintegral_union_le _ _ _).trans ?_
  refine (add_le_add (lintegral_union_le _ _ _) (lintegral_union_le _ _ _)).trans ?_
  rw [lintegral_strip_eq hF hper, lintegral_strip_eq hF hper, lintegral_strip_eq hF hper,
    lintegral_strip_eq hF hper]
  ring_nf
  exact le_rfl

lemma eLpNorm_four_eq' {α : Type*} [MeasurableSpace α] (f : α → ℝ) (μ : Measure α) :
    eLpNorm f 4 μ = (∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂μ) ^ (1 / 4 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  norm_num

theorem eLpNorm_window_le {G : ℝ × ℝ → ℝ} (hG : Continuous G)
    (hper : ∀ s t : ℝ, G (s, t + 1) = G (s, t)) {ξ₀ : ℂ} (ht : |ξ₀.im| ≤ 1 / 2) :
    eLpNorm (fun ζ => G (cplx (ξ₀ + ζ))) 4 (volume.restrict (ball (0 : ℂ) 1)) ≤
      2 * eLpNorm G 4 cylMeasure := by
  rw [eLpNorm_four_eq', eLpNorm_four_eq']
  have hF : Measurable fun q => ‖G q‖ₑ ^ (4 : ℝ) :=
    (hG.measurable.enorm).pow_const _
  have h := lintegral_window_le hF (fun s t => by simp only [hper]) ht
  calc (∫⁻ ζ in ball (0 : ℂ) 1, ‖G (cplx (ξ₀ + ζ))‖ₑ ^ (4 : ℝ)) ^ (1 / 4 : ℝ)
      ≤ (4 * ∫⁻ q, ‖G q‖ₑ ^ (4 : ℝ) ∂cylMeasure) ^ (1 / 4 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = (4 : ℝ≥0∞) ^ (1 / 4 : ℝ) * (∫⁻ q, ‖G q‖ₑ ^ (4 : ℝ) ∂cylMeasure) ^ (1 / 4 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ 2 * (∫⁻ q, ‖G q‖ₑ ^ (4 : ℝ) ∂cylMeasure) ^ (1 / 4 : ℝ) := by
        gcongr
        have : (4 : ℝ≥0∞) ^ (1 / 4 : ℝ) ≤ 2 := by
          rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) by rw [ENNReal.rpow_two]; norm_num, ← ENNReal.rpow_mul]
          calc (2 : ℝ≥0∞) ^ ((2 : ℝ) * (1 / 4)) ≤ 2 ^ (1 : ℝ) :=
                ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := ENNReal.rpow_one 2
        exact this

/-! ### Slope weights -/

lemma lip {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) {L : ℝ} (hL : ∀ s, |deriv χ s| ≤ L)
    (s s' : ℝ) : |χ s - χ s'| ≤ L * |s - s'| := by
  have hd : Differentiable ℝ χ := hχ.1.differentiable (by simp)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := χ) (C := L) (s := univ)
    (fun x _ => hd x) (fun x _ => by simpa using hL x) convex_univ (mem_univ s') (mem_univ s)
  simpa [Real.norm_eq_abs] using this

/-- Upper bound on `[A, ∞)` of a continuous function affine with slope `≤ 0` on `[1, ∞)`. -/
lemma upper_halfline {f : ℝ → ℝ} (hf : Continuous f) {b : ℝ} (hb : b ≤ 0)
    (heq : ∀ s ≥ 1, f s = f 1 + b * (s - 1)) (A : ℝ) : ∃ C, ∀ s ≥ A, f s ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := A) (b := 1)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C (f 1), fun s hs => ?_⟩
  rcases le_or_gt 1 s with h | h
  · rw [heq s h]
    have : b * (s - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb (by linarith)
    exact le_max_of_le_right (by linarith)
  · have := hC s ⟨hs, h.le⟩
    exact le_max_of_le_left ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this))

lemma weight_upper {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) (c : ℝ) (hbc : b - c ≤ 0)
    (A : ℝ) : ∃ C, ∀ s ≥ A, χ s - c * s ≤ C :=
  upper_halfline (hχ.1.continuous.sub (continuous_const.mul continuous_id)) hbc
    (fun s hs => by simp only [Pi.sub_apply, Pi.mul_apply, id]; rw [hχ.eq_right hs]; ring) A

lemma weight_diff_upper {χ₁ χ₂ : ℝ → ℝ} {a₁ b₁ a₂ b₂ : ℝ} (h₁ : IsSlopeWeight χ₁ a₁ b₁)
    (h₂ : IsSlopeWeight χ₂ a₂ b₂) (c : ℝ) (hbc : b₁ - b₂ + c ≤ 0) (A : ℝ) :
    ∃ C, ∀ s ≥ A, χ₁ s - χ₂ s + c * s ≤ C :=
  upper_halfline ((h₁.1.continuous.sub h₂.1.continuous).add (continuous_const.mul continuous_id))
    hbc (fun s hs => by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id]; rw [h₁.eq_right hs, h₂.eq_right hs]; ring) A

end QR18

end

end FiniteEnergyPlane

-- FILE: RSK_R19.lean
/-!
# Q-R, layer 19 (local, NOT published): pointwise window bounds

For a small zero `x` and a window centre `ξ₀` with `Re ξ₀ ≥ -1`, with scales
`μ1 = ‖x‖ e^{χT(s₀) - 2π s₀}` and `rr = e^{χN(s₀) - χT(s₀) + 2π s₀}` (`s₀ = Re ξ₀`):
* `h1_le`, `h2_le`, `τL_le`: the weighted pointwise bounds of the lift data (from R1);
* `sup_window`: smallness of `τL` and `h2` and a uniform bound of the rescaled lift
  `vT μ1 rr (uL x) (ξ₀ + ζ)` on the unit disc, plus bounds of the scales.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic
open scoped ContDiff ENNReal NNReal Real

noncomputable section

namespace QR19

open QL QR QR8 QR13 QR14 QR16 QR17 QR18 QN19W QN18

variable {χT χN β : ℝ → ℝ}

/-! ### Exponential weights -/

lemma one_add_exp_le {s : ℝ} (hs : -2 ≤ s) :
    1 + Real.exp (2 * π * s) ≤ (1 + Real.exp (4 * π)) * Real.exp (2 * π * s) := by
  have h1 : 1 ≤ Real.exp (4 * π) * Real.exp (2 * π * s) := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [Real.pi_pos])
  nlinarith [Real.exp_pos (2 * π * s)]

lemma rpow_pos_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {s : ℝ} (hs : -2 ≤ s) :
    (1 + Real.exp (2 * π * s)) ^ a ≤ (1 + Real.exp (4 * π)) * Real.exp (2 * π * a * s) := by
  have hE := Real.exp_pos (2 * π * s)
  have hA : 1 ≤ 1 + Real.exp (4 * π) := by linarith [Real.exp_pos (4 * π)]
  calc (1 + Real.exp (2 * π * s)) ^ a ≤ ((1 + Real.exp (4 * π)) * Real.exp (2 * π * s)) ^ a :=
        Real.rpow_le_rpow (by positivity) (one_add_exp_le hs) ha0
    _ = (1 + Real.exp (4 * π)) ^ a * Real.exp (2 * π * s) ^ a := Real.mul_rpow (by positivity) hE.le
    _ ≤ (1 + Real.exp (4 * π)) * Real.exp (2 * π * a * s) := by
        rw [← Real.exp_mul, show 2 * π * s * a = 2 * π * a * s by ring]
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        simpa using Real.rpow_le_rpow_of_exponent_le hA ha1

lemma rpow_neg_le {a : ℝ} (ha : a ≤ 0) (s : ℝ) :
    (1 + Real.exp (2 * π * s)) ^ a ≤ Real.exp (2 * π * a * s) := by
  calc (1 + Real.exp (2 * π * s)) ^ a ≤ Real.exp (2 * π * s) ^ a :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (by linarith) ha
    _ = _ := by rw [← Real.exp_mul]; ring_nf

/-- `b s - χ s` is bounded above on `[A, ∞)` for a slope weight with right slope `b`. -/
lemma lin_sub_upper {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) (A : ℝ) :
    ∃ C, ∀ s ≥ A, b * s - χ s ≤ C :=
  upper_halfline ((continuous_const.mul continuous_id).sub hχ.1.continuous) le_rfl
    (fun s hs => by
      show b * s - χ s = (b * 1 - χ 1) + 0 * (s - 1)
      rw [hχ.eq_right hs]; ring) A

lemma ratio_exp {X : ℝ} (hX : 0 < X) (K a b : ℝ) :
    (X * Real.exp a)⁻¹ * (K * X * Real.exp b) = K * Real.exp (b - a) := by
  rw [Real.exp_sub]; field_simp

/-! ### The lift data -/

lemma hC_eq_pLc (x : QDom) (ξ : ℂ) : hC χT χN β x (cplx ξ) = pLc χT χN β (Eexp ξ) x := by
  have h := congrFun (pLc_eq_pfG (χT := χT) (χN := χN) (β := β) x) (Eexp ξ)
  rw [h, ← cylInf_eq_Eexp, pfG_cylInf (fun s t => hC_per x s t)]

variable {δ δT K₀ : ℝ}

section C0

variable (hC0 : ∀ (y : QDom) (z : ℂ),
      ‖(pLc χT χN β z y).1‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(pLc χT χN β z y).2‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π))) (hK₀ : 0 ≤ K₀)

include hC0 hK₀ in
lemma h1_le (hδT : δT ∈ Set.Ioo (-(2 * π)) 0) (x : QDom) {ξ : ℂ} (hs : -2 ≤ ξ.re) :
    ‖h1 χT χN β x ξ‖ ≤ K₀ * (1 + Real.exp (4 * π)) * ‖x‖ * Real.exp ((2 * π + δT) * ξ.re) := by
  have hπ : 0 < 2 * π := by positivity
  have h := (hC0 x (Eexp ξ)).1
  rw [norm_Eexp] at h
  have ha0 : 0 ≤ 1 + δT / (2 * π) := by
    rw [← sub_nonneg]; have : -1 < δT / (2 * π) := by
      rw [lt_div_iff₀ hπ]; linarith [hδT.1]
    linarith
  have ha1 : 1 + δT / (2 * π) ≤ 1 := by
    have : δT / (2 * π) < 0 := div_neg_of_neg_of_pos hδT.2 hπ
    linarith
  have hw := rpow_pos_le ha0 ha1 hs
  have e : 2 * π * (1 + δT / (2 * π)) * ξ.re = (2 * π + δT) * ξ.re := by field_simp
  rw [e] at hw
  have : h1 χT χN β x ξ = (pLc χT χN β (Eexp ξ) x).1 := by
    simp only [h1, hC_eq_pLc]
  rw [this]
  calc _ ≤ K₀ * ‖x‖ * (1 + Real.exp (2 * π * ξ.re)) ^ (1 + δT / (2 * π)) := h
    _ ≤ K₀ * ‖x‖ * ((1 + Real.exp (4 * π)) * Real.exp ((2 * π + δT) * ξ.re)) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

include hC0 hK₀ in
lemma h2_le (hδ : δ < 0) (x : QDom) (ξ : ℂ) :
    ‖h2 χT χN β x ξ‖ ≤ K₀ * ‖x‖ * Real.exp (δ * ξ.re) := by
  have hπ : 0 < 2 * π := by positivity
  have h := (hC0 x (Eexp ξ)).2
  rw [norm_Eexp] at h
  have hw := rpow_neg_le (div_neg_of_neg_of_pos hδ hπ).le ξ.re
  have e : 2 * π * (δ / (2 * π)) * ξ.re = δ * ξ.re := by field_simp
  rw [e] at hw
  have : h2 χT χN β x ξ = (pLc χT χN β (Eexp ξ) x).2 := by
    simp only [h2, hC_eq_pLc]
  rw [this]
  exact h.trans (mul_le_mul_of_nonneg_left hw (by positivity))

include hC0 hK₀ in
lemma τL_le (hδT : δT ∈ Set.Ioo (-(2 * π)) 0) (x : QDom) {ξ : ℂ} (hs : -2 ≤ ξ.re) :
    ‖τL χT χN β x ξ‖ ≤ K₀ * (1 + Real.exp (4 * π)) * ‖x‖ * Real.exp (δT * ξ.re) := by
  rw [τL, norm_div, norm_Eexp, div_le_iff₀ (Real.exp_pos _)]
  refine (h1_le hC0 hK₀ hδT x hs).trans (le_of_eq ?_)
  rw [mul_assoc _ (Real.exp (δT * ξ.re)), ← Real.exp_add]
  ring_nf

end C0

/-! ### The scales and the rescaled lift -/

variable (χT) in
/-- The tangential scale. -/
def μ1 (x : QDom) (s : ℝ) : ℝ := ‖x‖ * Real.exp (χT s - 2 * π * s)

variable (χT χN) in
/-- The scale ratio. -/
def rr (s : ℝ) : ℝ := Real.exp (χN s - χT s + 2 * π * s)

lemma μ1_mul_rr (x : QDom) (s : ℝ) : μ1 χT x s * rr χT χN s = ‖x‖ * Real.exp (χN s) := by
  rw [μ1, rr, mul_assoc, ← Real.exp_add]; ring_nf

lemma μ1_pos {x : QDom} (hx : 0 < ‖x‖) (s : ℝ) : 0 < μ1 χT x s := mul_pos hx (Real.exp_pos _)

lemma rr_pos (s : ℝ) : 0 < rr χT χN s := Real.exp_pos _

lemma uL_sub (x : QDom) (ξ : ℂ) : uL χT χN β x ξ - (ξ, 0) =
    (((2 * π : ℝ) : ℂ)⁻¹ * Complex.log (1 + τL χT χN β x ξ), h2 χT χN β x ξ) := by
  simp [uL]

lemma norm_vT_uL_le {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r) (x : QDom) {ξ : ℂ}
    (hτ : ‖τL χT χN β x ξ‖ ≤ 1 / 2) :
    ‖vT μ r (uL χT χN β x) ξ‖ ≤ μ⁻¹ * ‖τL χT χN β x ξ‖ + (μ * r)⁻¹ * ‖h2 χT χN β x ξ‖ := by
  have hlog := Complex.norm_log_one_add_half_le_self hτ
  have hπ : (1 : ℝ) < 2 * π := by nlinarith [Real.pi_gt_three]
  have h1 : ‖((2 * π : ℝ) : ℂ)⁻¹ * Complex.log (1 + τL χT χN β x ξ)‖ ≤ ‖τL χT χN β x ξ‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [inv_mul_le_iff₀ (by positivity)]
    have h32 : (3 / 2 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    exact hlog.trans (mul_le_mul_of_nonneg_right h32 (norm_nonneg _))
  rw [vT, uL_sub, dg_apply]
  have a1 : ‖μ⁻¹ • (((2 * π : ℝ) : ℂ)⁻¹ * Complex.log (1 + τL χT χN β x ξ))‖ ≤
      μ⁻¹ * ‖τL χT χN β x ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hμ)]
    exact mul_le_mul_of_nonneg_left h1 (inv_pos.2 hμ).le
  have a2 : ‖(μ * r)⁻¹ • h2 χT χN β x ξ‖ = (μ * r)⁻¹ * ‖h2 χT χN β x ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (mul_pos hμ hr))]
  have b1 := mul_nonneg (inv_pos.2 hμ).le (norm_nonneg (τL χT χN β x ξ))
  have b2 := mul_nonneg (inv_pos.2 (mul_pos hμ hr)).le (norm_nonneg (h2 χT χN β x ξ))
  refine norm_prod_le_iff.2 ⟨le_add_of_le_of_nonneg a1 b2, ?_⟩
  rw [a2]; exact le_add_of_nonneg_left b1

/-! ### The window bounds -/

lemma re_window {ξ₀ ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    ξ₀.re - 1 ≤ (ξ₀ + ζ).re ∧ (ξ₀ + ζ).re ≤ ξ₀.re + 1 := by
  have h := (Complex.abs_re_le_norm ζ).trans (mem_ball_zero_iff.1 hζ).le
  rw [Complex.add_re]
  constructor <;> linarith [neg_abs_le ζ.re, le_abs_self ζ.re]

set_option maxHeartbeats 1000000 in
/-- Smallness of the lift data, sup bound of the rescaled lift, and bounds of the scales. -/
theorem sup_window (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hC0 : ∀ (y : QDom) (z : ℂ),
      ‖(pLc χT χN β z y).1‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(pLc χT χN β z y).2‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π))) (hK₀ : 0 ≤ K₀) :
    ∃ ε > 0, ∃ Kτ ≥ 0, ∃ BV Bp : ℝ, ∀ x : QDom, 0 < ‖x‖ → ‖x‖ < ε → ∀ ξ₀ : ℂ, -1 ≤ ξ₀.re →
      (∀ ξ : ℂ, -2 ≤ ξ.re → ‖τL χT χN β x ξ‖ ≤ Kτ * ‖x‖ ∧ Kτ * ‖x‖ < 1 / 2 ∧
        ‖h2 χT χN β x ξ‖ < ρ / 4) ∧
      (∀ ζ ∈ ball (0 : ℂ) 1,
        ‖vT (μ1 χT x ξ₀.re) (rr χT χN ξ₀.re) (uL χT χN β x) (ξ₀ + ζ)‖ ≤ BV) ∧
      μ1 χT x ξ₀.re ≤ Bp * ‖x‖ ∧ rr χT χN ξ₀.re ≤ Bp := by
  have hδT' : δT ∈ Set.Ioo (-(2 * π)) 0 := ⟨(le_max_right _ _).trans_lt hδT.1, hδT.2⟩
  set A1 := K₀ * (1 + Real.exp (4 * π)) with hA1
  have hA1 : 0 ≤ A1 := by positivity
  set Kτ := A1 * Real.exp (-(2 * δT)) with hKτ
  have hKτ0 : 0 ≤ Kτ := by positivity
  set Kh := K₀ * Real.exp (-(2 * δ)) with hKh
  have hKh0 : 0 ≤ Kh := by positivity
  set ε : ℝ := 1 / (4 * (Kτ + 1)) ⊓ ρ / (8 * (Kh + 1)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨CT, hCT⟩ := lin_sub_upper hχT (-1)
  obtain ⟨CN, hCN⟩ := lin_sub_upper hχN (-1)
  obtain ⟨CM, hCM⟩ := weight_upper hχT (2 * π) (by linarith [hδT.2]) (-1)
  obtain ⟨CR, hCR⟩ := weight_diff_upper hχN hχT (2 * π) (by linarith [hδT.1, le_max_left δ (-(2 * π))]) (-1)
  refine ⟨ε, hε0, Kτ, hKτ0, A1 * Real.exp (-δT) * Real.exp CT + K₀ * Real.exp (-δ) * Real.exp CN,
    Real.exp CM + Real.exp CR, fun x hx hxε ξ₀ hs₀ => ?_⟩
  have hxε1 : ‖x‖ < 1 / (4 * (Kτ + 1)) := lt_of_lt_of_le hxε (min_le_left _ _)
  have hxε2 : ‖x‖ < ρ / (8 * (Kh + 1)) := lt_of_lt_of_le hxε (min_le_right _ _)
  have hsmall : ∀ ξ : ℂ, -2 ≤ ξ.re → ‖τL χT χN β x ξ‖ ≤ Kτ * ‖x‖ ∧ Kτ * ‖x‖ < 1 / 2 ∧
      ‖h2 χT χN β x ξ‖ < ρ / 4 := by
    intro ξ hs
    refine ⟨?_, ?_, ?_⟩
    · refine (τL_le hC0 hK₀ hδT' x hs).trans ?_
      have : Real.exp (δT * ξ.re) ≤ Real.exp (-(2 * δT)) :=
        Real.exp_le_exp.2 (by nlinarith [hδT.2])
      calc A1 * ‖x‖ * Real.exp (δT * ξ.re) ≤ A1 * ‖x‖ * Real.exp (-(2 * δT)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = Kτ * ‖x‖ := by rw [hKτ]; ring
    · have h4 : 4 * (Kτ + 1) * ‖x‖ < 1 := by
        rw [lt_div_iff₀ (by positivity)] at hxε1; linarith
      nlinarith [norm_nonneg x]
    · refine lt_of_le_of_lt (h2_le hC0 hK₀ hδ x ξ) ?_
      have : Real.exp (δ * ξ.re) ≤ Real.exp (-(2 * δ)) := Real.exp_le_exp.2 (by nlinarith)
      have h8 : 8 * (Kh + 1) * ‖x‖ < ρ := by
        rw [lt_div_iff₀ (by positivity)] at hxε2; linarith
      calc K₀ * ‖x‖ * Real.exp (δ * ξ.re) ≤ K₀ * ‖x‖ * Real.exp (-(2 * δ)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = Kh * ‖x‖ := by rw [hKh]; ring
        _ < ρ / 4 := by nlinarith [norm_nonneg x]
  refine ⟨hsmall, fun ζ hζ => ?_, ?_, ?_⟩
  · obtain ⟨hl, hu⟩ := re_window (ξ₀ := ξ₀) hζ
    set s := (ξ₀ + ζ).re with hsdef
    set s₀ := ξ₀.re with hs₀def
    have hs2 : -2 ≤ s := by linarith
    have hμ := μ1_pos (χT := χT) hx s₀
    have hr := rr_pos (χT := χT) (χN := χN) s₀
    obtain ⟨hτ1, hτ2, -⟩ := hsmall (ξ₀ + ζ) hs2
    refine (norm_vT_uL_le hμ hr x (hτ1.trans hτ2.le)).trans (add_le_add ?_ ?_)
    · -- tangential part
      have h := τL_le hC0 hK₀ hδT' x hs2
      calc (μ1 χT x s₀)⁻¹ * ‖τL χT χN β x (ξ₀ + ζ)‖
          ≤ (μ1 χT x s₀)⁻¹ * (A1 * ‖x‖ * Real.exp (δT * s)) :=
            mul_le_mul_of_nonneg_left h (inv_pos.2 hμ).le
        _ = A1 * Real.exp (δT * s - (χT s₀ - 2 * π * s₀)) := ratio_exp hx _ _ _
        _ ≤ A1 * (Real.exp (-δT) * Real.exp CT) := by
            refine mul_le_mul_of_nonneg_left ?_ hA1
            rw [← Real.exp_add]
            refine Real.exp_le_exp.2 ?_
            have := hCT s₀ hs₀
            nlinarith [hδT.2]
        _ = _ := by ring
    · -- normal part
      have h := h2_le hC0 hK₀ hδ x (ξ₀ + ζ)
      rw [μ1_mul_rr]
      calc (‖x‖ * Real.exp (χN s₀))⁻¹ * ‖h2 χT χN β x (ξ₀ + ζ)‖
          ≤ (‖x‖ * Real.exp (χN s₀))⁻¹ * (K₀ * ‖x‖ * Real.exp (δ * s)) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = K₀ * Real.exp (δ * s - χN s₀) := ratio_exp hx _ _ _
        _ ≤ K₀ * (Real.exp (-δ) * Real.exp CN) := by
            refine mul_le_mul_of_nonneg_left ?_ hK₀
            rw [← Real.exp_add]
            refine Real.exp_le_exp.2 ?_
            have := hCN ξ₀.re hs₀
            nlinarith
        _ = _ := by ring
  · have := hCM ξ₀.re hs₀
    rw [μ1]
    have h1 : Real.exp (χT ξ₀.re - 2 * π * ξ₀.re) ≤ Real.exp CM := Real.exp_le_exp.2 this
    have h2 : 0 ≤ Real.exp CR := (Real.exp_pos _).le
    nlinarith [norm_nonneg x]
  · have := hCR ξ₀.re hs₀
    rw [rr]
    have h1 : Real.exp (χN ξ₀.re - χT ξ₀.re + 2 * π * ξ₀.re) ≤ Real.exp CR :=
      Real.exp_le_exp.2 this
    linarith [Real.exp_pos CM]

end QR19

end

end FiniteEnergyPlane

-- FILE: NSK_N20.lean
/-!
# Q-N, layer 20 (local, NOT published): the `L⁴` factors and the linear part

Component selectors `QDom →L LpCyl 1 4`, their complex pairs in `L⁴(ℂ × ℂ)`, and the linear part
`Lin x = (χT' a1 + a2 + i a3, e^{-χN} β' c + χN' b1 + b2 + i b3)` as a continuous linear map.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal BoundedContinuousFunction

noncomputable section

namespace QN20

open QN QN18

/-! ### Selectors and factors -/

def c1 : Triple 1 4 →L[ℝ] LpCyl 1 4 := ContinuousLinearMap.fst ℝ _ _

/-! ### The fixed coefficients -/

lemma deriv_beta_zero {β : ℝ → ℝ} (hβ : IsLeftCutoff β) {s : ℝ} (hs : s < -1 ∨ 0 < s) :
    deriv β s = 0 := by
  rcases hs with hs | hs
  · have : β =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs] with y hy using hβ.2.1 y (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]
  · have : β =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hs] with y hy using hβ.2.2 y (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]

/-! ### The linear part -/

end QN20

end

end FiniteEnergyPlane

-- FILE: RSK_R19b.lean
/-!
# Q-R, layer 19b (local, NOT published): the `L⁴` window bound of the rescaled derivative

`deriv_window`: for a small zero `x` (smooth representatives) and a window centre `ξ₀` with
`Re ξ₀ ≥ -1`, `|Im ξ₀| ≤ 1/2`, where `‖τL‖ ≤ 1/2` on the window, the rescaled lift
`V ζ = vT μ1 rr (uL x) (ξ₀ + ζ)` is smooth on the unit disc and `‖DV‖_{L⁴(disc)} ≤ CS`,
with `CS` independent of `x` and `ξ₀`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic
open scoped ContDiff ENNReal NNReal Real

noncomputable section

namespace QR19

open QL QR QR3 QR8 QR13 QR14 QR15 QR16 QR17 QR18 QN19W QN18

variable {χT χN β : ℝ → ℝ} {δ δT : ℝ}

/-! ### Generic derivative bounds -/

lemma norm_fderiv_pair_le {f g : ℂ → ℂ} {ζ : ℂ} (hf : DifferentiableAt ℝ f ζ)
    (hg : DifferentiableAt ℝ g ζ) :
    ‖fderiv ℝ (fun ζ => (f ζ, g ζ)) ζ‖ ≤ ‖fderiv ℝ f ζ‖ + ‖fderiv ℝ g ζ‖ := by
  rw [(hf.hasFDerivAt.prodMk hg.hasFDerivAt).fderiv, ContinuousLinearMap.opNorm_prod,
    Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

lemma slit_of_half {τ : ℂ} (h : ‖τ‖ ≤ 1 / 2) : 1 + τ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 := Complex.abs_re_le_norm τ
  simp only [Complex.add_re, Complex.one_re]
  linarith [neg_abs_le τ.re]

lemma hasFDerivAt_log_one_add {τ : ℂ → ℂ} {ξ : ℂ} (hτ : DifferentiableAt ℝ τ ξ)
    (h : ‖τ ξ‖ ≤ 1 / 2) :
    HasFDerivAt (fun ξ => Complex.log (1 + τ ξ)) ((1 + τ ξ)⁻¹ • fderiv ℝ τ ξ) ξ := by
  have hl : HasDerivAt Complex.log (1 + τ ξ)⁻¹ (1 + τ ξ) :=
    (Complex.hasStrictDerivAt_log (slit_of_half h)).hasDerivAt
  exact hl.comp_hasFDerivAt ξ (hτ.hasFDerivAt.const_add 1)

lemma norm_fderiv_log_le {τ : ℂ → ℂ} {ξ : ℂ} (hτ : DifferentiableAt ℝ τ ξ)
    (h : ‖τ ξ‖ ≤ 1 / 2) :
    ‖fderiv ℝ (fun ξ => Complex.log (1 + τ ξ)) ξ‖ ≤ 2 * ‖fderiv ℝ τ ξ‖ := by
  rw [(hasFDerivAt_log_one_add hτ h).fderiv, norm_smul, norm_inv]
  have h1 : 1 / 2 ≤ ‖1 + τ ξ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-τ ξ)
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    linarith
  have h2 : ‖1 + τ ξ‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

lemma Eexp_inv (ξ : ℂ) : (Eexp ξ)⁻¹ = Eexp (-ξ) := by
  rw [Eexp, Eexp, mul_neg, Complex.exp_neg]

lemma norm_fderiv_Eexp_inv_le (ξ : ℂ) :
    ‖fderiv ℝ (fun ξ => (Eexp ξ)⁻¹) ξ‖ ≤ 2 * π * ‖(Eexp ξ)⁻¹‖ := by
  have e : (fun ξ => (Eexp ξ)⁻¹) = fun ξ => Eexp (-ξ) := funext Eexp_inv
  have hd : HasFDerivAt (fun ξ => Eexp (-ξ))
      (((ContinuousLinearMap.toSpanSingleton ℂ (Eexp (-ξ) * ((2 * π : ℝ) : ℂ))).restrictScalars
        ℝ).comp (-ContinuousLinearMap.id ℝ ℂ)) ξ :=
    (hasFDerivAt_Eexp (-ξ)).comp ξ (hasFDerivAt_id ξ).neg
  rw [e, hd.fderiv, Eexp_inv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have hpi : |π| = π := abs_of_pos Real.pi_pos
  try simp only [hpi, abs_two]
  exact le_of_eq (by ring)

lemma norm_fderiv_comp_cplx_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ × ℝ → E) (z : ℂ) : ‖fderiv ℝ (fun z => u (cplx z)) z‖ ≤ ‖fderiv ℝ u (cplx z)‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a => by
    rw [fderiv_comp_cplx]
    exact ((fderiv ℝ u (cplx z)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_cplx_le a) (norm_nonneg _))

/-! ### The lift data: derivative bounds -/

/-- The pointwise size of a representative and its partials. -/
def Gw (w : ↥(W1p 4 1)) (q : ℝ × ℝ) : ℝ :=
  ‖wrep w q‖ + ‖partialS (wrep w) q‖ + ‖partialT (wrep w) q‖

lemma Gw_nonneg (w : ↥(W1p 4 1)) (q : ℝ × ℝ) : 0 ≤ Gw w q := by unfold Gw; positivity

lemma continuous_Gw {w : ↥(W1p 4 1)} (hsm : ContDiff ℝ ∞ (wrep w)) : Continuous (Gw w) := by
  have hdc : Continuous (fderiv ℝ (wrep w)) := hsm.continuous_fderiv (by simp)
  exact ((hsm.continuous.norm.add (hdc.clm_apply continuous_const).norm).add
    (hdc.clm_apply continuous_const).norm)

lemma Gw_per (w : ↥(W1p 4 1)) (s t : ℝ) : Gw w (s, t + 1) = Gw w (s, t) := by
  have hper := (wrep_prop w).2.1
  have e : (fun q : ℝ × ℝ => wrep w (q + ((0 : ℝ), (1 : ℝ)))) = wrep w := by
    funext q; obtain ⟨a, b⟩ := q; simpa using hper a b
  have hf : fderiv ℝ (wrep w) ((s, t) + ((0 : ℝ), (1 : ℝ))) = fderiv ℝ (wrep w) (s, t) := by
    rw [← fderiv_comp_add_right, e]
  have e2 : ((s, t) + ((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) = (s, t + 1) := by simp
  rw [e2] at hf
  simp only [Gw, partialS, partialT, hf, hper]

lemma eLpNorm_Gw_le {w : ↥(W1p 4 1)} (hsm : ContDiff ℝ ∞ (wrep w)) :
    eLpNorm (Gw w) 4 cylMeasure ≤ ENNReal.ofReal (3 * ‖w‖) := by
  have hgc : Continuous (wrep w) := hsm.continuous
  have hdc : Continuous (fderiv ℝ (wrep w)) := hsm.continuous_fderiv (by simp)
  have m1 : AEStronglyMeasurable (fun q => ‖wrep w q‖) cylMeasure :=
    hgc.norm.aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun q => ‖partialS (wrep w) q‖) cylMeasure :=
    (hdc.clm_apply continuous_const).norm.aestronglyMeasurable
  have m3 : AEStronglyMeasurable (fun q => ‖partialT (wrep w) q‖) cylMeasure :=
    (hdc.clm_apply continuous_const).norm.aestronglyMeasurable
  have e : Gw w = ((fun q => ‖wrep w q‖) + fun q => ‖partialS (wrep w) q‖) +
      fun q => ‖partialT (wrep w) q‖ := rfl
  rw [e]
  refine (eLpNorm_add_le (m1.add m2) m3 (by norm_num)).trans ?_
  refine (add_le_add (eLpNorm_add_le m1 m2 (by norm_num)) le_rfl).trans ?_
  have b1 : eLpNorm (fun q => ‖wrep w q‖) 4 cylMeasure ≤ ENNReal.ofReal ‖w‖ := by
    rw [eLpNorm_norm]; exact eLpNorm_wrep_le w
  have b2 : eLpNorm (fun q => ‖partialS (wrep w) q‖) 4 cylMeasure ≤ ENNReal.ofReal ‖w‖ := by
    rw [eLpNorm_norm]; exact eLpNorm_partialS_le w hsm
  have b3 : eLpNorm (fun q => ‖partialT (wrep w) q‖) 4 cylMeasure ≤ ENNReal.ofReal ‖w‖ := by
    rw [eLpNorm_norm]; exact eLpNorm_partialT_le w hsm
  calc _ ≤ ENNReal.ofReal ‖w‖ + ENNReal.ofReal ‖w‖ + ENNReal.ofReal ‖w‖ := by gcongr
    _ = ENNReal.ofReal (3 * ‖w‖) := by
        rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
          ← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]
        congr 1; ring

lemma norm_vOf_le (χ : ℝ → ℝ) (g : ℝ × ℝ → Vec 1) (q : ℝ × ℝ) :
    ‖vOf χ g q‖ = Real.exp (χ q.1) * ‖g q‖ := by
  rw [vOf, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma h1_eq (x : QDom) : h1 χT χN β x = fun ξ => vL (vOf χT (wrep x.1) (cplx ξ)) := rfl

lemma h2_eq (x : QDom) : h2 χT χN β x =
    fun ξ => (fun q : ℝ × ℝ => β q.1 • x.2.1 + vL (vOf χN (wrep x.2.2) q)) (cplx ξ) := rfl

lemma norm_h1_le (x : QDom) (ξ : ℂ) :
    ‖h1 χT χN β x ξ‖ ≤ ‖vL‖ * (Real.exp (χT (cplx ξ).1) * Gw x.1 (cplx ξ)) := by
  rw [h1_eq]
  refine (vL.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [norm_vOf_le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  unfold Gw; linarith [norm_nonneg (partialS (wrep x.1) (cplx ξ)),
    norm_nonneg (partialT (wrep x.1) (cplx ξ))]

lemma norm_fderiv_h1_le (hχ : ContDiff ℝ ∞ χT) {x : QDom} (hw : ContDiff ℝ ∞ (wrep x.1))
    {L : ℝ} (hL : ∀ s, |deriv χT s| ≤ L) (ξ : ℂ) :
    ‖fderiv ℝ (h1 χT χN β x) ξ‖ ≤ ‖vL‖ * (Real.exp (χT (cplx ξ).1) * ((L + 1) * Gw x.1 (cplx ξ))) := by
  rw [h1_eq]
  refine (norm_fderiv_comp_cplx_le (fun q => vL (vOf χT (wrep x.1) q)) ξ).trans ?_
  refine (norm_fderiv_vL_le (vOf_contDiff hχ hw) _).trans
    (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine (norm_fderiv_vOf_le hχ hw _).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have h0 := hL (cplx ξ).1
  have hL0 : 0 ≤ L := (abs_nonneg _).trans h0
  have a := norm_nonneg (wrep x.1 (cplx ξ))
  have b := norm_nonneg (partialS (wrep x.1) (cplx ξ))
  have c := norm_nonneg (partialT (wrep x.1) (cplx ξ))
  unfold Gw
  nlinarith [mul_le_mul_of_nonneg_right h0 a]

lemma norm_fderiv_beta_le (hβ : ContDiff ℝ ∞ β) (c : ℂ) (q : ℝ × ℝ) :
    ‖fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q‖ ≤ |deriv β q.1| * ‖c‖ := by
  have hd : HasFDerivAt (fun q : ℝ × ℝ => β q.1 • c)
      ((deriv β q.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight c) q :=
    (((hβ.differentiable (by simp)) q.1).hasDerivAt.comp_hasFDerivAt q
      (hasFDerivAt_fst (𝕜 := ℝ) (p := q))).smul_const c
  rw [hd.fderiv, ContinuousLinearMap.norm_smulRight_apply]
  refine mul_le_mul_of_nonneg_right ((norm_smul_le (deriv β q.1)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)).trans ?_) (norm_nonneg _)
  rw [Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)

lemma norm_fderiv_h2_le (hχ : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β) {x : QDom}
    (hw : ContDiff ℝ ∞ (wrep x.2.2)) {L : ℝ} (hL : ∀ s, |deriv χN s| ≤ L) (ξ : ℂ) :
    ‖fderiv ℝ (h2 χT χN β x) ξ‖ ≤ |deriv β (cplx ξ).1| * ‖x.2.1‖ +
      ‖vL‖ * (Real.exp (χN (cplx ξ).1) * ((L + 1) * Gw x.2.2 (cplx ξ))) := by
  rw [h2_eq]
  refine (norm_fderiv_comp_cplx_le
    (fun q : ℝ × ℝ => β q.1 • x.2.1 + vL (vOf χN (wrep x.2.2) q)) ξ).trans ?_
  have hb : DifferentiableAt ℝ (fun q : ℝ × ℝ => β q.1 • x.2.1) (cplx ξ) :=
    ((hβ.comp contDiff_fst).smul contDiff_const).differentiable (by simp) _
  have hv : DifferentiableAt ℝ (fun q => vL (vOf χN (wrep x.2.2) q)) (cplx ξ) :=
    (vL.contDiff.comp (vOf_contDiff hχ hw)).differentiable (by simp) _
  rw [fderiv_fun_add hb hv]
  refine (norm_add_le _ _).trans (add_le_add (norm_fderiv_beta_le hβ _ _) ?_)
  refine (norm_fderiv_vL_le (vOf_contDiff hχ hw) _).trans
    (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine (norm_fderiv_vOf_le hχ hw _).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have h0 := hL (cplx ξ).1
  have a := norm_nonneg (wrep x.2.2 (cplx ξ))
  have b := norm_nonneg (partialS (wrep x.2.2) (cplx ξ))
  have c := norm_nonneg (partialT (wrep x.2.2) (cplx ξ))
  have hL0 : 0 ≤ L := (abs_nonneg _).trans h0
  unfold Gw
  nlinarith [mul_le_mul_of_nonneg_right h0 a]

lemma τL_eq (x : QDom) : τL χT χN β x = fun ξ => h1 χT χN β x ξ * (Eexp ξ)⁻¹ := by
  funext ξ; simp [τL, div_eq_mul_inv]

lemma norm_Eexp_inv (ξ : ℂ) : ‖(Eexp ξ)⁻¹‖ = Real.exp (-(2 * π * ξ.re)) := by
  rw [norm_inv, norm_Eexp, Real.exp_neg]

lemma norm_fderiv_τL_le (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)
    {x : QDom} (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2)) {L : ℝ}
    (hL : ∀ s, |deriv χT s| ≤ L) (ξ : ℂ) :
    ‖fderiv ℝ (τL χT χN β x) ξ‖ ≤ Real.exp (-(2 * π * ξ.re)) *
      (‖vL‖ * (Real.exp (χT (cplx ξ).1) * ((2 * π + L + 1) * Gw x.1 (cplx ξ)))) := by
  have hh : DifferentiableAt ℝ (h1 χT χN β x) ξ :=
    (contDiff_fst.comp (contDiff_hCc hχT hχN hβ hw1 hw2)).differentiable (by simp) _
  have hg : DifferentiableAt ℝ (fun ξ => (Eexp ξ)⁻¹) ξ := by
    rw [show (fun ξ => (Eexp ξ)⁻¹) = fun ξ => Eexp (-ξ) from funext Eexp_inv]
    exact (contDiff_Eexp.comp contDiff_neg).differentiable (by simp) _
  have hm := hh.hasFDerivAt.mul hg.hasFDerivAt
  rw [τL_eq, show (fun ξ => h1 χT χN β x ξ * (Eexp ξ)⁻¹) =
    h1 χT χN β x * (fun ξ => (Eexp ξ)⁻¹) from rfl, hm.fderiv]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  have e1 := norm_h1_le (χT := χT) (χN := χN) (β := β) x ξ
  have e2 := norm_fderiv_h1_le (χN := χN) (β := β) hχT hw1 hL ξ
  have e3 := norm_fderiv_Eexp_inv_le ξ
  rw [norm_Eexp_inv] at e3 ⊢
  have hE := Real.exp_pos (-(2 * π * ξ.re))
  have hG := Gw_nonneg x.1 (cplx ξ)
  have hv := norm_nonneg vL
  have hX := Real.exp_pos (χT (cplx ξ).1)
  set E := Real.exp (-(2 * π * ξ.re))
  set G := Gw x.1 (cplx ξ)
  set X := Real.exp (χT (cplx ξ).1)
  calc ‖h1 χT χN β x ξ‖ * ‖fderiv ℝ (fun ξ => (Eexp ξ)⁻¹) ξ‖ + E * ‖fderiv ℝ (h1 χT χN β x) ξ‖
      ≤ (‖vL‖ * (X * G)) * (2 * π * E) + E * (‖vL‖ * (X * ((L + 1) * G))) := by
        gcongr
    _ = E * (‖vL‖ * (X * ((2 * π + L + 1) * G))) := by ring

/-! ### The window derivative -/

lemma vT_uL_eq (μ r : ℝ) (x : QDom) (ξ₀ : ℂ) :
    (fun ζ => vT μ r (uL χT χN β x) (ξ₀ + ζ)) = fun ζ =>
      ((μ⁻¹ * (2 * π)⁻¹) • Complex.log (1 + τL χT χN β x (ξ₀ + ζ)),
        (μ * r)⁻¹ • h2 χT χN β x (ξ₀ + ζ)) := by
  funext ζ
  rw [vT, uL_sub, dg_apply]
  congr 1
  rw [Complex.real_smul, Complex.real_smul, ← mul_assoc]
  push_cast; ring

lemma cplx_re (ξ : ℂ) : (cplx ξ).1 = ξ.re := rfl

lemma exp_ratio_T {χ : ℝ → ℝ} {a b L : ℝ} (hχ : IsSlopeWeight χ a b) (hL : ∀ s, |deriv χ s| ≤ L)
    {X : ℝ} (hX : 0 < X) {s s₀ : ℝ} (hss : |s - s₀| ≤ 1) :
    Real.exp (-(2 * π * s)) * Real.exp (χ s) * (X * Real.exp (χ s₀ - 2 * π * s₀))⁻¹ ≤
      Real.exp (L + 2 * π) / X := by
  have hl1 := lip hχ hL s s₀
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have h3 : χ s - χ s₀ ≤ L := by
    have := (le_abs_self _).trans hl1
    nlinarith
  have h4 : -(2 * π * (s - s₀)) ≤ 2 * π := by
    have := neg_abs_le (s - s₀)
    nlinarith [Real.pi_pos]
  have e : Real.exp (-(2 * π * s)) * Real.exp (χ s) * (X * Real.exp (χ s₀ - 2 * π * s₀))⁻¹ =
      Real.exp ((χ s - χ s₀) + -(2 * π * (s - s₀))) / X := by
    rw [Real.exp_add, Real.exp_neg, Real.exp_sub, Real.exp_neg, Real.exp_sub]
    have : Real.exp (2 * π * (s - s₀)) = Real.exp (2 * π * s) / Real.exp (2 * π * s₀) := by
      rw [← Real.exp_sub]; ring_nf
    rw [this]
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hX.le

lemma exp_ratio_N {χ : ℝ → ℝ} {a b L : ℝ} (hχ : IsSlopeWeight χ a b) (hL : ∀ s, |deriv χ s| ≤ L)
    {X : ℝ} (hX : 0 < X) {s s₀ : ℝ} (hss : |s - s₀| ≤ 1) :
    (X * Real.exp (χ s₀))⁻¹ * Real.exp (χ s) ≤ Real.exp L / X := by
  have hl1 := lip hχ hL s s₀
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have h3 : χ s - χ s₀ ≤ L := by
    have := (le_abs_self _).trans hl1
    nlinarith
  have e : (X * Real.exp (χ s₀))⁻¹ * Real.exp (χ s) = Real.exp (χ s - χ s₀) / X := by
    rw [Real.exp_sub]; field_simp
  rw [e]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 h3) hX.le

lemma tang_bound (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : ContDiff ℝ ∞ χN)
    (hβ : ContDiff ℝ ∞ β) {L1 : ℝ} (hL1 : ∀ s, |deriv χT s| ≤ L1) {x : QDom} (hx : 0 < ‖x‖)
    (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2)) {s₀ : ℝ} {ξ : ℂ}
    (hss : |ξ.re - s₀| ≤ 1) (hτ : ‖τL χT χN β x ξ‖ ≤ 1 / 2) :
    |(μ1 χT x s₀)⁻¹ * (2 * π)⁻¹| * ‖fderiv ℝ (fun ξ => Complex.log (1 + τL χT χN β x ξ)) ξ‖ ≤
      (‖vL‖ * (2 * π + L1 + 1) / π * Real.exp (L1 + 2 * π)) / ‖x‖ * Gw x.1 (cplx ξ) := by
  have hμ : 0 < μ1 χT x s₀ := μ1_pos hx _
  rw [abs_of_pos (by positivity)]
  have hτd : DifferentiableAt ℝ (τL χT χN β x) ξ :=
    (contDiff_τL hχT.1 hχN hβ hw1 hw2).differentiable (by simp) _
  have h1 := norm_fderiv_log_le hτd hτ
  have h2 := norm_fderiv_τL_le hχT.1 hχN hβ hw1 hw2 hL1 ξ
  rw [cplx_re] at h2
  have hG := Gw_nonneg x.1 (cplx ξ)
  have hL10 : 0 ≤ L1 := (abs_nonneg _).trans (hL1 0)
  have hratio := exp_ratio_T hχT hL1 hx hss
  rw [← μ1] at hratio
  calc (μ1 χT x s₀)⁻¹ * (2 * π)⁻¹ * ‖fderiv ℝ (fun ξ => Complex.log (1 + τL χT χN β x ξ)) ξ‖
      ≤ (μ1 χT x s₀)⁻¹ * (2 * π)⁻¹ * (2 * (Real.exp (-(2 * π * ξ.re)) * (‖vL‖ *
          (Real.exp (χT ξ.re) * ((2 * π + L1 + 1) * Gw x.1 (cplx ξ)))))) := by
        gcongr; exact h1.trans (by gcongr)
    _ = (Real.exp (-(2 * π * ξ.re)) * Real.exp (χT ξ.re) * (μ1 χT x s₀)⁻¹) *
          (‖vL‖ * (2 * π + L1 + 1) / π * Gw x.1 (cplx ξ)) := by field_simp; try ring
    _ ≤ (Real.exp (L1 + 2 * π) / ‖x‖) * (‖vL‖ * (2 * π + L1 + 1) / π * Gw x.1 (cplx ξ)) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring

lemma norm_bound (hχN : IsSlopeWeight χN π δ) (hβ : IsLeftCutoff β) {L2 Lβ Bn : ℝ}
    (hL2 : ∀ s, |deriv χN s| ≤ L2) (hLβ : ∀ s, |deriv β s| ≤ Lβ)
    (hBn : ∀ s ∈ Icc (-2 : ℝ) 1, Real.exp (-χN s) ≤ Bn) {x : QDom} (hx : 0 < ‖x‖)
    (hw2 : ContDiff ℝ ∞ (wrep x.2.2)) {s₀ : ℝ} (hs₀ : -1 ≤ s₀) {ξ : ℂ}
    (hss : |ξ.re - s₀| ≤ 1) :
    |(μ1 χT x s₀ * rr χT χN s₀)⁻¹| * ‖fderiv ℝ (h2 χT χN β x) ξ‖ ≤
      (‖vL‖ * (L2 + 1) * Real.exp L2) / ‖x‖ * Gw x.2.2 (cplx ξ) + Lβ * Bn := by
  rw [μ1_mul_rr, abs_of_pos (by positivity)]
  have h1 := norm_fderiv_h2_le (χT := χT) hχN.1 hβ.1 hw2 hL2 ξ
  rw [cplx_re] at h1
  have hG := Gw_nonneg x.2.2 (cplx ξ)
  have hL20 : 0 ≤ L2 := (abs_nonneg _).trans (hL2 0)
  have hc : ‖x.2.1‖ ≤ ‖x‖ := (norm_fst_le x.2).trans (norm_snd_le x)
  have hβt : (‖x‖ * Real.exp (χN s₀))⁻¹ * (|deriv β ξ.re| * ‖x.2.1‖) ≤ Lβ * Bn := by
    rcases le_or_gt s₀ 1 with h | h
    · have hb := hBn s₀ ⟨by linarith, h⟩
      rw [mul_inv, ← Real.exp_neg]
      calc ‖x‖⁻¹ * Real.exp (-χN s₀) * (|deriv β ξ.re| * ‖x.2.1‖)
          = (|deriv β ξ.re| * Real.exp (-χN s₀)) * (‖x.2.1‖ * ‖x‖⁻¹) := by ring
        _ ≤ (Lβ * Bn) * 1 := by
            have hLβ0 : 0 ≤ Lβ := (abs_nonneg _).trans (hLβ 0)
            exact mul_le_mul (mul_le_mul (hLβ _) hb (Real.exp_pos _).le hLβ0)
              (by rw [mul_inv_le_iff₀ hx, one_mul]; exact hc) (by positivity)
              (mul_nonneg hLβ0 ((Real.exp_pos _).le.trans hb))
        _ = Lβ * Bn := mul_one _
    · have hd : deriv β ξ.re = 0 := QN20.deriv_beta_zero hβ (Or.inr (by
        have := neg_abs_le (ξ.re - s₀); linarith))
      rw [hd, abs_zero, zero_mul, mul_zero]
      have hBn0 : 0 ≤ Bn := (Real.exp_pos _).le.trans (hBn 0 ⟨by norm_num, by norm_num⟩)
      have hLβ0 : 0 ≤ Lβ := (abs_nonneg _).trans (hLβ 0)
      positivity
  have hratio := exp_ratio_N hχN hL2 hx hss
  calc (‖x‖ * Real.exp (χN s₀))⁻¹ * ‖fderiv ℝ (h2 χT χN β x) ξ‖
      ≤ (‖x‖ * Real.exp (χN s₀))⁻¹ * (|deriv β ξ.re| * ‖x.2.1‖ +
          ‖vL‖ * (Real.exp (χN ξ.re) * ((L2 + 1) * Gw x.2.2 (cplx ξ)))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (‖x‖ * Real.exp (χN s₀))⁻¹ * (|deriv β ξ.re| * ‖x.2.1‖) +
          ((‖x‖ * Real.exp (χN s₀))⁻¹ * Real.exp (χN ξ.re)) *
            (‖vL‖ * (L2 + 1) * Gw x.2.2 (cplx ξ)) := by ring
    _ ≤ Lβ * Bn + (Real.exp L2 / ‖x‖) * (‖vL‖ * (L2 + 1) * Gw x.2.2 (cplx ξ)) :=
        add_le_add hβt (mul_le_mul_of_nonneg_right hratio (by positivity))
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- The pointwise derivative bound on the window. -/
lemma norm_fderiv_V_le (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) {L1 L2 Lβ Bn : ℝ} (hL1 : ∀ s, |deriv χT s| ≤ L1)
    (hL2 : ∀ s, |deriv χN s| ≤ L2) (hLβ : ∀ s, |deriv β s| ≤ Lβ)
    (hBn : ∀ s ∈ Icc (-2 : ℝ) 1, Real.exp (-χN s) ≤ Bn) {x : QDom} (hx : 0 < ‖x‖)
    (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2)) {ξ₀ : ℂ}
    (hs₀ : -1 ≤ ξ₀.re) {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1)
    (hτ : ‖τL χT χN β x (ξ₀ + ζ)‖ ≤ 1 / 2) :
    ‖fderiv ℝ (fun ζ => vT (μ1 χT x ξ₀.re) (rr χT χN ξ₀.re) (uL χT χN β x) (ξ₀ + ζ)) ζ‖ ≤
      (‖vL‖ * (2 * π + L1 + 1) / π * Real.exp (L1 + 2 * π)) / ‖x‖ * Gw x.1 (cplx (ξ₀ + ζ)) +
      ((‖vL‖ * (L2 + 1) * Real.exp L2) / ‖x‖ * Gw x.2.2 (cplx (ξ₀ + ζ)) + Lβ * Bn) := by
  obtain ⟨hl, hu⟩ := re_window (ξ₀ := ξ₀) hζ
  have hss : |(ξ₀ + ζ).re - ξ₀.re| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hτd : DifferentiableAt ℝ (τL χT χN β x) (ξ₀ + ζ) :=
    (contDiff_τL hχT.1 hχN.1 hβ.1 hw1 hw2).differentiable (by simp) _
  have hh2d : DifferentiableAt ℝ (h2 χT χN β x) (ξ₀ + ζ) :=
    (contDiff_snd.comp (contDiff_hCc hχT.1 hχN.1 hβ.1 hw1 hw2)).differentiable (by simp) _
  have hlogd : DifferentiableAt ℝ (fun ξ => Complex.log (1 + τL χT χN β x ξ)) (ξ₀ + ζ) :=
    (hasFDerivAt_log_one_add hτd hτ).differentiableAt
  have hT : DifferentiableAt ℝ (fun ζ => Complex.log (1 + τL χT χN β x (ξ₀ + ζ))) ζ :=
    hlogd.comp ζ (differentiableAt_id.const_add ξ₀)
  have hH : DifferentiableAt ℝ (fun ζ => h2 χT χN β x (ξ₀ + ζ)) ζ :=
    hh2d.comp ζ (differentiableAt_id.const_add ξ₀)
  rw [vT_uL_eq]
  refine (norm_fderiv_pair_le (hT.const_smul ((μ1 χT x ξ₀.re)⁻¹ * (2 * π)⁻¹))
    (hH.const_smul (μ1 χT x ξ₀.re * rr χT χN ξ₀.re)⁻¹)).trans ?_
  rw [fderiv_const_smul hT, fderiv_const_smul hH, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs,
    fderiv_comp_add_left (f := fun ξ => Complex.log (1 + τL χT χN β x ξ)),
    fderiv_comp_add_left (f := h2 χT χN β x)]
  exact add_le_add (tang_bound hχT hχN.1 hβ.1 hL1 hx hw1 hw2 hss hτ)
    (norm_bound hχN hβ hL2 hLβ hBn hx hw2 hs₀ hss)

/-! ### Smoothness and the `L⁴` bound on the window -/

lemma contDiffAt_V (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)
    {x : QDom} (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2)) (μ r : ℝ)
    {ξ₀ ζ : ℂ} (hτ : ‖τL χT χN β x (ξ₀ + ζ)‖ < 1) :
    ContDiffAt ℝ ∞ (fun ζ => vT μ r (uL χT χN β x) (ξ₀ + ζ)) ζ := by
  have ht : ContDiffAt ℝ ∞ (fun ζ : ℂ => ξ₀ + ζ) ζ := contDiffAt_const.add contDiffAt_id
  have h := (contDiffAt_uL hχT hχN hβ hw1 hw2 hτ).comp ζ ht
  have h2 : ContDiffAt ℝ ∞ (fun ζ => uL χT χN β x (ξ₀ + ζ) - (ξ₀ + ζ, (0 : ℂ))) ζ :=
    h.sub (ht.prodMk contDiffAt_const)
  exact (dg μ⁻¹ (μ * r)⁻¹).contDiff.contDiffAt.comp ζ h2

lemma enn_bound {A X : ℝ} (hA : 0 ≤ A) (hX : 0 < X) {E : ℝ≥0∞}
    (hE : E ≤ 2 * ENNReal.ofReal (3 * X)) : ENNReal.ofReal (A / X) * E ≤ ENNReal.ofReal (6 * A) := by
  calc _ ≤ ENNReal.ofReal (A / X) * (2 * ENNReal.ofReal (3 * X)) := by gcongr
    _ = ENNReal.ofReal (6 * A) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp; ring

lemma window_term {w : ↥(W1p 4 1)} (hsm : ContDiff ℝ ∞ (wrep w)) {X A : ℝ} (hX : 0 < X)
    (hA : 0 ≤ A) (hwX : ‖w‖ ≤ X) {ξ₀ : ℂ} (ht : |ξ₀.im| ≤ 1 / 2) :
    eLpNorm (fun ζ => A / X * Gw w (cplx (ξ₀ + ζ))) 4 (volume.restrict (ball (0 : ℂ) 1)) ≤
      ENNReal.ofReal (6 * A) := by
  have e : (fun ζ => A / X * Gw w (cplx (ξ₀ + ζ))) = (A / X) • fun ζ => Gw w (cplx (ξ₀ + ζ)) := rfl
  rw [e, eLpNorm_smul_real _ (by positivity)]
  refine enn_bound hA hX ((eLpNorm_window_le (continuous_Gw hsm) (Gw_per w) ht).trans ?_)
  gcongr
  exact (eLpNorm_Gw_le hsm).trans (ENNReal.ofReal_le_ofReal (by linarith))

lemma eLpNorm_const_ball_ne_top (c : ℝ) :
    eLpNorm (fun _ : ℂ => c) 4 (volume.restrict (ball (0 : ℂ) 1)) ≠ ⊤ := by
  refine (eLpNorm_const_lt_top_iff (by norm_num) (by simp)).2 (Or.inr ?_) |>.ne
  rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top

/-- The `L⁴` window bound of the derivative of the rescaled lift. -/
theorem deriv_window (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ CS : ℝ≥0∞, CS ≠ ⊤ ∧ ∀ x : QDom, 0 < ‖x‖ → ContDiff ℝ ∞ (wrep x.1) →
      ContDiff ℝ ∞ (wrep x.2.2) → ∀ ξ₀ : ℂ, -1 ≤ ξ₀.re → |ξ₀.im| ≤ 1 / 2 →
      (∀ ζ ∈ ball (0 : ℂ) 1, ‖τL χT χN β x (ξ₀ + ζ)‖ ≤ 1 / 2) →
      eLpNorm (fderiv ℝ (fun ζ => vT (μ1 χT x ξ₀.re) (rr χT χN ξ₀.re) (uL χT χN β x) (ξ₀ + ζ)))
        4 (volume.restrict (ball (0 : ℂ) 1)) ≤ CS := by
  obtain ⟨L1, hL10, hL1⟩ := QN18.deriv_bdd hχT
  obtain ⟨L2, hL20, hL2⟩ := QN18.deriv_bdd hχN
  obtain ⟨Mb, hMb⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 0)).exists_bound_of_continuousOn
    (hβ.1.continuous_deriv (by simp)).continuousOn
  have hLβ : ∀ s, |deriv β s| ≤ max Mb 0 := by
    intro s
    by_cases hs : s ∈ Icc (-1 : ℝ) 0
    · have := hMb s hs; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
    · have : s < -1 ∨ 0 < s := by
        simp only [mem_Icc, not_and_or, not_le] at hs; exact hs
      rw [QN20.deriv_beta_zero hβ this, abs_zero]; exact le_max_right _ _
  obtain ⟨Bn0, hBn0⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((Real.continuous_exp.comp hχN.1.continuous.neg)).continuousOn
  have hBn : ∀ s ∈ Icc (-2 : ℝ) 1, Real.exp (-χN s) ≤ Bn0 := fun s hs => by
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hBn0 s hs
  set A1 := ‖vL‖ * (2 * π + L1 + 1) / π * Real.exp (L1 + 2 * π) with hA1
  set A2 := ‖vL‖ * (L2 + 1) * Real.exp L2 with hA2
  set c := max Mb 0 * Bn0 with hc
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  refine ⟨ENNReal.ofReal (6 * A1) + (ENNReal.ofReal (6 * A2) +
    eLpNorm (fun _ : ℂ => c) 4 (volume.restrict (ball (0 : ℂ) 1))),
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, eLpNorm_const_ball_ne_top c⟩⟩,
    fun x hx hw1 hw2 ξ₀ hs₀ ht hτ => ?_⟩
  set μv := volume.restrict (ball (0 : ℂ) 1) with hμv
  have hpt : ∀ᵐ ζ ∂μv, ‖fderiv ℝ (fun ζ => vT (μ1 χT x ξ₀.re) (rr χT χN ξ₀.re)
      (uL χT χN β x) (ξ₀ + ζ)) ζ‖ ≤ A1 / ‖x‖ * Gw x.1 (cplx (ξ₀ + ζ)) +
        (A2 / ‖x‖ * Gw x.2.2 (cplx (ξ₀ + ζ)) + c) :=
    (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun ζ hζ =>
      norm_fderiv_V_le hχT hχN hβ hL1 hL2 hLβ hBn hx hw1 hw2 hs₀ hζ (hτ ζ hζ))
  refine (eLpNorm_mono_ae_real hpt).trans ?_
  have hcx : Continuous fun ζ : ℂ => cplx (ξ₀ + ζ) :=
    Complex.equivRealProdCLM.continuous.comp (continuous_const.add continuous_id)
  have m1 : AEStronglyMeasurable (fun ζ => A1 / ‖x‖ * Gw x.1 (cplx (ξ₀ + ζ))) μv :=
    (continuous_const.mul ((continuous_Gw hw1).comp hcx)).aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun ζ => A2 / ‖x‖ * Gw x.2.2 (cplx (ξ₀ + ζ))) μv :=
    (continuous_const.mul ((continuous_Gw hw2).comp hcx)).aestronglyMeasurable
  have m3 : AEStronglyMeasurable (fun _ : ℂ => c) μv := aestronglyMeasurable_const
  refine (eLpNorm_add_le (p := 4) m1 (m2.add m3) (by norm_num)).trans ?_
  refine add_le_add (window_term hw1 hx hA10 (norm_fst_le x) ht) ?_
  refine (eLpNorm_add_le (p := 4) m2 m3 (by norm_num)).trans (add_le_add ?_ le_rfl)
  exact window_term hw2 hx hA20 ((norm_snd_le x.2).trans (norm_snd_le x)) ht

end QR19

end

end FiniteEnergyPlane

-- FILE: RSK_R21.lean
/-!
# Q-R, layer 21 (local, NOT published): `C^∞_loc` convergence of the two-scale structures

* `tendsto_of_sub`, `sub_small`: `C^∞_loc` convergence on `univ` via the differences.
* `Hc_eq`, `Hc_sub`, `tendsto_Hc`: the `w`-divided difference `Hc` is continuous for `C^∞_loc`
  convergence on `univ`.
* `tendsto_TS`: hence so is the two-scale structure `TS`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology JHolomorphic
open scoped ContDiff ENNReal NNReal Real

noncomputable section

namespace QR21

open QR11 QR16

/-! ### Criteria -/

section Crit

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

lemma tendsto_of_sub {f : ℕ → X → Y} {g : X → Y} (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hg : ContDiff ℝ ∞ g)
    (h : ∀ K : Set X, IsCompact K → ∀ m : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (f n - g) x‖ < ε) :
    TendstoCInftyLocOn f g univ := by
  intro K _ hK m
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h K hK m ε hε] with n hn x hx
  rw [dist_eq_norm, ← norm_neg, neg_sub, ← iteratedFDeriv_sub_apply
    ((hf n).contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact hn x hx

lemma sub_small {f : ℕ → X → Y} {g : X → Y} (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hg : ContDiff ℝ ∞ g) (h : TendstoCInftyLocOn f g univ) {K : Set X} (hK : IsCompact K)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f n - g) x‖ < ε := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (h K (subset_univ _) hK m) ε hε] with n hn x hx
  have := hn x hx
  rw [dist_eq_norm, ← norm_neg, neg_sub, ← iteratedFDeriv_sub_apply
    ((hf n).contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.contDiffAt.of_le (by exact_mod_cast le_top))] at this
  exact this

lemma tendsto_const' (g : X → Y) (O : Set X) : TendstoCInftyLocOn (fun _ : ℕ => g) g O :=
  fun _ _ _ _ => Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun _ x _ => by
    simpa using hε

end Crit

/-! ### The divided difference -/

section Hc

variable {K : ℂ × ℂ → CL}

/-- The integrand of `Hc`. -/
def FK (D : ℂ × ℂ → CL) (y : ℂ × ℂ × ℂ) (θ : ℝ) : CL :=
  fderiv ℝ D (y.1, θ • y.2.1) (0, y.2.2)

lemma fderiv_partial (hK : ContDiff ℝ ∞ K) (a : ℂ) :
    fderiv ℝ (fun w => K (a, w)) = fun p => (fderiv ℝ K (a, p)).comp
      (ContinuousLinearMap.inr ℝ ℂ ℂ) := by
  funext p
  exact ((hK.differentiable (by simp) _).hasFDerivAt.comp p (hasFDerivAt_prodMk_right a p)).fderiv

lemma continuous_FK (hK : ContDiff ℝ ∞ K) (y : ℂ × ℂ × ℂ) : Continuous (FK K y) :=
  ((hK.continuous_fderiv (by simp)).comp
    (continuous_const.prodMk (continuous_id.smul continuous_const))).clm_apply continuous_const

lemma Hc_eq (hK : ContDiff ℝ ∞ K) (y : ℂ × ℂ × ℂ) : Hc K y = ∫ θ in (0 : ℝ)..1, FK K y θ := by
  have hc : Continuous fun θ : ℝ => (fderiv ℝ K (y.1, θ • y.2.1)).comp
      (ContinuousLinearMap.inr ℝ ℂ ℂ) :=
    ((hK.continuous_fderiv (by simp)).comp
      (continuous_const.prodMk (continuous_id.smul continuous_const))).clm_comp continuous_const
  simp only [Hc, Hg, fderiv_partial hK]
  rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1)]
  rfl

lemma Hc_sub {K₁ K₂ : ℂ × ℂ → CL} (h₁ : ContDiff ℝ ∞ K₁) (h₂ : ContDiff ℝ ∞ K₂) :
    Hc K₁ - Hc K₂ = Hc (K₁ - K₂) := by
  funext y
  rw [Pi.sub_apply, Hc_eq h₁, Hc_eq h₂, Hc_eq (K := K₁ - K₂) (h₁.sub h₂),
    ← intervalIntegral.integral_sub ((continuous_FK h₁ y).intervalIntegrable 0 1)
      ((continuous_FK h₂ y).intervalIntegrable 0 1)]
  congr 1
  funext θ
  simp only [FK]
  rw [fderiv_sub (h₁.differentiable (by simp) _) (h₂.differentiable (by simp) _)]
  rfl

/-- The linear map `y ↦ (y.1, θ y.2.1)`. -/
def Lθ (θ : ℝ) : ℂ × ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  (ContinuousLinearMap.fst ℝ ℂ (ℂ × ℂ)).prod
    (θ • (ContinuousLinearMap.fst ℝ ℂ ℂ).comp (ContinuousLinearMap.snd ℝ ℂ (ℂ × ℂ)))

/-- The linear map `y ↦ (0, y.2.2)`. -/
def Mv : ℂ × ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  (ContinuousLinearMap.inr ℝ ℂ ℂ).comp
    ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp (ContinuousLinearMap.snd ℝ ℂ (ℂ × ℂ)))

lemma norm_Lθ_apply_le {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (y : ℂ × ℂ × ℂ) : ‖Lθ θ y‖ ≤ ‖y‖ := by
  have h1 : ‖y.1‖ ≤ ‖y‖ := norm_fst_le y
  have h2 : ‖y.2.1‖ ≤ ‖y‖ := (norm_fst_le y.2).trans (norm_snd_le y)
  have : ‖θ • y.2.1‖ ≤ ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    nlinarith [norm_nonneg y.2.1, hθ.2]
  exact norm_prod_le_iff.2 ⟨h1, by simpa [Lθ] using this⟩

lemma norm_Lθ_le {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) : ‖Lθ θ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul]; exact norm_Lθ_apply_le hθ y

lemma FK_eq (D : ℂ × ℂ → CL) (θ : ℝ) :
    (fun y => FK D y θ) = fun y => (fderiv ℝ D (Lθ θ y)) (Mv y) := by
  funext y; rfl

/-- The bound for the integrand. -/
lemma norm_iteratedFDeriv_FK_le {D : ℂ × ℂ → CL} (hD : ContDiff ℝ ∞ D) (k : ℕ) {θ : ℝ}
    (hθ : θ ∈ Icc (0 : ℝ) 1) (y : ℂ × ℂ × ℂ) {η : ℝ}
    (hη : ∀ i ≤ k, ‖iteratedFDeriv ℝ (i + 1) D (Lθ θ y)‖ ≤ η) {B : ℝ}
    (hB : ∀ i ≤ k, ‖iteratedFDeriv ℝ i Mv y‖ ≤ B) (hη0 : 0 ≤ η) (hB0 : 0 ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y => FK D y θ) y‖ ≤ 2 ^ k * η * B := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ D) := hD.fderiv_right (m := ∞) (by simp)
  have hf : ContDiff ℝ ∞ (fun y => fderiv ℝ D (Lθ θ y)) := hfd.comp (Lθ θ).contDiff
  rw [FK_eq]
  refine (norm_iteratedFDeriv_clm_apply hf Mv.contDiff y (by exact_mod_cast le_top)).trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ D (Lθ θ y)) y‖ *
        ‖iteratedFDeriv ℝ (k - i) Mv y‖ ≤ (k.choose i : ℝ) * η * B := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have e : (fun y => fderiv ℝ D (Lθ θ y)) = fderiv ℝ D ∘ Lθ θ := rfl
    have h1 : ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ D (Lθ θ y)) y‖ ≤ η := by
      rw [e, (Lθ θ).iteratedFDeriv_comp_right hfd y (by exact_mod_cast le_top)]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      have hp : ∏ _ : Fin i, ‖Lθ θ‖ ≤ 1 :=
        Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_Lθ_le hθ
      rw [norm_iteratedFDeriv_fderiv]
      calc _ ≤ ‖iteratedFDeriv ℝ (i + 1) D (Lθ θ y)‖ * 1 :=
            mul_le_mul_of_nonneg_left hp (norm_nonneg _)
        _ ≤ η := by rw [mul_one]; exact hη i hik
    have h2 := hB (k - i) (Nat.sub_le k i)
    have hc : (0 : ℝ) ≤ k.choose i := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _) (by positivity)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hs : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [hs]

lemma contDiff_uncurry_FK {D : ℂ × ℂ → CL} (hD : ContDiff ℝ ∞ D) :
    ContDiff ℝ ∞ (Function.uncurry (FK D)) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ D) := hD.fderiv_right (m := ∞) (by simp)
  have hL : ContDiff ℝ ∞ (fun p : (ℂ × ℂ × ℂ) × ℝ => ((p.1.1, p.2 • p.1.2.1) : ℂ × ℂ)) :=
    (contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_snd.smul (contDiff_fst.comp (contDiff_snd.comp contDiff_fst)))
  have hM : ContDiff ℝ ∞ (fun p : (ℂ × ℂ × ℂ) × ℝ => (((0 : ℂ), p.1.2.2) : ℂ × ℂ)) :=
    contDiff_const.prodMk (contDiff_snd.comp (contDiff_snd.comp contDiff_fst))
  exact (hfd.comp hL).clm_apply hM

/-- `Hc` is continuous for `C^∞_loc` convergence on `univ`. -/
theorem tendsto_Hc {Kn : ℕ → ℂ × ℂ → CL} (hKn : ∀ n, ContDiff ℝ ∞ (Kn n))
    (hK : ContDiff ℝ ∞ K) (h : TendstoCInftyLocOn Kn K univ) :
    TendstoCInftyLocOn (fun n => Hc (Kn n)) (Hc K) univ := by
  refine tendsto_of_sub (fun n => contDiff_Hc (hKn n)) (contDiff_Hc hK) fun S hS k ε hε => ?_
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall 0
  -- bound for the derivatives of `Mv` on `S`
  obtain ⟨B, hB0, hB⟩ : ∃ B ≥ 0, ∀ y ∈ S, ∀ i ≤ k, ‖iteratedFDeriv ℝ i Mv y‖ ≤ B := by
    have hc : ∀ i, ∃ C, ∀ y ∈ S, ‖iteratedFDeriv ℝ i Mv y‖ ≤ C := fun i => by
      obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn
        (Mv.contDiff.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).continuousOn
      exact ⟨C, fun y hy => by simpa using hC y hy⟩
    choose C hC using hc
    refine ⟨∑ i ∈ Finset.range (k + 1), |C i|, by positivity, fun y hy i hi => ?_⟩
    exact (hC i y hy).trans ((le_abs_self _).trans (Finset.single_le_sum
      (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))))
  set η : ℝ := ε / (2 * (2 ^ k * (B + 1))) with hηdef
  have hη : 0 < η := by positivity
  have hsm : ∀ n, ContDiff ℝ ∞ (Kn n - K) := fun n => (hKn n).sub hK
  have hev : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k + 1), ∀ q ∈ closedBall (0 : ℂ × ℂ) R,
      ‖iteratedFDeriv ℝ (i + 1) (Kn n - K) q‖ < η := by
    rw [eventually_all_finset]
    intro i _
    exact sub_small hKn hK h (isCompact_closedBall 0 R) (i + 1) hη
  filter_upwards [hev] with n hn y hy
  rw [Hc_sub (hKn n) hK]
  have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.1 (hR hy)
  have hint : ∀ θ ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ k (fun y => FK (Kn n - K) y θ) y‖ ≤ 2 ^ k * η * B := by
    intro θ hθ
    refine norm_iteratedFDeriv_FK_le (hsm n) k hθ y (fun i hi => ?_) (hB y hy) hη.le hB0
    refine (hn i (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) _ ?_).le
    exact mem_closedBall_zero_iff.2 ((norm_Lθ_apply_le hθ y).trans hyR)
  have heq : Hc (Kn n - K) = fun y => ∫ θ in (0 : ℝ)..1, FK (Kn n - K) y θ :=
    funext (Hc_eq (hsm n))
  rw [heq]
  refine lt_of_le_of_lt (norm_iteratedFDeriv_intervalIntegral_le
    (contDiff_uncurry_FK (hsm n)) k y _ hint) ?_
  have hBB : B < B + 1 := by linarith
  calc 2 ^ k * η * B ≤ 2 ^ k * η * (B + 1) := by gcongr
    _ = ε / 2 := by rw [hηdef]; field_simp
    _ < ε := by linarith

end Hc

/-! ### The two-scale structure -/

lemma norm_inr_le' : ‖ContinuousLinearMap.inr ℝ TE CL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp

/-- `TS` is continuous for `C^∞_loc` convergence on `univ`. -/
theorem tendsto_TS {K : ℂ × ℂ → CL} {Kn : ℕ → ℂ × ℂ → CL} (hKn : ∀ n, ContDiff ℝ ∞ (Kn n))
    (hK : ContDiff ℝ ∞ K) (h : TendstoCInftyLocOn Kn K univ) :
    TendstoCInftyLocOn (fun n => TS (Kn n)) (TS K) univ := by
  have hHc := tendsto_Hc hKn hK h
  have hgT : TendstoCInftyLocOn (fun n => gT (Kn n)) (gT K) univ :=
    tendstoCInftyLocOn_comp isOpen_univ isOpen_univ (fun _ => iT) iT (fun n => Hc (Kn n)) (Hc K)
      (fun _ => contDiff_iT.contDiffOn) contDiff_iT.contDiffOn
      (fun n => (contDiff_Hc (hKn n)).contDiffOn) (contDiff_Hc hK).contDiffOn
      (fun _ => mapsTo_univ _ _) (mapsTo_univ _ _) (tendsto_const' _ _) hHc
  have hgn : ∀ n, ContDiff ℝ ∞ (gT (Kn n)) := fun n => contDiff_gT (hKn n)
  have hg : ContDiff ℝ ∞ (gT K) := contDiff_gT hK
  have hpair : TendstoCInftyLocOn (fun n (e : TE) => (e, gT (Kn n) e)) (fun e => (e, gT K e))
      univ := by
    refine tendsto_of_sub (fun n => contDiff_id.prodMk (hgn n)) (contDiff_id.prodMk hg)
      fun S hS m ε hε => ?_
    filter_upwards [sub_small hgn hg hgT hS m hε] with n hn x hx
    have e : ((fun e : TE => (e, gT (Kn n) e)) - fun e => (e, gT K e)) =
        (ContinuousLinearMap.inr ℝ TE CL) ∘ (gT (Kn n) - gT K) := by
      funext e; simp
    rw [e]
    refine lt_of_le_of_lt ((ContinuousLinearMap.inr ℝ TE CL).norm_iteratedFDeriv_comp_left
      (((hgn n).sub hg).contDiffAt) (by exact_mod_cast le_top)) ?_
    calc _ ≤ 1 * ‖iteratedFDeriv ℝ m (gT (Kn n) - gT K) x‖ :=
          mul_le_mul_of_nonneg_right norm_inr_le' (norm_nonneg _)
      _ < ε := by rw [one_mul]; exact hn x hx
  exact tendstoCInftyLocOn_comp isOpen_univ isOpen_univ (fun n (e : TE) => (e, gT (Kn n) e))
    (fun e => (e, gT K e)) (fun _ => Φ) Φ (fun n => (contDiff_id.prodMk (hgn n)).contDiffOn)
    (contDiff_id.prodMk hg).contDiffOn (fun _ => contDiff_Φ.contDiffOn) contDiff_Φ.contDiffOn
    (fun _ => mapsTo_univ _ _) (mapsTo_univ _ _) hpair (tendsto_const' _ _)

/-! ### The limit structure at `+∞` -/

section Inf

open QR17

variable {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}

variable (ρ Jinf) in
/-- The globalized limit structure. -/
def Kinf (y : ℂ × ℂ) : CL := Jinf (y.1.im, rtr ρ y.2)

lemma contDiff_Kinf (hρ : 0 < ρ) (hJi : ContDiffOn ℝ ∞ Jinf (univ ×ˢ ball (0 : ℂ) ρ)) :
    ContDiff ℝ ∞ (Kinf ρ Jinf) := by
  have h : ContDiff ℝ ∞ (fun y : ℂ × ℂ => ((y.1.im, rtr ρ y.2) : ℝ × ℂ)) :=
    (Complex.imCLM.contDiff.comp contDiff_fst).prodMk ((rtr_contDiff ρ).comp contDiff_snd)
  exact hJi.comp_contDiff h fun y => ⟨mem_univ _, mem_ball_zero_iff.2 (norm_rtr_lt hρ _)⟩

/-- The difference in the decay hypothesis. -/
def fd (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (q : ℝ × ℝ × ℂ) : CL := cylJ Jbar q.1 q.2.1 q.2.2 - Jinf (q.2.1, q.2.2)

lemma tendsto_cylJ (hb : 0 < b) (hdec : ExpDecayCInftyTube (fd Jbar Jinf) ρ b) (t : ℝ) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) ρ) :
    Tendsto (fun s => cylJ Jbar s t w) atTop (𝓝 (Jinf (t, w))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨C, s₁, hC⟩ := hdec.2 0
  have ht : Tendsto (fun s : ℝ => C * Real.exp (-(b * s))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hb)).const_mul C
    simpa [Function.comp_def] using this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_atTop.2 ⟨s₁, fun s hs => ?_⟩) ht
  have := hC s hs t w hw
  simpa [norm_iteratedFDeriv_zero, fd] using this

lemma cylJ_sq (hsq : ∀ p ∈ univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (s t : ℝ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) (v : ℂ × ℂ) :
    cylJ Jbar s t w (cylJ Jbar s t w v) = -v := by
  have h := congrArg (fun L : ℂ × ℂ →L[ℝ] ℂ × ℂ => L (cylScale s t v))
    (hsq (cylInf s t, w) ⟨mem_univ _, hw⟩)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply] at h
  simp only [cylJ, ContinuousLinearMap.comp_apply, cylScale_cylScaleInv, h, map_neg,
    cylScaleInv_cylScale]

lemma Jinf_zero (hb : 0 < b) (hρ : 0 < ρ) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (hdec : ExpDecayCInftyTube (fd Jbar Jinf) ρ b) (t : ℝ) : Jinf (t, 0) = jStd := by
  have h := tendsto_cylJ hb hdec t (mem_ball_self hρ)
  simp only [cylJ_zero Jbar h0] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

lemma Jinf_sq (hb : 0 < b) (hsq : ∀ p ∈ univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (hdec : ExpDecayCInftyTube (fd Jbar Jinf) ρ b) (t : ℝ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ)
    (v : ℂ × ℂ) : Jinf (t, w) (Jinf (t, w) v) = -v := by
  have h := tendsto_cylJ hb hdec t hw
  have hc : Continuous fun L : CL => L (L v) :=
    continuous_id.clm_apply (continuous_id.clm_apply continuous_const)
  have h2 := (hc.tendsto _).comp h
  have e : ((fun L : CL => L (L v)) ∘ fun s => cylJ Jbar s t w) = fun _ => -v := by
    funext s; exact cylJ_sq hsq s t hw v
  rw [e] at h2
  exact tendsto_nhds_unique h2 tendsto_const_nhds

lemma Kinf_zero (hρ : 0 < ρ) (hJ0 : ∀ t, Jinf (t, 0) = jStd) (a : ℂ) :
    Kinf ρ Jinf (a, 0) = jStd := by
  rw [Kinf, rtr_eq hρ (by rw [norm_zero]; positivity : ‖(0 : ℂ)‖ < ρ / 4), hJ0]

lemma Kinf_sq (hρ : 0 < ρ)
    (hJsq : ∀ t, ∀ w ∈ ball (0 : ℂ) ρ, ∀ v, Jinf (t, w) (Jinf (t, w) v) = -v) (y v : ℂ × ℂ) :
    Kinf ρ Jinf y (Kinf ρ Jinf y v) = -v :=
  hJsq _ _ (mem_ball_zero_iff.2 (norm_rtr_lt hρ _)) v

/-- The shift map. -/
def Ψs (ρ σ : ℝ) (y : ℂ × ℂ) : ℝ × ℝ × ℂ := (y.1.re + σ, y.1.im, rtr ρ y.2)

lemma Ψs_eq (ρ σ : ℝ) : Ψs ρ σ = Ψs ρ 0 + fun _ => ((σ, 0, 0) : ℝ × ℝ × ℂ) := by
  funext y; simp [Ψs]

lemma contDiff_Ψs (ρ σ : ℝ) : ContDiff ℝ ∞ (Ψs ρ σ) :=
  ((Complex.reCLM.contDiff.comp contDiff_fst).add contDiff_const).prodMk
    ((Complex.imCLM.contDiff.comp contDiff_fst).prodMk ((rtr_contDiff ρ).comp contDiff_snd))

lemma iteratedFDeriv_Ψs (ρ σ : ℝ) {i : ℕ} (hi : i ≠ 0) (y : ℂ × ℂ) :
    iteratedFDeriv ℝ i (Ψs ρ σ) y = iteratedFDeriv ℝ i (Ψs ρ 0) y := by
  rw [Ψs_eq ρ σ, iteratedFDeriv_add_apply ((contDiff_Ψs ρ 0).contDiffAt.of_le
    (by exact_mod_cast le_top)) contDiffAt_const, iteratedFDeriv_const_of_ne hi, Pi.zero_apply,
    add_zero]

lemma Kc_sub_Kinf (σ : ℝ) : Kc ρ Jbar σ - Kinf ρ Jinf = fd Jbar Jinf ∘ Ψs ρ σ := rfl

/-- The shifted structures converge to the limit structure. -/
theorem tendsto_Kc (hρ : 0 < ρ) (hb : 0 < b) (hJs : ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ))
    (hJi : ContDiffOn ℝ ∞ Jinf (univ ×ˢ ball (0 : ℂ) ρ))
    (hdec : ExpDecayCInftyTube (fd Jbar Jinf) ρ b) {σ : ℕ → ℝ} (hσ : Tendsto σ atTop atTop) :
    TendstoCInftyLocOn (fun n => Kc ρ Jbar (σ n)) (Kinf ρ Jinf) univ := by
  refine tendsto_of_sub (fun n => contDiff_Kc hρ hJs (σ n)) (contDiff_Kinf hρ hJi)
    fun S hS m ε hε => ?_
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall 0
  obtain ⟨s₀, hs₀⟩ := hdec.1
  choose Cd sd hd using hdec.2
  -- derivative bound of the shift map on `S`
  obtain ⟨B, hB0, hB⟩ : ∃ B ≥ 0, ∀ y ∈ S, ∀ i ≤ m, ‖iteratedFDeriv ℝ i (Ψs ρ 0) y‖ ≤ B := by
    have hc : ∀ i, ∃ C, ∀ y ∈ S, ‖iteratedFDeriv ℝ i (Ψs ρ 0) y‖ ≤ C := fun i => by
      obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn
        ((contDiff_Ψs ρ 0).continuous_iteratedFDeriv (m := i)
          (by exact_mod_cast le_top)).continuousOn
      exact ⟨C, fun y hy => by simpa using hC y hy⟩
    choose C hC using hc
    refine ⟨∑ i ∈ Finset.range (m + 1), |C i|, by positivity, fun y hy i hi => ?_⟩
    exact (hC i y hy).trans ((le_abs_self _).trans (Finset.single_le_sum
      (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))))
  set D : ℝ := B + 1 with hD
  have hD1 : 1 ≤ D := by linarith
  set Cm : ℝ := ∑ i ∈ Finset.range (m + 1), |Cd i| with hCm
  set Sm : ℝ := ∑ i ∈ Finset.range (m + 1), |sd i| with hSm
  have hCi : ∀ i ≤ m, Cd i ≤ Cm := fun i hi => (le_abs_self _).trans (Finset.single_le_sum
    (f := fun i => |Cd i|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
  have hSi : ∀ i ≤ m, sd i ≤ Sm := fun i hi => (le_abs_self _).trans (Finset.single_le_sum
    (f := fun i => |sd i|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
  have hCm0 : 0 ≤ Cm := by positivity
  set g : ℝ → ℝ := fun s => (m.factorial : ℝ) * (Cm * Real.exp (-(b * (s - R)))) * D ^ m with hg
  have hgt : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => b * (s - R)) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-R) tendsto_id).const_mul_atTop hb |>.congr
        fun s => by simp [sub_eq_add_neg]
    have := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul Cm).const_mul
      (m.factorial : ℝ) |>.mul_const (D ^ m)
    simpa [hg, Function.comp_def] using this
  filter_upwards [(hgt.comp hσ).eventually (Iio_mem_nhds hε),
    hσ.eventually_ge_atTop (max (s₀ + R + 1) (R + Sm))] with n hn hσn y hy
  have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.1 (hR hy)
  have hre : -R ≤ y.1.re := by
    have := (Complex.abs_re_le_norm y.1).trans ((norm_fst_le y).trans hyR)
    linarith [neg_abs_le y.1.re]
  set U : Set (ℂ × ℂ) := {y | -R - 1 < y.1.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
  have hyU : y ∈ U := show -R - 1 < y.1.re by linarith
  set T : Set (ℝ × ℝ × ℂ) := Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ with hT
  have hTo : IsOpen T := isOpen_Ioi.prod (isOpen_univ.prod isOpen_ball)
  have hσ1 : s₀ + R + 1 ≤ σ n := (le_max_left _ _).trans hσn
  have hσ2 : R + Sm ≤ σ n := (le_max_right _ _).trans hσn
  have hst : MapsTo (Ψs ρ (σ n)) U T := fun y' hy' =>
    ⟨show s₀ < y'.1.re + σ n by have : -R - 1 < y'.1.re := hy'; linarith, mem_univ _,
      mem_ball_zero_iff.2 (norm_rtr_lt hρ _)⟩
  rw [Kc_sub_Kinf, ← iteratedFDerivWithin_of_isOpen m hUo hyU]
  have hbound := norm_iteratedFDerivWithin_comp_le (n := m) hs₀ (contDiff_Ψs ρ (σ n)).contDiffOn
    (by exact_mod_cast le_top) hTo.uniqueDiffOn hUo.uniqueDiffOn hst hyU
    (C := Cm * Real.exp (-(b * (σ n - R)))) (D := D) (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hTo (hst hyU)]
      have h1 := hd i (y.1.re + σ n) (by linarith [hSi i hi]) y.1.im (rtr ρ y.2)
        (mem_ball_zero_iff.2 (norm_rtr_lt hρ _))
      have h2 : Real.exp (-(b * (y.1.re + σ n))) ≤ Real.exp (-(b * (σ n - R))) :=
        Real.exp_le_exp.2 (by nlinarith)
      calc _ ≤ Cd i * Real.exp (-(b * (y.1.re + σ n))) := h1
        _ ≤ Cm * Real.exp (-(b * (y.1.re + σ n))) :=
            mul_le_mul_of_nonneg_right (hCi i hi) (Real.exp_pos _).le
        _ ≤ Cm * Real.exp (-(b * (σ n - R))) := mul_le_mul_of_nonneg_left h2 hCm0)
    (fun i hi1 him => by
      rw [iteratedFDerivWithin_of_isOpen i hUo hyU, iteratedFDeriv_Ψs ρ (σ n) (by omega)]
      exact (hB y hy i him).trans ((by linarith : B ≤ D).trans
        (le_self_pow₀ hD1 (by omega))))
  exact lt_of_le_of_lt hbound hn

/-- The structures at `+∞`: the limit is almost complex and the shifted two-scale structures
converge to it. -/
theorem infinity_structure {Sinf : ℝ → CauchyRiemannIndex.Mat 1} (hρ : 0 < ρ) (hb : 0 < b)
    (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    IsAlmostComplexOn (TS (Kinf ρ Jinf)) univ ∧ ∀ σ : ℕ → ℝ, Tendsto σ atTop atTop →
      TendstoCInftyLocOn (fun n => TS (Kc ρ Jbar (σ n))) (TS (Kinf ρ Jinf)) univ := by
  obtain ⟨hJs, hsq, h0, hJi, -, hdec, -⟩ := hstd
  have hdec' : ExpDecayCInftyTube (fd Jbar Jinf) ρ b := hdec
  refine ⟨isAlmostComplexOn_TS (contDiff_Kinf hρ hJi)
    (Kinf_zero hρ (Jinf_zero hb hρ h0 hdec'))
    (Kinf_sq hρ fun t w hw v => Jinf_sq hb hsq hdec' t hw v), fun σ hσ => ?_⟩
  exact tendsto_TS (fun n => contDiff_Kc hρ hJs (σ n)) (contDiff_Kinf hρ hJi)
    (tendsto_Kc hρ hb hJs hJi hdec' hσ)

end Inf

end QR21

end

end FiniteEnergyPlane

-- FILE: RSK_R20.lean
/-!
# Q-R, layer 20 (local, NOT published): the window package

For a small zero `x ≠ 0`, a window centre `ξ₀` (`Re ξ₀ ≥ -1`, `|Im ξ₀| ≤ 1/2`) and a shift `σ`,
the graph `gU x ξ₀ σ ζ = (ξ₀ - σ + ζ, vT μ1 rr (uS x σ) (ξ₀ - σ + ζ), ⟨μ1, rr⟩)` is smooth and
`TS (Kc σ)`-holomorphic on the unit disc, bounded, with a `W^{1,4}` bound independent of
`x`, `ξ₀`, `σ` (given a bound on `‖ξ₀ - σ‖`); its derivative at `0` controls the derivative of the
rescaled lift at `ξ₀`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic DbarRegularity
open scoped ContDiff ENNReal NNReal Real

noncomputable section

namespace QR20

open QL QR QR11 QR15 QR16 QR17 QR19 QN19W QN18

variable {χT χN β : ℝ → ℝ}

variable (χT χN β) in
/-- The window graph. -/
def gU (x : QDom) (ξ₀ : ℂ) (σ : ℝ) : ℂ → TE :=
  graph (ξ₀ - σ) (fun ζ => vT (μ1 χT x ξ₀.re) (rr χT χN ξ₀.re) (uS χT χN β x σ) (ξ₀ - σ + ζ))
    ⟨μ1 χT x ξ₀.re, rr χT χN ξ₀.re⟩

lemma fib_eq (x : QDom) (ξ₀ : ℂ) (σ μ r : ℝ) :
    (fun ζ => vT μ r (uS χT χN β x σ) (ξ₀ - σ + ζ)) = fun ζ => vT μ r (uL χT χN β x) (ξ₀ + ζ) := by
  funext ζ; rw [vT_uS]; congr 1; ring

lemma gU_eq (x : QDom) (ξ₀ : ℂ) (σ : ℝ) : gU χT χN β x ξ₀ σ =
    graph (ξ₀ - σ) (fun ζ => vT (μ1 χT x ξ₀.re) (rr χT χN ξ₀.re) (uL χT χN β x) (ξ₀ + ζ))
      ⟨μ1 χT x ξ₀.re, rr χT χN ξ₀.re⟩ := by
  rw [gU, fib_eq]

lemma h4 : ENNReal.ofReal 4 = (4 : ℝ≥0∞) := by simp

set_option maxHeartbeats 1600000 in
/-- The window package. -/
theorem window_package (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ Kτ ≥ 0, ∃ BV BP : ℝ, ∃ CS : ℝ≥0∞, CS ≠ ⊤ ∧
      ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → 0 < ‖x‖ →
      (∀ ξ : ℂ, -2 ≤ ξ.re → ‖τL χT χN β x ξ‖ ≤ Kτ * ‖x‖ ∧ Kτ * ‖x‖ < 1 / 2) ∧
      μ1 χT x 0 ≤ BP * ‖x‖ ∧
      ∀ ξ₀ : ℂ, -1 ≤ ξ₀.re → |ξ₀.im| ≤ 1 / 2 → ∀ σ : ℝ,
        ContDiffOn ℝ ∞ (gU χT χN β x ξ₀ σ) (ball 0 1) ∧
        IsJHolomorphicOn (TS (Kc ρ Jbar σ)) (ball 0 1) (gU χT χN β x ξ₀ σ) ∧
        (∀ ζ ∈ ball (0 : ℂ) 1, ‖gU χT χN β x ξ₀ σ ζ‖ ≤ ‖ξ₀ - σ‖ + 1 + BV + BP) ∧
        sobolevNorm 1 (ENNReal.ofReal 4) (ball 0 1) (gU χT χN β x ξ₀ σ) ≤
          eLpNorm (fun _ : ℂ => ‖ξ₀ - σ‖ + 1 + BV + BP) (ENNReal.ofReal 4)
            (volume.restrict (ball (0 : ℂ) 1)) +
          (eLpNorm (fun _ : ℂ => (1 : ℝ)) (ENNReal.ofReal 4) (volume.restrict (ball (0 : ℂ) 1)) +
            CS) ∧
        ‖fderiv ℝ (vT (μ1 χT x ξ₀.re) (rr χT χN ξ₀.re) (uL χT χN β x)) ξ₀‖ ≤
          ‖fderiv ℝ (gU χT χN β x ξ₀ σ) 0‖ ∧
        μ1 χT x ξ₀.re ≤ BP * ‖x‖ := by
  obtain ⟨εf, hεf, hfacts⟩ :=
    small_zero_facts ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨K₀, hK₀, hC0⟩ := QRF.c0_bound_stub δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨εs, hεs, Kτ, hKτ, BV, Bp, hsup⟩ :=
    sup_window (β := β) hχT hχN hδ hδT hρ hC0 hK₀.le
  obtain ⟨CS, hCS, hder⟩ := deriv_window (β := β) hχT hχN hβ
  have hJs := hstd.1
  have hsq := hstd.2.1
  have h0 := hstd.2.2.1
  refine ⟨min εf εs, lt_min hεf hεs, Kτ, hKτ, BV, Bp * min εf εs + Bp + Bp, CS, hCS,
    fun x hx hq hx0 => ?_⟩
  have hxn : ‖x‖ < min εf εs := mem_ball_zero_iff.1 hx
  have hxf : x ∈ ball (0 : QDom) εf := mem_ball_zero_iff.2 (lt_of_lt_of_le hxn (min_le_left _ _))
  have hxs : ‖x‖ < εs := lt_of_lt_of_le hxn (min_le_right _ _)
  obtain ⟨hgsm, hdb, hw1, hw2, -, -⟩ := hfacts x hxf hq
  have hsmall := fun ξ hs => (hsup x hx0 hxs 0 (by norm_num)).1 ξ hs
  have hBp0 : 0 ≤ Bp := by
    have := (hsup x hx0 hxs 0 (by norm_num)).2.2.2
    exact (rr_pos (χT := χT) (χN := χN) 0).le.trans this
  have hBPx : ∀ s₀ : ℝ, -1 ≤ s₀ → μ1 χT x s₀ ≤ (Bp * min εf εs + Bp + Bp) * ‖x‖ := by
    intro s₀ hs₀
    have h1 := (hsup x hx0 hxs (s₀ : ℂ) (by simpa using hs₀)).2.2.1
    simp only [Complex.ofReal_re] at h1
    have : Bp * ‖x‖ ≤ (Bp * min εf εs + Bp + Bp) * ‖x‖ := by
      have := mul_nonneg hBp0 (le_min hεf.le hεs.le)
      nlinarith [norm_nonneg x]
    linarith
  refine ⟨fun ξ hs => ⟨(hsmall ξ hs).1, (hsmall ξ hs).2.1⟩, hBPx 0 (by norm_num),
    fun ξ₀ hs₀ ht σ => ?_⟩
  obtain ⟨-, hVb, hμb, hrb⟩ := hsup x hx0 hxs ξ₀ hs₀
  set μ := μ1 χT x ξ₀.re with hμdef
  set r := rr χT χN ξ₀.re with hrdef
  have hμ : 0 < μ := μ1_pos hx0 _
  have hr : 0 < r := rr_pos _
  have hwin : ∀ ζ ∈ ball (0 : ℂ) 1, -2 ≤ (ξ₀ + ζ).re := fun ζ hζ => by
    have := (re_window (ξ₀ := ξ₀) hζ).1; linarith
  have hτw : ∀ ζ ∈ ball (0 : ℂ) 1, ‖τL χT χN β x (ξ₀ + ζ)‖ ≤ 1 / 2 := fun ζ hζ =>
    (hsmall _ (hwin ζ hζ)).1.trans (hsmall _ (hwin ζ hζ)).2.1.le
  have hτ1 : ∀ ζ ∈ ball (0 : ℂ) 1, ‖τL χT χN β x (ξ₀ + ζ)‖ < 1 := fun ζ hζ =>
    lt_of_le_of_lt (hτw ζ hζ) (by norm_num)
  let V : ℂ → ℂ × ℂ := fun ζ => vT μ r (uL χT χN β x) (ξ₀ + ζ)
  have hV : V = fun ζ => vT μ r (uL χT χN β x) (ξ₀ + ζ) := rfl
  have hVc : ∀ ζ ∈ ball (0 : ℂ) 1, ContDiffAt ℝ ∞ V ζ := fun ζ hζ =>
    contDiffAt_V hχT.1 hχN.1 hβ.1 hw1 hw2 μ r (hτ1 ζ hζ)
  have hVon : ContDiffOn ℝ ∞ V (ball 0 1) := fun ζ hζ => (hVc ζ hζ).contDiffWithinAt
  have hgU : gU χT χN β x ξ₀ σ = graph (ξ₀ - σ) V ⟨μ, r⟩ := gU_eq x ξ₀ σ
  have hpn : ‖(⟨μ, r⟩ : ℂ)‖ ≤ Bp * min εf εs + Bp + Bp := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [abs_of_pos hμ, abs_of_pos hr]
    have : μ ≤ Bp * min εf εs := hμb.trans (mul_le_mul_of_nonneg_left hxn.le hBp0)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, hBPx ξ₀.re hs₀⟩
  · rw [hgU]
    intro ζ hζ
    exact ((contDiffAt_const.add contDiffAt_id).prodMk
      ((hVc ζ hζ).prodMk contDiffAt_const)).contDiffWithinAt
  · rw [gU]
    refine isJHolomorphicOn_graph_vT (contDiff_Kc hρ hJs σ) (Kc_zero hρ h0 σ) hμ.ne' hr.ne'
      (ξ₀ - σ) fun ζ hζ => ?_
    have e : ξ₀ - σ + ζ + σ = ξ₀ + ζ := by ring
    have hs := hsmall (ξ₀ + ζ) (hwin ζ hζ)
    exact dbarJ_uS hχT.1 hχN.1 hβ.1 hρ hw1 hw2 hgsm hdb (by rw [e]; exact hτ1 ζ hζ)
      (by rw [e]; exact hs.2.2)
  · intro ζ hζ
    rw [hgU]
    refine (norm_graph_le _ _ _ _).trans ?_
    have h1 : ‖ξ₀ - σ + ζ‖ ≤ ‖ξ₀ - σ‖ + 1 :=
      (norm_add_le _ _).trans (by linarith [(mem_ball_zero_iff.1 hζ).le])
    linarith [hVb ζ hζ]
  · rw [hgU]
    refine (sobolevNorm_one_le (A := ‖ξ₀ - σ‖ + 1 + BV + (Bp * min εf εs + Bp + Bp))
      (fun ζ hζ => ?_) measurableSet_ball).trans (add_le_add le_rfl ?_)
    · refine (norm_graph_le _ _ _ _).trans ?_
      have h1 : ‖ξ₀ - σ + ζ‖ ≤ ‖ξ₀ - σ‖ + 1 :=
        (norm_add_le _ _).trans (by linarith [(mem_ball_zero_iff.1 hζ).le])
      linarith [hVb ζ hζ]
    · refine (eLpNorm_fderiv_graph_le (by simp) isOpen_ball (ξ₀ - σ) ⟨μ, r⟩
        (hVon.of_le (by simp))).trans (add_le_add le_rfl ?_)
      rw [h4]
      exact hder x hx0 hw1 hw2 ξ₀ hs₀ ht hτw
  · rw [hgU]
    have hd : DifferentiableAt ℝ V 0 := (hVc 0 (mem_ball_self one_pos)).differentiableAt (by simp)
    refine le_trans (le_of_eq ?_) (norm_fderiv_le_graph (ξ₀ - σ) ⟨μ, r⟩ hd)
    rw [hV, fderiv_comp_add_left (f := vT μ r (uL χT χN β x)), add_zero]

end QR20

end

end FiniteEnergyPlane

-- FILE: RSK_R22.lean
/-!
# Q-R, layer 22 (local, NOT published): the uniform centre bound

`center_bound`: for small zeros `x ≠ 0` and every window centre `ξ₀` with `Re ξ₀ ≥ -1`,
`|Im ξ₀| ≤ 1/2`, the derivative of the rescaled lift `vT μ1 rr (uL x)` at `ξ₀` is bounded by a
constant `M` independent of `x` and `ξ₀`. The middle regime `Re ξ₀ ≤ S` uses one structure
(`QR11.bound_const` for `TS (Kc 0)`); the regime `Re ξ₀ ≥ S` argues by contradiction with
Thm 2.22(2a) for the shifted structures `TS (Kc σₙ) → TS Kinf`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic DbarRegularity
open scoped ContDiff ENNReal NNReal Real

noncomputable section

namespace QR22

open QL QR QR11 QR15 QR16 QR17 QR19 QR20 QR21 QN19W QN18

lemma norm_sub_re (ξ : ℂ) : ‖ξ - (ξ.re : ℂ)‖ ≤ |ξ.im| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  simp

lemma norm_le_of_window {ξ : ℂ} {S : ℝ} (h1 : -1 ≤ ξ.re) (h2 : ξ.re ≤ S) (ht : |ξ.im| ≤ 1 / 2) :
    ‖ξ‖ ≤ |S| + 2 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have : |ξ.re| ≤ |S| + 1 := by
    rw [abs_le]; constructor <;> linarith [le_abs_self S, neg_abs_le S]
  linarith

lemma eLpNorm_const_mono {a b : ℝ} (h : |a| ≤ b) :
    eLpNorm (fun _ : ℂ => a) (ENNReal.ofReal 4) (volume.restrict (ball (0 : ℂ) 1)) ≤
      eLpNorm (fun _ : ℂ => b) (ENNReal.ofReal 4) (volume.restrict (ball (0 : ℂ) 1)) :=
  eLpNorm_mono fun _ => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ((abs_nonneg a).trans h)]; exact h

lemma const_ne_top (c : ℝ) :
    eLpNorm (fun _ : ℂ => c) (ENNReal.ofReal 4) (volume.restrict (ball (0 : ℂ) 1)) ≠ ⊤ := by
  refine (eLpNorm_const_lt_top_iff (by norm_num) (by simp)).2 (Or.inr ?_) |>.ne
  rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top

set_option maxHeartbeats 1600000 in
/-- The uniform centre bound. -/
theorem center_bound (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ Kτ ≥ 0, ∃ BP M : ℝ, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → 0 < ‖x‖ →
      (∀ ξ : ℂ, -2 ≤ ξ.re → ‖τL χT χN β x ξ‖ ≤ Kτ * ‖x‖ ∧ Kτ * ‖x‖ < 1 / 2) ∧
      ∀ ξ₀ : ℂ, -1 ≤ ξ₀.re → |ξ₀.im| ≤ 1 / 2 →
        ‖fderiv ℝ (vT (μ1 χT x ξ₀.re) (rr χT χN ξ₀.re) (uL χT χN β x)) ξ₀‖ ≤ M ∧
        μ1 χT x ξ₀.re ≤ BP * ‖x‖ := by
  obtain ⟨ε, hε, Kτ, hKτ, BV, BP, CS, hCS, hpack⟩ :=
    window_package ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  have hinf := infinity_structure hρ hb hstd
  obtain ⟨hJs, hsq, h0, -⟩ := hstd
  -- the uniform Sobolev constant and target compact for `‖ξ₀ - σ‖ ≤ R`
  let B : ℝ → ℝ := fun R => R + 1 + |BV| + |BP|
  have hB : B = fun R => R + 1 + |BV| + |BP| := rfl
  let CR : ℝ → ℝ≥0∞ := fun R =>
    eLpNorm (fun _ : ℂ => B R) (ENNReal.ofReal 4) (volume.restrict (ball (0 : ℂ) 1)) +
      (eLpNorm (fun _ : ℂ => (1 : ℝ)) (ENNReal.ofReal 4) (volume.restrict (ball (0 : ℂ) 1)) + CS)
  have hCRne : ∀ R, CR R ≠ ⊤ := fun R =>
    ENNReal.add_ne_top.2 ⟨const_ne_top _, ENNReal.add_ne_top.2 ⟨const_ne_top _, hCS⟩⟩
  have hgood : ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → 0 < ‖x‖ →
      ∀ ξ₀ : ℂ, -1 ≤ ξ₀.re → |ξ₀.im| ≤ 1 / 2 → ∀ σ : ℝ, ∀ R, 0 ≤ R → ‖ξ₀ - σ‖ ≤ R →
        MapsTo (gU χT χN β x ξ₀ σ) (ball 0 1) (closedBall 0 (B R)) ∧
        sobolevNorm 1 (ENNReal.ofReal 4) (ball 0 1) (gU χT χN β x ξ₀ σ) ≤ ((CR R).toNNReal : ℝ≥0∞) := by
    intro x hx hq hx0 ξ₀ hs₀ ht σ R hR hc
    obtain ⟨-, -, hpk⟩ := hpack x hx hq hx0
    obtain ⟨-, -, hbd, hsob, -, -⟩ := hpk ξ₀ hs₀ ht σ
    have hab : |‖ξ₀ - σ‖ + 1 + BV + BP| ≤ B R := by
      have e1 := abs_add_le (‖ξ₀ - (σ : ℂ)‖ + 1 + BV) BP
      have e2 := abs_add_le (‖ξ₀ - (σ : ℂ)‖ + 1) BV
      have e3 := abs_add_le ‖ξ₀ - (σ : ℂ)‖ 1
      simp only [abs_norm, abs_one] at e3
      simp only [hB]; linarith
    refine ⟨fun ζ hζ => mem_closedBall_zero_iff.2 ((hbd ζ hζ).trans
      ((le_abs_self _).trans hab)), ?_⟩
    rw [ENNReal.coe_toNNReal (hCRne R)]
    exact hsob.trans (add_le_add (eLpNorm_const_mono hab) le_rfl)
  -- the regime near `+∞`, by contradiction
  have hfar : ∃ S M₁ : ℝ, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → 0 < ‖x‖ →
      ∀ ξ₀ : ℂ, S ≤ ξ₀.re → |ξ₀.im| ≤ 1 / 2 →
        ‖fderiv ℝ (vT (μ1 χT x ξ₀.re) (rr χT χN ξ₀.re) (uL χT χN β x)) ξ₀‖ ≤ M₁ := by
    by_contra hne
    push_neg at hne
    choose x hx hq hx0 ξ hξs hξt hbig using fun n : ℕ => hne (n : ℝ) (n : ℝ)
    set σ : ℕ → ℝ := fun n => (ξ n).re with hσdef
    have hσ : Tendsto σ atTop atTop :=
      tendsto_atTop_mono (fun n => hξs n) tendsto_natCast_atTop_atTop
    have hs₀ : ∀ n, -1 ≤ (ξ n).re := fun n => le_trans (by
      have := Nat.cast_nonneg (α := ℝ) n; linarith) (hξs n)
    have hc : ∀ n, ‖ξ n - (σ n : ℂ)‖ ≤ 1 / 2 := fun n => (norm_sub_re _).trans (hξt n)
    set u : ℕ → ℂ → TE := fun n => gU χT χN β (x n) (ξ n) (σ n) with hu
    have hJn : ∀ n, IsAlmostComplexOn (TS (Kc ρ Jbar (σ n))) univ := fun n =>
      isAlmostComplexOn_TS (contDiff_Kc hρ hJs (σ n)) (Kc_zero hρ h0 (σ n))
        (Kc_sq hρ hsq (σ n))
    have hpk := fun n => ((hpack (x n) (hx n) (hq n) (hx0 n)).2.2 (ξ n) (hs₀ n) (hξt n) (σ n))
    obtain ⟨M, hM⟩ := bounded_iteratedFDeriv_of_sobolevNorm_le 4 (by norm_num)
      (TS (Kinf ρ Jinf)) (fun n => TS (Kc ρ Jbar (σ n))) univ (closedBall 0 (B (1 / 2)))
      hinf.1 hJn (hinf.2 σ hσ) (isCompact_closedBall _ _) (subset_univ _) u
      (fun n => (hpk n).1) (fun n => (hpk n).2.1)
      (fun n => (hgood (x n) (hx n) (hq n) (hx0 n) (ξ n) (hs₀ n) (hξt n) (σ n) (1 / 2)
        (by norm_num) (hc n)).1)
      (CR (1 / 2)).toNNReal
      (fun n => (hgood (x n) (hx n) (hq n) (hx0 n) (ξ n) (hs₀ n) (hξt n) (σ n) (1 / 2)
        (by norm_num) (hc n)).2)
      {0} (singleton_subset_iff.2 (mem_ball_self one_pos)) isCompact_singleton 1
    obtain ⟨n, hn⟩ := exists_nat_gt M
    have h1 := hM n 0 (mem_singleton _)
    rw [norm_iteratedFDeriv_one] at h1
    have h2 := (hpk n).2.2.2.2.1
    linarith [hbig n]
  obtain ⟨S, M₁, hM₁⟩ := hfar
  -- the middle regime
  have hJ0 : IsAlmostComplexOn (TS (Kc ρ Jbar 0)) univ :=
    isAlmostComplexOn_TS (contDiff_Kc hρ hJs 0) (Kc_zero hρ h0 0) (Kc_sq hρ hsq 0)
  obtain ⟨M₀, hM₀⟩ := bound_const (TS (Kc ρ Jbar 0)) univ (closedBall 0 (B (|S| + 2))) hJ0
    (isCompact_closedBall _ _) (subset_univ _) {0}
    (singleton_subset_iff.2 (mem_ball_self one_pos)) isCompact_singleton (CR (|S| + 2)).toNNReal
  refine ⟨ε, hε, Kτ, hKτ, BP, max M₀ M₁, fun x hx hq hx0 => ?_⟩
  obtain ⟨hτ, -, hpk⟩ := hpack x hx hq hx0
  refine ⟨hτ, fun ξ₀ hs₀ ht => ⟨?_, (hpk ξ₀ hs₀ ht 0).2.2.2.2.2⟩⟩
  rcases le_or_gt S ξ₀.re with h | h
  · exact (hM₁ x hx hq hx0 ξ₀ h ht).trans (le_max_right _ _)
  · obtain ⟨hcd, hhol, -, -, hfd, -⟩ := hpk ξ₀ hs₀ ht 0
    have hc : ‖ξ₀ - ((0 : ℝ) : ℂ)‖ ≤ |S| + 2 := by
      rw [Complex.ofReal_zero, sub_zero]; exact norm_le_of_window hs₀ h.le ht
    obtain ⟨hmaps, hsob⟩ := hgood x hx hq hx0 ξ₀ hs₀ ht 0 (|S| + 2) (by positivity) hc
    have := hM₀ _ hcd hhol hmaps hsob 0 (mem_singleton _)
    exact hfd.trans (this.trans (le_max_left _ _))

end QR22

end

end FiniteEnergyPlane

-- FILE: RSK_R23.lean
/-!
# Q-R, layer 23 (local, NOT published): assembly of R4 `uniform_C1`

The cylinder centre bound `QR22.center_bound` is transported to the plane through
`z = Eexp ξ₀` (`QR8.norm_mul_norm_fderiv_pfG_le`), combined with `QR15.near_zero` on
`‖z‖ ≤ 1/2`, and the weight `(1 + ‖z‖)^(1 - δ/2π)` is absorbed by the slope of `χN`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic
open scoped ContDiff ENNReal NNReal Real

noncomputable section

namespace QR23

open QL QR QR8 QR13 QR14 QR15 QR16 QR17 QR18 QR19 QR22 QN19W QN18

variable {χT χN β : ℝ → ℝ} {δ δT : ℝ}

/-! ### Generic derivative facts -/

lemma norm_toC_le (v : ℝ × ℝ) : ‖toC v‖ ≤ 2 * ‖v‖ := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [toC_re, toC_im]
  have h1 : |v.1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le v
  linarith

/-- The hard direction of the `cplx` transfer. -/
lemma norm_fderiv_le_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ × ℝ → E) (ξ : ℂ) :
    ‖fderiv ℝ u (cplx ξ)‖ ≤ 2 * ‖fderiv ℝ (fun z => u (cplx z)) ξ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have h := fderiv_comp_cplx u ξ (toC v)
  rw [cplx_toC] at h
  rw [← h]
  refine ((fderiv ℝ (fun z => u (cplx z)) ξ).le_opNorm _).trans ?_
  have := mul_le_mul_of_nonneg_left (norm_toC_le v) (norm_nonneg (fderiv ℝ (fun z => u (cplx z)) ξ))
  linarith

lemma pfG_fst {F G : Type*} (c₀ : F × G) (g : ℝ × ℝ → F × G) :
    (fun z => (pfG c₀ g z).1) = pfG c₀.1 (fun q => (g q).1) := by
  funext z; unfold pfG; split_ifs <;> rfl

lemma pfG_snd {F G : Type*} (c₀ : F × G) (g : ℝ × ℝ → F × G) :
    (fun z => (pfG c₀ g z).2) = pfG c₀.2 (fun q => (g q).2) := by
  funext z; unfold pfG; split_ifs <;> rfl

/-! ### The plane side -/

lemma pLc_fst_eq (x : QDom) :
    (fun z => (pLc χT χN β z x).1) = pfG (0 : ℂ) (fun q => (hC χT χN β x q).1) := by
  rw [← pfG_fst ((0 : ℂ), x.2.1), ← pLc_eq_pfG]

lemma pLc_snd_eq (x : QDom) :
    (fun z => (pLc χT χN β z x).2) = pfG x.2.1 (fun q => (hC χT χN β x q).2) := by
  rw [← pfG_snd ((0 : ℂ), x.2.1), ← pLc_eq_pfG]

lemma norm_Eexp_two_pi (ξ : ℂ) :
    ‖Eexp ξ * ((2 * π : ℝ) : ℂ)‖ = Real.exp (2 * π * ξ.re) * (2 * π) := by
  rw [norm_mul, norm_Eexp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

lemma plane_fst (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)
    {x : QDom} (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2)) (ξ : ℂ) :
    Real.exp (2 * π * ξ.re) * (2 * π) *
        ‖fderiv ℝ (fun z => (pLc χT χN β z x).1) (Eexp ξ)‖ ≤
      2 * ‖fderiv ℝ (h1 χT χN β x) ξ‖ := by
  rw [pLc_fst_eq, ← norm_Eexp_two_pi]
  refine (norm_mul_norm_fderiv_pfG_le (contDiff_fst.comp (contDiff_hC hχT hχN hβ hw1 hw2))
    (fun s t => by simp only [Function.comp, hC_per]) ξ).trans ?_
  exact norm_fderiv_le_two (fun q => (hC χT χN β x q).1) ξ

lemma plane_snd (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)
    {x : QDom} (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2)) (ξ : ℂ) :
    Real.exp (2 * π * ξ.re) * (2 * π) *
        ‖fderiv ℝ (fun z => (pLc χT χN β z x).2) (Eexp ξ)‖ ≤
      2 * ‖fderiv ℝ (h2 χT χN β x) ξ‖ := by
  rw [pLc_snd_eq, ← norm_Eexp_two_pi]
  refine (norm_mul_norm_fderiv_pfG_le (contDiff_snd.comp (contDiff_hC hχT hχN hβ hw1 hw2))
    (fun s t => by simp only [Function.comp, hC_per]) ξ).trans ?_
  exact norm_fderiv_le_two (fun q => (hC χT χN β x q).2) ξ

/-! ### The choice of the centre -/

lemma exists_center {z : ℂ} (hz : 1 / 2 < ‖z‖) :
    ∃ ξ₀ : ℂ, Eexp ξ₀ = z ∧ -1 ≤ ξ₀.re ∧ |ξ₀.im| ≤ 1 / 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
  have hπ : 0 < 2 * π := by positivity
  refine ⟨Complex.log z * (((2 * π : ℝ) : ℂ))⁻¹, ?_, ?_, ?_⟩
  · rw [Eexp, mul_comm (Complex.log z), ← mul_assoc, mul_inv_cancel₀
      (Complex.ofReal_ne_zero.2 hπ.ne'), one_mul, Complex.exp_log hz0]
  · rw [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, Complex.log_re]
    have hl : Real.log (1 / 2) ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) hz.le
    have h2 : Real.log (1 / 2) = - Real.log 2 := by
      rw [one_div, Real.log_inv]
    have h3 := Real.log_two_lt_d9
    have h4 := Real.pi_gt_three
    rw [← div_eq_mul_inv, le_div_iff₀ hπ]
    nlinarith
  · simp only [← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, add_zero, Complex.log_im]
    rw [abs_mul, abs_inv, abs_of_pos hπ]
    have := Complex.abs_arg_le_pi z
    rw [← div_eq_mul_inv, div_le_iff₀ hπ]
    linarith

/-! ### The cylinder side -/

lemma vT_uL_fun (μ r : ℝ) (x : QDom) :
    vT μ r (uL χT χN β x) = fun ξ =>
      ((μ⁻¹ : ℝ) • ((((2 * π : ℝ) : ℂ))⁻¹ * Complex.log (1 + τL χT χN β x ξ)),
        ((μ * r)⁻¹ : ℝ) • h2 χT χN β x ξ) := by
  funext ξ
  rw [vT, uL_sub, dg_apply]

lemma norm_span_le (c : ℂ) :
    ‖(ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ‖ ≤ ‖c‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => le_of_eq ?_
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, norm_mul]
  ring

/-- The derivative of the rescaled lift at a centre controls `D τL` and `D h2`. -/
lemma cyl_bounds (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)
    {x : QDom} (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2))
    {μ r M : ℝ} (hμ : 0 < μ) (hr : 0 < r) {ξ₀ : ℂ} (hτ : ‖τL χT χN β x ξ₀‖ ≤ 1 / 2)
    (hM : ‖fderiv ℝ (vT μ r (uL χT χN β x)) ξ₀‖ ≤ M) :
    ‖fderiv ℝ (τL χT χN β x) ξ₀‖ ≤ 3 * π * μ * M ∧
      ‖fderiv ℝ (h2 χT χN β x) ξ₀‖ ≤ μ * r * M := by
  have hπ : 0 < 2 * π := by positivity
  have hτd : DifferentiableAt ℝ (τL χT χN β x) ξ₀ :=
    (contDiff_τL hχT hχN hβ hw1 hw2).differentiable (by simp) ξ₀
  have h2d : DifferentiableAt ℝ (h2 χT χN β x) ξ₀ :=
    (contDiff_snd.comp (contDiff_hCc hχT hχN hβ hw1 hw2)).differentiable (by simp) ξ₀
  have hL := (hasFDerivAt_log_one_add hτd hτ).const_mul ((((2 * π : ℝ) : ℂ))⁻¹)
  have hV := (hL.const_smul (μ⁻¹ : ℝ)).prodMk (h2d.hasFDerivAt.const_smul ((μ * r)⁻¹ : ℝ))
  have hV' := hV.congr_of_eventuallyEq (f₁ := vT μ r (uL χT χN β x))
    (Filter.Eventually.of_forall fun ξ => by rw [vT_uL_fun]; rfl)
  rw [hV'.fderiv, ContinuousLinearMap.opNorm_prod, Prod.norm_def] at hM
  have ha := (le_max_left _ _).trans hM
  have hb := (le_max_right _ _).trans hM
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hμ, inv_mul_le_iff₀ hμ, norm_smul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ, inv_mul_le_iff₀ hπ, norm_smul,
    norm_inv] at ha
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (mul_pos hμ hr),
    inv_mul_le_iff₀ (mul_pos hμ hr)] at hb
  refine ⟨?_, hb⟩
  have hn1 : ‖1 + τL χT χN β x ξ₀‖ ≤ 3 / 2 :=
    (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have hn0 : 1 / 2 ≤ ‖1 + τL χT χN β x ξ₀‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-τL χT χN β x ξ₀)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this; linarith
  rw [inv_mul_le_iff₀ (by linarith)] at ha
  have hM0 : 0 ≤ M := (le_max_of_le_left (norm_nonneg _)).trans hM
  calc _ ≤ ‖1 + τL χT χN β x ξ₀‖ * (2 * π * (μ * M)) := ha
    _ ≤ 3 / 2 * (2 * π * (μ * M)) := mul_le_mul_of_nonneg_right hn1 (by positivity)
    _ = 3 * π * μ * M := by ring

lemma h1_bound (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)
    {x : QDom} (hw1 : ContDiff ℝ ∞ (wrep x.1)) (hw2 : ContDiff ℝ ∞ (wrep x.2.2)) (ξ₀ : ℂ) :
    ‖fderiv ℝ (h1 χT χN β x) ξ₀‖ ≤ Real.exp (2 * π * ξ₀.re) *
      (2 * π * ‖τL χT χN β x ξ₀‖ + ‖fderiv ℝ (τL χT χN β x) ξ₀‖) := by
  have hτd : DifferentiableAt ℝ (τL χT χN β x) ξ₀ :=
    (contDiff_τL hχT hχN hβ hw1 hw2).differentiable (by simp) ξ₀
  have e : h1 χT χN β x = τL χT χN β x * Eexp := by
    funext ξ; simp only [Pi.mul_apply, τL]; rw [div_mul_cancel₀ _ (Eexp_ne ξ)]
  have hd := hτd.hasFDerivAt.mul (hasFDerivAt_Eexp ξ₀)
  rw [e, hd.fderiv]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_Eexp]
  have hs := norm_span_le (Eexp ξ₀ * ((2 * π : ℝ) : ℂ))
  rw [norm_Eexp_two_pi] at hs
  have := mul_le_mul_of_nonneg_left hs (norm_nonneg (τL χT χN β x ξ₀))
  nlinarith [Real.exp_pos (2 * π * ξ₀.re), norm_nonneg (fderiv ℝ (τL χT χN β x) ξ₀)]

/-! ### Algebra of the far region -/

lemma weight_far (hδ : δ < 0) (s : ℝ) (hz : 1 / 2 < Real.exp (2 * π * s)) :
    (1 + Real.exp (2 * π * s)) ^ (1 - δ / (2 * π)) ≤
      3 ^ (1 - δ / (2 * π)) * Real.exp (2 * π * s - δ * s) := by
  have hπ : 0 < 2 * π := by positivity
  have ha : 0 ≤ 1 - δ / (2 * π) := by
    have : δ / (2 * π) < 0 := div_neg_of_neg_of_pos hδ hπ
    linarith
  have hE := Real.exp_pos (2 * π * s)
  calc (1 + Real.exp (2 * π * s)) ^ (1 - δ / (2 * π))
      ≤ (3 * Real.exp (2 * π * s)) ^ (1 - δ / (2 * π)) :=
        Real.rpow_le_rpow (by positivity) (by linarith) ha
    _ = 3 ^ (1 - δ / (2 * π)) * Real.exp (2 * π * s - δ * s) := by
        rw [Real.mul_rpow (by norm_num) hE.le, ← Real.exp_mul]
        congr 2; field_simp

lemma far_alg {E Y W P Q : ℝ} (hE : 0 < E) (hW0 : 0 ≤ W) (hpf : E * (2 * π) * Y ≤ 2 * P)
    (hWE : W * P ≤ E * Q) : W * Y ≤ Q / π := by
  have hπ := Real.pi_pos
  have h : W * Y * (E * (2 * π)) ≤ Q / π * (E * (2 * π)) := by
    calc W * Y * (E * (2 * π)) = W * (E * (2 * π) * Y) := by ring
      _ ≤ W * (2 * P) := mul_le_mul_of_nonneg_left hpf hW0
      _ = 2 * (W * P) := by ring
      _ ≤ 2 * (E * Q) := by linarith
      _ = Q / π * (E * (2 * π)) := by field_simp
  exact le_of_mul_le_mul_right h (by positivity)

/-! ### The assembly -/

end QR23

end

end FiniteEnergyPlane

-- FILE: RSK_R23F.lean
/-!
# Q-R, layer 23F (local, NOT published): the far-region part of R4 (`1/2 < ‖z‖`)

`QR23.uniform_C1_proof` restricted to `1/2 < ‖z‖`, without the near-zero layer.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic
open scoped ContDiff ENNReal NNReal Real

noncomputable section

namespace QR23

open QL QR QR8 QR13 QR14 QR15 QR16 QR17 QR18 QR19 QR22 QN19W QN18

variable {χT χN β : ℝ → ℝ} {δ δT : ℝ}

set_option maxHeartbeats 1600000 in
theorem far_bound_proof (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ K ≥ 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → ∀ z : ℂ, 1 / 2 < ‖z‖ →
      ‖fderiv ℝ (fun z => (pG χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K * ‖x‖ ∧
      (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (pG χT χN β x z).2) z‖ ≤ K * ‖x‖ := by
  have hπ : 0 < 2 * π := by positivity
  have ha1 : 1 ≤ 1 - δ / (2 * π) := by
    have : δ / (2 * π) < 0 := div_neg_of_neg_of_pos hδ hπ
    linarith
  obtain ⟨εf, hεf, hfacts⟩ :=
    small_zero_facts ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨εc, hεc, Kτ, hKτ, BP, M, hcen⟩ :=
    center_bound ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨Cw, hCw⟩ := weight_upper hχN δ (by linarith) (-1)
  set a : ℝ := 1 - δ / (2 * π) with ha
  set K1 : ℝ := 2 * Kτ + 3 * |BP| * |M| with hK1
  set K2 : ℝ := 3 ^ a * Real.exp Cw * |M| / π with hK2
  have hK10 : 0 ≤ K1 := by positivity
  have hK20 : 0 ≤ K2 := by positivity
  refine ⟨min εf εc, lt_min hεf hεc, K1 + K2, by positivity,
    fun x hx hq z hz => ?_⟩
  have hxn : ‖x‖ < min εf εc := mem_ball_zero_iff.1 hx
  have hxf : x ∈ ball (0 : QDom) εf := mem_ball_zero_iff.2 (hxn.trans_le (min_le_left _ _))
  have hxc : x ∈ ball (0 : QDom) εc := mem_ball_zero_iff.2 (hxn.trans_le (min_le_right _ _))
  obtain ⟨-, -, hw1, hw2, hpGs, -⟩ := hfacts x hxf hq
  -- reduction to the linear part
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
  rcases eq_or_ne x 0 with h0 | h0
  · subst h0
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero, fderiv_const_apply, norm_zero, mul_zero,
      le_refl, and_self]
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 h0
  -- the far region, through the cylinder
  obtain ⟨ξ₀, hzξ, hre, him⟩ := exists_center hz
  subst hzξ
  set s := ξ₀.re with hs
  obtain ⟨hτall, hcb⟩ := hcen x hxc hq hx0
  obtain ⟨hMξ, hμ⟩ := hcb ξ₀ hre him
  have hτ0 := hτall ξ₀ (by linarith)
  have hμ0 := μ1_pos (χT := χT) hx0 s
  have hr0 := rr_pos (χT := χT) (χN := χN) s
  obtain ⟨hDτ, hDh2⟩ := cyl_bounds hχT.1 hχN.1 hβ.1 hw1 hw2 hμ0 hr0
    (hτ0.1.trans hτ0.2.le) hMξ
  have hDh1 := h1_bound hχT.1 hχN.1 hβ.1 hw1 hw2 ξ₀
  have pf1 := plane_fst hχT.1 hχN.1 hβ.1 hw1 hw2 ξ₀
  have pf2 := plane_snd hχT.1 hχN.1 hβ.1 hw1 hw2 ξ₀
  have hE := Real.exp_pos (2 * π * s)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hMξ
  have hμB : μ1 χT x s ≤ |BP| * ‖x‖ :=
    hμ.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hx0.le)
  refine ⟨?_, ?_⟩
  · have c1 : Real.exp (2 * π * s) * (2 * π) *
        ‖fderiv ℝ (fun z => (pLc χT χN β z x).1) (Eexp ξ₀)‖ ≤
        Real.exp (2 * π * s) * (2 * π) * (K1 * ‖x‖) := by
      have hτK := hτ0.1
      have h3 : 3 * π * μ1 χT x s * M ≤ 3 * π * (|BP| * ‖x‖) * |M| :=
        mul_le_mul (mul_le_mul_of_nonneg_left hμB (by positivity)) (le_abs_self _) hM0
          (by positivity)
      calc _ ≤ 2 * ‖fderiv ℝ (h1 χT χN β x) ξ₀‖ := pf1
        _ ≤ 2 * (Real.exp (2 * π * s) * (2 * π * ‖τL χT χN β x ξ₀‖ +
              ‖fderiv ℝ (τL χT χN β x) ξ₀‖)) := by linarith
        _ ≤ 2 * (Real.exp (2 * π * s) * (2 * π * (Kτ * ‖x‖) + 3 * π * (|BP| * ‖x‖) * |M|)) := by
            gcongr; linarith
        _ = Real.exp (2 * π * s) * (2 * π) * (K1 * ‖x‖) := by rw [hK1]; ring
    refine (le_of_mul_le_mul_left c1 (by positivity)).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hx0.le
  · rw [norm_Eexp]
    have hz' : 1 / 2 < Real.exp (2 * π * s) := by rw [← norm_Eexp]; exact hz
    have hW := weight_far hδ s hz'
    have hD2 : 2 * ‖fderiv ℝ (h2 χT χN β x) ξ₀‖ ≤ 2 * (‖x‖ * Real.exp (χN s) * |M|) := by
      have := hDh2.trans (mul_le_mul_of_nonneg_left (le_abs_self M)
        (mul_pos hμ0 hr0).le)
      rw [μ1_mul_rr] at this; linarith
    have hWE : (1 + Real.exp (2 * π * s)) ^ a * (‖x‖ * Real.exp (χN s) * |M|) ≤
        Real.exp (2 * π * s) * (3 ^ a * Real.exp Cw * |M| * ‖x‖) := by
      have hc := hCw s (by linarith)
      have hexp : Real.exp (2 * π * s - δ * s) * Real.exp (χN s) ≤
          Real.exp (2 * π * s) * Real.exp Cw := by
        rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
      calc (1 + Real.exp (2 * π * s)) ^ a * (‖x‖ * Real.exp (χN s) * |M|)
          ≤ 3 ^ a * Real.exp (2 * π * s - δ * s) * (‖x‖ * Real.exp (χN s) * |M|) :=
            mul_le_mul_of_nonneg_right hW (by positivity)
        _ = 3 ^ a * (‖x‖ * |M|) * (Real.exp (2 * π * s - δ * s) * Real.exp (χN s)) := by ring
        _ ≤ 3 ^ a * (‖x‖ * |M|) * (Real.exp (2 * π * s) * Real.exp Cw) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = Real.exp (2 * π * s) * (3 ^ a * Real.exp Cw * |M| * ‖x‖) := by ring
    have hfin := far_alg hE (by positivity) (pf2.trans hD2) hWE
    have hK2x : 3 ^ a * Real.exp Cw * |M| * ‖x‖ / π = K2 * ‖x‖ := by rw [hK2]; ring
    rw [hK2x] at hfin
    exact hfin.trans (mul_le_mul_of_nonneg_right (by linarith) hx0.le)

end QR23

end

end FiniteEnergyPlane

-- FILE: RSK_RP4F.lean
namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QRB

theorem exists_norm_fderiv_qMember_le_of_half_lt_norm_proof (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ K ≥ 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → ∀ z : ℂ, 1 / 2 < ‖z‖ →
      ‖fderiv ℝ (fun z => (qMember χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K * ‖x‖ ∧
      (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (qMember χT χN β x z).2) z‖ ≤
        K * ‖x‖ := by
  rw [← pG_eq_qMember]
  exact QR23.far_bound_proof ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ

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
    ∃ ε > 0, ∃ K ≥ 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → ∀ z : ℂ, 1 / 2 < ‖z‖ →
      ‖fderiv ℝ (fun z => (qMember χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K * ‖x‖ ∧
      (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (qMember χT χN β x z).2) z‖ ≤
        K * ‖x‖ :=
  QRB.exists_norm_fderiv_qMember_le_of_half_lt_norm_proof ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
