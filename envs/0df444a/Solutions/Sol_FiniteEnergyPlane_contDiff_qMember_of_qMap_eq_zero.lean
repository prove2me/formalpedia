-- Prove2me | solution 1 for FiniteEnergyPlane.contDiff_qMember_of_qMap_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T10:27:10.00812+00:00
-- url     : https://prove2.me/submissions/75852136-3b63-4528-8fe4-96c09fd76136

import Definitions.Def_FiniteEnergyPlane_QMember
import Theorems.Thm_CauchyRiemannIndex_exists_continuous_representative_of_mem_W1p
import Theorems.Thm_CauchyRiemannIndex_eq_of_continuous_periodic_ae_eq
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
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq
import Theorems.Thm_FiniteEnergyPlane_exists_smooth_qPoint_rep
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_ball_of_energy_lt_top
import Definitions.Def_FiniteEnergyPlane_TubeFamily

open Metric Set Filter Topology BoundedContinuousFunction
open Metric Set Filter Topology MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open MeasureTheory Metric Set Filter Topology BoundedContinuousFunction
open scoped ENNReal ContDiff
open Metric Set Filter Topology
open scoped ContDiff

-- FILE: _imports_RSK_RP2.lean


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

lemma vecToC_cToVec (z : ℂ) : vecToC (cToVec z) = z := by
  apply Complex.ext <;> simp [cToVec, vecToC]

lemma cToVec_add (a b : ℂ) : cToVec (a + b) = cToVec a + cToVec b := by
  ext i; rcases i with i | i <;> simp [cToVec]

lemma cToVec_smul (r : ℝ) (a : ℂ) : cToVec ((r : ℂ) * a) = r • cToVec a := by
  ext i; rcases i with i | i <;> simp [cToVec]

lemma toLpOrZero_eq_toLp {f : ℝ × ℝ → Vec 1} (hf : MemLp f 4 cylMeasure) :
    toLpOrZero f = hf.toLp f := by
  simp [toLpOrZero, hf]

lemma coeFn_toLpOrZero {f : ℝ × ℝ → Vec 1} (hf : MemLp f 4 cylMeasure) :
    (toLpOrZero f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] f := by
  rw [toLpOrZero_eq_toLp hf]; exact hf.coeFn_toLp

/-! ### The pointwise formula in terms of values -/

/-- `qPoint` with the nine values `T.i q`, `N.i q` (as complex numbers) and `c` made explicit. -/
def qPt (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (c : ℂ)
    (a1 a2 a3 b1 b2 b3 : ℂ) : ℂ × ℂ :=
  let s := q.1
  let z := cylInf q.1 q.2
  let eT : ℂ := (Real.exp (χT s) : ℂ)
  let eN : ℂ := (Real.exp (χN s) : ℂ)
  let ψ := z + eT * a1
  let ψs := ((2 * π : ℝ) : ℂ) * z + eT * (((deriv χT s : ℝ) : ℂ) * a1 + a2)
  let ψt := ((2 * π : ℝ) : ℂ) * Complex.I * z + eT * a3
  let v := (β s : ℂ) * c + eN * b1
  let vs := ((deriv β s : ℝ) : ℂ) * c + eN * (((deriv χN s : ℝ) : ℂ) * b1 + b2)
  let vt := eN * b3
  let E := (ψs, vs) + Jbar (ψ, v) (ψt, vt)
  ((Real.exp (-χT s) : ℂ) * E.1, (Real.exp (-χN s) : ℂ) * E.2)

lemma qPoint_eq (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (x : QDom) (q : ℝ × ℝ) :
    qPoint Jbar χT χN β x q = qPt Jbar χT χN β q x.2.1
      (vecToC ((x.1 : Triple 1 4).1 q)) (vecToC ((x.1 : Triple 1 4).2.1 q))
      (vecToC ((x.1 : Triple 1 4).2.2 q)) (vecToC ((x.2.2 : Triple 1 4).1 q))
      (vecToC ((x.2.2 : Triple 1 4).2.1 q)) (vecToC ((x.2.2 : Triple 1 4).2.2 q)) := rfl

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

/-- Transport of an a.e. statement on the period strip to `ℝ × [-1, 1)`. -/
lemma ae_of_cyl (P Q : ℝ × ℝ → Prop) (hP : ∀ᵐ x ∂cylMeasure, P x)
    (hup : ∀ x ∈ upS, P x → Q x) (hlow : ∀ x ∈ lowS, P (x + tup) → Q x) :
    ∀ᵐ x ∂(volume.restrict ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1)), Q x := by
  rw [← lowS_union_upS, ae_restrict_union_iff]
  constructor
  · have h := measurePreserving_tup_restrict.quasiMeasurePreserving.ae hP
    filter_upwards [h, ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with x hx hm
    exact hlow x hm hx
  · have hP' : ∀ᵐ x ∂(volume.restrict upS), P x := hP
    filter_upwards [hP', ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with x hx hm
    exact hup x hm hx

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

/-- The a.e. version of an a.e. statement on the plane strip. -/
lemma ae_stripU_of (Q : ℂ → Prop)
    (hQ : ∀ᵐ x ∂(volume.restrict ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1)), Q (toC x)) :
    ∀ᵐ z ∂(volume.restrict stripU), Q z := by
  have hm : MeasurableSet ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1) :=
    MeasurableSet.univ.prod measurableSet_Ico
  have h := (measurePreserving_cplx.restrict_preimage hm).quasiMeasurePreserving.ae hQ
  have hsub : stripU ⊆ cplx ⁻¹' ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1) := by
    intro z hz
    simp only [stripU, mem_setOf_eq, abs_lt] at hz
    simp [cplx_apply, hz.1.le, hz.2]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub h] with z hz
  simpa only [toC_cplx] using hz

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

lemma memLp_pair {r : ℝ≥0∞} {μ : Measure ℂ} {f : ℂ → ℂ} {g : ℂ → F} (hf : MemLp f r μ)
    (hg : MemLp g r μ) : MemLp (fun z => (f z, g z)) r μ := by
  have h := ((ContinuousLinearMap.inl ℝ ℂ F).comp_memLp' hf).add
    ((ContinuousLinearMap.inr ℝ ℂ F).comp_memLp' hg)
  have e : (fun z => (f z, g z)) =
      (⇑(ContinuousLinearMap.inl ℝ ℂ F) ∘ f) + (⇑(ContinuousLinearMap.inr ℝ ℂ F) ∘ g) := by
    funext z; simp
  rw [e]; exact h

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

lemma norm_vecToC_le (a : Vec 1) : ‖vecToC a‖ ≤ ‖a‖ := by
  have h1 : ‖vecToC a‖ ^ 2 = a (Sum.inl 0) ^ 2 + a (Sum.inr 0) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [vecToC]; ring
  have h2 : ‖a‖ ^ 2 = a (Sum.inl 0) ^ 2 + a (Sum.inr 0) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [Fintype.sum_sum_type]
  exact le_of_eq (by nlinarith [norm_nonneg (vecToC a), norm_nonneg a])

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

/-- The plane function of `v`. -/
def pf (v : ℝ × ℝ → Vec 1) (z : ℂ) : ℂ :=
  if z = 0 then 0 else vecToC (v (Real.log ‖z‖ / (2 * π), Complex.arg z / (2 * π)))

variable {v : ℝ × ℝ → Vec 1}

lemma pf_zero : pf v 0 = 0 := by simp [pf]

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

lemma norm_pf_le (B : ℝ) (g : ℝ × ℝ → Vec 1) (hB : ∀ x, ‖g x‖ ≤ B) (χ : ℝ → ℝ)
    (hvg : ∀ x, v x = Real.exp (χ x.1) • g x) (z : ℂ) (hz : z ≠ 0) :
    ‖pf v z‖ ≤ B * Real.exp (χ (Real.log ‖z‖ / (2 * π))) := by
  rw [pf, if_neg hz, hvg]
  refine (norm_vecToC_le _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le

lemma tendsto_pf_zero (B : ℝ) (g : ℝ × ℝ → Vec 1) (hB : ∀ x, ‖g x‖ ≤ B) (χ : ℝ → ℝ)
    (hχ : ∀ s ≤ -1, χ s = χ (-1) + π * (s + 1))
    (hvg : ∀ x, v x = Real.exp (χ x.1) • g x) : ContinuousAt (pf v) 0 := by
  have hlog : Tendsto (fun z : ℂ => Real.log ‖z‖ / (2 * π)) (𝓝[≠] 0) atBot := by
    have h1 : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] 0) (𝓝[>] 0) := tendsto_norm_nhdsNE_zero
    exact (Real.tendsto_log_nhdsGT_zero.comp h1).atBot_div_const (by positivity)
  have hχb : Tendsto χ atBot atBot := by
    have h : Tendsto (fun s => χ (-1) + π * (s + 1)) atBot atBot :=
      tendsto_atBot_add_const_left _ _ ((tendsto_atBot_add_const_right _ 1 tendsto_id).const_mul_atBot
        Real.pi_pos)
    refine h.congr' ?_
    filter_upwards [eventually_le_atBot (-1)] with s hs
    exact (hχ s hs).symm
  have hexp : Tendsto (fun z : ℂ => B * Real.exp (χ (Real.log ‖z‖ / (2 * π)))) (𝓝[≠] 0) (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (hχb.comp hlog)).const_mul B
    simpa using this
  have hne : Tendsto (pf v) (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hexp
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact norm_pf_le B g hB χ hvg z hz
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, pf_zero]
  exact hne

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

/-- The unweighted pointwise operator in terms of values. -/
def Eq0 (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (c : ℂ)
    (a1 a2 a3 b1 b2 b3 : ℂ) : ℂ × ℂ :=
  (((2 * π : ℝ) : ℂ) * cylInf q.1 q.2 +
      (Real.exp (χT q.1) : ℂ) * (((deriv χT q.1 : ℝ) : ℂ) * a1 + a2),
    ((deriv β q.1 : ℝ) : ℂ) * c + (Real.exp (χN q.1) : ℂ) * (((deriv χN q.1 : ℝ) : ℂ) * b1 + b2)) +
  Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * a1, (β q.1 : ℂ) * c + (Real.exp (χN q.1) : ℂ) * b1)
    (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * a3,
      (Real.exp (χN q.1) : ℂ) * b3)

lemma qPt_eq (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (c : ℂ)
    (a1 a2 a3 b1 b2 b3 : ℂ) :
    qPt Jbar χT χN β q c a1 a2 a3 b1 b2 b3 =
      ((Real.exp (-χT q.1) : ℂ) * (Eq0 Jbar χT χN β q c a1 a2 a3 b1 b2 b3).1,
        (Real.exp (-χN q.1) : ℂ) * (Eq0 Jbar χT χN β q c a1 a2 a3 b1 b2 b3).2) := rfl

lemma eq0_of_qPt_eq_zero {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {χT χN β : ℝ → ℝ} {q : ℝ × ℝ}
    {c a1 a2 a3 b1 b2 b3 : ℂ} (h : qPt Jbar χT χN β q c a1 a2 a3 b1 b2 b3 = 0) :
    Eq0 Jbar χT χN β q c a1 a2 a3 b1 b2 b3 = 0 := by
  rw [qPt_eq] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_zero, Prod.snd_zero, mul_eq_zero, Complex.ofReal_eq_zero,
    (Real.exp_pos _).ne', false_or] at h1 h2
  exact Prod.ext h1 h2

/-- `qMap x = 0` on the ball where `qMap` has `L⁴` components: the pointwise formula vanishes
a.e. -/
theorem ae_qPoint_eq_zero (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 →
      ∀ᵐ q ∂cylMeasure, qPoint Jbar χT χN β x q = 0 := by
  obtain ⟨ε, hε, F, -, hF⟩ :=
    exists_smooth_qPoint_rep ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  refine ⟨ε, hε, fun x hx h0 => ?_⟩
  obtain ⟨h1, h2⟩ := hF x hx
  have m1 : MemLp (fun q => cToVec (qPoint Jbar χT χN β x q).1) 4 cylMeasure :=
    (Lp.memLp _).ae_eq h1
  have m2 : MemLp (fun q => cToVec (qPoint Jbar χT χN β x q).2) 4 cylMeasure :=
    (Lp.memLp _).ae_eq h2
  have e1 := congrArg Prod.fst h0
  have e2 := congrArg Prod.snd h0
  simp only [qMap, Prod.fst_zero, Prod.snd_zero] at e1 e2
  have a1 := coeFn_toLpOrZero m1
  have a2 := coeFn_toLpOrZero m2
  rw [e1] at a1
  rw [e2] at a2
  filter_upwards [a1, a2, Lp.coeFn_zero (Vec 1) 4 cylMeasure,
    Lp.coeFn_zero (Vec 1) 4 cylMeasure] with q b1 b2 z1 z2
  rw [z1] at b1
  rw [z2] at b2
  have c1 : (qPoint Jbar χT χN β x q).1 = 0 := by
    have := congrArg vecToC b1
    rwa [vecToC_cToVec, Pi.zero_apply, show vecToC (0 : Vec 1) = 0 by
      apply Complex.ext <;> simp [vecToC], eq_comm] at this
  have c2 : (qPoint Jbar χT χN β x q).2 = 0 := by
    have := congrArg vecToC b2
    rwa [vecToC_cToVec, Pi.zero_apply, show vecToC (0 : Vec 1) = 0 by
      apply Complex.ext <;> simp [vecToC], eq_comm] at this
  exact Prod.ext c1 c2

/-- The unweighted equation with the continuous representatives, a.e. on the cylinder. -/
theorem ae_eq0 {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {χT χN β : ℝ → ℝ} (x : QDom)
    (h : ∀ᵐ q ∂cylMeasure, qPoint Jbar χT χN β x q = 0) :
    ∀ᵐ q ∂cylMeasure, Eq0 Jbar χT χN β q x.2.1 (vecToC (wrep x.1 q))
      (vecToC ((x.1 : Triple 1 4).2.1 q)) (vecToC ((x.1 : Triple 1 4).2.2 q))
      (vecToC (wrep x.2.2 q)) (vecToC ((x.2.2 : Triple 1 4).2.1 q))
      (vecToC ((x.2.2 : Triple 1 4).2.2 q)) = 0 := by
  filter_upwards [h, (wrep_prop x.1).2.2, (wrep_prop x.2.2).2.2] with q hq h1 h2
  rw [qPoint_eq, h1, h2] at hq
  exact eq0_of_qPt_eq_zero hq

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

/-- Locally integrable on `U`. -/
def LocInt (U : Set ℂ) (u : ℂ → E) : Prop := ∀ K ⊆ U, IsCompact K → IntegrableOn u K

lemma LocInt.add {u v : ℂ → E} (hu : LocInt U u) (hv : LocInt U v) : LocInt U (u + v) :=
  fun K hK hKc => (hu K hK hKc).add (hv K hK hKc)

lemma LocInt.smul_cont {u : ℂ → E} (hu : LocInt U u) {f : ℂ → ℝ} (hf : Continuous f) :
    LocInt U (fun z => f z • u z) :=
  fun K hK hKc => (hu K hK hKc).continuousOn_smul hf.continuousOn hKc

lemma LocInt.of_continuous {u : ℂ → E} (hu : Continuous u) : LocInt U u :=
  fun _ _ hKc => hu.continuousOn.integrableOn_compact hKc

/-- A continuous function supported in a compact `K ⊆ U` times a locally integrable function
is integrable. -/
lemma integrable_smul_of_support {u : ℂ → E} (hu : LocInt U u) {ψ : ℂ → ℝ} {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) (hψ : Continuous ψ) (hψK : Function.support ψ ⊆ K) :
    Integrable (fun z => ψ z • u z) :=
  (integrableOn_iff_integrable_of_support_subset
    ((Function.support_smul_subset_left _ _).trans hψK)).1
    ((hu K hKU hK).continuousOn_smul hψ.continuousOn hK)

section test

variable {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
include hφ hφc hφU

lemma int_test {u : ℂ → E} (hu : LocInt U u) : Integrable (fun z => φ z • u z) :=
  integrable_smul_of_support hu hφc hφU hφ.continuous (subset_tsupport φ)

lemma int_dtest {u : ℂ → E} (hu : LocInt U u) (e : ℂ) :
    Integrable (fun z => fderiv ℝ φ z e • u z) := by
  refine integrable_smul_of_support hu hφc hφU
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) ?_
  intro z hz
  by_contra h
  have h0 : fderiv ℝ φ z = 0 := by
    have : z ∉ tsupport (fderiv ℝ φ) := fun h' => h (tsupport_fderiv_subset ℝ h')
    exact image_eq_zero_of_notMem_tsupport this
  exact hz (by simp [h0])

end test

/-- Sum. -/
lemma weak_add {u us ut v vs vt : ℂ → E} (h1 : HasWeakPartialsOn U u us ut)
    (h2 : HasWeakPartialsOn U v vs vt) (hu : LocInt U u) (hus : LocInt U us)
    (hut : LocInt U ut) (hv : LocInt U v) (hvs : LocInt U vs) (hvt : LocInt U vt) :
    HasWeakPartialsOn U (fun z => u z + v z) (fun z => us z + vs z) (fun z => ut z + vt z) := by
  intro φ hφ hφc hφU
  replace hφ : ContDiff ℝ ∞ φ := hφ
  obtain ⟨a1, a2⟩ := h1 φ hφ hφc hφU
  obtain ⟨b1, b2⟩ := h2 φ hφ hφc hφU
  refine ⟨?_, ?_⟩
  · simp only [smul_add]
    rw [integral_add (int_dtest hφ hφc hφU hu 1) (int_dtest hφ hφc hφU hv 1),
      integral_add (int_test hφ hφc hφU hus) (int_test hφ hφc hφU hvs), a1, b1, neg_add]
  · simp only [smul_add]
    rw [integral_add (int_dtest hφ hφc hφU hu _) (int_dtest hφ hφc hφU hv _),
      integral_add (int_test hφ hφc hφU hut) (int_test hφ hφc hφU hvt), a2, b2, neg_add]

/-- Continuous linear image. -/
lemma weak_clm [CompleteSpace E] [CompleteSpace F] {u us ut : ℂ → E}
    (h : HasWeakPartialsOn U u us ut) (hu : LocInt U u) (hus : LocInt U us) (hut : LocInt U ut)
    (L : E →L[ℝ] F) :
    HasWeakPartialsOn U (fun z => L (u z)) (fun z => L (us z)) (fun z => L (ut z)) := by
  intro φ hφ hφc hφU
  replace hφ : ContDiff ℝ ∞ φ := hφ
  obtain ⟨a1, a2⟩ := h φ hφ hφc hφU
  refine ⟨?_, ?_⟩
  · simp only [← L.map_smul]
    rw [L.integral_comp_comm (int_dtest hφ hφc hφU hu 1),
      L.integral_comp_comm (int_test hφ hφc hφU hus), a1, map_neg]
  · simp only [← L.map_smul]
    rw [L.integral_comp_comm (int_dtest hφ hφc hφU hu _),
      L.integral_comp_comm (int_test hφ hφc hφU hut), a2, map_neg]

/-- Product with a smooth real function. -/
lemma weak_smul {u us ut : ℂ → E} (h : HasWeakPartialsOn U u us ut) (hu : LocInt U u)
    (hus : LocInt U us) (hut : LocInt U ut) {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    HasWeakPartialsOn U (fun z => f z • u z)
      (fun z => fderiv ℝ f z 1 • u z + f z • us z)
      (fun z => fderiv ℝ f z Complex.I • u z + f z • ut z) := by
  intro φ hφ hφc hφU
  replace hφ : ContDiff ℝ ∞ φ := hφ
  have hφf : ContDiff ℝ ∞ (fun z => φ z * f z) := hφ.mul hf
  have hφfc : HasCompactSupport (fun z => φ z * f z) := hφc.mul_right
  have hφfU : tsupport (fun z => φ z * f z) ⊆ U :=
    (tsupport_mul_subset_left).trans hφU
  obtain ⟨a1, a2⟩ := h _ hφf hφfc hφfU
  have hfc : Continuous fun z => fderiv ℝ f z 1 := (hf.continuous_fderiv (by simp)).clm_apply
    continuous_const
  have hfcI : Continuous fun z => fderiv ℝ f z Complex.I :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hd : ∀ (e : ℂ) z, fderiv ℝ (fun z => φ z * f z) z e =
      fderiv ℝ φ z e * f z + φ z * fderiv ℝ f z e := by
    intro e z
    have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L e) ((hφ.differentiable (by simp) z).hasFDerivAt.mul
      (hf.differentiable (by simp) z).hasFDerivAt).fderiv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h
    exact h.trans (by ring)
  have hcf : ∀ e : ℂ, Continuous fun z => fderiv ℝ f z e := fun e =>
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have key : ∀ (e : ℂ), ∫ z, fderiv ℝ φ z e • (f z • u z) =
      (∫ z, fderiv ℝ (fun z => φ z * f z) z e • u z) - ∫ z, φ z • (fderiv ℝ f z e • u z) := by
    intro e
    have i1 : Integrable fun z => fderiv ℝ (fun z => φ z * f z) z e • u z :=
      int_dtest hφf hφfc hφfU hu e
    have i2 : Integrable fun z => φ z • (fderiv ℝ f z e • u z) :=
      int_test hφ hφc hφU (hu.smul_cont (hcf e))
    rw [← integral_sub i1 i2]
    congr 1; funext z
    rw [hd, smul_smul, smul_smul, add_smul, add_sub_cancel_right]
  have fin : ∀ (e : ℂ) (w : ℂ → E), LocInt U w →
      ∫ z, fderiv ℝ (fun z => φ z * f z) z e • u z = -∫ z, (φ z * f z) • w z →
      ∫ z, fderiv ℝ φ z e • (f z • u z) = -∫ z, φ z • (fderiv ℝ f z e • u z + f z • w z) := by
    intro e w hw hw'
    have e1 : ∫ z, φ z • (fderiv ℝ f z e • u z + f z • w z) =
        (∫ z, φ z • (fderiv ℝ f z e • u z)) + ∫ z, φ z • (f z • w z) := by
      simp only [smul_add]
      exact integral_add (int_test hφ hφc hφU (hu.smul_cont (hcf e)))
        (int_test hφ hφc hφU (hw.smul_cont hf.continuous))
    have e2 : ∫ z, (φ z * f z) • w z = ∫ z, φ z • (f z • w z) := by simp only [mul_smul]
    rw [key e, hw', e1, e2]
    abel
  exact ⟨fin 1 us hus a1, fin Complex.I ut hut a2⟩

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

lemma sq_le_one_add_rpow {a q : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) : a ^ 2 ≤ 1 + a ^ q := by
  rcases le_or_gt a 1 with h | h
  · have : a ^ 2 ≤ 1 := by nlinarith
    linarith [Real.rpow_nonneg ha q]
  · have : a ^ (2 : ℝ) ≤ a ^ q := Real.rpow_le_rpow_of_exponent_le h.le hq
    rw [Real.rpow_two] at this
    linarith

lemma integrableOn_exp_negS : IntegrableOn (fun x : ℝ × ℝ => Real.exp (2 * π * x.1)) negS := by
  have hf : IntegrableOn (fun s : ℝ => Real.exp (2 * π * s)) (Iio 0) :=
    (integrableOn_exp_mul_Iic (by positivity) 0).mono_set Iio_subset_Iic_self
  have hg : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico 0 1) := integrableOn_const (by simp)
  have h := hf.mul_prod hg
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  simp only [mul_one] at h
  exact h

lemma integrableOn_rpow_negS {f : ℝ × ℝ → Vec 1} {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤)
    (hf : MemLp f p cylMeasure) : IntegrableOn (fun x => ‖f x‖ ^ p.toReal) negS := by
  have h : IntegrableOn (fun x => ‖f x‖ ^ p.toReal) ((univ : Set ℝ) ×ˢ Ico 0 1) :=
    hf.integrable_norm_rpow hp hp'
  exact h.mono_set (prod_mono (subset_univ _) le_rfl)

variable {g : ℝ × ℝ → Vec 1} {χ : ℝ → ℝ}

/-- The energy of `v = e^χ g` on `(-∞, 0) × [0, 1)` is finite. -/
theorem lintegral_negS_lt_top (p : ℝ≥0∞) (hp : 2 < p) (hp' : p ≠ ⊤) (δ : ℝ)
    (hχ : IsSlopeWeight χ π δ) (hg : ContDiff ℝ ∞ g) (B : ℝ) (hB : ∀ x, ‖g x‖ ≤ B)
    (hgs : MemLp (partialS g) p cylMeasure) (hgt : MemLp (partialT g) p cylMeasure) :
    ∫⁻ x in negS, ENNReal.ofReal (‖fderiv ℝ (vOf χ g) x‖ ^ 2) < ⊤ := by
  have hχc := hχ.1
  have hcd : Continuous (deriv χ) := hχc.continuous_deriv (by simp)
  obtain ⟨c₀, hc₀⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 0)).exists_bound_of_continuousOn
    hcd.continuousOn
  set c := max c₀ π
  have hc : ∀ s ≤ 0, |deriv χ s| ≤ c := by
    intro s hs
    rcases le_or_gt s (-1) with h1 | h1
    · rw [hχ.2.1 s h1, abs_of_pos Real.pi_pos]; exact le_max_right _ _
    · have := hc₀ s ⟨h1.le, hs⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
  obtain ⟨K, hK, hKb⟩ := exists_exp_bound_left χ hχc.continuous π (fun s hs => hχ.eq_left hs)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0 le_rfl)
  set q := p.toReal
  have hq : 2 < q := by
    have := (ENNReal.toReal_lt_toReal (by simp) hp').2 hp
    simpa using this
  have hp0 : p ≠ 0 := (lt_trans (by norm_num) hp).ne'
  set F : ℝ × ℝ → ℝ := fun x => 3 * K ^ 2 * ((c * B) ^ 2 + 2) * Real.exp (2 * π * x.1) +
    3 * K ^ 2 * (‖partialS g x‖ ^ q + ‖partialT g x‖ ^ q)
  have hF : IntegrableOn F negS :=
    (integrableOn_exp_negS.const_mul _).add
      (((integrableOn_rpow_negS hp0 hp' hgs).add (integrableOn_rpow_negS hp0 hp' hgt)).const_mul _)
  have hDc : Continuous (fun x => ‖fderiv ℝ (vOf χ g) x‖ ^ 2) :=
    ((vOf_contDiff hχc hg).continuous_fderiv (by simp)).norm.pow 2
  have hint : IntegrableOn (fun x => ‖fderiv ℝ (vOf χ g) x‖ ^ 2) negS := by
    refine Integrable.mono' hF hDc.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_negS).2 (Eventually.of_forall fun x hx => ?_)
    have hs : x.1 < 0 := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    set a := ‖partialS g x‖
    set b := ‖partialT g x‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    set e := Real.exp (π * x.1)
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have he2 : Real.exp (2 * π * x.1) = e ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    have hD := norm_fderiv_vOf_le hχc hg x
    have hE := hKb x.1 hs.le
    have hcg : |deriv χ x.1| * ‖g x‖ ≤ c * B :=
      mul_le_mul (hc _ hs.le) (hB x) (norm_nonneg _) hc0
    have hT : 0 ≤ |deriv χ x.1| * ‖g x‖ + a + b := by positivity
    have h1 : ‖fderiv ℝ (vOf χ g) x‖ ≤ K * e * (c * B + a + b) :=
      hD.trans (mul_le_mul hE (by linarith) hT (by positivity))
    have h2 : ‖fderiv ℝ (vOf χ g) x‖ ^ 2 ≤ (K * e) ^ 2 * (3 * ((c * B) ^ 2 + a ^ 2 + b ^ 2)) := by
      have h0 := norm_nonneg (fderiv ℝ (vOf χ g) x)
      have : (K * e * (c * B + a + b)) ^ 2 ≤ (K * e) ^ 2 * (3 * ((c * B) ^ 2 + a ^ 2 + b ^ 2)) := by
        rw [mul_pow]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [sq_nonneg (c * B - a), sq_nonneg (c * B - b), sq_nonneg (a - b)]
      exact (pow_le_pow_left₀ h0 h1 2).trans this
    have hae := sq_le_one_add_rpow ha hq.le
    have hbe := sq_le_one_add_rpow hb hq.le
    have hapos := Real.rpow_nonneg ha q
    have hbpos := Real.rpow_nonneg hb q
    have he2' : e ^ 2 ≤ 1 := by nlinarith
    have hea : e ^ 2 * a ^ 2 ≤ e ^ 2 + a ^ q := by nlinarith
    have heb : e ^ 2 * b ^ 2 ≤ e ^ 2 + b ^ q := by nlinarith
    refine h2.trans ?_
    simp only [F, he2]
    have hK2 : 0 ≤ K ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hea hK2, mul_le_mul_of_nonneg_left heb hK2,
      mul_nonneg hK2 hapos, mul_nonneg hK2 hbpos, mul_nonneg hK2 (sq_nonneg e),
      mul_nonneg (mul_nonneg hK2 (sq_nonneg e)) (sq_nonneg (c * B))]
  exact hint.lintegral_lt_top

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

/-- Its weak `s`-partial on the plane strip. -/
def Ps (x : QDom) (ζ : ℂ) : ℂ × ℂ :=
  (((2 * π : ℝ) : ℂ) * cylInf (cplx ζ).1 (cplx ζ).2 +
      Real.exp (χT ζ.re) • (deriv χT ζ.re • vL (wrep x.1 (cplx ζ)) +
        vL (perF ((x.1 : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx ζ))),
    deriv β ζ.re • x.2.1 + Real.exp (χN ζ.re) • (deriv χN ζ.re • vL (wrep x.2.2 (cplx ζ)) +
        vL (perF ((x.2.2 : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx ζ))))

/-- Its weak `t`-partial on the plane strip. -/
def Pt (x : QDom) (ζ : ℂ) : ℂ × ℂ :=
  (((2 * π : ℝ) : ℂ) * Complex.I * cylInf (cplx ζ).1 (cplx ζ).2 +
      Real.exp (χT ζ.re) • vL (perF ((x.1 : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx ζ)),
    Real.exp (χN ζ.re) • vL (perF ((x.2.2 : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx ζ)))

variable {χT χN β}

lemma gC_per (x : QDom) (s t : ℝ) : gC χT χN β x (s, t + 1) = gC χT χN β x (s, t) := by
  simp only [gC, cylInf_add_one, (wrep_prop x.1).2.1, (wrep_prop x.2.2).2.1]

lemma continuous_gC (hχT : Continuous χT) (hχN : Continuous χN) (hβ : Continuous β)
    (x : QDom) : Continuous (gC χT χN β x) := by
  have hc : Continuous fun q : ℝ × ℝ => cylInf q.1 q.2 := by
    unfold cylInf ccwLoop; fun_prop
  refine (hc.add ((Real.continuous_exp.comp (hχT.comp continuous_fst)).smul
    (vL.continuous.comp (wrep_prop x.1).1))).prodMk
    (((hβ.comp continuous_fst).smul continuous_const).add
    ((Real.continuous_exp.comp (hχN.comp continuous_fst)).smul
      (vL.continuous.comp (wrep_prop x.2.2).1)))

/-! ### Smooth pieces on the plane -/

lemma cylInf_cplx (ζ : ℂ) : cylInf (cplx ζ).1 (cplx ζ).2 = Complex.exp (((2 * π : ℝ) : ℂ) * ζ) := by
  rw [cylInf_eq_exp]
  congr 2
  simp only [cplx_apply]
  exact Complex.re_add_im ζ

lemma hasFDerivAt_cyl (ζ : ℂ) :
    HasFDerivAt (fun ζ : ℂ => cylInf (cplx ζ).1 (cplx ζ).2)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (((2 * π : ℝ) : ℂ) * Complex.exp (((2 * π : ℝ) : ℂ) * ζ))).restrictScalars ℝ) ζ := by
  have e : (fun ζ : ℂ => cylInf (cplx ζ).1 (cplx ζ).2) =
      fun ζ => Complex.exp (((2 * π : ℝ) : ℂ) * ζ) := funext cylInf_cplx
  rw [e]
  have h := ((hasDerivAt_id ζ).const_mul (((2 * π : ℝ) : ℂ))).cexp
  simp only [mul_one, id] at h
  have h' : HasDerivAt (fun ζ : ℂ => Complex.exp (((2 * π : ℝ) : ℂ) * ζ))
      (((2 * π : ℝ) : ℂ) * Complex.exp (((2 * π : ℝ) : ℂ) * ζ)) ζ := by
    exact h.congr_deriv (by ring)
  exact h'.hasFDerivAt.restrictScalars ℝ

lemma contDiff_cyl : ContDiff ℝ ∞ (fun ζ : ℂ => cylInf (cplx ζ).1 (cplx ζ).2) := by
  have e : (fun ζ : ℂ => cylInf (cplx ζ).1 (cplx ζ).2) =
      fun ζ => Complex.exp (((2 * π : ℝ) : ℂ) * ζ) := funext cylInf_cplx
  rw [e]
  have h : ContDiff ℂ ∞ (fun ζ : ℂ => Complex.exp (((2 * π : ℝ) : ℂ) * ζ)) :=
    Complex.contDiff_exp.comp ((contDiff_const (𝕜 := ℂ)).mul contDiff_id)
  exact h.restrict_scalars ℝ

lemma fderiv_cyl_one (ζ : ℂ) :
    fderiv ℝ (fun ζ : ℂ => cylInf (cplx ζ).1 (cplx ζ).2) ζ 1 =
      ((2 * π : ℝ) : ℂ) * cylInf (cplx ζ).1 (cplx ζ).2 := by
  rw [(hasFDerivAt_cyl ζ).fderiv, cylInf_cplx]; simp

lemma fderiv_cyl_I (ζ : ℂ) :
    fderiv ℝ (fun ζ : ℂ => cylInf (cplx ζ).1 (cplx ζ).2) ζ Complex.I =
      ((2 * π : ℝ) : ℂ) * Complex.I * cylInf (cplx ζ).1 (cplx ζ).2 := by
  rw [(hasFDerivAt_cyl ζ).fderiv, cylInf_cplx]; simp; ring

lemma hasFDerivAt_re {g : ℝ → ℝ} {g' : ℝ} {ζ : ℂ} (hg : HasDerivAt g g' ζ.re) :
    HasFDerivAt (fun ζ : ℂ => g ζ.re) (g' • Complex.reCLM) ζ :=
  hg.comp_hasFDerivAt ζ Complex.reCLM.hasFDerivAt

lemma contDiff_re {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun ζ : ℂ => g ζ.re) :=
  hg.comp Complex.reCLM.contDiff

lemma fderiv_re_apply {g : ℝ → ℝ} (hg : Differentiable ℝ g) (ζ h : ℂ) :
    fderiv ℝ (fun ζ : ℂ => g ζ.re) ζ h = deriv g ζ.re * h.re := by
  rw [(hasFDerivAt_re (hg ζ.re).hasDerivAt).fderiv]; simp

lemma deriv_exp_comp {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) (s : ℝ) :
    deriv (fun s => Real.exp (χ s)) s = Real.exp (χ s) * deriv χ s :=
  ((hχ s).hasDerivAt.exp).deriv

/-! ### `L^p` on compact sets -/

lemma memLp_K_smul {p : ℝ≥0∞} {K : Set ℂ} (hK : IsCompact K) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℂ → ℝ} (hf : Continuous f) {u : ℂ → E}
    (hu : MemLp u p (volume.restrict K)) : MemLp (fun z => f z • u z) p (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine hu.of_le_mul (c := C) (hf.aestronglyMeasurable.smul hu.1) ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg _)

lemma memLp_K_clm {p : ℝ≥0∞} {K : Set ℂ} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {u : ℂ → E}
    (hu : MemLp u p (volume.restrict K)) : MemLp (fun z => L (u z)) p (volume.restrict K) :=
  hu.of_le_mul (c := ‖L‖) (L.continuous.comp_aestronglyMeasurable hu.1)
    (Eventually.of_forall fun z => L.le_opNorm _)

lemma locInt_of_memLp {K : Set ℂ} {E : Type*} [NormedAddCommGroup E] {u : ℂ → E}
    (hK : IsCompact K) (hu : MemLp u 4 (volume.restrict K)) : IntegrableOn u K := by
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  exact hu.integrable (by norm_num)

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

/-- The weak data of a `W1p` component, pushed through `vL`. -/
lemma weak_comp (w : ↥(W1p 4 1)) :
    HasWeakPartialsOn stripU (fun z => vL (wrep w (cplx z)))
        (fun z => vL (perF ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z)))
        (fun z => vL (perF ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z))) ∧
      (∀ K ⊆ stripU, IsCompact K →
        MemLp (fun z => vL (wrep w (cplx z))) 4 (volume.restrict K) ∧
        MemLp (fun z => vL (perF ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z))) 4
          (volume.restrict K) ∧
        MemLp (fun z => vL (perF ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z))) 4
          (volume.restrict K)) := by
  obtain ⟨hW, hM⟩ := isWeak_of_mem_W1p (w : Triple 1 4) w.2 (wrep w) (wrep_prop w).1
    (wrep_prop w).2.1 (wrep_prop w).2.2
  have hcont : Continuous fun z => wrep w (cplx z) :=
    (wrep_prop w).1.comp (Complex.equivRealProdCLM.continuous)
  have hM' : ∀ K ⊆ stripU, IsCompact K →
      MemLp (fun z => vL (wrep w (cplx z))) 4 (volume.restrict K) ∧
      MemLp (fun z => vL (perF ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z))) 4
        (volume.restrict K) ∧
      MemLp (fun z => vL (perF ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z))) 4
        (volume.restrict K) := by
    intro K hK hKc
    haveI : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
    refine ⟨?_, memLp_K_clm vL (hM K hK).1, memLp_K_clm vL (hM K hK).2⟩
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
      (vL.continuous.comp hcont).continuousOn
    exact MemLp.of_bound (vL.continuous.comp hcont).aestronglyMeasurable C
      ((ae_restrict_iff' hKc.measurableSet).2 (Eventually.of_forall hC))
  have li : ∀ {u : ℂ → ℂ}, (∀ K ⊆ stripU, IsCompact K → MemLp u 4 (volume.restrict K)) →
      LocInt stripU u := fun h K hK hKc => locInt_of_memLp hKc (h K hK hKc)
  refine ⟨?_, hM'⟩
  have l0 : LocInt stripU (fun z => wrep w (cplx z)) := LocInt.of_continuous hcont
  have l1 : LocInt stripU (fun z => perF ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z)) :=
    fun K hK hKc => locInt_of_memLp hKc (hM K hK).1
  have l2 : LocInt stripU (fun z => perF ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z)) :=
    fun K hK hKc => locInt_of_memLp hKc (hM K hK).2
  exact weak_clm hW l0 l1 l2 vL

lemma locInt_of_K {u : ℂ → ℂ} (h : ∀ K ⊆ stripU, IsCompact K → MemLp u 4 (volume.restrict K)) :
    LocInt stripU u := fun K hK hKc => locInt_of_memLp hKc (h K hK hKc)

lemma fderiv_expre_one {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (z : ℂ) :
    fderiv ℝ (fun z : ℂ => Real.exp (χ z.re)) z 1 = Real.exp (χ z.re) * deriv χ z.re := by
  have hd : Differentiable ℝ (fun s => Real.exp (χ s)) :=
    Real.differentiable_exp.comp (hχ.differentiable (by simp))
  rw [fderiv_re_apply hd, deriv_exp_comp (hχ.differentiable (by simp))]; simp

lemma fderiv_expre_I {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (z : ℂ) :
    fderiv ℝ (fun z : ℂ => Real.exp (χ z.re)) z Complex.I = 0 := by
  have hd : Differentiable ℝ (fun s => Real.exp (χ s)) :=
    Real.differentiable_exp.comp (hχ.differentiable (by simp))
  rw [fderiv_re_apply hd]; simp

/-- One weighted component. -/
lemma weak_wcomp (w : ↥(W1p 4 1)) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    HasWeakPartialsOn stripU (fun z => Real.exp (χ z.re) • vL (wrep w (cplx z)))
        (fun z => Real.exp (χ z.re) • (deriv χ z.re • vL (wrep w (cplx z)) +
          vL (perF ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z))))
        (fun z => Real.exp (χ z.re) •
          vL (perF ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z))) ∧
      LocInt stripU (fun z => Real.exp (χ z.re) • vL (wrep w (cplx z))) ∧
      LocInt stripU (fun z => Real.exp (χ z.re) • (deriv χ z.re • vL (wrep w (cplx z)) +
          vL (perF ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z)))) ∧
      LocInt stripU (fun z => Real.exp (χ z.re) •
          vL (perF ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z))) := by
  obtain ⟨hW, hM⟩ := weak_comp w
  have l0 := locInt_of_K fun K hK hKc => (hM K hK hKc).1
  have l1 := locInt_of_K fun K hK hKc => (hM K hK hKc).2.1
  have l2 := locInt_of_K fun K hK hKc => (hM K hK hKc).2.2
  have hf : ContDiff ℝ ∞ (fun z : ℂ => Real.exp (χ z.re)) :=
    contDiff_re (Real.contDiff_exp.comp hχ)
  have hfc : Continuous fun z : ℂ => Real.exp (χ z.re) := hf.continuous
  have hdc : Continuous fun z : ℂ => deriv χ z.re :=
    ((hχ.continuous_deriv (by simp)).comp Complex.continuous_re)
  have H := weak_smul hW l0 l1 l2 hf
  have e1 : (fun z => fderiv ℝ (fun z : ℂ => Real.exp (χ z.re)) z 1 • vL (wrep w (cplx z)) +
        Real.exp (χ z.re) • vL (perF ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z))) =
      (fun z => Real.exp (χ z.re) • (deriv χ z.re • vL (wrep w (cplx z)) +
          vL (perF ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z)))) := by
    funext z; rw [fderiv_expre_one hχ, smul_add, mul_smul]
  have e2 : (fun z => fderiv ℝ (fun z : ℂ => Real.exp (χ z.re)) z Complex.I •
          vL (wrep w (cplx z)) +
        Real.exp (χ z.re) • vL (perF ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z))) =
      (fun z => Real.exp (χ z.re) •
          vL (perF ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z))) := by
    funext z; rw [fderiv_expre_I hχ, zero_smul, zero_add]
  rw [e1, e2] at H
  exact ⟨H, l0.smul_cont hfc, ((l0.smul_cont hdc).add l1).smul_cont hfc, l2.smul_cont hfc⟩

/-- A smooth piece. -/
lemma weak_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℂ → E}
    (hu : ContDiff ℝ ∞ u) :
    HasWeakPartialsOn stripU u (fun z => fderiv ℝ u z 1) (fun z => fderiv ℝ u z Complex.I) ∧
      LocInt stripU u ∧ LocInt stripU (fun z => fderiv ℝ u z 1) ∧
      LocInt stripU (fun z => fderiv ℝ u z Complex.I) :=
  ⟨HasWeakPartialsOn.of_contDiffOn isOpen_stripU (hu.of_le (by simp)).contDiffOn,
    LocInt.of_continuous hu.continuous,
    LocInt.of_continuous ((hu.continuous_fderiv (by simp)).clm_apply continuous_const),
    LocInt.of_continuous ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)⟩

lemma fderiv_bc {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (c : ℂ) (z e : ℂ) :
    fderiv ℝ (fun z : ℂ => β z.re • c) z e = (deriv β z.re * e.re) • c := by
  have h := (hasFDerivAt_re ((hβ.differentiable (by simp)) z.re).hasDerivAt).smul_const c
  rw [h.fderiv]; simp

variable {χT χN β : ℝ → ℝ}

/-- R2 step 1. -/
theorem weak_gC (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)
    (x : QDom) :
    HasWeakPartialsOn stripU (fun ζ => gC χT χN β x (cplx ζ)) (Ps χT χN β x) (Pt χT χN x) ∧
      LocInt stripU (fun ζ => gC χT χN β x (cplx ζ)) ∧ LocInt stripU (Ps χT χN β x) ∧
      LocInt stripU (Pt χT χN x) := by
  obtain ⟨A, a0, a1, a2⟩ := weak_smooth contDiff_cyl
  obtain ⟨B, b0, b1, b2⟩ := weak_wcomp x.1 hχT
  obtain ⟨C, c0, c1, c2⟩ := weak_smooth ((contDiff_re hβ).smul (contDiff_const (c := x.2.1)))
  obtain ⟨D, d0, d1, d2⟩ := weak_wcomp x.2.2 hχN
  have H1 := weak_add A B a0 a1 a2 b0 b1 b2
  have H2 := weak_add C D c0 c1 c2 d0 d1 d2
  have l1 : ∀ K ⊆ stripU, IsCompact K →
      IntegrableOn (fun z => cylInf (cplx z).1 (cplx z).2 + Real.exp (χT z.re) •
        vL (wrep x.1 (cplx z))) K ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ :=
    fun K hK hKc => ⟨(a0.add b0) K hK hKc, (a1.add b1) K hK hKc, (a2.add b2) K hK hKc,
      (c0.add d0) K hK hKc, (c1.add d1) K hK hKc, (c2.add d2) K hK hKc⟩
  have H := HasWeakPartialsOn.prodMk H1 H2 l1
  have eg : (fun ζ => gC χT χN β x (cplx ζ)) = fun z =>
      (cylInf (cplx z).1 (cplx z).2 + Real.exp (χT z.re) • vL (wrep x.1 (cplx z)),
        β z.re • x.2.1 + Real.exp (χN z.re) • vL (wrep x.2.2 (cplx z))) := by
    funext z; simp [gC, cplx_apply]
  have es : Ps χT χN β x = fun z =>
      (fderiv ℝ (fun ζ : ℂ => cylInf (cplx ζ).1 (cplx ζ).2) z 1 +
          Real.exp (χT z.re) • (deriv χT z.re • vL (wrep x.1 (cplx z)) +
          vL (perF ((x.1 : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z))),
        fderiv ℝ (fun z : ℂ => β z.re • x.2.1) z 1 +
          Real.exp (χN z.re) • (deriv χN z.re • vL (wrep x.2.2 (cplx z)) +
          vL (perF ((x.2.2 : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z)))) := by
    funext z; rw [fderiv_cyl_one, fderiv_bc hβ]; simp [Ps]
  have et : Pt χT χN x = fun z =>
      (fderiv ℝ (fun ζ : ℂ => cylInf (cplx ζ).1 (cplx ζ).2) z Complex.I +
          Real.exp (χT z.re) • vL (perF ((x.1 : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z)),
        fderiv ℝ (fun z : ℂ => β z.re • x.2.1) z Complex.I +
          Real.exp (χN z.re) • vL (perF ((x.2.2 : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z))) := by
    funext z; rw [fderiv_cyl_I, fderiv_bc hβ]; simp [Pt]
  have lg : LocInt stripU (fun ζ => gC χT χN β x (cplx ζ)) := by
    rw [eg]; exact fun K hK hKc => ((a0.add b0) K hK hKc).prodMk ((c0.add d0) K hK hKc)
  refine ⟨?_, lg, ?_, ?_⟩
  · rw [eg, es, et]; exact H
  · rw [es]; exact fun K hK hKc => ((a1.add b1) K hK hKc).prodMk ((c1.add d1) K hK hKc)
  · rw [et]; exact fun K hK hKc => ((a2.add b2) K hK hKc).prodMk ((c2.add d2) K hK hKc)

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

lemma eq0_tup (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (q : ℝ × ℝ) (c a1 a2 a3 b1 b2 b3 : ℂ) :
    Eq0 Jbar χT χN β (q + tup) c a1 a2 a3 b1 b2 b3 = Eq0 Jbar χT χN β q c a1 a2 a3 b1 b2 b3 := by
  obtain ⟨s, t⟩ := q
  simp only [Eq0, tup, Prod.mk_add_mk, add_zero, cylInf_add_one]

lemma wrep_tup (w : ↥(W1p 4 1)) (q : ℝ × ℝ) : wrep w (q + tup) = wrep w q := by
  obtain ⟨s, t⟩ := q
  simp only [tup, Prod.mk_add_mk, add_zero, (wrep_prop w).2.1]

lemma pt_identity (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (x : QDom) (ζ : ℂ) :
    Ps χT χN β x ζ + Jbar (gC χT χN β x (cplx ζ)) (Pt χT χN x ζ) =
      Eq0 Jbar χT χN β (cplx ζ) x.2.1 (vecToC (wrep x.1 (cplx ζ)))
        (vecToC (perF ((x.1 : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx ζ)))
        (vecToC (perF ((x.1 : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx ζ)))
        (vecToC (wrep x.2.2 (cplx ζ)))
        (vecToC (perF ((x.2.2 : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx ζ)))
        (vecToC (perF ((x.2.2 : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx ζ))) := by
  simp only [Ps, Pt, gC, Eq0, vL_apply, Complex.real_smul, cplx_apply]

/-- R2 step 3: the a.e. equation on the plane strip. -/
theorem ae_eq_strip {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} (x : QDom)
    (h : ∀ᵐ q ∂cylMeasure, qPoint Jbar χT χN β x q = 0) :
    ∀ᵐ ζ ∂(volume.restrict stripU),
      Ps χT χN β x ζ + Jbar (gC χT χN β x (cplx ζ)) (Pt χT χN x ζ) = 0 := by
  have hP := ae_eq0 x h
  refine ae_stripU_of _ ?_
  simp only [pt_identity]
  simp only [cplx_toC]
  refine ae_of_cyl _ _ hP (fun q hq hq' => ?_) (fun q hq hq' => ?_)
  · rw [perF_of_mem _ hq, perF_of_mem _ hq, perF_of_mem _ hq, perF_of_mem _ hq]; exact hq'
  · rw [perF_of_mem_lowS _ hq, perF_of_mem_lowS _ hq, perF_of_mem_lowS _ hq,
      perF_of_mem_lowS _ hq]
    rw [eq0_tup, wrep_tup, wrep_tup] at hq'
    exact hq'

/-! ### `L⁴` on compacts -/

/-- `L⁴` on compact subsets of the strip. -/
def ML {E : Type*} [NormedAddCommGroup E] (u : ℂ → E) : Prop :=
  ∀ K ⊆ stripU, IsCompact K → MemLp u 4 (volume.restrict K)

lemma ML.of_continuous {E : Type*} [NormedAddCommGroup E] {u : ℂ → E} (hu : Continuous u) :
    ML u := by
  intro K _ hKc
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hu.continuousOn
  exact MemLp.of_bound hu.aestronglyMeasurable C
    ((ae_restrict_iff' hKc.measurableSet).2 (Eventually.of_forall hC))

lemma ML.add {E : Type*} [NormedAddCommGroup E] {u v : ℂ → E} (hu : ML u) (hv : ML v) :
    ML (fun z => u z + v z) := fun K hK hKc => (hu K hK hKc).add (hv K hK hKc)

lemma ML.smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℂ → E} (hu : ML u)
    {f : ℂ → ℝ} (hf : Continuous f) : ML (fun z => f z • u z) :=
  fun K hK hKc => memLp_K_smul hKc hf (hu K hK hKc)

lemma ML.pair {u v : ℂ → ℂ} (hu : ML u) (hv : ML v) : ML (fun z => (u z, v z)) :=
  fun K hK hKc => memLp_pair (hu K hK hKc) (hv K hK hKc)

lemma ML_perF1 (w : ↥(W1p 4 1)) :
    ML (fun z => vL (perF ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) (cplx z))) :=
  fun K hK hKc => ((weak_comp w).2 K hK hKc).2.1

lemma ML_perF2 (w : ↥(W1p 4 1)) :
    ML (fun z => vL (perF ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) (cplx z))) :=
  fun K hK hKc => ((weak_comp w).2 K hK hKc).2.2

lemma ML_wrep (w : ↥(W1p 4 1)) : ML (fun z => vL (wrep w (cplx z))) :=
  ML.of_continuous (vL.continuous.comp ((wrep_prop w).1.comp Complex.equivRealProdCLM.continuous))

lemma ML_Ps (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β) (x : QDom) :
    ML (Ps χT χN β x) := by
  have ce : ∀ {χ : ℝ → ℝ}, ContDiff ℝ ∞ χ → Continuous fun z : ℂ => Real.exp (χ z.re) :=
    fun h => Real.continuous_exp.comp (h.continuous.comp Complex.continuous_re)
  have cd : ∀ {χ : ℝ → ℝ}, ContDiff ℝ ∞ χ → Continuous fun z : ℂ => deriv χ z.re :=
    fun h => (h.continuous_deriv (by simp)).comp Complex.continuous_re
  have h1 := (ML.of_continuous (continuous_const.mul contDiff_cyl.continuous
    (f := fun _ : ℂ => ((2 * π : ℝ) : ℂ)))).add
    ((((ML_wrep x.1).smul (cd hχT)).add (ML_perF1 x.1)).smul (ce hχT))
  have h2 := (ML.of_continuous ((cd hβ).smul (continuous_const (y := x.2.1)))).add
    ((((ML_wrep x.2.2).smul (cd hχN)).add (ML_perF1 x.2.2)).smul (ce hχN))
  exact h1.pair h2

lemma ML_Pt (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (x : QDom) :
    ML (Pt χT χN x) := by
  have ce : ∀ {χ : ℝ → ℝ}, ContDiff ℝ ∞ χ → Continuous fun z : ℂ => Real.exp (χ z.re) :=
    fun h => Real.continuous_exp.comp (h.continuous.comp Complex.continuous_re)
  have hc : Continuous fun ζ : ℂ => ((2 * π : ℝ) : ℂ) * Complex.I * cylInf (cplx ζ).1 (cplx ζ).2 :=
    continuous_const.mul contDiff_cyl.continuous
  exact (ML.of_continuous hc |>.add ((ML_perF2 x.1).smul (ce hχT))).pair
    ((ML_perF2 x.2.2).smul (ce hχN))

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

lemma isAlmostComplexOn_of_std {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
    {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Sinf : ℝ → Mat 1}
    (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    IsAlmostComplexOn Jbar (univ ×ˢ ball (0 : ℂ) ρ) :=
  ⟨isOpen_univ.prod isOpen_ball, hstd.1, hstd.2.1⟩

/-- R2 step 4. -/
theorem contDiff_gC {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
    {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Sinf : ℝ → Mat 1}
    (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β) (x : QDom)
    (hO : ∀ q : ℝ × ℝ, (gC χT χN β x q).2 ∈ ball (0 : ℂ) ρ)
    (h : ∀ᵐ q ∂cylMeasure, qPoint Jbar χT χN β x q = 0) :
    ContDiff ℝ ∞ (gC χT χN β x) := by
  obtain ⟨hW, -, -, -⟩ := weak_gC hχT hχN hβ x
  have hcplx : Continuous cplx := Complex.equivRealProdCLM.continuous
  have hgc := continuous_gC hχT.continuous hχN.continuous hβ.continuous x
  have hO4 : ENNReal.ofReal 4 = 4 := by norm_num
  have hweak : IsWeakJHolomorphicOn 4 Jbar (univ ×ˢ ball (0 : ℂ) ρ) stripU
      (fun ζ => gC χT χN β x (cplx ζ)) := by
    refine ⟨(hgc.comp hcplx).continuousOn, fun ζ _ => ⟨mem_univ _, hO _⟩,
      Ps χT χN β x, Pt χT χN x, hW, fun K hK hKc => ?_, ae_eq_strip x h⟩
    rw [hO4]
    exact ⟨ML.of_continuous (hgc.comp hcplx) K hK hKc, ML_Ps hχT hχN hβ x K hK hKc,
      ML_Pt hχT hχN x K hK hKc⟩
  have hsmU : ContDiffOn ℝ ∞ (fun ζ => gC χT χN β x (cplx ζ)) stripU :=
    contDiffOn_of_isWeakJHolomorphicOn 4 (by norm_num) Jbar _ (isAlmostComplexOn_of_std hstd)
      stripU isOpen_stripU _ hweak
  have hper : ∀ s t : ℝ, gC χT χN β x (s, t + 1) = gC χT χN β x (s, t) := gC_per x
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  set k : ℤ := round y.2
  have e : gC χT χN β x = (fun ζ => gC χT χN β x (cplx ζ)) ∘ toC ∘
      fun y => y - ((0 : ℝ), (k : ℝ)) := by
    funext y; simp only [Function.comp_apply, cplx_toC, per_int hper]
  have hin : toC (y - ((0 : ℝ), (k : ℝ))) ∈ stripU := by
    simp only [stripU, mem_setOf_eq, toC_im, Prod.snd_sub]
    have := abs_sub_round y.2
    linarith
  rw [e]
  refine ContDiffAt.comp _ ((hsmU _ hin).contDiffAt (isOpen_stripU.mem_nhds hin)) ?_
  exact (Complex.equivRealProdCLM.symm.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt

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

/-- `L⁴` classical partials of a smooth representative. -/
theorem memLp_partials_wrep (w : ↥(W1p 4 1)) (hsm : ContDiff ℝ ∞ (wrep w)) :
    MemLp (partialS (wrep w)) 4 cylMeasure ∧ MemLp (partialT (wrep w)) 4 cylMeasure := by
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
  have hpull : ∀ᵐ x ∂cylMeasure, ((w : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) x = partialS (wrep w) x ∧
      ((w : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) x = partialT (wrep w) x := by
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
  exact ⟨(Lp.memLp _).ae_eq (hpull.mono fun x hx => hx.1),
    (Lp.memLp _).ae_eq (hpull.mono fun x hx => hx.2)⟩

/-- The pointwise operator of a map on `ℝ × ℝ`. -/
def dbarC (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (g : ℝ × ℝ → ℂ × ℂ) (q : ℝ × ℝ) : ℂ × ℂ :=
  fderiv ℝ g q (1, 0) + Jbar (g q) (fderiv ℝ g q (0, 1))

/-- R2 step 5: the classical equation everywhere. -/
theorem dbarC_gC {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
    {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Sinf : ℝ → Mat 1}
    (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β) (x : QDom)
    (hO : ∀ q : ℝ × ℝ, (gC χT χN β x q).2 ∈ ball (0 : ℂ) ρ)
    (h : ∀ᵐ q ∂cylMeasure, qPoint Jbar χT χN β x q = 0)
    (hsm : ContDiff ℝ ∞ (gC χT χN β x)) (q : ℝ × ℝ) :
    dbarC Jbar (gC χT χN β x) q = 0 := by
  obtain ⟨hW, -, hPs, hPt⟩ := weak_gC hχT hχN hβ x
  have hcplx : Continuous cplx := Complex.equivRealProdCLM.continuous
  have hsmC : ContDiff ℝ ∞ (fun ζ => gC χT χN β x (cplx ζ)) :=
    hsm.comp Complex.equivRealProdCLM.contDiff
  have hW' := HasWeakPartialsOn.of_contDiffOn isOpen_stripU (hsmC.of_le (by simp)).contDiffOn
  have hcd : Continuous (fderiv ℝ (fun ζ => gC χT χN β x (cplx ζ))) :=
    hsmC.continuous_fderiv (by simp)
  have hint : ∀ K ⊆ stripU, IsCompact K →
      IntegrableOn (Ps χT χN β x) K ∧ IntegrableOn (Pt χT χN x) K ∧
      IntegrableOn (fun z => fderiv ℝ (fun ζ => gC χT χN β x (cplx ζ)) z 1) K ∧
      IntegrableOn (fun z => fderiv ℝ (fun ζ => gC χT χN β x (cplx ζ)) z Complex.I) K :=
    fun K hK hKc => ⟨hPs K hK hKc, hPt K hK hKc,
      (hcd.clm_apply continuous_const).continuousOn.integrableOn_compact hKc,
      (hcd.clm_apply continuous_const).continuousOn.integrableOn_compact hKc⟩
  have heq := HasWeakPartialsOn.ae_eq isOpen_stripU hW hW' hint
  have hae := ae_eq_strip x h
  have hJc : Continuous fun ζ => Jbar (gC χT χN β x (cplx ζ)) :=
    hstd.1.continuousOn.comp_continuous hsmC.continuous fun ζ => ⟨mem_univ _, hO _⟩
  set F : ℂ → ℂ × ℂ := fun ζ => fderiv ℝ (fun ζ => gC χT χN β x (cplx ζ)) ζ 1 +
    Jbar (gC χT χN β x (cplx ζ)) (fderiv ℝ (fun ζ => gC χT χN β x (cplx ζ)) ζ Complex.I) with hF
  have hFc : Continuous F :=
    (hcd.clm_apply continuous_const).add (hJc.clm_apply (hcd.clm_apply continuous_const))
  have hF0 : F =ᵐ[volume.restrict stripU] fun _ => 0 := by
    filter_upwards [heq, hae] with ζ h1 h2
    simp only [hF, ← h1.1, ← h1.2]; exact h2
  have hEq := Measure.eqOn_open_of_ae_eq hF0 isOpen_stripU hFc.continuousOn
    continuous_const.continuousOn
  have hper : ∀ s t : ℝ, dbarC Jbar (gC χT χN β x) (s, t + 1) = dbarC Jbar (gC χT χN β x) (s, t) := by
    intro s t
    simp only [dbarC, fderiv_per (gC_per x), gC_per x]
  set k : ℤ := round q.2
  have hin : toC (q - ((0 : ℝ), (k : ℝ))) ∈ stripU := by
    simp only [stripU, mem_setOf_eq, toC_im, Prod.snd_sub]
    have := abs_sub_round q.2
    linarith
  rw [← per_int hper q k]
  have := hEq hin
  simp only [hF, fderiv_comp_cplx, cplx_toC] at this
  simpa [dbarC, cplx_apply] using this

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

/-- Energy of the plane map on the punctured disc. -/
theorem lintegral_pfG_lt_top (hG : ContDiff ℝ ∞ G) (hper : ∀ s t : ℝ, G (s, t + 1) = G (s, t))
    (hneg : ∫⁻ x in negS, ENNReal.ofReal (‖fderiv ℝ G x‖ ^ 2) < ⊤) :
    ∫⁻ z in ball (0 : ℂ) 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ (pfG c₀ G) z‖ ^ 2) < ⊤ := by
  have hd : ∀ ξ ∈ negC, HasFDerivWithinAt Eexp ((ContinuousLinearMap.toSpanSingleton ℂ
      (Eexp ξ * ((2 * π : ℝ) : ℂ))).restrictScalars ℝ) negC ξ :=
    fun ξ _ => (hasFDerivAt_Eexp ξ).hasFDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_negC hd
    injOn_Eexp (fun z => ENNReal.ofReal (‖fderiv ℝ (pfG c₀ G) z‖ ^ 2))
  have hmeas : Measurable fun ξ : ℂ => ENNReal.ofReal (‖fderiv ℝ G (cplx ξ)‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp
      ((((hG.continuous_fderiv (by simp)).comp
        Complex.equivRealProdCLM.continuous).norm.pow 2).measurable)
  have hmp := measurePreserving_cplx.restrict_preimage measurableSet_negS
  have hcomp : ∫⁻ ξ in negC, ENNReal.ofReal (‖fderiv ℝ G (cplx ξ)‖ ^ 2) =
      ∫⁻ x in negS, ENNReal.ofReal (‖fderiv ℝ G x‖ ^ 2) :=
    hmp.lintegral_comp (f := fun x => ENNReal.ofReal (‖fderiv ℝ G x‖ ^ 2))
      (ENNReal.measurable_ofReal.comp
        (((hG.continuous_fderiv (by simp)).norm.pow 2).measurable))
  calc ∫⁻ z in ball (0 : ℂ) 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ (pfG c₀ G) z‖ ^ 2)
      ≤ ∫⁻ z in Eexp '' negC, ENNReal.ofReal (‖fderiv ℝ (pfG c₀ G) z‖ ^ 2) :=
        lintegral_mono_set subset_image_negC
    _ = _ := key
    _ ≤ ∫⁻ ξ in negC, ENNReal.ofReal (‖fderiv ℝ G (cplx ξ)‖ ^ 2) := by
        refine setLIntegral_mono hmeas fun ξ _ => ?_
        rw [det_mul_restrict, abs_of_nonneg (Complex.normSq_nonneg _),
          ← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Complex.normSq_eq_norm_sq, ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (norm_mul_norm_fderiv_pfG_le hG hper ξ) 2
    _ = _ := hcomp
    _ < ⊤ := hneg

/-- The plane equation at `z ≠ 0`: for `A : ℂ →L[ℝ] E` and `J` with `J² = -1`,
`A w + J (A (w i)) = 0` for one `w ≠ 0` gives `A 1 + J (A i) = 0`. -/
lemma plane_transfer (A : ℂ →L[ℝ] E) (J : E →L[ℝ] E) (hJ : J.comp J = -ContinuousLinearMap.id ℝ E)
    {w : ℂ} (hw : w ≠ 0) (h : A w + J (A (w * Complex.I)) = 0) :
    A 1 + J (A Complex.I) = 0 := by
  have hJJ : ∀ y, J (J y) = -y := fun y => by
    have := congrArg (fun L : E →L[ℝ] E => L y) hJ; simpa using this
  -- `A (w i) = J (A w)`
  have h1 : A (w * Complex.I) = J (A w) := by
    have := congrArg J h
    rw [map_add, hJJ, map_zero, add_comm, neg_add_eq_zero] at this
    exact this
  -- `E v = A v + J (A (v i))` vanishes at `w` and at `w i`
  have hE : ∀ v : ℂ, A v + J (A (v * Complex.I)) = 0 →
      A (v * Complex.I) + J (A (v * Complex.I * Complex.I)) = 0 := by
    intro v hv
    have hvI : A (v * Complex.I * Complex.I) = -A v := by
      rw [mul_assoc, Complex.I_mul_I, mul_neg_one, map_neg]
    rw [hvI, map_neg]
    have := congrArg J hv
    rw [map_add, hJJ, map_zero, add_comm, neg_add_eq_zero] at this
    rw [this, add_neg_cancel]
  have h2 := hE w h
  -- `1 = a w + b (w i)` with `a, b` real
  set u : ℂ := w⁻¹ with hu
  have hdec : (1 : ℂ) = u.re • w + u.im • (w * Complex.I) := by
    have : (1 : ℂ) = u * w := by rw [hu, inv_mul_cancel₀ hw]
    conv_lhs => rw [this]
    rw [Complex.real_smul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im u]
    ring
  have hdecI : Complex.I = u.re • (w * Complex.I) + u.im • (w * Complex.I * Complex.I) := by
    have := congrArg (· * Complex.I) hdec
    simp only [one_mul, add_mul, smul_mul_assoc] at this
    exact this
  have a1 : A 1 = u.re • A w + u.im • A (w * Complex.I) := by
    conv_lhs => rw [hdec]
    simp only [map_add, map_smul]
  have aI : A Complex.I = u.re • A (w * Complex.I) + u.im • A (w * Complex.I * Complex.I) := by
    conv_lhs => rw [hdecI]
    simp only [map_add, map_smul]
  rw [a1, aI]
  calc _ = u.re • (A w + J (A (w * Complex.I))) +
        u.im • (A (w * Complex.I) + J (A (w * Complex.I * Complex.I))) := by
          simp only [map_add, map_smul, smul_add]; abel
    _ = 0 := by rw [h, h2, smul_zero, smul_zero, add_zero]

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

lemma vecToC_smul' (r : ℝ) (a : Vec 1) : vecToC (r • a) = (r : ℂ) * vecToC a := by
  rw [← vL_apply, map_smul, vL_apply, Complex.real_smul]

/-- The bridge. -/
theorem pG_eq_pfG (x : QDom) : pG χT χN β x = pfG ((0 : ℂ), x.2.1) (gC χT χN β x) := by
  funext z
  by_cases hz : z = 0
  · subst hz; rw [pfG_zero, pG, pLc_zero]; simp
  · rw [pfG_ne hz, pG, pLc_ne _ _ _ hz, wV_apply, U_apply]
    simp only [Uv, gC, zc]
    rw [cylInf_log_arg hz]
    refine Prod.ext ?_ ?_ <;> simp [Complex.real_smul]

lemma pG_fst_eq (x : QDom) (z : ℂ) :
    (pG χT χN β x z).1 = z + pf (vOf χT (wrep x.1)) z := by
  by_cases hz : z = 0
  · subst hz; simp [pG, pLc_zero, pf_zero]
  · rw [pG, pLc_ne _ _ _ hz, wV_apply, U_apply, pf, if_neg hz]
    simp [Uv, vOf, zc, vecToC_smul']

lemma log_div_le {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < Real.exp (-(2 * π))) :
    Real.log ‖z‖ / (2 * π) ≤ -1 := by
  rw [div_le_iff₀ (by positivity)]
  have := (Real.log_lt_iff_lt_exp (norm_pos_iff.2 hz0)).2 hz
  linarith

lemma pG_snd_eq_near (hβ : IsLeftCutoff β) (x : QDom) {z : ℂ}
    (hz : ‖z‖ < Real.exp (-(2 * π))) :
    (pG χT χN β x z).2 = x.2.1 + pf (vOf χN (wrep x.2.2)) z := by
  by_cases hz0 : z = 0
  · subst hz0; simp [pG, pLc_zero, pf_zero]
  · have hb : β (Real.log ‖z‖ / (2 * π)) = 1 := hβ.2.1 _ (log_div_le hz0 hz)
    rw [pG, pLc_ne _ _ _ hz0, wV_apply, U_apply, pf, if_neg hz0]
    simp [Uv, vOf, zc, vecToC_smul', hb]

/-- Continuity at the puncture. -/
theorem continuousAt_pG_zero {a b : ℝ} (hχT : IsSlopeWeight χT π a)
    (hχN : IsSlopeWeight χN π b) (hβ : IsLeftCutoff β) (x : QDom) :
    ContinuousAt (pG χT χN β x) 0 := by
  have h1 : ContinuousAt (fun z => (pG χT χN β x z).1) 0 := by
    have e : (fun z => (pG χT χN β x z).1) = fun z => z + pf (vOf χT (wrep x.1)) z :=
      funext (pG_fst_eq x)
    rw [e]
    exact continuousAt_id.add (tendsto_pf_zero _ (wrep x.1) (wrep_bound x.1) χT
      (fun s hs => hχT.eq_left hs) (fun _ => rfl))
  have h2 : ContinuousAt (fun z => (pG χT χN β x z).2) 0 := by
    have hc : ContinuousAt (fun z => x.2.1 + pf (vOf χN (wrep x.2.2)) z) 0 :=
      continuousAt_const.add (tendsto_pf_zero _ (wrep x.2.2) (wrep_bound x.2.2) χN
        (fun s hs => hχN.eq_left hs) (fun _ => rfl))
    refine hc.congr ?_
    filter_upwards [ball_mem_nhds (0 : ℂ) (Real.exp_pos (-(2 * π)))] with z hz
    rw [mem_ball_zero_iff] at hz
    exact (pG_snd_eq_near hβ x hz).symm
  exact h1.prodMk h2

/-! ### Finite cylinder energy on `negS` -/

lemma lint_lt_top {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {f g h k : ℝ × ℝ → ℝ}
    (hg0 : ∀ q, 0 ≤ g q) (hh0 : ∀ q, 0 ≤ h q) (hk0 : ∀ q, 0 ≤ k q)
    (hgm : Measurable g) (hhm : Measurable h)
    (hle : ∀ q ∈ S, f q ≤ g q + h q + k q)
    (hg : ∫⁻ q in S, ENNReal.ofReal (g q) < ⊤) (hh : ∫⁻ q in S, ENNReal.ofReal (h q) < ⊤)
    (hk : ∫⁻ q in S, ENNReal.ofReal (k q) < ⊤) :
    ∫⁻ q in S, ENNReal.ofReal (f q) < ⊤ := by
  calc ∫⁻ q in S, ENNReal.ofReal (f q)
      ≤ ∫⁻ q in S, (ENNReal.ofReal (g q) + ENNReal.ofReal (h q)) + ENNReal.ofReal (k q) := by
        refine setLIntegral_mono' hS fun q hq => ?_
        rw [← ENNReal.ofReal_add (hg0 q) (hh0 q),
          ← ENNReal.ofReal_add (add_nonneg (hg0 q) (hh0 q)) (hk0 q)]
        exact ENNReal.ofReal_le_ofReal (hle q hq)
    _ = (∫⁻ q in S, ENNReal.ofReal (g q)) + (∫⁻ q in S, ENNReal.ofReal (h q)) +
          ∫⁻ q in S, ENNReal.ofReal (k q) := by
        have m1 : Measurable fun q => ENNReal.ofReal (g q) := ENNReal.measurable_ofReal.comp hgm
        have m2 : Measurable fun q => ENNReal.ofReal (h q) := ENNReal.measurable_ofReal.comp hhm
        rw [lintegral_add_left' (f := fun q => ENNReal.ofReal (g q) + ENNReal.ofReal (h q))
          (m1.add m2).aemeasurable, lintegral_add_left' m1.aemeasurable]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hg, hh⟩, hk⟩

lemma lint_const_mul_lt_top {S : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hf : ∫⁻ q in S, ENNReal.ofReal (f q) < ⊤) :
    ∫⁻ q in S, ENNReal.ofReal (K * f q) < ⊤ := by
  simp only [ENNReal.ofReal_mul hK]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

lemma sq_sum4_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

lemma deriv_beta_eq_zero (hβ : IsLeftCutoff β) {s : ℝ} (hs : s < -1) : deriv β s = 0 := by
  have : β =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds hs] with r hr
    exact hβ.2.1 r (le_of_lt hr)
  rw [this.deriv_eq, deriv_const]

/-- The cylinder part. -/
lemma norm_fderiv_cyl_le (q : ℝ × ℝ) :
    ‖fderiv ℝ (fun q : ℝ × ℝ => cylInf q.1 q.2) q‖ ≤
      (2 * π) * ‖(Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)‖ * Real.exp (2 * π * q.1) := by
  have h := (hasFDerivAt_Ecyl q).fderiv
  have e : (fun q : ℝ × ℝ => cylInf q.1 q.2) = Ecyl := rfl
  rw [e, h]
  refine (norm_smul_le (((2 * π : ℝ) : ℂ) * Ecyl q)
    (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), Ecyl,
    norm_cylInf]
  ring

/-- R2 step 6a: finite cylinder energy. -/
theorem lintegral_gC_negS {a δ : ℝ} (hχT : IsSlopeWeight χT π a) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) (x : QDom) (h1 : ContDiff ℝ ∞ (wrep x.1))
    (h2 : ContDiff ℝ ∞ (wrep x.2.2)) :
    ∫⁻ q in negS, ENNReal.ofReal (‖fderiv ℝ (gC χT χN β x) q‖ ^ 2) < ⊤ := by
  set c : ℂ := x.2.1
  -- the four pieces
  have hA : ContDiff ℝ ∞ (fun q : ℝ × ℝ => cylInf q.1 q.2) := contDiff_cylP
  have hB : ContDiff ℝ ∞ (fun q => vL (vOf χT (wrep x.1) q)) :=
    vL.contDiff.comp (vOf_contDiff hχT.1 h1)
  have hC : ContDiff ℝ ∞ (fun q : ℝ × ℝ => β q.1 • c) :=
    (hβ.1.comp contDiff_fst).smul contDiff_const
  have hD : ContDiff ℝ ∞ (fun q => vL (vOf χN (wrep x.2.2) q)) :=
    vL.contDiff.comp (vOf_contDiff hχN.1 h2)
  have hg : gC χT χN β x = fun q => (cylInf q.1 q.2 + vL (vOf χT (wrep x.1) q),
      β q.1 • c + vL (vOf χN (wrep x.2.2) q)) := by
    funext q; simp only [gC, vOf, map_smul]; rfl
  have d1 : ∀ {f : ℝ × ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ q, HasFDerivAt f (fderiv ℝ f q) q :=
    fun hf q => (hf.differentiable (by simp) q).hasFDerivAt
  have hfd : ∀ q, fderiv ℝ (gC χT χN β x) q =
      (fderiv ℝ (fun q : ℝ × ℝ => cylInf q.1 q.2) q +
        fderiv ℝ (fun q => vL (vOf χT (wrep x.1) q)) q).prod
      (fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q +
        fderiv ℝ (fun q => vL (vOf χN (wrep x.2.2) q)) q) := by
    intro q
    rw [hg]
    exact (((d1 hA q).add (d1 hB q)).prodMk ((d1 hC q).add (d1 hD q))).fderiv
  -- bounds of the pieces
  set K0 := ‖(Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)‖
  have bA : ∀ q, ‖fderiv ℝ (fun q : ℝ × ℝ => cylInf q.1 q.2) q‖ ≤
      (2 * π) * K0 * Real.exp (2 * π * q.1) := norm_fderiv_cyl_le
  have bB : ∀ q, ‖fderiv ℝ (fun q => vL (vOf χT (wrep x.1) q)) q‖ ≤
      ‖vL‖ * ‖fderiv ℝ (vOf χT (wrep x.1)) q‖ := by
    intro q
    rw [fderiv_comp' q vL.differentiableAt ((vOf_contDiff hχT.1 h1).differentiable (by simp) q),
      ContinuousLinearMap.fderiv]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have bD : ∀ q, ‖fderiv ℝ (fun q => vL (vOf χN (wrep x.2.2) q)) q‖ ≤
      ‖vL‖ * ‖fderiv ℝ (vOf χN (wrep x.2.2)) q‖ := by
    intro q
    rw [fderiv_comp' q vL.differentiableAt ((vOf_contDiff hχN.1 h2).differentiable (by simp) q),
      ContinuousLinearMap.fderiv]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  obtain ⟨Mb, hMb⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 0)).exists_bound_of_continuousOn
    (hβ.1.continuous_deriv (by simp)).continuousOn
  set K1 := ‖(ContinuousLinearMap.fst ℝ ℝ ℝ)‖ * ‖c‖
  have bC0 : ∀ q : ℝ × ℝ, ‖fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q‖ ≤ |deriv β q.1| * K1 := by
    intro q
    have hd : HasFDerivAt (fun q : ℝ × ℝ => β q.1 • c)
        ((deriv β q.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight c) q := by
      have := (((hβ.1.differentiable (by simp)) q.1).hasDerivAt.comp_hasFDerivAt q
        (hasFDerivAt_fst (𝕜 := ℝ) (p := q))).smul_const c
      exact this
    rw [hd.fderiv, ContinuousLinearMap.norm_smulRight_apply]
    refine (mul_le_mul_of_nonneg_right (norm_smul_le (deriv β q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ)) (norm_nonneg _)).trans (le_of_eq ?_)
    rw [Real.norm_eq_abs]; ring
  have bC : ∀ q ∈ negS, ‖fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q‖ ^ 2 ≤
      (Mb ^ 2 * K1 ^ 2 * Real.exp (2 * π)) * Real.exp (2 * π * q.1) := by
    intro q hq
    have hs : q.1 < 0 := hq.1
    have hK1 : 0 ≤ K1 := by positivity
    rcases lt_or_ge q.1 (-1) with h | h
    · have := bC0 q
      rw [deriv_beta_eq_zero hβ h, abs_zero, zero_mul] at this
      have h0 : ‖fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q‖ = 0 :=
        le_antisymm this (norm_nonneg _)
      rw [h0, zero_pow two_ne_zero]; positivity
    · have hb : |deriv β q.1| ≤ Mb := by
        have := hMb q.1 ⟨h, hs.le⟩; rwa [Real.norm_eq_abs] at this
      have he : 1 ≤ Real.exp (2 * π) * Real.exp (2 * π * q.1) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [Real.pi_pos])
      have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans hb
      calc ‖fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q‖ ^ 2 ≤ (|deriv β q.1| * K1) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (bC0 q) 2
        _ ≤ (Mb * K1) ^ 2 := by gcongr
        _ = Mb ^ 2 * K1 ^ 2 * 1 := by ring
        _ ≤ Mb ^ 2 * K1 ^ 2 * (Real.exp (2 * π) * Real.exp (2 * π * q.1)) := by gcongr
        _ = _ := by ring
  -- the energy bound
  set KE := 4 * ((2 * π * K0) ^ 2 + Mb ^ 2 * K1 ^ 2 * Real.exp (2 * π))
  have hKE : 0 ≤ KE := by positivity
  have hle : ∀ q ∈ negS, ‖fderiv ℝ (gC χT χN β x) q‖ ^ 2 ≤
      KE * Real.exp (2 * π * q.1) + (4 * ‖vL‖ ^ 2) * ‖fderiv ℝ (vOf χT (wrep x.1)) q‖ ^ 2 + (4 * ‖vL‖ ^ 2) * ‖fderiv ℝ (vOf χN (wrep x.2.2)) q‖ ^ 2 := by
    intro q hq
    have hs : q.1 < 0 := hq.1
    have hn : ‖fderiv ℝ (gC χT χN β x) q‖ ≤
        ‖fderiv ℝ (fun q : ℝ × ℝ => cylInf q.1 q.2) q‖ +
          ‖fderiv ℝ (fun q => vL (vOf χT (wrep x.1) q)) q‖ +
          ‖fderiv ℝ (fun q : ℝ × ℝ => β q.1 • c) q‖ +
          ‖fderiv ℝ (fun q => vL (vOf χN (wrep x.2.2) q)) q‖ := by
      rw [hfd, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
      refine max_le ((norm_add_le _ _).trans (by linarith [norm_nonneg (fderiv ℝ
        (fun q : ℝ × ℝ => β q.1 • c) q), norm_nonneg (fderiv ℝ
        (fun q => vL (vOf χN (wrep x.2.2) q)) q)]))
        ((norm_add_le _ _).trans (by linarith [norm_nonneg (fderiv ℝ
        (fun q : ℝ × ℝ => cylInf q.1 q.2) q), norm_nonneg (fderiv ℝ
        (fun q => vL (vOf χT (wrep x.1) q)) q)]))
    have hsq := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (sq_sum4_le _ _ _ _)
    have eA : ‖fderiv ℝ (fun q : ℝ × ℝ => cylInf q.1 q.2) q‖ ^ 2 ≤
        (2 * π * K0) ^ 2 * Real.exp (2 * π * q.1) := by
      calc _ ≤ ((2 * π) * K0 * Real.exp (2 * π * q.1)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (bA q) 2
        _ = (2 * π * K0) ^ 2 * Real.exp (2 * π * q.1 + 2 * π * q.1) := by
            rw [Real.exp_add]; ring
        _ ≤ (2 * π * K0) ^ 2 * Real.exp (2 * π * q.1) := by
            gcongr; nlinarith [Real.pi_pos]
    have eB : ‖fderiv ℝ (fun q => vL (vOf χT (wrep x.1) q)) q‖ ^ 2 ≤ ‖vL‖ ^ 2 * ‖fderiv ℝ (vOf χT (wrep x.1)) q‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (bB q) 2
    have eD : ‖fderiv ℝ (fun q => vL (vOf χN (wrep x.2.2) q)) q‖ ^ 2 ≤ ‖vL‖ ^ 2 * ‖fderiv ℝ (vOf χN (wrep x.2.2)) q‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (bD q) 2
    have eC := bC q hq
    have he0 : 0 ≤ Real.exp (2 * π * q.1) := (Real.exp_pos _).le
    calc ‖fderiv ℝ (gC χT χN β x) q‖ ^ 2 ≤ _ := hsq
      _ ≤ 4 * ((2 * π * K0) ^ 2 * Real.exp (2 * π * q.1) + ‖vL‖ ^ 2 * ‖fderiv ℝ (vOf χT (wrep x.1)) q‖ ^ 2 +
          (Mb ^ 2 * K1 ^ 2 * Real.exp (2 * π)) * Real.exp (2 * π * q.1) + ‖vL‖ ^ 2 * ‖fderiv ℝ (vOf χN (wrep x.2.2)) q‖ ^ 2) := by
          gcongr
      _ = _ := by simp only [KE]; ring
  have hV1 : ∫⁻ q in negS, ENNReal.ofReal (‖fderiv ℝ (vOf χT (wrep x.1)) q‖ ^ 2) < ⊤ := by
    obtain ⟨p1, p2⟩ := memLp_partials_wrep x.1 h1
    exact lintegral_negS_lt_top 4 (by norm_num) (by norm_num) a hχT h1 _
      (wrep_bound x.1) p1 p2
  have hV2 : ∫⁻ q in negS, ENNReal.ofReal (‖fderiv ℝ (vOf χN (wrep x.2.2)) q‖ ^ 2) < ⊤ := by
    obtain ⟨p1, p2⟩ := memLp_partials_wrep x.2.2 h2
    exact lintegral_negS_lt_top 4 (by norm_num) (by norm_num) δ hχN h2 _
      (wrep_bound x.2.2) p1 p2
  have hE : ∫⁻ q in negS, ENNReal.ofReal (KE * Real.exp (2 * π * q.1)) < ⊤ :=
    (integrableOn_exp_negS.const_mul KE).lintegral_lt_top
  have hm1 : Measurable fun q : ℝ × ℝ => KE * Real.exp (2 * π * q.1) := by fun_prop
  have hm2 : Measurable fun q : ℝ × ℝ => (4 * ‖vL‖ ^ 2) * ‖fderiv ℝ (vOf χT (wrep x.1)) q‖ ^ 2 :=
    (continuous_const.mul (((vOf_contDiff hχT.1 h1).continuous_fderiv
      (by simp)).norm.pow 2)).measurable
  exact lint_lt_top measurableSet_negS (fun q => by positivity) (fun q => by positivity)
    (fun q => by positivity) hm1 hm2 hle hE (lint_const_mul_lt_top (by positivity) hV1)
    (lint_const_mul_lt_top (by positivity) hV2)

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

/-- Regularity of one member, from the cylinder facts. -/
theorem member_regular_of {ρ b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
    {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Sinf : ℝ → Mat 1}
    (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) {a δ : ℝ}
    (hχT : IsSlopeWeight χT π a) (hχN : IsSlopeWeight χN π δ) (hβ : IsLeftCutoff β)
    (x : QDom) (hc : ‖x.2.1‖ < ρ)
    (hO : ∀ q : ℝ × ℝ, (gC χT χN β x q).2 ∈ ball (0 : ℂ) ρ)
    (hae : ∀ᵐ q ∂cylMeasure, qPoint Jbar χT χN β x q = 0) :
    ContDiff ℝ ∞ (pG χT χN β x) ∧ IsJHolomorphicOn Jbar univ (pG χT χN β x) := by
  have hsm := contDiff_gC hstd hχT.1 hχN.1 hβ.1 x hO hae
  have hdb := dbarC_gC hstd hχT.1 hχN.1 hβ.1 x hO hae hsm
  have h1 := contDiff_wrep1 (χN := χN) (β := β) hχT.1 x hsm
  have h2 := contDiff_wrep2 (χT := χT) hχN.1 hβ.1 x hsm
  have hper : ∀ s t : ℝ, gC χT χN β x (s, t + 1) = gC χT χN β x (s, t) := gC_per x
  have key := pG_eq_pfG (χT := χT) (χN := χN) (β := β) x
  have hval : ∀ z, z ≠ 0 → pG χT χN β x z = gC χT χN β x (zc z) := by
    intro z hz; rw [key, pfG_ne hz]
  have hmapsU : ∀ z, pG χT χN β x z ∈ univ ×ˢ ball (0 : ℂ) ρ := by
    intro z
    by_cases hz : z = 0
    · subst hz; rw [key, pfG_zero]; exact ⟨mem_univ _, mem_ball_zero_iff.2 hc⟩
    · rw [hval z hz]; exact ⟨mem_univ _, hO _⟩
  have off0 : ∀ z, z ≠ 0 → ContDiffAt ℝ ∞ (pG χT χN β x) z := by
    intro z hz; rw [key]; exact pfG_contDiffAt hsm hper hz
  have hol0 : ∀ z, z ≠ 0 → DifferentiableAt ℝ (pG χT χN β x) z ∧
      dbarJ Jbar (pG χT χN β x) z = 0 := by
    intro z hz
    refine ⟨(off0 z hz).differentiableAt (by simp), ?_⟩
    have hJ := hstd.2.1 _ (hmapsU z)
    have hw : ((2 * π : ℝ) : ℂ) * z ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) hz
    have d1 := fderiv_pfG_cylInf (c₀ := ((0 : ℂ), x.2.1)) hsm hper (zc z) 1
    have dI := fderiv_pfG_cylInf (c₀ := ((0 : ℂ), x.2.1)) hsm hper (zc z) Complex.I
    rw [Ecyl_zc hz, ← key, mul_one] at d1
    rw [Ecyl_zc hz, ← key] at dI
    have e := hdb (zc z)
    rw [dbarC, ← hval z hz] at e
    have hc1 : cplx (1 : ℂ) = (1, 0) := by simp [cplx_apply]
    have hcI : cplx Complex.I = (0, 1) := by simp [cplx_apply]
    rw [hc1] at d1
    rw [hcI] at dI
    refine plane_transfer (fderiv ℝ (pG χT χN β x) z) (Jbar (pG χT χN β x z)) hJ hw ?_
    rw [d1, dI]; exact e
  have hE : ∫⁻ z in ball (0 : ℂ) 1 \ {0},
      ENNReal.ofReal (‖fderiv ℝ (pG χT χN β x) z‖ ^ 2) < ⊤ := by
    rw [key]; exact lintegral_pfG_lt_top hsm hper (lintegral_gC_negS hχT hχN hβ x h1 h2)
  have hcont : ContinuousOn (pG χT χN β x) (ball 0 1) := by
    intro z _
    by_cases hz : z = 0
    · subst hz; exact (continuousAt_pG_zero hχT hχN hβ x).continuousWithinAt
    · exact (off0 z hz).continuousAt.continuousWithinAt
  have rem := contDiffOn_ball_of_energy_lt_top Jbar _ (isAlmostComplexOn_of_std hstd)
    (pG χT χN β x) hcont (fun z hz => (off0 z hz.2).contDiffWithinAt)
    (fun z hz => hol0 z hz.2) (fun z _ => hmapsU z) hE
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  refine ⟨contDiff_iff_contDiffAt.2 fun z => ?_, fun z _ => ?_⟩
  · by_cases hz : z = 0
    · subst hz; exact (rem.1 0 h0).contDiffAt (ball_mem_nhds _ one_pos)
    · exact off0 z hz
  · by_cases hz : z = 0
    · subst hz; exact rem.2 0 h0
    · exact hol0 z hz

/-- R2. -/
theorem member_regular_proof (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 →
      ContDiff ℝ ∞ (pG χT χN β x) ∧ JHolomorphic.IsJHolomorphicOn Jbar univ (pG χT χN β x) := by
  obtain ⟨ε1, hε1, hq⟩ :=
    ae_qPoint_eq_zero ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨ε2, hε2, hmap⟩ := exists_mapsTo (χT := χT) hρ hδ hχN hβ
  refine ⟨min (min ε1 ε2) ρ, lt_min (lt_min hε1 hε2) hρ, fun x hx h0 => ?_⟩
  have hx' : ‖x‖ < min (min ε1 ε2) ρ := mem_ball_zero_iff.1 hx
  have hx1 : ‖x‖ < ε1 := lt_of_lt_of_le hx' ((min_le_left _ _).trans (min_le_left _ _))
  have hx2 : ‖x‖ < ε2 := lt_of_lt_of_le hx' ((min_le_left _ _).trans (min_le_right _ _))
  have hx3 : ‖x‖ < ρ := lt_of_lt_of_le hx' (min_le_right _ _)
  have hc : ‖x.2.1‖ < ρ := lt_of_le_of_lt ((norm_fst_le x.2).trans (norm_snd_le x)) hx3
  exact member_regular_of hstd hχT hχN hβ x hc (hmap x hx2)
    (hq x (mem_ball_zero_iff.2 hx1) h0)

end QR10

end

end FiniteEnergyPlane

-- FILE: RSK_RP2.lean
namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QRB

theorem contDiff_qMember_of_qMap_eq_zero_proof (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 →
      ContDiff ℝ ∞ (qMember χT χN β x) ∧
        JHolomorphic.IsJHolomorphicOn Jbar univ (qMember χT χN β x) := by
  rw [← pG_eq_qMember]
  exact QR10.member_regular_proof ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ

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
    ∃ ε > 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 →
      ContDiff ℝ ∞ (qMember χT χN β x) ∧
        JHolomorphic.IsJHolomorphicOn Jbar univ (qMember χT χN β x) :=
  QRB.contDiff_qMember_of_qMap_eq_zero_proof ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
