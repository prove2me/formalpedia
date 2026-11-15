-- Prove2me | solution 1 for FiniteEnergyPlane.contDiffOn_qFamily_of_qMap_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T10:36:12.905724+00:00
-- url     : https://prove2.me/submissions/faaca000-cefb-4ecd-9458-ccf57c371d8c

import Definitions.Def_FiniteEnergyPlane_QMember
import Theorems.Thm_CauchyRiemannIndex_exists_continuous_representative_of_mem_W1p
import Theorems.Thm_CauchyRiemannIndex_eq_of_continuous_periodic_ae_eq
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_hadamard_integral_fderiv
import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_bounded_iteratedFDeriv_of_sobolevNorm_le
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Theorems.Thm_JHolomorphic_exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv
import Theorems.Thm_JHolomorphic_contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv
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
import Theorems.Thm_JHolomorphic_contDiffOn_of_isWeakJHolomorphicOn
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_prodMk
import Theorems.Thm_JHolomorphic_memLp_of_continuousOn_compact
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq
import Theorems.Thm_FiniteEnergyPlane_exists_smooth_qPoint_rep
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_ball_of_energy_lt_top
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

-- FILE: _imports_RSK_RP3.lean


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

/-- The family of a curve. -/
def fam (χT χN β : ℝ → ℝ) (γ : ℝ → QDom) (p : ℂ × ℝ) : ℂ × ℂ := pG χT χN β (γ p.2) p.1

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

lemma fam_eq_qFamily (χT χN β : ℝ → ℝ) : fam χT χN β = qFamily χT χN β := by
  funext γ p
  simp only [fam, qFamily, pG_eq_qMember]

end QRB

end

end FiniteEnergyPlane

-- FILE: RSK_R24.lean
/-!
# Q-R, layer 24 (local, NOT published): joint smoothness from partial derivatives

Pure calculus on `ℂ × ℝ`, for R3 `fam_contDiffOn`.
* `hasFDerivAt_of_partials`: a continuous `ζ`-partial and a `t`-partial at the point give a
  derivative.
* `hasDerivAt_fderiv_swap`: interchange of the `t`-derivative with the `ζ`-derivative.
* `contDiffOn_of_partials`: a family `G k` with smooth `ζ`-slices, jointly continuous
  `ζ`-derivatives of all orders and `∂ₜ G k = G (k+1)` is jointly `C^n` for every `n`.
-/

namespace FiniteEnergyPlane

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace QR24

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The derivative of a map on `ℂ × ℝ` from a continuous `ζ`-partial and a `t`-partial. -/
theorem hasFDerivAt_of_partials {W : Set (ℂ × ℝ)} (hW : IsOpen W) {f : ℂ × ℝ → X}
    {A : ℂ × ℝ → ℂ →L[ℝ] X} {B : X} {p : ℂ × ℝ} (hp : p ∈ W)
    (hA : ∀ q ∈ W, HasFDerivAt (fun ζ => f (ζ, q.2)) (A q) q.1)
    (hAc : ContinuousAt A p)
    (hB : HasDerivAt (fun t => f (p.1, t)) B p.2) :
    HasFDerivAt f ((A p).comp (ContinuousLinearMap.fst ℝ ℂ ℝ) +
      (ContinuousLinearMap.snd ℝ ℂ ℝ).smulRight B) p := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ₁, hδ₁, hW⟩ := Metric.isOpen_iff.1 hW p hp
  obtain ⟨δ₂, hδ₂, hA2⟩ := Metric.continuousAt_iff.1 hAc (c / 2) (half_pos hc)
  set δ := min δ₁ δ₂ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hB2 := Asymptotics.isLittleO_iff.1 (hasDerivAt_iff_isLittleO.1 hB) (half_pos hc)
  have hB3 : ∀ᶠ q in 𝓝 p, ‖f (p.1, q.2) - f (p.1, p.2) - (q.2 - p.2) • B‖ ≤
      c / 2 * ‖q.2 - p.2‖ :=
    continuous_snd.continuousAt.tendsto.eventually hB2
  filter_upwards [hB3, ball_mem_nhds p hδ] with q hq1 hq2
  have hq2' : dist q p < δ := hq2
  have hs : ∀ ζ ∈ ball p.1 δ, (ζ, q.2) ∈ ball p δ := by
    intro ζ hζ
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨hζ, lt_of_le_of_lt ?_ hq2'⟩
    rw [Prod.dist_eq]; exact le_max_right _ _
  have hsW : ∀ ζ ∈ ball p.1 δ, (ζ, q.2) ∈ W := fun ζ hζ =>
    hW (mem_ball.2 (lt_of_lt_of_le (mem_ball.1 (hs ζ hζ)) (min_le_left _ _)))
  have hsA : ∀ ζ ∈ ball p.1 δ, ‖A (ζ, q.2) - A p‖ ≤ c / 2 := fun ζ hζ => by
    have := hA2 (lt_of_lt_of_le (mem_ball.1 (hs ζ hζ)) (min_le_right _ _))
    rw [dist_eq_norm] at this; exact this.le
  have hq1m : q.1 ∈ ball p.1 δ := by
    rw [mem_ball]; refine lt_of_le_of_lt ?_ hq2'
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le' (f := fun ζ => f (ζ, q.2)) (φ := A p)
    (C := c / 2) (s := ball p.1 δ)
    (fun ζ hζ => (hA (ζ, q.2) (hsW ζ hζ)).differentiableAt)
    (fun ζ hζ => by rw [(hA (ζ, q.2) (hsW ζ hζ)).fderiv]; exact hsA ζ hζ) (convex_ball _ _)
    (mem_ball_self hδ) hq1m
  have e : f q - f p - ((A p).comp (ContinuousLinearMap.fst ℝ ℂ ℝ) +
      (ContinuousLinearMap.snd ℝ ℂ ℝ).smulRight B) (q - p) =
      (f (q.1, q.2) - f (p.1, q.2) - A p (q.1 - p.1)) +
        (f (p.1, q.2) - f (p.1, p.2) - (q.2 - p.2) • B) := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub]
    abel
  rw [e]
  calc _ ≤ ‖f (q.1, q.2) - f (p.1, q.2) - A p (q.1 - p.1)‖ +
        ‖f (p.1, q.2) - f (p.1, p.2) - (q.2 - p.2) • B‖ := norm_add_le _ _
    _ ≤ c / 2 * ‖q.1 - p.1‖ + c / 2 * ‖q.2 - p.2‖ := add_le_add hmv hq1
    _ ≤ c / 2 * ‖q - p‖ + c / 2 * ‖q - p‖ := by
        gcongr
        · exact norm_fst_le (q - p)
        · exact norm_snd_le (q - p)
    _ = c * ‖q - p‖ := by ring

/-- Interchange of the `t`-derivative with the `ζ`-derivative. -/
theorem hasDerivAt_fderiv_swap [CompleteSpace X] {U : Set ℂ} {I : Set ℝ} (hU : IsOpen U)
    (hI : IsOpen I) {f g : ℂ × ℝ → X} {A B : ℂ × ℝ → ℂ →L[ℝ] X}
    (hA : ∀ q ∈ U ×ˢ I, HasFDerivAt (fun ζ => f (ζ, q.2)) (A q) q.1)
    (hB : ∀ q ∈ U ×ˢ I, HasFDerivAt (fun ζ => g (ζ, q.2)) (B q) q.1)
    (hfg : ∀ q ∈ U ×ˢ I, HasDerivAt (fun t => f (q.1, t)) (g q) q.2)
    (hg : ContinuousOn g (U ×ˢ I)) (hBc : ContinuousOn B (U ×ˢ I))
    {q : ℂ × ℝ} (hq : q ∈ U ×ˢ I) :
    HasDerivAt (fun t => A (q.1, t)) (B q) q.2 := by
  obtain ⟨r1, hr1, hU1⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hq.1)
  obtain ⟨r2, hr2, hI2⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hI.mem_nhds hq.2)
  have hmem : ∀ x ∈ closedBall q.1 r1, ∀ τ ∈ closedBall q.2 r2, (x, τ) ∈ U ×ˢ I :=
    fun x hx τ hτ => ⟨hU1 hx, hI2 hτ⟩
  have hsl : ∀ {F' : Type u} [NormedAddCommGroup F'] (h : ℂ × ℝ → F'),
      ContinuousOn h (U ×ˢ I) → ∀ x ∈ closedBall q.1 r1,
        ContinuousOn (fun τ => h (x, τ)) (closedBall q.2 r2) := fun h hh x hx =>
    hh.comp (continuous_const.prodMk continuous_id).continuousOn fun τ hτ => hmem x hx τ hτ
  have hsub : ∀ t ∈ ball q.2 r2, uIcc q.2 t ⊆ closedBall q.2 r2 := by
    intro t ht
    rw [Real.closedBall_eq_Icc]
    refine Set.uIcc_subset_Icc ?_ ?_
    · rw [← Real.closedBall_eq_Icc]; exact mem_closedBall_self hr2.le
    · rw [← Real.closedBall_eq_Icc]; exact ball_subset_closedBall ht
  have key : ∀ t ∈ ball q.2 r2, A (q.1, t) - A (q.1, q.2) = ∫ τ in q.2..t, B (q.1, τ) := by
    intro t ht
    have hK : IsCompact (closedBall q.1 r1 ×ˢ uIcc q.2 t) :=
      (isCompact_closedBall _ _).prod isCompact_uIcc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (hBc.mono fun y hy => hmem y.1 hy.1 y.2 (hsub t ht hy.2))
    have hΦ : HasFDerivAt (fun ζ => f (ζ, t) - f (ζ, q.2)) (A (q.1, t) - A (q.1, q.2)) q.1 :=
      (hA (q.1, t) (hmem _ (mem_closedBall_self hr1.le) _ (ball_subset_closedBall ht))).sub
        (hA (q.1, q.2) hq)
    have hgi : ∀ x ∈ closedBall q.1 r1, ContinuousOn (fun τ => g (x, τ)) (uIcc q.2 t) :=
      fun x hx => (hsl g hg x hx).mono (hsub t ht)
    have hBi : ∀ x ∈ closedBall q.1 r1, ContinuousOn (fun τ => B (x, τ)) (uIcc q.2 t) :=
      fun x hx => (hsl B hBc x hx).mono (hsub t ht)
    have hΨ : HasFDerivAt (fun ζ => ∫ τ in q.2..t, g (ζ, τ)) (∫ τ in q.2..t, B (q.1, τ)) q.1 := by
      refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
        (𝕜 := ℝ) (μ := MeasureTheory.volume) (F := fun x τ => g (x, τ))
        (F' := fun x τ => B (x, τ)) (x₀ := q.1) (s := ball q.1 r1) (bound := fun _ => C)
        (ball_mem_nhds _ hr1) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
      · filter_upwards [ball_mem_nhds q.1 hr1] with x hx
        exact ((hgi x (ball_subset_closedBall hx)).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
          measurableSet_uIoc
      · exact (hgi q.1 (mem_closedBall_self hr1.le)).intervalIntegrable
      · exact ((hBi q.1 (mem_closedBall_self hr1.le)).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
          measurableSet_uIoc
      · exact Eventually.of_forall fun τ hτ x hx =>
          hC (x, τ) ⟨ball_subset_closedBall hx, Set.uIoc_subset_uIcc hτ⟩
      · exact Eventually.of_forall fun τ hτ x hx =>
          hB (x, τ) (hmem x (ball_subset_closedBall hx) τ (hsub t ht (Set.uIoc_subset_uIcc hτ)))
    have heq : (fun ζ => f (ζ, t) - f (ζ, q.2)) =ᶠ[𝓝 q.1] fun ζ => ∫ τ in q.2..t, g (ζ, τ) := by
      filter_upwards [ball_mem_nhds q.1 hr1] with x hx
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ => f (x, τ))]
      · intro τ hτ
        exact hfg (x, τ) (hmem x (ball_subset_closedBall hx) τ (hsub t ht hτ))
      · exact (hgi x (ball_subset_closedBall hx)).intervalIntegrable
    exact hΦ.unique (hΨ.congr_of_eventuallyEq heq)
  have hBc2 : ContinuousOn (fun τ => B (q.1, τ)) (ball q.2 r2) :=
    (hsl B hBc q.1 (mem_closedBall_self hr1.le)).mono ball_subset_closedBall
  have hint : HasDerivAt (fun t => ∫ τ in q.2..t, B (q.1, τ)) (B (q.1, q.2)) q.2 :=
    intervalIntegral.integral_hasDerivAt_right (IntervalIntegrable.refl)
      (hBc2.stronglyMeasurableAtFilter isOpen_ball q.2 (mem_ball_self hr2))
      (hBc2.continuousAt (ball_mem_nhds _ hr2))
  have h2 := hint.const_add (A (q.1, q.2))
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds q.2 hr2] with t ht
  rw [← key t ht]; abel

lemma cont_of_iter0 {W : Set (ℂ × ℝ)} {H : ℂ × ℝ → X}
    (h : ContinuousOn (fun q : ℂ × ℝ => iteratedFDeriv ℝ 0 (fun ζ => H (ζ, q.2)) q.1) W) :
    ContinuousOn H W := by
  have := (continuousMultilinearCurryFin0 ℝ ℂ X).continuous.comp_continuousOn h
  refine this.congr fun q _ => ?_
  simp only [Function.comp_apply, iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.apply_symm_apply]

lemma cont_of_iter1 {W : Set (ℂ × ℝ)} {H : ℂ × ℝ → X}
    (h : ContinuousOn (fun q : ℂ × ℝ => iteratedFDeriv ℝ 1 (fun ζ => H (ζ, q.2)) q.1) W) :
    ContinuousOn (fun q : ℂ × ℝ => fderiv ℝ (fun ζ => H (ζ, q.2)) q.1) W := by
  have := (continuousMultilinearCurryFin1 ℝ ℂ X).continuous.comp_continuousOn h
  refine this.congr fun q _ => ?_
  ext v
  simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]

lemma iter_fderiv_eq (F : ℂ → X) (a : ℕ) (ζ : ℂ) :
    iteratedFDeriv ℝ a (fun y => fderiv ℝ F y) ζ =
      continuousMultilinearCurryRightEquiv' ℝ a ℂ X (iteratedFDeriv ℝ (a + 1) F ζ) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]

lemma cont_iter_fderiv {W : Set (ℂ × ℝ)} {H : ℂ × ℝ → X} (a : ℕ)
    (h : ContinuousOn (fun q : ℂ × ℝ => iteratedFDeriv ℝ (a + 1) (fun ζ => H (ζ, q.2)) q.1) W) :
    ContinuousOn (fun q : ℂ × ℝ =>
      iteratedFDeriv ℝ a (fun ζ => fderiv ℝ (fun ζ' => H (ζ', q.2)) ζ) q.1) W := by
  have := (continuousMultilinearCurryRightEquiv' ℝ a ℂ X).continuous.comp_continuousOn h
  refine this.congr fun q _ => ?_
  simp only [Function.comp_apply, iter_fderiv_eq]

/-- Joint `C^n` from smooth slices, continuous slice derivatives and `∂ₜ G k = G (k+1)`. -/
theorem contDiffOn_of_partials (n : ℕ) {U : Set ℂ} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    [CompleteSpace X] (G : ℕ → ℂ × ℝ → X)
    (h1 : ∀ k, ∀ t ∈ I, ContDiffOn ℝ ∞ (fun ζ => G k (ζ, t)) U)
    (h2 : ∀ k a, ContinuousOn
      (fun q : ℂ × ℝ => iteratedFDeriv ℝ a (fun ζ => G k (ζ, q.2)) q.1) (U ×ˢ I))
    (h3 : ∀ k, ∀ q ∈ U ×ˢ I, HasDerivAt (fun t => G k (q.1, t)) (G (k + 1) q) q.2) :
    ContDiffOn ℝ n (G 0) (U ×ˢ I) := by
  have hW : IsOpen (U ×ˢ I) := hU.prod hI
  induction n generalizing X with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact cont_of_iter0 (h2 0 0)
  | succ n ih =>
    have hdiff : ∀ k, ∀ q ∈ U ×ˢ I, HasFDerivAt (fun ζ => G k (ζ, q.2))
        (fderiv ℝ (fun ζ => G k (ζ, q.2)) q.1) q.1 := fun k q hq =>
      ((((h1 k q.2 hq.2).differentiableOn (by simp)) q.1 hq.1).differentiableAt
        (hU.mem_nhds hq.1)).hasFDerivAt
    have hAc : ∀ k, ContinuousOn (fun q : ℂ × ℝ => fderiv ℝ (fun ζ => G k (ζ, q.2)) q.1)
        (U ×ˢ I) := fun k => cont_of_iter1 (h2 k 1)
    have hD : ∀ q ∈ U ×ˢ I, HasFDerivAt (G 0)
        ((fderiv ℝ (fun ζ => G 0 (ζ, q.2)) q.1).comp (ContinuousLinearMap.fst ℝ ℂ ℝ) +
          (ContinuousLinearMap.snd ℝ ℂ ℝ).smulRight (G 1 q)) q := fun q hq =>
      hasFDerivAt_of_partials hW hq (hdiff 0) ((hAc 0).continuousAt (hW.mem_nhds hq)) (h3 0 q hq)
    have h1' : ∀ k, ∀ t ∈ I, ContDiffOn ℝ ∞
        (fun ζ => fderiv ℝ (fun ζ' => G k (ζ', t)) ζ) U := fun k t ht =>
      (h1 k t ht).fderiv_of_isOpen hU (le_of_eq (by norm_cast))
    have h3' : ∀ k, ∀ q ∈ U ×ˢ I, HasDerivAt (fun t => fderiv ℝ (fun ζ => G k (ζ, t)) q.1)
        (fderiv ℝ (fun ζ => G (k + 1) (ζ, q.2)) q.1) q.2 := fun k q hq =>
      hasDerivAt_fderiv_swap hU hI (hdiff k) (hdiff (k + 1)) (h3 k)
        (cont_of_iter0 (h2 (k + 1) 0)) (hAc (k + 1)) hq
    have hA_n : ContDiffOn ℝ n (fun q : ℂ × ℝ => fderiv ℝ (fun ζ => G 0 (ζ, q.2)) q.1)
        (U ×ˢ I) :=
      ih (X := ℂ →L[ℝ] X) (fun k q => fderiv ℝ (fun ζ => G k (ζ, q.2)) q.1) h1'
        (fun k a => cont_iter_fderiv a (h2 k (a + 1))) h3'
    have hG1_n : ContDiffOn ℝ n (G 1) (U ×ˢ I) :=
      ih (fun k => G (k + 1)) (fun k => h1 (k + 1)) (fun k => h2 (k + 1)) (fun k => h3 (k + 1))
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiffOn_succ_iff_fderiv_of_isOpen hW]
    refine ⟨fun q hq => (hD q hq).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    refine ContDiffOn.congr (f := fun q => (fderiv ℝ (fun ζ => G 0 (ζ, q.2)) q.1).comp
      (ContinuousLinearMap.fst ℝ ℂ ℝ) + (ContinuousLinearMap.snd ℝ ℂ ℝ).smulRight (G 1 q))
      ?_ (fun q hq => (hD q hq).fderiv)
    exact (hA_n.clm_comp contDiffOn_const).add (contDiffOn_const.smulRight hG1_n)

end QR24

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

/-- The coupling term of the difference structure. -/
def Hd (J : E → E →L[ℝ] E) (e : E × E × ℂ) : E →L[ℝ] E :=
  Hg J (e.1, e.2.2.re • e.2.1) e.2.1

/-- The difference structure. -/
def DJ (J : E → E →L[ℝ] E) (e : E × E × ℂ) : (E × E × ℂ) →L[ℝ] (E × E × ℂ) :=
  ((J e.1).comp (ContinuousLinearMap.fst ℝ E (E × ℂ))).prod
    ((((J (e.1 + e.2.2.re • e.2.1)).comp
        ((ContinuousLinearMap.fst ℝ E ℂ).comp (ContinuousLinearMap.snd ℝ E (E × ℂ)))) +
      (Hd J e).comp (ContinuousLinearMap.fst ℝ E (E × ℂ))).prod
      ((Complex.I • ContinuousLinearMap.id ℝ ℂ).comp
        ((ContinuousLinearMap.snd ℝ E ℂ).comp (ContinuousLinearMap.snd ℝ E (E × ℂ)))))

lemma DJ_apply (J : E → E →L[ℝ] E) (e y : E × E × ℂ) :
    DJ J e y = (J e.1 y.1, J (e.1 + e.2.2.re • e.2.1) y.2.1 + Hd J e y.1,
      Complex.I * y.2.2) := by
  simp [DJ]

variable [FiniteDimensional ℝ E]

lemma Hd_mul {J : E → E →L[ℝ] E} (hJ : ContDiff ℝ ∞ J) (e : E × E × ℂ) :
    e.2.2.re • Hd J e = J (e.1 + e.2.2.re • e.2.1) - J e.1 := by
  have hf : ContDiff ℝ ∞ (fun p : E × E => J (p.1 + p.2)) := hJ.comp (contDiff_fst.add contDiff_snd)
  have h := (hadamard_integral_fderiv (fun p : E × E => J (p.1 + p.2)) hf).2 (e.1, e.2.2.re • e.2.1)
  simp only [add_zero] at h
  have e1 : Hd J e = Hg J (e.1, e.2.2.re • e.2.1) e.2.1 := rfl
  have e2 : Hg J (e.1, e.2.2.re • e.2.1) =
      ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => J (e.1 + a)) (θ • (e.2.2.re • e.2.1)) := rfl
  rw [e1, ← map_smul, e2]
  rw [h]; abel

theorem isAlmostComplexOn_DJ {J : E → E →L[ℝ] E} (hJ : IsAlmostComplexOn J univ) :
    IsAlmostComplexOn (DJ J) univ := by
  obtain ⟨-, hJs, hsq⟩ := hJ
  have hJc : ContDiff ℝ ∞ J := contDiffOn_univ.1 hJs
  have hsq' : ∀ x v, J x (J x v) = -v := fun x v => by
    have := congrArg (fun T : E →L[ℝ] E => T v) (hsq x (mem_univ _)); simpa using this
  refine ⟨isOpen_univ, ?_, fun e _ => ?_⟩
  · refine contDiffOn_univ.2 ?_
    rw [contDiff_clm_apply_iff]
    intro y
    simp only [DJ_apply]
    have hHg : ContDiff ℝ ∞ (Hg J) :=
      (hadamard_integral_fderiv (fun p : E × E => J (p.1 + p.2))
        (hJc.comp (contDiff_fst.add contDiff_snd))).1
    have hHd : ContDiff ℝ ∞ (fun e : E × E × ℂ => Hd J e y.1) := by
      have h1 : ContDiff ℝ ∞ (fun e : E × E × ℂ => Hg J (e.1, e.2.2.re • e.2.1)) :=
        hHg.comp (contDiff_fst.prodMk ((Complex.reCLM.contDiff.comp
          (contDiff_snd.comp contDiff_snd)).smul (contDiff_fst.comp contDiff_snd)))
      exact (h1.clm_apply (contDiff_fst.comp contDiff_snd)).clm_apply contDiff_const
    have hJ2 : ContDiff ℝ ∞ (fun e : E × E × ℂ => J (e.1 + e.2.2.re • e.2.1)) :=
      hJc.comp (contDiff_fst.add ((Complex.reCLM.contDiff.comp
          (contDiff_snd.comp contDiff_snd)).smul (contDiff_fst.comp contDiff_snd)))
    exact ((hJc.comp contDiff_fst).clm_apply contDiff_const).prodMk
      (((hJ2.clm_apply contDiff_const).add hHd).prodMk contDiff_const)
  · refine ContinuousLinearMap.ext fun y => ?_
    rw [ContinuousLinearMap.comp_apply, DJ_apply, DJ_apply]
    set u := e.1
    set J' := J (e.1 + e.2.2.re • e.2.1)
    set H := Hd J e
    have key : ∀ w, J' (H w) + H (J u w) = 0 := by
      by_cases hs : e.2.2.re = 0
      · -- `H = DJ(u)[v]`, and `D(J ∘ J) = 0`
        have hH : H = fderiv ℝ J u e.2.1 := by
          have e2 : H = (∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => J (e.1 + a))
              (θ • (e.2.2.re • e.2.1))) e.2.1 := rfl
          rw [e2]
          simp only [hs, zero_smul, smul_zero, intervalIntegral.integral_const, sub_zero,
            one_smul]
          rw [fderiv_comp_add_left, add_zero]
        have hJ'u : J' = J u := by simp only [J', hs, zero_smul, add_zero, u]
        have hd : HasFDerivAt (fun x => (J x).comp (J x))
            ((ContinuousLinearMap.compL ℝ E E E (J u)).comp (fderiv ℝ J u) +
              ((ContinuousLinearMap.compL ℝ E E E).flip (J u)).comp (fderiv ℝ J u)) u :=
          (hJc.differentiable (by simp) u).hasFDerivAt.clm_comp
            (hJc.differentiable (by simp) u).hasFDerivAt
        have hc : HasFDerivAt (fun x => (J x).comp (J x)) (0 : E →L[ℝ] (E →L[ℝ] E)) u := by
          have : (fun x => (J x).comp (J x)) = fun _ => -ContinuousLinearMap.id ℝ E :=
            funext fun x => hsq x (mem_univ _)
          rw [this]; exact hasFDerivAt_const _ _
        intro w'
        have h0' := congrArg (fun T : E →L[ℝ] (E →L[ℝ] E) => T e.2.1 w') (hd.unique hc)
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.zero_apply] at h0'
        rw [hJ'u, hH]
        rw [← h0']

      · intro w
        have hm := Hd_mul hJc e
        have hHw : H w = e.2.2.re⁻¹ • (J' w - J u w) := by
          have := congrArg (fun T : E →L[ℝ] E => T w) hm
          simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply] at this
          rw [← this, smul_smul, inv_mul_cancel₀ hs, one_smul]
        have hHw' : H (J u w) = e.2.2.re⁻¹ • (J' (J u w) - J u (J u w)) := by
          have := congrArg (fun T : E →L[ℝ] E => T (J u w)) hm
          simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply] at this
          rw [← this, smul_smul, inv_mul_cancel₀ hs, one_smul]
        rw [hHw, hHw', map_smul, map_sub, hsq', hsq', ← smul_add]

        have : -w - J' (J u w) + (J' (J u w) - -w) = 0 := by abel
        rw [this, smul_zero]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp [hsq']
    · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.snd_neg,
        Prod.fst_neg, map_add, hsq']
      have := key y.1
      rw [show J' (J' y.2.1) = -y.2.1 from hsq' _ _]
      calc -y.2.1 + J' (H y.1) + H (J u y.1) = -y.2.1 + (J' (H y.1) + H (J u y.1)) := by abel
        _ = -y.2.1 := by rw [this, add_zero]
    · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.snd_neg]
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

theorem isJHolomorphicOn_diff {J : E → E →L[ℝ] E} (hJ : ContDiff ℝ ∞ J) {U : Set ℂ}
    {u u' : ℂ → E} (hu : IsJHolomorphicOn J U u) (hu' : IsJHolomorphicOn J U u') {h : ℝ}
    (hh : h ≠ 0) :
    IsJHolomorphicOn (DJ J) U (fun ζ => (u ζ, h⁻¹ • (u' ζ - u ζ), (h : ℂ))) := by
  intro ζ hζ
  obtain ⟨hd, h0⟩ := hu ζ hζ
  obtain ⟨hd', h0'⟩ := hu' ζ hζ
  rw [dbarJ] at h0 h0'
  have hW : HasFDerivAt (fun ζ => (u ζ, h⁻¹ • (u' ζ - u ζ), (h : ℂ)))
      ((fderiv ℝ u ζ).prod ((h⁻¹ • (fderiv ℝ u' ζ - fderiv ℝ u ζ)).prod 0)) ζ :=
    hd.hasFDerivAt.prodMk (((hd'.hasFDerivAt.sub hd.hasFDerivAt).const_smul h⁻¹).prodMk
      (hasFDerivAt_const _ _))
  refine ⟨hW.differentiableAt, ?_⟩
  have hre : ((h : ℂ)).re = h := Complex.ofReal_re h
  have hpt : u ζ + h • h⁻¹ • (u' ζ - u ζ) = u' ζ := by
    rw [smul_smul, mul_inv_cancel₀ hh, one_smul]; abel
  have hHd : ∀ y, Hd J (u ζ, h⁻¹ • (u' ζ - u ζ), (h : ℂ)) y =
      h⁻¹ • (J (u' ζ) y - J (u ζ) y) := by
    intro y
    have := congrArg (fun T : E →L[ℝ] E => T y) (Hd_mul hJ (u ζ, h⁻¹ • (u' ζ - u ζ), (h : ℂ)))
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, hre, hpt] at this
    rw [← this, smul_smul, inv_mul_cancel₀ hh, one_smul]
  rw [dbarJ, hW.fderiv, DJ_apply]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply, hre, hpt, hHd]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simpa using h0
  · simp only [Prod.snd_add, Prod.fst_add, Prod.snd_zero, Prod.fst_zero]
    rw [map_smul, map_sub]
    have hB1 : fderiv ℝ u' ζ 1 = -J (u' ζ) (fderiv ℝ u' ζ Complex.I) :=
      eq_neg_of_add_eq_zero_left h0'
    have hA1 : fderiv ℝ u ζ 1 = -J (u ζ) (fderiv ℝ u ζ Complex.I) := eq_neg_of_add_eq_zero_left h0
    rw [hA1, hB1]
    simp only [smul_sub, smul_add, smul_neg, map_neg]
    abel
  · simp

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

theorem dbarJ_of_comp {J : F → F →L[ℝ] F} {u : ℂ → F} {φ : ℂ → ℂ} {ζ : ℂ}
    (hJ : (J (u (φ ζ))).comp (J (u (φ ζ))) = -ContinuousLinearMap.id ℝ F)
    (hu : DifferentiableAt ℝ u (φ ζ)) (hφ : IsHoloAt φ ζ) (hne : fderiv ℝ φ ζ 1 ≠ 0)
    (h : dbarJ J (fun ζ => u (φ ζ)) ζ = 0) : dbarJ J u (φ ζ) = 0 := by
  obtain ⟨hφd, hφI⟩ := hφ
  have hT : ∀ v, J (u (φ ζ)) (J (u (φ ζ)) v) = -v := fun v => by
    have := congrArg (fun T : F →L[ℝ] F => T v) hJ; simpa using this
  have hc : HasFDerivAt (fun ζ => u (φ ζ)) ((fderiv ℝ u (φ ζ)).comp (fderiv ℝ φ ζ)) ζ :=
    hu.hasFDerivAt.comp ζ hφd.hasFDerivAt
  rw [dbarJ, hc.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hφI,
    cr_alg _ _ hT] at h
  rw [dbarJ]
  set a := fderiv ℝ φ ζ 1
  set X := fderiv ℝ u (φ ζ) 1 + J (u (φ ζ)) (fderiv ℝ u (φ ζ) Complex.I)
  set T := J (u (φ ζ))
  have e2 : a.re • T X + a.im • X = 0 := by
    have := congrArg T h
    rw [map_sub, map_smul, map_smul, hT, map_zero] at this
    rw [← this]; simp
  have e3 : (a.re * a.re + a.im * a.im) • X = 0 := by
    have : (a.re * a.re + a.im * a.im) • X =
        a.re • (a.re • X - a.im • T X) + a.im • (a.re • T X + a.im • X) := by module
    rw [this, h, e2]; simp
  have hpos : a.re * a.re + a.im * a.im ≠ 0 := by
    rw [← Complex.normSq_apply]; exact (Complex.normSq_pos.2 hne).ne'
  exact (smul_eq_zero.1 e3).resolve_left hpos

end FiniteEnergyPlane.QR25

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

variable [FiniteDimensional ℝ F]

/-! ### Graphs -/

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

/-! ### The uniform bound for one structure -/

variable [FiniteDimensional ℝ E]

end QR11

end

end FiniteEnergyPlane

-- FILE: RSK_R26.lean
/-!
# Q-R, layer 26 (local, NOT published): the abstract setup, limits, and the lift

* `Setup E Y I`: a family `b z + L z (ys 0 t)` of smooth `J`-holomorphic planes (`t ∈ I`),
  `L z : Y →L E`, with the jet `ys k` of the curve (`∂ₜ ys k = ys (k+1)`), holomorphic charts
  `φ z` around each `z` (local inverses `ψ z`), and on each chart disc a sup bound of `L` and
  a `W^{1,4}` bound of `L(φ ·) w` by `‖w‖` for every `w` with `L(·) w` smooth.
* `limit`: Thm 2.22(2a) + G1 + G2 for one structure: pointwise limits of `W^{1,4}`-bounded
  holomorphic discs are smooth, holomorphic, and the limit of all derivatives along a subsequence.
* `cont_derivs`: the `ζ`-derivatives of the chart pull-backs are jointly continuous in `(ζ, t)`.
* `tangent_hol`: `(b + L(·) ys0, L(·) ys1, 0)` is smooth and `DJ J`-holomorphic.
* `Setup.lift`: the same setup for `DJ J` on `E × E × ℂ` and the jet `(ys k, ys (k+1))`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Set Filter Topology Metric JHolomorphic DbarRegularity
open scoped ContDiff ENNReal NNReal

noncomputable section

namespace QR26

open QR25

/-- The abstract setup. -/
structure Setup (E Y : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (I : Set ℝ) where
  hI : IsOpen I
  J : E → E →L[ℝ] E
  hJ : IsAlmostComplexOn J univ
  L : ℂ → Y →L[ℝ] E
  b : ℂ → E
  hb : ContDiff ℝ ∞ b
  ys : ℕ → ℝ → Y
  hys : ∀ k, ∀ t ∈ I, HasDerivAt (ys k) (ys (k + 1) t) t
  hsm : ∀ t ∈ I, ContDiff ℝ ∞ (fun z => L z (ys 0 t))
  hhol : ∀ t ∈ I, IsJHolomorphicOn J univ (fun z => b z + L z (ys 0 t))
  φ : ℂ → ℂ → ℂ
  ψ : ℂ → ℂ → ℂ
  hφ : ∀ z, ContDiff ℝ ∞ (φ z) ∧ (∀ ζ, IsHoloAt (φ z) ζ) ∧ ∀ ζ, fderiv ℝ (φ z) ζ 1 ≠ 0
  hψ : ∀ z, ∃ V, IsOpen V ∧ z ∈ V ∧ ContDiffOn ℝ ∞ (ψ z) V ∧ MapsTo (ψ z) V (ball 0 1) ∧
    ∀ w ∈ V, φ z (ψ z w) = w
  hBd : ∀ z, ∃ C, ∀ ζ ∈ ball (0 : ℂ) 1, ‖L (φ z ζ)‖ ≤ C ∧ ‖b (φ z ζ)‖ ≤ C
  hSb : ∀ z, ∃ C : ℝ, eLpNorm (fderiv ℝ (fun ζ => b (φ z ζ))) 4
    (volume.restrict (ball (0 : ℂ) 1)) ≤ ENNReal.ofReal C
  hSob : ∀ z, ∃ C : ℝ, ∀ w : Y, ContDiff ℝ ∞ (fun z' => L z' w) →
    eLpNorm (fderiv ℝ (fun ζ => L (φ z ζ) w)) 4 (volume.restrict (ball (0 : ℂ) 1)) ≤
      ENNReal.ofReal (C * ‖w‖)

variable {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {I : Set ℝ}

section Helpers

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma fderiv_eq_curry1 (f : ℂ → F) (x : ℂ) :
    fderiv ℝ f x = continuousMultilinearCurryFin1 ℝ ℂ F (iteratedFDeriv ℝ 1 f x) := by
  ext v; simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]

lemma eLp_fderiv_le_two {μ : Measure ℂ} (u : ℂ → F) (f : ℂ → G) (g : ℂ → H)
    (hf : Continuous (fderiv ℝ f)) (hg : Continuous (fderiv ℝ g))
    (h : ∀ ζ, ‖fderiv ℝ u ζ‖ ≤ ‖fderiv ℝ f ζ‖ + ‖fderiv ℝ g ζ‖) :
    eLpNorm (fderiv ℝ u) 4 μ ≤ eLpNorm (fderiv ℝ f) 4 μ + eLpNorm (fderiv ℝ g) 4 μ := by
  refine (eLpNorm_mono_real h).trans ?_
  refine (eLpNorm_add_le hf.norm.aestronglyMeasurable hg.norm.aestronglyMeasurable
    (by norm_num)).trans ?_
  rw [eLpNorm_norm, eLpNorm_norm]

lemma sob_le (u : ℂ → F) (R D : ℝ) (hR : ∀ ζ ∈ ball (0 : ℂ) 1, ‖u ζ‖ ≤ R)
    (hD : eLpNorm (fderiv ℝ u) 4 (volume.restrict (ball (0 : ℂ) 1)) ≤ ENNReal.ofReal D) :
    sobolevNorm 1 (ENNReal.ofReal 4) (ball 0 1) u ≤
      eLpNorm (fun _ : ℂ => R) (ENNReal.ofReal 4) (volume.restrict (ball (0 : ℂ) 1)) +
        ENNReal.ofReal D := by
  refine (QR11.sobolevNorm_one_le hR measurableSet_ball).trans ?_
  gcongr
  rw [show ENNReal.ofReal 4 = 4 by norm_num]; exact hD

end Helpers

/-- The limit lemma for one structure. -/
theorem limit [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (hJ : IsAlmostComplexOn J univ)
    (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ ∞ (u ν) (ball 0 1))
    (hhol : ∀ ν, IsJHolomorphicOn J (ball 0 1) (u ν)) (R : ℝ)
    (hR : ∀ ν, ∀ ζ ∈ ball (0 : ℂ) 1, ‖u ν ζ‖ ≤ R) (D : ℝ)
    (hD : ∀ ν, eLpNorm (fderiv ℝ (u ν)) 4 (volume.restrict (ball (0 : ℂ) 1)) ≤ ENNReal.ofReal D)
    (v : ℂ → E) (hv : ∀ ζ ∈ ball (0 : ℂ) 1, Tendsto (fun ν => u ν ζ) atTop (𝓝 (v ζ))) :
    ContDiffOn ℝ ∞ v (ball 0 1) ∧ IsJHolomorphicOn J (ball 0 1) v ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m, TendstoLocallyUniformlyOn
        (fun ν => iteratedFDeriv ℝ m (u (φ ν))) (iteratedFDeriv ℝ m v) atTop (ball 0 1) := by
  have hJc : Continuous J := (contDiffOn_univ.1 hJ.2.1).continuous
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hC0 : eLpNorm (fun _ : ℂ => R) (ENNReal.ofReal 4) (volume.restrict (ball (0 : ℂ) 1)) +
      ENNReal.ofReal D ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨(memLp_const R).eLpNorm_ne_top, ENNReal.ofReal_ne_top⟩
  have hC : ∀ ν, sobolevNorm 1 (ENNReal.ofReal 4) (ball 0 1) (u ν) ≤
      ((eLpNorm (fun _ : ℂ => R) (ENNReal.ofReal 4) (volume.restrict (ball (0 : ℂ) 1)) +
        ENNReal.ofReal D).toNNReal : ℝ≥0∞) := fun ν => by
    rw [ENNReal.coe_toNNReal hC0]; exact sob_le (u ν) R D (hR ν) (hD ν)
  have hconv : TendstoCInftyLocOn (fun _ : ℕ => J) J univ := fun K' _ _ m =>
    Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun _ x _ => by
      simpa using hε
  have hmaps : ∀ ν, MapsTo (u ν) (ball 0 1) (closedBall 0 R) := fun ν ζ hζ =>
    mem_closedBall_zero_iff.2 (hR ν ζ hζ)
  have hb : ∀ K ⊆ ball (0 : ℂ) 1, IsCompact K → ∀ m : ℕ, ∃ M : ℝ, ∀ ν, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (u ν) x‖ ≤ M := fun K hK hKc m =>
    bounded_iteratedFDeriv_of_sobolevNorm_le 4 (by norm_num) J (fun _ => J) univ (closedBall 0 R)
      hJ (fun _ => hJ) hconv (isCompact_closedBall _ _) (subset_univ _) u hu hhol hmaps _ hC
      K hK hKc m
  obtain ⟨φ, hφ, g, hg⟩ := exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv isOpen_ball u hu hb
  have hv' : ∀ x ∈ ball (0 : ℂ) 1, Tendsto (fun ν => u (φ ν) x) atTop (𝓝 (v x)) :=
    fun x hx => (hv x hx).comp hφ.tendsto_atTop
  obtain ⟨hvs, hvg⟩ := contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv isOpen_ball
    (fun ν => u (φ ν)) (fun ν => hu (φ ν)) v hv' g hg
  have hconvv : ∀ m, TendstoLocallyUniformlyOn (fun ν => iteratedFDeriv ℝ m (u (φ ν)))
      (iteratedFDeriv ℝ m v) atTop (ball 0 1) := fun m =>
    (hg m).congr_right (fun x hx => (hvg m hx).symm)
  refine ⟨hvs, ?_, φ, hφ, hconvv⟩
  intro ζ hζ
  have hdv : DifferentiableAt ℝ v ζ :=
    (hvs.differentiableOn (by simp) ζ hζ).differentiableAt (isOpen_ball.mem_nhds hζ)
  refine ⟨hdv, ?_⟩
  have h1 : Tendsto (fun ν => fderiv ℝ (u (φ ν)) ζ) atTop (𝓝 (fderiv ℝ v ζ)) := by
    have h2 := ((continuousMultilinearCurryFin1 ℝ ℂ E).continuous.tendsto _).comp
      ((hconvv 1).tendsto_at hζ)
    rw [show (fun ν => fderiv ℝ (u (φ ν)) ζ) = fun ν => continuousMultilinearCurryFin1 ℝ ℂ E
      (iteratedFDeriv ℝ 1 (u (φ ν)) ζ) from funext fun ν => fderiv_eq_curry1 _ _,
      fderiv_eq_curry1 v]
    exact h2
  have hJt : Tendsto (fun ν => J (u (φ ν) ζ)) atTop (𝓝 (J (v ζ))) :=
    (hJc.tendsto _).comp (hv' ζ hζ)
  have hA1 : Tendsto (fun ν => fderiv ℝ (u (φ ν)) ζ 1) atTop (𝓝 (fderiv ℝ v ζ 1)) :=
    ((ContinuousLinearMap.apply ℝ E (1 : ℂ)).continuous.tendsto _).comp h1
  have hAI : Tendsto (fun ν => fderiv ℝ (u (φ ν)) ζ Complex.I) atTop
      (𝓝 (fderiv ℝ v ζ Complex.I)) :=
    ((ContinuousLinearMap.apply ℝ E Complex.I).continuous.tendsto _).comp h1
  have hJA : Tendsto (fun ν => J (u (φ ν) ζ) (fderiv ℝ (u (φ ν)) ζ Complex.I)) atTop
      (𝓝 (J (v ζ) (fderiv ℝ v ζ Complex.I))) :=
    (isBoundedBilinearMap_apply.continuous.tendsto _).comp (hJt.prodMk_nhds hAI)
  have hlim := hA1.add hJA
  have h0 : ∀ ν, fderiv ℝ (u (φ ν)) ζ 1 + J (u (φ ν) ζ) (fderiv ℝ (u (φ ν)) ζ Complex.I) = 0 :=
    fun ν => (hhol (φ ν) ζ hζ).2
  simp only [h0] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

lemma nat_le_infty (a : ℕ) : (a : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top

section Triple

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
  [NormedSpace ℝ H]

lemma norm_prod_le_add (A : ℂ →L[ℝ] G) (B : ℂ →L[ℝ] H) : ‖A.prod B‖ ≤ ‖A‖ + ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.prod_apply, Prod.norm_def, add_mul]
  exact max_le ((A.le_opNorm v).trans (le_add_of_nonneg_right (by positivity)))
    ((B.le_opNorm v).trans (le_add_of_nonneg_left (by positivity)))

lemma norm_triple_le (a : G) (b : H) (c : ℂ) : ‖(a, b, c)‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hc := norm_nonneg c
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le (by linarith) (max_le (by linarith) (by linarith))

lemma eLp_fderiv_triple_le {μ : Measure ℂ} (f : ℂ → G) (g : ℂ → H) (c : ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    eLpNorm (fderiv ℝ (fun ζ => (f ζ, g ζ, c))) 4 μ ≤
      eLpNorm (fderiv ℝ f) 4 μ + eLpNorm (fderiv ℝ g) 4 μ := by
  refine eLp_fderiv_le_two _ f g (hf.continuous_fderiv (by simp)) (hg.continuous_fderiv (by simp))
    fun ζ => ?_
  have hd : HasFDerivAt (fun ζ => (f ζ, g ζ, c))
      ((fderiv ℝ f ζ).prod ((fderiv ℝ g ζ).prod 0)) ζ :=
    ((hf.differentiable (by simp)) ζ).hasFDerivAt.prodMk
      (((hg.differentiable (by simp)) ζ).hasFDerivAt.prodMk (hasFDerivAt_const c ζ))
  rw [hd.fderiv]
  refine (norm_prod_le_add _ _).trans ?_
  gcongr
  refine (norm_prod_le_add _ _).trans ?_
  simp

end Triple

/-- The chart pull-back of a member. -/
def wC (S : Setup E Y I) (z : ℂ) (t : ℝ) (ζ : ℂ) : E :=
  S.b (S.φ z ζ) + S.L (S.φ z ζ) (S.ys 0 t)

lemma contDiff_wC (S : Setup E Y I) (z : ℂ) {t : ℝ} (ht : t ∈ I) :
    ContDiff ℝ ∞ (wC S z t) :=
  (S.hb.comp (S.hφ z).1).add ((S.hsm t ht).comp (S.hφ z).1)

lemma sq_of_setup (S : Setup E Y I) (x : E) (v : E) : S.J x (S.J x v) = -v := by
  have := congrArg (fun T : E →L[ℝ] E => T v) (S.hJ.2.2 x (mem_univ _)); simpa using this

lemma hol_wC (S : Setup E Y I) (z : ℂ) {t : ℝ} (ht : t ∈ I) :
    IsJHolomorphicOn S.J (ball 0 1) (wC S z t) :=
  isJHolomorphicOn_comp (u := fun z => S.b z + S.L z (S.ys 0 t)) (S.hhol t ht)
    (fun ζ _ => (S.hφ z).2.1 ζ) (mapsTo_univ _ _) (fun ζ _ v => sq_of_setup S _ v)

lemma bd_wC (S : Setup E Y I) (z : ℂ) :
    ∃ C ≥ 0, ∀ t, ∀ ζ ∈ ball (0 : ℂ) 1, ‖wC S z t ζ‖ ≤ C + C * ‖S.ys 0 t‖ ∧
      ‖S.L (S.φ z ζ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := S.hBd z
  refine ⟨max C 0, le_max_right _ _, fun t ζ hζ => ⟨?_, (hC ζ hζ).1.trans (le_max_left _ _)⟩⟩
  calc ‖wC S z t ζ‖ ≤ ‖S.b (S.φ z ζ)‖ + ‖S.L (S.φ z ζ)‖ * ‖S.ys 0 t‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl ((S.L (S.φ z ζ)).le_opNorm _))
    _ ≤ max C 0 + max C 0 * ‖S.ys 0 t‖ := by
        gcongr
        · exact (hC ζ hζ).2.trans (le_max_left _ _)
        · exact (hC ζ hζ).1.trans (le_max_left _ _)

lemma eLp_L (S : Setup E Y I) (z : ℂ) :
    ∃ C ≥ 0, ∀ w : Y, ContDiff ℝ ∞ (fun z' => S.L z' w) →
      eLpNorm (fderiv ℝ (fun ζ => S.L (S.φ z ζ) w)) 4 (volume.restrict (ball (0 : ℂ) 1)) ≤
        ENNReal.ofReal (C * ‖w‖) := by
  obtain ⟨C, hC⟩ := S.hSob z
  refine ⟨max C 0, le_max_right _ _, fun w hw => (hC w hw).trans ?_⟩
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

lemma eLp_wC (S : Setup E Y I) (z : ℂ) :
    ∃ C ≥ 0, ∀ t ∈ I, eLpNorm (fderiv ℝ (wC S z t)) 4 (volume.restrict (ball (0 : ℂ) 1)) ≤
      ENNReal.ofReal (C + C * ‖S.ys 0 t‖) := by
  obtain ⟨Cb, hCb⟩ := S.hSb z
  obtain ⟨CS, hCS0, hCS⟩ := eLp_L S z
  refine ⟨max (max Cb CS) 0, le_max_right _ _, fun t ht => ?_⟩
  have hf : ContDiff ℝ ∞ (fun ζ => S.b (S.φ z ζ)) := S.hb.comp (S.hφ z).1
  have hg : ContDiff ℝ ∞ (fun ζ => S.L (S.φ z ζ) (S.ys 0 t)) := (S.hsm t ht).comp (S.hφ z).1
  have h2 := eLp_fderiv_le_two (μ := volume.restrict (ball (0 : ℂ) 1)) (wC S z t) _ _
    (hf.continuous_fderiv (by simp)) (hg.continuous_fderiv (by simp)) fun ζ => by
      have hd := ((hf.differentiable (by simp)) ζ).hasFDerivAt.add
        ((hg.differentiable (by simp)) ζ).hasFDerivAt
      rw [show fderiv ℝ (wC S z t) ζ = fderiv ℝ (fun ζ => S.b (S.φ z ζ)) ζ +
        fderiv ℝ (fun ζ => S.L (S.φ z ζ) (S.ys 0 t)) ζ from hd.fderiv]
      exact norm_add_le _ _
  refine h2.trans ?_
  have hM : 0 ≤ max (max Cb CS) 0 := le_max_right _ _
  rw [ENNReal.ofReal_add hM (mul_nonneg hM (norm_nonneg _))]
  gcongr
  · exact hCb.trans (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_left _ _)))
  · exact (hCS _ (S.hsm t ht)).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_left _ _)) (norm_nonneg _)))

theorem cont_wC [FiniteDimensional ℝ E] (S : Setup E Y I) (z : ℂ) (a : ℕ) :
    ContinuousOn (fun q : ℂ × ℝ => iteratedFDeriv ℝ a (wC S z q.2) q.1) (ball 0 1 ×ˢ I) := by
  obtain ⟨C1, hC10, hC1⟩ := bd_wC S z
  obtain ⟨C2, hC20, hC2⟩ := eLp_wC S z
  intro q0 hq0
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hns self_mem_nhdsWithin)
  have hns' : Tendsto ns atTop (𝓝 q0) := hns.mono_right nhdsWithin_le_nhds
  have hqs : ∀ ν, ns (ν + N) ∈ ball (0 : ℂ) 1 ×ˢ I := fun ν => hN _ (by omega)
  have hqt : Tendsto (fun ν => ns (ν + N)) atTop (𝓝 q0) := hns'.comp (tendsto_add_atTop_nat N)
  have hys : Tendsto (fun ν => S.ys 0 (ns (ν + N)).2) atTop (𝓝 (S.ys 0 q0.2)) :=
    ((S.hys 0 q0.2 hq0.2).continuousAt.tendsto).comp ((continuous_snd.tendsto _).comp hqt)
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (isBounded_range_of_tendsto _ hys)
  have hM' : ∀ ν, ‖S.ys 0 (ns (ν + N)).2‖ ≤ M := fun ν => hM _ ⟨ν, rfl⟩
  obtain ⟨-, -, φ', hφ', hconv⟩ := limit S.J S.hJ (fun ν => wC S z (ns (ν + N)).2)
    (fun ν => (contDiff_wC S z (hqs ν).2).contDiffOn) (fun ν => hol_wC S z (hqs ν).2)
    (C1 + C1 * M) (fun ν ζ hζ => (hC1 _ ζ hζ).1.trans (by gcongr; exact hM' ν))
    (C2 + C2 * M) (fun ν => (hC2 _ (hqs ν).2).trans (ENNReal.ofReal_le_ofReal
      (by gcongr; exact hM' ν)))
    (wC S z q0.2) (fun ζ _ => tendsto_const_nhds.add
      (((S.L (S.φ z ζ)).continuous.tendsto _).comp hys))
  refine ⟨fun ν => φ' ν + N, ?_⟩
  have hg : Tendsto (fun ν => (ns (φ' ν + N)).1) atTop (𝓝[ball (0 : ℂ) 1] q0.1) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto _).comp
      (hqt.comp hφ'.tendsto_atTop), Eventually.of_forall fun ν => (hqs _).1⟩
  exact (hconv a).tendsto_comp
    ((contDiff_wC S z hq0.2).continuous_iteratedFDeriv (nat_le_infty a)).continuousWithinAt hq0.1 hg

/-- Joint continuity of the chart derivatives. -/
theorem cont_derivs [FiniteDimensional ℝ E] (S : Setup E Y I) (z : ℂ) (a : ℕ) :
    ContinuousOn (fun q : ℂ × ℝ =>
      iteratedFDeriv ℝ a (fun ζ => S.L (S.φ z ζ) (S.ys 0 q.2)) q.1) (ball 0 1 ×ˢ I) := by
  have hb : ContDiff ℝ ∞ (fun ζ => S.b (S.φ z ζ)) := S.hb.comp (S.hφ z).1
  have hbc : ContinuousOn (fun q : ℂ × ℝ => iteratedFDeriv ℝ a (fun ζ => S.b (S.φ z ζ)) q.1)
      (ball 0 1 ×ˢ I) :=
    ((hb.continuous_iteratedFDeriv (nat_le_infty a)).comp continuous_fst).continuousOn
  refine ((cont_wC S z a).sub hbc).congr fun q hq => ?_
  have hw := contDiff_wC S z hq.2
  have e : (fun ζ => S.L (S.φ z ζ) (S.ys 0 q.2)) = wC S z q.2 - fun ζ => S.b (S.φ z ζ) := by
    funext ζ; simp [wC]
  rw [e]
  exact iteratedFDeriv_sub_apply (hw.contDiffAt.of_le (nat_le_infty a)) (hb.contDiffAt.of_le (nat_le_infty a))

/-- The local statement on one chart. -/
theorem tangent_loc [FiniteDimensional ℝ E] (S : Setup E Y I) {t : ℝ} (ht : t ∈ I) (z : ℂ) :
    ContDiffOn ℝ ∞ (fun ζ => (wC S z t ζ, S.L (S.φ z ζ) (S.ys 1 t), (0 : ℂ))) (ball 0 1) ∧
      IsJHolomorphicOn (DJ S.J) (ball 0 1)
        (fun ζ => (wC S z t ζ, S.L (S.φ z ζ) (S.ys 1 t), (0 : ℂ))) := by
  have hJc : ContDiff ℝ ∞ S.J := contDiffOn_univ.1 S.hJ.2.1
  obtain ⟨δ, hδ, hδI⟩ := Metric.isOpen_iff.1 S.hI t ht
  have hpos : ∀ ν : ℕ, 0 < δ / ((ν : ℝ) + 2) := fun ν => div_pos hδ (by positivity)
  have hlt : ∀ ν : ℕ, δ / ((ν : ℝ) + 2) < δ := fun ν =>
    div_lt_self hδ (by have := (Nat.cast_nonneg ν : (0 : ℝ) ≤ ν); linarith)
  have hI' : ∀ ν : ℕ, t + δ / ((ν : ℝ) + 2) ∈ I := fun ν => hδI (by
    rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (hpos ν)]; exact hlt ν)
  have hh0 : Tendsto (fun ν : ℕ => δ / ((ν : ℝ) + 2)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds),
      Eventually.of_forall fun ν => (hpos ν).ne'⟩
  set d : ℕ → Y := fun ν => (δ / ((ν : ℝ) + 2))⁻¹ •
    (S.ys 0 (t + δ / ((ν : ℝ) + 2)) - S.ys 0 t) with hd_def
  have hd : Tendsto d atTop (𝓝 (S.ys 1 t)) := (S.hys 0 t ht).tendsto_slope_zero.comp hh0
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (isBounded_range_of_tendsto _ hd)
  have hM' : ∀ ν, ‖d ν‖ ≤ M := fun ν => hM _ ⟨ν, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM' 0)
  have hLd : ∀ ν, ContDiff ℝ ∞ (fun z' => S.L z' (d ν)) := fun ν => by
    have e : (fun z' => S.L z' (d ν)) = fun z' => (δ / ((ν : ℝ) + 2))⁻¹ •
        (S.L z' (S.ys 0 (t + δ / ((ν : ℝ) + 2))) - S.L z' (S.ys 0 t)) := by
      funext z'; simp [hd_def, map_sub, map_smul]
    rw [e]; exact ((S.hsm _ (hI' ν)).sub (S.hsm t ht)).const_smul _
  have hdiff : ∀ (ν : ℕ) (ζ : ℂ), (δ / ((ν : ℝ) + 2))⁻¹ •
      (wC S z (t + δ / ((ν : ℝ) + 2)) ζ - wC S z t ζ) = S.L (S.φ z ζ) (d ν) := fun ν ζ => by
    simp [wC, hd_def, map_sub, map_smul]
  obtain ⟨C1, hC10, hC1⟩ := bd_wC S z
  obtain ⟨C2, hC20, hC2⟩ := eLp_wC S z
  obtain ⟨CS, hCS0, hCS⟩ := eLp_L S z
  have hsmooth : ∀ ν, ContDiff ℝ ∞ (fun ζ => S.L (S.φ z ζ) (d ν)) := fun ν =>
    (hLd ν).comp (S.hφ z).1
  have hholν : ∀ ν, IsJHolomorphicOn (DJ S.J) (ball 0 1)
      (fun ζ => (wC S z t ζ, S.L (S.φ z ζ) (d ν), ((δ / ((ν : ℝ) + 2) : ℝ) : ℂ))) := fun ν => by
    have h := isJHolomorphicOn_diff hJc (hol_wC S z ht) (hol_wC S z (hI' ν)) (hpos ν).ne'
    have e : (fun ζ => (wC S z t ζ, (δ / ((ν : ℝ) + 2))⁻¹ •
        (wC S z (t + δ / ((ν : ℝ) + 2)) ζ - wC S z t ζ), ((δ / ((ν : ℝ) + 2) : ℝ) : ℂ))) =
        fun ζ => (wC S z t ζ, S.L (S.φ z ζ) (d ν), ((δ / ((ν : ℝ) + 2) : ℝ) : ℂ)) := by
      funext ζ; rw [hdiff]
    rwa [e] at h
  obtain ⟨hvs, hvh, -⟩ := limit (DJ S.J) (isAlmostComplexOn_DJ S.hJ)
    (fun ν ζ => (wC S z t ζ, S.L (S.φ z ζ) (d ν), ((δ / ((ν : ℝ) + 2) : ℝ) : ℂ)))
    (fun ν => ((contDiff_wC S z ht).prodMk ((hsmooth ν).prodMk contDiff_const)).contDiffOn)
    hholν ((C1 + C1 * ‖S.ys 0 t‖) + C1 * M + δ)
    (fun ν ζ hζ => by
      refine (norm_triple_le _ _ _).trans ?_
      have h1 := (hC1 t ζ hζ).1
      have h2 : ‖S.L (S.φ z ζ) (d ν)‖ ≤ C1 * M :=
        ((S.L (S.φ z ζ)).le_opNorm _).trans (mul_le_mul (hC1 t ζ hζ).2 (hM' ν) (norm_nonneg _)
          hC10)
      have h3 : ‖((δ / ((ν : ℝ) + 2) : ℝ) : ℂ)‖ ≤ δ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (hpos ν).le]; exact (hlt ν).le
      linarith)
    ((C2 + C2 * ‖S.ys 0 t‖) + CS * M)
    (fun ν => by
      refine (eLp_fderiv_triple_le _ _ _ (contDiff_wC S z ht) (hsmooth ν)).trans ?_
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      gcongr
      · exact hC2 t ht
      · exact ((hCS _ (hLd ν))).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hM' ν) hCS0)))
    (fun ζ => (wC S z t ζ, S.L (S.φ z ζ) (S.ys 1 t), (0 : ℂ)))
    (fun ζ _ => by
      refine tendsto_const_nhds.prodMk_nhds ((((S.L (S.φ z ζ)).continuous.tendsto _).comp
        hd).prodMk_nhds ?_)
      have := ((Complex.continuous_ofReal.tendsto 0).comp (tendsto_nhdsWithin_iff.1 hh0).1)
      rw [Complex.ofReal_zero] at this
      exact this)
  exact ⟨hvs, hvh⟩

/-- The `t`-derivative plane, with the base, is `DJ J`-holomorphic. -/
theorem tangent_hol [FiniteDimensional ℝ E] (S : Setup E Y I) :
    ∀ t ∈ I, ContDiff ℝ ∞ (fun z => S.L z (S.ys 1 t)) ∧
      IsJHolomorphicOn (DJ S.J) univ
        (fun z => (S.b z + S.L z (S.ys 0 t), S.L z (S.ys 1 t), (0 : ℂ))) := by
  intro t ht
  have hsm1 : ContDiff ℝ ∞ (fun z => S.L z (S.ys 1 t)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    obtain ⟨V, hVo, hzV, hψ, hψm, hφψ⟩ := S.hψ z
    have h1 := (tangent_loc S ht z).1.comp hψ hψm
    have h2 : ContDiffOn ℝ ∞ (fun w => S.L w (S.ys 1 t)) V := by
      have := (contDiff_fst.comp contDiff_snd).comp_contDiffOn h1
      refine this.congr fun w hw => ?_
      simp only [Function.comp_apply, hφψ w hw]
    exact h2.contDiffAt (hVo.mem_nhds hzV)
  refine ⟨hsm1, fun z _ => ?_⟩
  obtain ⟨V, hVo, hzV, hψ, hψm, hφψ⟩ := S.hψ z
  have hζ0 : S.ψ z z ∈ ball (0 : ℂ) 1 := hψm hzV
  have hφζ : S.φ z (S.ψ z z) = z := hφψ z hzV
  have hW : ContDiff ℝ ∞ (fun z => (S.b z + S.L z (S.ys 0 t), S.L z (S.ys 1 t), (0 : ℂ))) :=
    (S.hb.add (S.hsm t ht)).prodMk (hsm1.prodMk contDiff_const)
  have hWd := hW.differentiable (by simp)
  refine ⟨hWd z, ?_⟩
  have hcomp := ((tangent_loc S ht z).2 _ hζ0).2
  have := dbarJ_of_comp (J := DJ S.J)
    (u := fun z => (S.b z + S.L z (S.ys 0 t), S.L z (S.ys 1 t), (0 : ℂ))) (φ := S.φ z)
    ((isAlmostComplexOn_DJ S.hJ).2.2 _ (mem_univ _)) (hWd _) ((S.hφ z).2.1 _) ((S.hφ z).2.2 _)
    hcomp
  rwa [hφζ] at this

/-- The lifted linear part. -/
def Lft (L : ℂ → Y →L[ℝ] E) (z : ℂ) : Y × Y →L[ℝ] E × E × ℂ :=
  ((L z).comp (ContinuousLinearMap.fst ℝ Y Y)).prod
    (((L z).comp (ContinuousLinearMap.snd ℝ Y Y)).prod 0)

@[simp] lemma Lft_apply (L : ℂ → Y →L[ℝ] E) (z : ℂ) (w : Y × Y) :
    Lft L z w = (L z w.1, L z w.2, 0) := rfl

lemma norm_Lft_le (L : ℂ → Y →L[ℝ] E) (z : ℂ) : ‖Lft L z‖ ≤ ‖L z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
  rw [Lft_apply, Prod.norm_def, Prod.norm_def, Prod.norm_def, norm_zero]
  have h1 := (L z).le_opNorm w.1
  have h2 := (L z).le_opNorm w.2
  have hn : 0 ≤ ‖L z‖ := norm_nonneg _
  refine max_le (h1.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hn))
    (max_le (h2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hn)) (by positivity))

lemma eLp_fderiv_const_zero {μ : Measure ℂ} :
    eLpNorm (fderiv ℝ (fun _ : ℂ => (0 : E))) 4 μ = 0 := by
  refine le_antisymm ((eLpNorm_mono_real (g := fun _ => (0 : ℝ)) fun x => ?_).trans ?_) zero_le
  · simp
  · exact (eLpNorm_zero' (α := ℂ) (ε := ℝ)).le

/-- The lifted setup. -/
def Setup.lift [FiniteDimensional ℝ E] (S : Setup E Y I) : Setup (E × E × ℂ) (Y × Y) I where
  hI := S.hI
  J := DJ S.J
  hJ := isAlmostComplexOn_DJ S.hJ
  L := Lft S.L
  b := fun z => (S.b z, 0, 0)
  hb := S.hb.prodMk (contDiff_const.prodMk contDiff_const)
  ys := fun k t => (S.ys k t, S.ys (k + 1) t)
  hys := fun k t ht => (S.hys k t ht).prodMk (S.hys (k + 1) t ht)
  hsm := fun t ht => (S.hsm t ht).prodMk ((tangent_hol S t ht).1.prodMk contDiff_const)
  hhol := fun t ht => by
    have e : (fun z => ((S.b z, (0 : E), (0 : ℂ)) + Lft S.L z (S.ys 0 t, S.ys (0 + 1) t))) =
        fun z => (S.b z + S.L z (S.ys 0 t), S.L z (S.ys 1 t), (0 : ℂ)) := by
      funext z; simp [Lft_apply]
    rw [e]; exact (tangent_hol S t ht).2
  φ := S.φ
  ψ := S.ψ
  hφ := S.hφ
  hψ := S.hψ
  hBd := fun z => by
    obtain ⟨C, hC⟩ := S.hBd z
    refine ⟨C, fun ζ hζ => ⟨(norm_Lft_le _ _).trans (hC ζ hζ).1, ?_⟩⟩
    rw [Prod.norm_def, Prod.norm_def, norm_zero, norm_zero, max_self]
    exact max_le (hC ζ hζ).2 ((norm_nonneg _).trans (hC ζ hζ).2)
  hSb := fun z => by
    obtain ⟨C, hC⟩ := S.hSb z
    refine ⟨C, ?_⟩
    refine (eLp_fderiv_triple_le (fun ζ => S.b (S.φ z ζ)) (fun _ => (0 : E)) 0
      (S.hb.comp (S.hφ z).1) contDiff_const).trans ?_
    rw [eLp_fderiv_const_zero, add_zero]; exact hC
  hSob := fun z => by
    obtain ⟨C, hC0, hC⟩ := eLp_L S z
    refine ⟨2 * C, fun w hw => ?_⟩
    have h1 : ContDiff ℝ ∞ (fun z' => S.L z' w.1) := contDiff_fst.comp hw
    have h2 : ContDiff ℝ ∞ (fun z' => S.L z' w.2) := (contDiff_fst.comp contDiff_snd).comp hw
    refine (eLp_fderiv_triple_le (fun ζ => S.L (S.φ z ζ) w.1) (fun ζ => S.L (S.φ z ζ) w.2) 0
      (h1.comp (S.hφ z).1) (h2.comp (S.hφ z).1)).trans ?_
    refine (add_le_add (hC _ h1) (hC _ h2)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := norm_fst_le w
    have := norm_snd_le w
    nlinarith

@[simp] lemma lift_L [FiniteDimensional ℝ E] (S : Setup E Y I) : S.lift.L = Lft S.L := rfl
@[simp] lemma lift_ys [FiniteDimensional ℝ E] (S : Setup E Y I) (k : ℕ) (t : ℝ) :
    S.lift.ys k t = (S.ys k t, S.ys (k + 1) t) := rfl
@[simp] lemma lift_φ [FiniteDimensional ℝ E] (S : Setup E Y I) : S.lift.φ = S.φ := rfl
@[simp] lemma lift_b [FiniteDimensional ℝ E] (S : Setup E Y I) (z : ℂ) :
    S.lift.b z = (S.b z, 0, 0) := rfl

end QR26

end

end FiniteEnergyPlane

-- FILE: RSK_R27.lean
/-!
# Q-R, layer 27 (local, NOT published): the induction over the jet, and joint smoothness

* `jet_facts k`: for every setup, `L(·) (ys k t)` is smooth and the chart pull-backs have jointly
  continuous `ζ`-derivatives of all orders (induction on `k` over all setups, via `Setup.lift`).
* `abs_contDiffOn`: `(z, t) ↦ b z + L z (ys 0 t)` is `C^n` on `univ ×ˢ I` for every `n`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Set Filter Topology Metric JHolomorphic
open scoped ContDiff

noncomputable section

namespace QR27

open QR25 QR26

/-- The jet facts, for all setups at once. -/
theorem jet_facts (k : ℕ) : ∀ (E Y : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (I : Set ℝ)
    (S : Setup E Y I),
    (∀ t ∈ I, ContDiff ℝ ∞ (fun z => S.L z (S.ys k t))) ∧
      ∀ z a, ContinuousOn (fun q : ℂ × ℝ =>
        iteratedFDeriv ℝ a (fun ζ => S.L (S.φ z ζ) (S.ys k q.2)) q.1) (ball 0 1 ×ˢ I) := by
  induction k with
  | zero =>
    intro E Y _ _ _ _ _ I S
    exact ⟨S.hsm, fun z a => cont_derivs S z a⟩
  | succ k ih =>
    intro E Y _ _ _ _ _ I S
    obtain ⟨h1, h2⟩ := ih (E × E × ℂ) (Y × Y) I S.lift
    let π : E × E × ℂ →L[ℝ] E :=
      (ContinuousLinearMap.fst ℝ E ℂ).comp (ContinuousLinearMap.snd ℝ E (E × ℂ))
    refine ⟨fun t ht => ?_, fun z a => ?_⟩
    · have := π.contDiff.comp (h1 t ht)
      exact this
    · have hc := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a => ℂ)
        (E × E × ℂ) E π).continuous.comp_continuousOn (h2 z a)
      refine hc.congr fun q hq => ?_
      have hF : ContDiff ℝ ∞ (fun ζ => S.lift.L (S.lift.φ z ζ) (S.lift.ys k q.2)) :=
        (h1 q.2 hq.2).comp (S.hφ z).1
      have e := π.iteratedFDeriv_comp_left hF.contDiffAt (x := q.1) (QR26.nat_le_infty a)
      exact e


variable {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {I : Set ℝ}

/-- Joint smoothness of the family. -/
theorem abs_contDiffOn (S : Setup E Y I) (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℂ × ℝ => S.b p.1 + S.L p.1 (S.ys 0 p.2)) (univ ×ˢ I) := by
  refine contDiffOn_of_locally_contDiffOn fun p hp => ?_
  obtain ⟨V, hVo, hzV, hψ, hψm, hφψ⟩ := S.hψ p.1
  refine ⟨V ×ˢ I, hVo.prod S.hI, ⟨hzV, hp.2⟩, ?_⟩
  have hG := QR24.contDiffOn_of_partials n isOpen_ball S.hI
    (fun k q => S.L (S.φ p.1 q.1) (S.ys k q.2))
    (fun k t ht => (((jet_facts k E Y I S).1 t ht).comp (S.hφ p.1).1).contDiffOn)
    (fun k a => (jet_facts k E Y I S).2 p.1 a)
    (fun k q hq => (S.L (S.φ p.1 q.1)).hasFDerivAt.comp_hasDerivAt _ (S.hys k q.2 hq.2))
  have hm : ContDiffOn ℝ n (fun q : ℂ × ℝ => (S.ψ p.1 q.1, q.2)) (V ×ˢ I) :=
    ((hψ.comp contDiffOn_fst fun q hq => hq.1).prodMk contDiffOn_snd).of_le
      (QR26.nat_le_infty n)
  have hcomp := hG.comp hm fun q hq => ⟨hψm hq.1, hq.2⟩
  have hb : ContDiffOn ℝ n (fun q : ℂ × ℝ => S.b q.1) (V ×ˢ I) :=
    ((S.hb.comp contDiff_fst).of_le (QR26.nat_le_infty n)).contDiffOn
  refine ((hb.add hcomp).congr fun q hq => ?_).mono fun q hq => hq.2
  simp only [Function.comp_apply, hφψ q.1 hq.1]

end QR27

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

/-- Compact coordinates `((λ̃, μ̃, ẽN, κ), (uT, uN, c))`. -/
abbrev Cs := (ℂ × ℂ × ℝ × ℝ) × (ℂ × ℂ × ℂ)

/-- `ζ = λ̃ uT`, retracted into `ball 0 (1/2)` (identity on `ball 0 (1/8)`). -/
def zr (c : Cs) : ℂ := rtr (1 / 2) (c.1.1 * c.2.1)

/-- `λ̃ / (2π (1 + ζ))`. -/
def d1 (c : Cs) : ℂ := c.1.1 * (((2 * π : ℝ) : ℂ) * (1 + zr c))⁻¹

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

-- FILE: RSK_R1.lean
/-!
# Q-R, layer 1 (local, NOT published): weighted pointwise bounds of the linear part

R1 `c0_bound_proof`: `‖(pLc z y).1‖ ≤ K‖y‖(1+‖z‖)^{1+δT/2π}` and
`‖(pLc z y).2‖ ≤ K‖y‖(1+‖z‖)^{δ/2π}`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QR

open QN19W

lemma norm_c_le (y : QDom) : ‖y.2.1‖ ≤ ‖y‖ := (norm_fst_le _).trans (norm_snd_le _)

end QR

end

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

include hρ in
lemma Kh_eq {q : ℂ × ℂ} (hq : ‖q.2‖ < ρ / 4) : Kh ρ Jbar q = Jbar q := by
  rw [Kh, rtr_eq hρ hq]

/-! ### The rescaled equation -/

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

/-- Real diagonal scaling. -/
def dg (α β : ℝ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  ContinuousLinearMap.prodMap (α • ContinuousLinearMap.id ℝ ℂ) (β • ContinuousLinearMap.id ℝ ℂ)

@[simp] lemma dg_apply (α β : ℝ) (v : ℂ × ℂ) : dg α β v = (α • v.1, β • v.2) := rfl

/-- The fibre structure from data `X`. -/
def JfX (e : TE) (X : CL) : CL :=
  jStd + (dg e.2.2.im 1).comp (X.comp (dg e.2.2.re (e.2.2.re * e.2.2.im)))

/-- The inhomogeneous term from data `X`. -/
def mX (e : TE) (X : CL) : ℂ × ℂ := dg e.2.2.im 1 (X (Complex.I, 0))

/-- The fixed outer map. -/
def Φ (y : TE × CL) : TE →L[ℝ] TE := vgJ (fun _ => JfX y.1 y.2) (fun _ => mX y.1 y.2) y.1

/-! ### Smoothness -/

section Smooth

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

end Smooth

variable {K : ℂ × ℂ → CL}

/-! ### Conjugation identities -/

/-! ### Almost complexity -/

/-! ### The rescaled equation -/

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

end Kc

/-! ### The lift -/

variable {χT χN β : ℝ → ℝ}

variable (χT χN β) in
/-- The tangential perturbation. -/
def h1 (x : QDom) (ξ : ℂ) : ℂ := (hC χT χN β x (cplx ξ)).1

variable (χT χN β) in
/-- The normal perturbation. -/
def h2 (x : QDom) (ξ : ℂ) : ℂ := (hC χT χN β x (cplx ξ)).2

/-! ### Smoothness of the lift -/

variable (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)

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

/-! ### The lift data -/

variable {δ δT K₀ : ℝ}

section C0

variable (hC0 : ∀ (y : QDom) (z : ℂ),
      ‖(pLc χT χN β z y).1‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(pLc χT χN β z y).2‖ ≤ K₀ * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π))) (hK₀ : 0 ≤ K₀)

end C0

/-! ### The scales and the rescaled lift -/

/-! ### The window bounds -/

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

/-! ### The fixed coefficients -/

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

lemma h1_eq (x : QDom) : h1 χT χN β x = fun ξ => vL (vOf χT (wrep x.1) (cplx ξ)) := rfl

lemma h2_eq (x : QDom) : h2 χT χN β x =
    fun ξ => (fun q : ℝ × ℝ => β q.1 • x.2.1 + vL (vOf χN (wrep x.2.2) q)) (cplx ξ) := rfl

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

/-! ### The window derivative -/

lemma cplx_re (ξ : ℂ) : (cplx ξ).1 = ξ.re := rfl

/-! ### Smoothness and the `L⁴` bound on the window -/

end QR19

end

end FiniteEnergyPlane

-- FILE: RSK_R28a.lean
/-!
# Q-R, layer 28a (local, NOT published): charts and setup fields for the plane family

Charts: the identity for `‖z‖ < 1/2`, and `ζ ↦ Eexp (xi z + ζ)` (with `Eexp (xi z) = z`) otherwise,
with local inverses `ψc`. Field lemmas: chart regularity, local inverses, sup bounds, `L⁴` bounds.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic
open scoped ContDiff Real ENNReal NNReal

noncomputable section

namespace QR28

open QL QR QR25 QR26

/-- The log-coordinate base point of `z`. -/
def xi (z : ℂ) : ℂ := toC (zc z)

open Classical in
/-- The chart at `z`. -/
def φc (z : ℂ) : ℂ → ℂ := if ‖z‖ < 1 / 2 then fun ζ => ζ else fun ζ => Eexp (xi z + ζ)

open Classical in
/-- Its local inverse near `z`. -/
def ψc (z : ℂ) : ℂ → ℂ := if ‖z‖ < 1 / 2 then fun w => w else fun w => lchart (w / z - 1)

lemma φc_of_lt {z : ℂ} (h : ‖z‖ < 1 / 2) : φc z = fun ζ => ζ := by rw [φc, if_pos h]

lemma φc_of_le {z : ℂ} (h : 1 / 2 ≤ ‖z‖) : φc z = fun ζ => Eexp (xi z + ζ) := by
  rw [φc, if_neg (not_lt.2 h)]

lemma ψc_of_lt {z : ℂ} (h : ‖z‖ < 1 / 2) : ψc z = fun w => w := by rw [ψc, if_pos h]

lemma ψc_of_le {z : ℂ} (h : 1 / 2 ≤ ‖z‖) : ψc z = fun w => lchart (w / z - 1) := by
  rw [ψc, if_neg (not_lt.2 h)]

lemma holo_of_hasDerivAt {f : ℂ → ℂ} {d ζ : ℂ} (h : HasDerivAt f d ζ) :
    IsHoloAt f ζ ∧ fderiv ℝ f ζ 1 = d := by
  have hf : HasFDerivAt f ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ) ζ :=
    h.hasFDerivAt.restrictScalars ℝ
  refine ⟨⟨hf.differentiableAt, ?_⟩, ?_⟩ <;> rw [hf.fderiv] <;> simp

lemma Eexp_xi {z : ℂ} (hz : z ≠ 0) : Eexp (xi z) = z := by
  rw [xi, ← Ecyl_cplx, cplx_toC]
  exact QR10.Ecyl_zc hz

lemma hasDerivAt_Eexp_shift (ξ ζ : ℂ) : HasDerivAt (fun ζ => Eexp (ξ + ζ))
    (Complex.exp (((2 * π : ℝ) : ℂ) * (ξ + ζ)) * (((2 * π : ℝ) : ℂ) * 1)) ζ := by
  have h := (((hasDerivAt_id ζ).const_add ξ).const_mul (((2 * π : ℝ) : ℂ))).cexp
  exact h

theorem hφc (z : ℂ) :
    ContDiff ℝ ∞ (φc z) ∧ (∀ ζ, IsHoloAt (φc z) ζ) ∧ ∀ ζ, fderiv ℝ (φc z) ζ 1 ≠ 0 := by
  rcases lt_or_ge ‖z‖ (1 / 2) with h | h
  · rw [φc_of_lt h]
    refine ⟨contDiff_id, fun ζ => ⟨differentiableAt_id, ?_⟩, fun ζ => ?_⟩
    · rw [fderiv_id']; simp
    · rw [fderiv_id']; simp
  · rw [φc_of_le h]
    refine ⟨?_, fun ζ => (holo_of_hasDerivAt (hasDerivAt_Eexp_shift (xi z) ζ)).1, fun ζ => ?_⟩
    · have hc : ContDiff ℂ ∞ (fun ζ : ℂ => Eexp (xi z + ζ)) :=
        Complex.contDiff_exp.comp (contDiff_const.mul (contDiff_const.add contDiff_id))
      exact hc.restrict_scalars ℝ
    · rw [(holo_of_hasDerivAt (hasDerivAt_Eexp_shift (xi z) ζ)).2, mul_one]
      exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.2 (by positivity))

lemma norm_div_sub_one_lt {z w : ℂ} (hz : z ≠ 0) (hw : w ∈ ball z (‖z‖ / 2)) :
    ‖w / z - 1‖ < 1 / 2 := by
  rw [div_sub_one hz, norm_div]
  have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [div_lt_iff₀ hzp]
  rw [mem_ball, dist_eq_norm] at hw
  linarith

theorem hψc (z : ℂ) : ∃ V, IsOpen V ∧ z ∈ V ∧ ContDiffOn ℝ ∞ (ψc z) V ∧
    MapsTo (ψc z) V (ball 0 1) ∧ ∀ w ∈ V, φc z (ψc z w) = w := by
  rcases lt_or_ge ‖z‖ (1 / 2) with h | h
  · refine ⟨ball 0 1, isOpen_ball, mem_ball_zero_iff.2 (by linarith), ?_, ?_, ?_⟩
    · rw [ψc_of_lt h]; exact contDiffOn_id
    · rw [ψc_of_lt h]; exact fun w hw => hw
    · intro w _; rw [φc_of_lt h, ψc_of_lt h]
  · have hz : z ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith
    have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [ψc_of_le h, φc_of_le h]
    have hcd : ContDiffOn ℝ ∞ (fun w => lchart (w / z - 1)) (ball z (‖z‖ / 2)) := by
      intro w hw
      have hu : ‖w / z - 1‖ < 1 := (norm_div_sub_one_lt hz hw).trans (by norm_num)
      have hin : ContDiffAt ℝ ∞ (fun w : ℂ => w / z - 1) w :=
        (contDiffAt_id.mul contDiffAt_const).sub contDiffAt_const
      exact ((lchart_contDiffAt hu).comp w hin).contDiffWithinAt
    refine ⟨ball z (‖z‖ / 2) ∩ (fun w => lchart (w / z - 1)) ⁻¹' ball 0 1,
      hcd.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball, ⟨mem_ball_self (by positivity),
        ?_⟩, hcd.mono inter_subset_left, fun w hw => hw.2, fun w hw => ?_⟩
    · show lchart (z / z - 1) ∈ ball (0 : ℂ) 1
      rw [div_self hz, sub_self, lchart, add_zero, Complex.log_one, zero_mul]
      exact mem_ball_self one_pos
    · have hu : ‖w / z - 1‖ < 1 := (norm_div_sub_one_lt hz hw.1).trans (by norm_num)
      have hne : 1 + (w / z - 1) ≠ 0 := Complex.slitPlane_ne_zero (one_add_mem_slitPlane' hu)
      have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
      show Eexp (xi z + lchart (w / z - 1)) = w
      have e : Eexp (xi z + lchart (w / z - 1)) = Eexp (xi z) * (1 + (w / z - 1)) := by
        rw [Eexp, Eexp, mul_add, Complex.exp_add, lchart]
        congr 1
        rw [show ((2 * π : ℝ) : ℂ) * (Complex.log (1 + (w / z - 1)) * (((2 * π : ℝ) : ℂ))⁻¹) =
          Complex.log (1 + (w / z - 1)) by field_simp]
        exact Complex.exp_log hne
      rw [e, Eexp_xi hz, add_sub_cancel, mul_div_cancel₀ _ hz]

theorem eLp_ball_of_continuous {F : Type*} [NormedAddCommGroup F] {f : ℂ → F}
    (hf : Continuous f) : ∃ C : ℝ, eLpNorm f 4 (volume.restrict (ball (0 : ℂ) 1)) ≤
      ENNReal.ofReal C := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf.continuousOn
  have h := eLpNorm_le_of_ae_bound (μ := volume.restrict (ball (0 : ℂ) 1)) (p := 4) (f := f) (C := M)
    ((ae_restrict_iff' measurableSet_ball).2
      (Eventually.of_forall fun x hx => hM x (ball_subset_closedBall hx)))
  refine ⟨((volume.restrict (ball (0 : ℂ) 1)) univ ^ (4 : ℝ≥0∞).toReal⁻¹ *
    ENNReal.ofReal M).toReal, h.trans (le_of_eq (ENNReal.ofReal_toReal ?_).symm)⟩
  refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) ?_)
    ENNReal.ofReal_ne_top
  rw [Measure.restrict_apply_univ]
  exact measure_ball_lt_top.ne

theorem hys_iter {r : ℝ} {γ : ℝ → QDom} (hγ : ContDiffOn ℝ ∞ γ (Ioo (-r) r)) (k : ℕ) (t : ℝ)
    (ht : t ∈ Ioo (-r) r) : HasDerivAt (iteratedDerivWithin k γ (Ioo (-r) r))
      (iteratedDerivWithin (k + 1) γ (Ioo (-r) r) t) t := by
  have hIo : IsOpen (Ioo (-r) r) := isOpen_Ioo
  have hlt : ((k : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.2 (ENat.coe_lt_top k)
  have hd := hγ.differentiableOn_iteratedDerivWithin hlt (uniqueDiffOn_Ioo (-r) r) t ht
  have h := ((hd.differentiableAt (hIo.mem_nhds ht)).hasDerivAt)
  rw [iteratedDerivWithin_succ, derivWithin_of_isOpen hIo ht]
  exact h

variable {χT χN β : ℝ → ℝ}

theorem hBd_pLc {K a e : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (he : e ≤ 0) (hK : 0 ≤ K)
    (hC0 : ∀ (y : QDom) (z : ℂ), ‖(pLc χT χN β z y).1‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ a ∧
      ‖(pLc χT χN β z y).2‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ e) (z : ℂ) :
    ∃ C, ∀ ζ ∈ ball (0 : ℂ) 1, ‖pLc χT χN β (φc z ζ)‖ ≤ C ∧
      ‖((φc z ζ, (0 : ℂ)) : ℂ × ℂ)‖ ≤ C := by
  set R := max 1 (Real.exp (2 * π * (xi z).re + 2 * π))
  have hR : ∀ ζ ∈ ball (0 : ℂ) 1, ‖φc z ζ‖ ≤ R := by
    intro ζ hζ
    have hζ' := mem_ball_zero_iff.1 hζ
    rcases lt_or_ge ‖z‖ (1 / 2) with h | h
    · rw [φc_of_lt h]; exact hζ'.le.trans (le_max_left _ _)
    · rw [φc_of_le h, QR13.norm_Eexp]
      refine le_trans (Real.exp_le_exp.2 ?_) (le_max_right _ _)
      have := Complex.re_le_norm ζ
      rw [Complex.add_re]
      nlinarith [Real.pi_pos]
  have hop : ∀ w : ℂ, ‖pLc χT χN β w‖ ≤ K * (1 + ‖w‖) := by
    intro w
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
    obtain ⟨h1, h2⟩ := hC0 y w
    have hx : 1 ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
    have p1 : (1 + ‖w‖) ^ a ≤ 1 + ‖w‖ := by
      have := Real.rpow_le_rpow_of_exponent_le hx ha1; rwa [Real.rpow_one] at this
    have p2 : (1 + ‖w‖) ^ e ≤ 1 + ‖w‖ :=
      (Real.rpow_le_one_of_one_le_of_nonpos hx he).trans hx
    have hKy : 0 ≤ K * ‖y‖ := by positivity
    rw [Prod.norm_def]
    refine max_le (h1.trans ?_) (h2.trans ?_)
    · calc K * ‖y‖ * (1 + ‖w‖) ^ a ≤ K * ‖y‖ * (1 + ‖w‖) := mul_le_mul_of_nonneg_left p1 hKy
        _ = K * (1 + ‖w‖) * ‖y‖ := by ring
    · calc K * ‖y‖ * (1 + ‖w‖) ^ e ≤ K * ‖y‖ * (1 + ‖w‖) := mul_le_mul_of_nonneg_left p2 hKy
        _ = K * (1 + ‖w‖) * ‖y‖ := by ring
  refine ⟨K * (1 + R) + R, fun ζ hζ => ⟨?_, ?_⟩⟩
  · have hR0 : 0 ≤ R := le_trans zero_le_one (le_max_left _ _)
    calc ‖pLc χT χN β (φc z ζ)‖ ≤ K * (1 + ‖φc z ζ‖) := hop _
      _ ≤ K * (1 + R) := mul_le_mul_of_nonneg_left (by linarith [hR ζ hζ]) hK
      _ ≤ K * (1 + R) + R := by linarith
  · rw [Prod.norm_def, norm_zero]
    have hR0 : 0 ≤ R := le_trans zero_le_one (le_max_left _ _)
    refine max_le ((hR ζ hζ).trans ?_) (by positivity)
    nlinarith [mul_nonneg hK (by linarith : (0 : ℝ) ≤ 1 + R)]

end QR28

end

end FiniteEnergyPlane

-- FILE: RSK_R28b.lean
/-!
# Q-R, layer 28b (local, NOT published): the chart `L⁴` bound of `pLc`

* `pLc_Eexp`: `pLc (Eexp ξ) w = hC w (cplx ξ)`.
* `wrep_smooth`: if `z ↦ pLc z w` is smooth, so are the representatives `wrep w.1`, `wrep w.2.2`.
* `hSob_pLc`: on each chart disc, `‖D_ζ pLc (φc z ζ) w‖_{L⁴} ≤ C ‖w‖`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic
open scoped ContDiff Real ENNReal NNReal

noncomputable section

namespace QR28

open QL QN QN18 QN19W QR QR8 QR13 QR14 QR17 QR18 QR19

variable {χT χN β : ℝ → ℝ}

lemma pLc_Eexp (w : QDom) (ξ : ℂ) : pLc χT χN β (Eexp ξ) w = hC χT χN β w (cplx ξ) := by
  have h := congrFun (pLc_eq_pfG (χT := χT) (χN := χN) (β := β) w) (Eexp ξ)
  rw [h, ← Ecyl_cplx]
  exact pfG_cylInf (hC_per w) _ _

lemma contDiff_Eexp' : ContDiff ℝ ∞ Eexp := by
  have h : ContDiff ℂ ∞ Eexp := Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  exact h.restrict_scalars ℝ

lemma cL_vL (a : Vec 1) : cL (vL a) = a := by simp [cToVec_vecToC]

lemma wrep_smooth (hχT : ContDiff ℝ ∞ χT) (hχN : ContDiff ℝ ∞ χN) (hβ : ContDiff ℝ ∞ β)
    {w : QDom} (h : ContDiff ℝ ∞ (fun z => pLc χT χN β z w)) :
    ContDiff ℝ ∞ (wrep w.1) ∧ ContDiff ℝ ∞ (wrep w.2.2) := by
  have eH : hC χT χN β w = fun q => pLc χT χN β (Eexp (toC q)) w := by
    funext q; rw [pLc_Eexp, cplx_toC]
  have hH : ContDiff ℝ ∞ (hC χT χN β w) := by
    rw [eH]
    exact h.comp (contDiff_Eexp'.comp Complex.equivRealProdCLM.symm.contDiff)
  have e1 : wrep w.1 = fun q => Real.exp (-χT q.1) • cL (hC χT χN β w q).1 := by
    funext q
    show wrep w.1 q = Real.exp (-χT q.1) • cL (vL (Real.exp (χT q.1) • wrep w.1 q))
    rw [map_smul, map_smul, cL_vL, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_smul]
  have e2 : wrep w.2.2 =
      fun q => Real.exp (-χN q.1) • cL ((hC χT χN β w q).2 - β q.1 • w.2.1) := by
    funext q
    show wrep w.2.2 q = Real.exp (-χN q.1) •
      cL ((β q.1 • w.2.1 + vL (Real.exp (χN q.1) • wrep w.2.2 q)) - β q.1 • w.2.1)
    rw [add_sub_cancel_left, map_smul, map_smul, cL_vL, smul_smul, ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, one_smul]
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact (Real.contDiff_exp.comp (hχT.comp contDiff_fst).neg).smul
      (cL.contDiff.comp (contDiff_fst.comp hH))
  · rw [e2]
    exact (Real.contDiff_exp.comp (hχN.comp contDiff_fst).neg).smul
      (cL.contDiff.comp ((contDiff_snd.comp hH).sub ((hβ.comp contDiff_fst).smul contDiff_const)))

lemma abs_im_xi_le (z : ℂ) : |(xi z).im| ≤ 1 / 2 := by
  have h : (xi z).im = Complex.arg z / (2 * π) := by simp [xi, toC, zc]
  rw [h, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), div_le_iff₀ (by positivity)]
  have := Complex.abs_arg_le_pi z
  linarith

lemma enn_final {A1 A3 m Mb a c d W : ℝ} (hA1 : 0 ≤ A1) (hA3 : 0 ≤ A3) (hm : 0 ≤ m)
    (hMb : 0 ≤ Mb) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (haW : a ≤ W) (hcW : c ≤ W)
    (hdW : d ≤ W) :
    2 * (ENNReal.ofReal A1 * ENNReal.ofReal (3 * a) + ENNReal.ofReal A3 * ENNReal.ofReal (3 * d)) +
        ENNReal.ofReal m * ENNReal.ofReal (Mb * c) ≤
      ENNReal.ofReal ((6 * A1 + 6 * A3 + m * Mb) * W) := by
  rw [← ENNReal.ofReal_mul hA1, ← ENNReal.ofReal_mul hA3,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hm,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_le_mul_of_nonneg_left haW hA1, mul_le_mul_of_nonneg_left hdW hA3,
    mul_le_mul_of_nonneg_left hcW (mul_nonneg hm hMb)]

set_option maxHeartbeats 1600000 in
theorem hSob_exp {aT δ : ℝ} (hχT : IsSlopeWeight χT π aT) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) :
    ∃ C : ℝ, ∀ w : QDom, ContDiff ℝ ∞ (fun z' => pLc χT χN β z' w) →
      eLpNorm (fderiv ℝ (fun ζ => pLc χT χN β (φc z ζ) w)) 4
        (volume.restrict (ball (0 : ℂ) 1)) ≤ ENNReal.ofReal (C * ‖w‖) := by
  set ξ₀ := xi z with hξ₀
  obtain ⟨LT, hLT0, hLT⟩ := deriv_bdd hχT
  obtain ⟨LN, hLN0, hLN⟩ := deriv_bdd hχN
  have hc0 : ξ₀.re ∈ Icc (ξ₀.re - 1) (ξ₀.re + 1) := ⟨by linarith, by linarith⟩
  obtain ⟨MT, hMT⟩ := (isCompact_Icc (a := ξ₀.re - 1) (b := ξ₀.re + 1)).exists_bound_of_continuousOn
    (Real.continuous_exp.comp hχT.1.continuous).continuousOn
  obtain ⟨MN, hMN⟩ := (isCompact_Icc (a := ξ₀.re - 1) (b := ξ₀.re + 1)).exists_bound_of_continuousOn
    (Real.continuous_exp.comp hχN.1.continuous).continuousOn
  obtain ⟨Mb, hMb⟩ := (isCompact_Icc (a := ξ₀.re - 1) (b := ξ₀.re + 1)).exists_bound_of_continuousOn
    (hβ.1.continuous_deriv (by simp)).continuousOn
  have hMT0 : 0 ≤ MT := (norm_nonneg _).trans (hMT _ hc0)
  have hMN0 : 0 ≤ MN := (norm_nonneg _).trans (hMN _ hc0)
  have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans (hMb _ hc0)
  set μ := volume.restrict (ball (0 : ℂ) 1)
  set m : ℝ := (μ univ ^ (4 : ℝ≥0∞).toReal⁻¹).toReal
  have hm_eq : μ univ ^ (4 : ℝ≥0∞).toReal⁻¹ = ENNReal.ofReal m := by
    refine (ENNReal.ofReal_toReal ?_).symm
    refine ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) ?_
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top.ne
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set A1 := ‖vL‖ * (MT * (LT + 1))
  set A3 := ‖vL‖ * (MN * (LN + 1))
  have hA1 : 0 ≤ A1 := by positivity
  have hA3 : 0 ≤ A3 := by positivity
  refine ⟨6 * A1 + 6 * A3 + m * Mb, fun w hw => ?_⟩
  obtain ⟨hs1, hs2⟩ := wrep_smooth hχT.1 hχN.1 hβ.1 hw
  -- pointwise bound on the disc
  have hpt : ∀ ζ ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (fun ζ => pLc χT χN β (φc z ζ) w) ζ‖ ≤
      (A1 * Gw w.1 (cplx (ξ₀ + ζ)) + A3 * Gw w.2.2 (cplx (ξ₀ + ζ))) + Mb * ‖w.2.1‖ := by
    intro ζ hζ
    have hre : (cplx (ξ₀ + ζ)).1 ∈ Icc (ξ₀.re - 1) (ξ₀.re + 1) := by
      rw [cplx_re, Complex.add_re]
      have h1 := Complex.abs_re_le_norm ζ
      have h2 := mem_ball_zero_iff.1 hζ
      have h3 := abs_le.1 (h1.trans h2.le)
      exact ⟨by linarith [h3.1], by linarith [h3.2]⟩
    have e : (fun ζ => pLc χT χN β (φc z ζ) w) =
        fun ζ => (h1 χT χN β w (ξ₀ + ζ), h2 χT χN β w (ξ₀ + ζ)) := by
      rw [φc_of_le hz]; funext ζ; rw [pLc_Eexp]; rfl
    have hh1 : ContDiff ℝ ∞ (h1 χT χN β w) := by
      rw [h1_eq]
      exact (vL.contDiff.comp (vOf_contDiff hχT.1 hs1)).comp
        Complex.equivRealProdCLM.toContinuousLinearMap.contDiff
    have hh2 : ContDiff ℝ ∞ (h2 χT χN β w) := by
      rw [h2_eq]
      exact (((hβ.1.comp contDiff_fst).smul contDiff_const).add
        (vL.contDiff.comp (vOf_contDiff hχN.1 hs2))).comp
        Complex.equivRealProdCLM.toContinuousLinearMap.contDiff
    have d1 : DifferentiableAt ℝ (fun ζ => h1 χT χN β w (ξ₀ + ζ)) ζ :=
      ((hh1.comp (contDiff_const.add contDiff_id)).differentiable (by simp)) ζ
    have d2 : DifferentiableAt ℝ (fun ζ => h2 χT χN β w (ξ₀ + ζ)) ζ :=
      ((hh2.comp (contDiff_const.add contDiff_id)).differentiable (by simp)) ζ
    rw [e]
    refine (norm_fderiv_pair_le d1 d2).trans ?_
    rw [fderiv_comp_add_left (f := h1 χT χN β w), fderiv_comp_add_left (f := h2 χT χN β w)]
    have b1 := norm_fderiv_h1_le (χN := χN) (β := β) hχT.1 hs1 hLT (ξ₀ + ζ)
    have b2 := norm_fderiv_h2_le (χT := χT) hχN.1 hβ.1 hs2 hLN (ξ₀ + ζ)
    have eT := hMT _ hre
    have eN := hMN _ hre
    have eb := hMb _ hre
    rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at eT eN
    rw [Real.norm_eq_abs] at eb
    have g1 := Gw_nonneg w.1 (cplx (ξ₀ + ζ))
    have g2 := Gw_nonneg w.2.2 (cplx (ξ₀ + ζ))
    have k1 : ‖vL‖ * (Real.exp (χT (cplx (ξ₀ + ζ)).1) * ((LT + 1) * Gw w.1 (cplx (ξ₀ + ζ)))) ≤
        A1 * Gw w.1 (cplx (ξ₀ + ζ)) := by
      calc _ ≤ ‖vL‖ * (MT * ((LT + 1) * Gw w.1 (cplx (ξ₀ + ζ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right eT (by positivity))
              (norm_nonneg _)
        _ = _ := by ring
    have k3 : ‖vL‖ * (Real.exp (χN (cplx (ξ₀ + ζ)).1) * ((LN + 1) * Gw w.2.2 (cplx (ξ₀ + ζ)))) ≤
        A3 * Gw w.2.2 (cplx (ξ₀ + ζ)) := by
      calc _ ≤ ‖vL‖ * (MN * ((LN + 1) * Gw w.2.2 (cplx (ξ₀ + ζ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right eN (by positivity))
              (norm_nonneg _)
        _ = _ := by ring
    have kb : |deriv β (cplx (ξ₀ + ζ)).1| * ‖w.2.1‖ ≤ Mb * ‖w.2.1‖ :=
      mul_le_mul_of_nonneg_right eb (norm_nonneg _)
    linarith
  -- the window function
  set G : ℝ × ℝ → ℝ := fun q => A1 * Gw w.1 q + A3 * Gw w.2.2 q
  have hGc : Continuous G :=
    (continuous_const.mul (continuous_Gw hs1)).add (continuous_const.mul (continuous_Gw hs2))
  have hGp : ∀ s t : ℝ, G (s, t + 1) = G (s, t) := fun s t => by
    simp only [G, Gw_per]
  have hcz : Continuous fun ζ : ℂ => G (cplx (ξ₀ + ζ)) :=
    hGc.comp (Complex.equivRealProdCLM.continuous.comp (continuous_const.add continuous_id))
  have step1 : eLpNorm (fderiv ℝ (fun ζ => pLc χT χN β (φc z ζ) w)) 4 μ ≤
      eLpNorm (fun ζ => G (cplx (ξ₀ + ζ)) + Mb * ‖w.2.1‖) 4 μ :=
    eLpNorm_mono_ae_real ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall hpt))
  have step2 : eLpNorm (fun ζ => G (cplx (ξ₀ + ζ)) + Mb * ‖w.2.1‖) 4 μ ≤
      eLpNorm (fun ζ => G (cplx (ξ₀ + ζ))) 4 μ + eLpNorm (fun _ : ℂ => Mb * ‖w.2.1‖) 4 μ :=
    eLpNorm_add_le (f := fun ζ => G (cplx (ξ₀ + ζ))) (g := fun _ : ℂ => Mb * ‖w.2.1‖)
      hcz.aestronglyMeasurable aestronglyMeasurable_const (by norm_num)
  have step3 : eLpNorm (fun ζ => G (cplx (ξ₀ + ζ))) 4 μ ≤ 2 * eLpNorm G 4 cylMeasure :=
    eLpNorm_window_le hGc hGp (abs_im_xi_le z)
  have step4 : eLpNorm G 4 cylMeasure ≤
      ENNReal.ofReal A1 * ENNReal.ofReal (3 * ‖w.1‖) +
        ENNReal.ofReal A3 * ENNReal.ofReal (3 * ‖w.2.2‖) := by
    have hG : G = A1 • Gw w.1 + A3 • Gw w.2.2 := by funext q; simp [G]
    rw [hG]
    refine (eLpNorm_add_le ((continuous_Gw hs1).aestronglyMeasurable.const_smul A1)
      ((continuous_Gw hs2).aestronglyMeasurable.const_smul A3) (by norm_num)).trans ?_
    rw [eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal hA1,
      Real.enorm_eq_ofReal hA3]
    gcongr
    · exact eLpNorm_Gw_le hs1
    · exact eLpNorm_Gw_le hs2
  have step5 : eLpNorm (fun _ : ℂ => Mb * ‖w.2.1‖) 4 μ ≤
      ENNReal.ofReal m * ENNReal.ofReal (Mb * ‖w.2.1‖) := by
    rw [← hm_eq]
    refine eLpNorm_le_of_ae_bound (Eventually.of_forall fun _ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hw1 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  have hw2 : ‖w.2.2‖ ≤ ‖w‖ := (norm_snd_le w.2).trans (norm_snd_le w)
  have hwc : ‖w.2.1‖ ≤ ‖w‖ := norm_c_le w
  calc eLpNorm (fderiv ℝ (fun ζ => pLc χT χN β (φc z ζ) w)) 4 μ
      ≤ 2 * (ENNReal.ofReal A1 * ENNReal.ofReal (3 * ‖w.1‖) +
          ENNReal.ofReal A3 * ENNReal.ofReal (3 * ‖w.2.2‖)) +
        ENNReal.ofReal m * ENNReal.ofReal (Mb * ‖w.2.1‖) := by
        refine step1.trans (step2.trans (add_le_add (step3.trans ?_) step5))
        gcongr
    _ ≤ _ := enn_final hA1 hA3 hm0 hMb0 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hw1 hwc hw2

theorem hSob_pLc {aT δ : ℝ} (hχT : IsSlopeWeight χT π aT) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) (z : ℂ) :
    ∃ C : ℝ, ∀ w : QDom, ContDiff ℝ ∞ (fun z' => pLc χT χN β z' w) →
      eLpNorm (fderiv ℝ (fun ζ => pLc χT χN β (φc z ζ) w)) 4
        (volume.restrict (ball (0 : ℂ) 1)) ≤ ENNReal.ofReal (C * ‖w‖) := by
  rcases lt_or_ge ‖z‖ (1 / 2) with h | h
  · obtain ⟨C, -, hCb⟩ := eLpNorm_pLc_ball hχT hχN hβ
    refine ⟨C, fun w hw => ?_⟩
    obtain ⟨h1, h2⟩ := wrep_smooth hχT.1 hχN.1 hβ.1 hw
    rw [φc_of_lt h]
    exact hCb w h1 h2
  · exact hSob_exp hχT hχN hβ h

end QR28

end

end FiniteEnergyPlane

-- FILE: RSK_R28.lean
/-!
# Q-R, layer 28 (local, NOT published): R3 `fam_contDiffOn` from the abstract setup

The plane family `fam γ (z, t) = (z, 0) + pLc z (γ t)` as a `QR26.Setup (ℂ × ℂ) QDom (Ioo (-r) r)`
with `J = Kh ρ Jbar` (R12), `ys k = iteratedDerivWithin k γ (Ioo (-r) r)`, the identity chart near
`0` and exponential charts `ζ ↦ Eexp (xi z + ζ)` elsewhere (R28a).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex JHolomorphic DbarRegularity
open scoped ContDiff Real ENNReal NNReal

noncomputable section

namespace QR28

open QR QR12 QR25 QR26 QR27

theorem fam_contDiffOn_proof (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∀ r > 0, ∀ γ : ℝ → QDom, ContDiffOn ℝ ∞ γ (Ioo (-r) r) →
      (∀ t ∈ Ioo (-r) r, γ t ∈ ball (0 : QDom) ε ∧ qMap Jbar χT χN β (γ t) = 0) →
      ∀ n : ℕ, ContDiffOn ℝ n (fam χT χN β γ) (univ ×ˢ Ioo (-r) r) := by
  obtain ⟨K, hK, hC0⟩ := QRF.c0_bound_stub δ δT hδ hδT χT χN β hχT hχN hβ
  obtain ⟨ε1, hε1, hsz⟩ :=
    QR15.small_zero_facts ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  have hπ : 0 < 2 * π := by positivity
  have he : δ / (2 * π) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ.le hπ.le
  have hT1 : -(2 * π) < δT := lt_of_le_of_lt (le_max_right _ _) hδT.1
  have ha0 : 0 ≤ 1 + δT / (2 * π) := by
    have : -1 < δT / (2 * π) := by rw [lt_div_iff₀ hπ]; linarith
    linarith
  have ha1 : 1 + δT / (2 * π) ≤ 1 := by
    have : δT / (2 * π) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδT.2.le hπ.le
    linarith
  refine ⟨min ε1 (ρ / (4 * K)), lt_min hε1 (by positivity), fun r hr γ hγ hγz n => ?_⟩
  have hIo : IsOpen (Ioo (-r) r) := isOpen_Ioo
  -- facts about the members
  have hfacts : ∀ t ∈ Ioo (-r) r, ContDiff ℝ ∞ (pG χT χN β (γ t)) ∧
      IsJHolomorphicOn Jbar univ (pG χT χN β (γ t)) ∧
      ∀ z, ‖(pLc χT χN β z (γ t)).2‖ < ρ / 4 := by
    intro t ht
    obtain ⟨hx, h0⟩ := hγz t ht
    have hx' := mem_ball_zero_iff.1 hx
    have hx1 : ‖γ t‖ < ε1 := lt_of_lt_of_le hx' (min_le_left _ _)
    have hx2 : ‖γ t‖ < ρ / (4 * K) := lt_of_lt_of_le hx' (min_le_right _ _)
    obtain ⟨-, -, -, -, h5, h6⟩ := hsz (γ t) (mem_ball_zero_iff.2 hx1) h0
    refine ⟨h5, h6, fun z => ?_⟩
    have h2 := (hC0 (γ t) z).2
    have hp : (1 + ‖z‖) ^ (δ / (2 * π)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) he
    have hKx : K * ‖γ t‖ < ρ / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hx2
      linarith
    calc ‖(pLc χT χN β z (γ t)).2‖ ≤ K * ‖γ t‖ * (1 + ‖z‖) ^ (δ / (2 * π)) := h2
      _ ≤ K * ‖γ t‖ * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ < ρ / 4 := by rw [mul_one]; exact hKx
  have hys0 : ∀ t, iteratedDerivWithin 0 γ (Ioo (-r) r) t = γ t := fun t => by
    rw [iteratedDerivWithin_zero]
  have hsm' : ∀ t ∈ Ioo (-r) r,
      ContDiff ℝ ∞ (fun z => pLc χT χN β z (iteratedDerivWithin 0 γ (Ioo (-r) r) t)) := by
    intro t ht
    rw [hys0]
    have e : (fun z => pLc χT χN β z (γ t)) =
        fun z => pG χT χN β (γ t) z - ((z, (0 : ℂ)) : ℂ × ℂ) := by
      funext z; simp only [pG]; abel
    rw [e]
    exact (hfacts t ht).1.sub (contDiff_id.prodMk contDiff_const)
  have hhol' : ∀ t ∈ Ioo (-r) r, IsJHolomorphicOn (Kh ρ Jbar) univ (fun z =>
      ((z, (0 : ℂ)) : ℂ × ℂ) + pLc χT χN β z (iteratedDerivWithin 0 γ (Ioo (-r) r) t)) := by
    intro t ht
    rw [hys0]
    obtain ⟨-, hJh, hsmall⟩ := hfacts t ht
    have key : IsJHolomorphicOn (Kh ρ Jbar) univ (pG χT χN β (γ t)) := by
      intro z _
      refine ⟨(hJh z trivial).1, ?_⟩
      have hz := (hJh z trivial).2
      unfold dbarJ at hz ⊢
      have hs : ‖(pG χT χN β (γ t) z).2‖ < ρ / 4 := by
        unfold pG
        rw [Prod.snd_add, zero_add]; exact hsmall z
      rw [Kh_eq hρ hs]
      exact hz
    exact key
  have hJ' : IsAlmostComplexOn (Kh ρ Jbar) univ := ⟨isOpen_univ, (contDiff_Kh hρ hstd.1).contDiffOn,
    fun q _ => ContinuousLinearMap.ext fun v => by simpa using Kh_sq hρ hstd.2.1 q v⟩
  let S : Setup (ℂ × ℂ) QDom (Ioo (-r) r) :=
    { hI := hIo
      J := Kh ρ Jbar
      hJ := hJ'
      L := pLc χT χN β
      b := fun z => ((z, (0 : ℂ)) : ℂ × ℂ)
      hb := contDiff_id.prodMk contDiff_const
      ys := fun k => iteratedDerivWithin k γ (Ioo (-r) r)
      hys := hys_iter hγ
      hsm := hsm'
      hhol := hhol'
      φ := φc
      ψ := ψc
      hφ := hφc
      hψ := hψc
      hBd := hBd_pLc ha0 ha1 he hK.le hC0
      hSb := fun z => eLp_ball_of_continuous
        (((hφc z).1.prodMk contDiff_const).continuous_fderiv (by simp))
      hSob := hSob_pLc hχT hχN hβ }
  refine (abs_contDiffOn S n).congr fun p _ => ?_
  show pG χT χN β (γ p.2) p.1 = ((p.1, (0 : ℂ)) : ℂ × ℂ) +
    pLc χT χN β p.1 (iteratedDerivWithin 0 γ (Ioo (-r) r) p.2)
  rw [hys0]
  rfl

end QR28

end

end FiniteEnergyPlane

-- FILE: RSK_RP3.lean
namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QRB

theorem contDiffOn_qFamily_of_qMap_eq_zero_proof (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∀ r > 0, ∀ γ : ℝ → QDom, ContDiffOn ℝ ∞ γ (Ioo (-r) r) →
      (∀ t ∈ Ioo (-r) r, γ t ∈ ball (0 : QDom) ε ∧ qMap Jbar χT χN β (γ t) = 0) →
      ∀ n : ℕ, ContDiffOn ℝ n (qFamily χT χN β γ) (univ ×ˢ Ioo (-r) r) := by
  rw [← fam_eq_qFamily]
  exact QR28.fam_contDiffOn_proof ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ

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
    ∃ ε > 0, ∀ r > 0, ∀ γ : ℝ → QDom, ContDiffOn ℝ ∞ γ (Ioo (-r) r) →
      (∀ t ∈ Ioo (-r) r, γ t ∈ ball (0 : QDom) ε ∧ qMap Jbar χT χN β (γ t) = 0) →
      ∀ n : ℕ, ContDiffOn ℝ n (qFamily χT χN β γ) (univ ×ˢ Ioo (-r) r) :=
  QRB.contDiffOn_qFamily_of_qMap_eq_zero_proof ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
