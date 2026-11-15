-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_qMember_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T10:31:08.488778+00:00
-- url     : https://prove2.me/submissions/a1e87044-ffdf-4924-b0d5-b45c4b5a63c3

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
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Definitions.Def_FiniteEnergyPlane_TubeFamily

open Metric Set Filter Topology BoundedContinuousFunction
open Metric Set Filter Topology MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open MeasureTheory Metric Set Filter Topology BoundedContinuousFunction
open scoped ENNReal ContDiff
open Metric Set Filter Topology
open scoped ContDiff

-- FILE: _imports_RSK_RP1.lean


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

lemma norm_U_apply_le (x : QDom) (q : ℝ × ℝ) : ‖U x q‖ ≤ UK * ‖x‖ := by
  rw [U_apply]; exact Uv_bound x q

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

lemma norm_U_apply_le (x : QDom) (q : ℝ × ℝ) : ‖U x q‖ ≤ UK * ‖x‖ :=
  ((U x).norm_coe_le_norm q).trans ((U.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (by unfold UK; linarith) (norm_nonneg x)))

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

/-! ### The worked instance -/

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

lemma beta_bdd {β : ℝ → ℝ} (hβ : IsLeftCutoff β) : ∃ M, 0 ≤ M ∧ ∀ s, |β s| ≤ M := by
  refine bdd_mid _ hβ.1.continuous 1 fun s hs => ?_
  rcases hs with hs | hs
  · rw [hβ.2.1 s hs]; simp
  · rw [hβ.2.2 s (by linarith)]; simp

end QN18

end

end FiniteEnergyPlane

-- FILE: CR411Bridge.lean
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma IsTestSection.continuous {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : Continuous u :=
  hu.1.continuous

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

end

end CauchyRiemannIndex

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

lemma norm_zc_exp {z : ℂ} (hz : z ≠ 0) : Real.exp (2 * π * (zc z).1) = ‖z‖ := by
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  simp only [zc]
  rw [mul_div_cancel₀ _ hπ, Real.exp_log (norm_pos_iff.2 hz)]

lemma exp_rate_eq (a s : ℝ) : Real.exp (2 * π * a * s) = Real.exp (2 * π * s) ^ a := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; ring_nf

/-- A function with rate `x^a` for `s ≥ 0` (`x = e^{2πs}`) and bounded for `s ≤ 0` is bounded by
`K (1 + x)^a`. -/
lemma rate_bound (f : ℝ → ℝ) (a C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (h1 : ∀ s ≥ 0, f s ≤ C * Real.exp (2 * π * a * s)) (h2 : ∀ s ≤ 0, f s ≤ M) :
    ∃ K > 0, ∀ s, f s ≤ K * (1 + Real.exp (2 * π * s)) ^ a := by
  have hx1 : ∀ s, 0 < 1 + Real.exp (2 * π * s) := fun s => by positivity
  rcases le_or_gt 0 a with ha | ha
  · refine ⟨C + M + 1, by positivity, fun s => ?_⟩
    have hge : 1 ≤ (1 + Real.exp (2 * π * s)) ^ a :=
      Real.one_le_rpow (by linarith [Real.exp_pos (2 * π * s)]) ha
    rcases le_or_gt 0 s with hs | hs
    · have e1 := h1 s hs
      rw [exp_rate_eq] at e1
      have e2 : Real.exp (2 * π * s) ^ a ≤ (1 + Real.exp (2 * π * s)) ^ a :=
        Real.rpow_le_rpow (Real.exp_pos _).le (by linarith) ha
      have e3 : 0 ≤ Real.exp (2 * π * s) ^ a := Real.rpow_nonneg (Real.exp_pos _).le _
      nlinarith
    · have e1 := h2 s hs.le
      nlinarith
  · -- negative rate
    set c2 : ℝ := (2 : ℝ) ^ (-a)
    set c3 : ℝ := (1 + Real.exp (2 * π * 0)) ^ (-a)
    refine ⟨C * c2 + M * c3 + 1, by positivity, fun s => ?_⟩
    have hp : 0 < (1 + Real.exp (2 * π * s)) ^ a := Real.rpow_pos_of_pos (hx1 s) _
    rcases le_or_gt 0 s with hs | hs
    · have e1 := h1 s hs
      rw [exp_rate_eq] at e1
      have hxge : 1 ≤ Real.exp (2 * π * s) := Real.one_le_exp (by positivity)
      -- `x^a ≤ 2^{-a} (1+x)^a`
      have e2 : Real.exp (2 * π * s) ^ a ≤ c2 * (1 + Real.exp (2 * π * s)) ^ a := by
        have h12 : 1 + Real.exp (2 * π * s) ≤ 2 * Real.exp (2 * π * s) := by linarith
        have h3 : (2 * Real.exp (2 * π * s)) ^ a ≤ (1 + Real.exp (2 * π * s)) ^ a :=
          Real.rpow_le_rpow_of_nonpos (hx1 s) h12 ha.le
        rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le] at h3
        have h4 : c2 * (2 : ℝ) ^ a = 1 := by
          simp only [c2]; rw [← Real.rpow_add (by norm_num)]; simp
        have h5 : 0 ≤ c2 := by positivity
        calc Real.exp (2 * π * s) ^ a = c2 * ((2 : ℝ) ^ a * Real.exp (2 * π * s) ^ a) := by
              rw [← mul_assoc, h4, one_mul]
          _ ≤ c2 * (1 + Real.exp (2 * π * s)) ^ a := mul_le_mul_of_nonneg_left h3 h5
      have e3 : C * Real.exp (2 * π * s) ^ a ≤ C * (c2 * (1 + Real.exp (2 * π * s)) ^ a) :=
        mul_le_mul_of_nonneg_left e2 hC
      have e4 : 0 ≤ M * c3 * (1 + Real.exp (2 * π * s)) ^ a := by positivity
      nlinarith
    · have e1 := h2 s hs.le
      -- `(1+x)^a ≥ (1 + e^0)^a`
      have hxle : Real.exp (2 * π * s) ≤ Real.exp (2 * π * 0) :=
        Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
      have h3 : (1 + Real.exp (2 * π * 0)) ^ a ≤ (1 + Real.exp (2 * π * s)) ^ a :=
        Real.rpow_le_rpow_of_nonpos (hx1 s) (by linarith) ha.le
      have h4 : c3 * (1 + Real.exp (2 * π * 0)) ^ a = 1 := by
        simp only [c3]; rw [← Real.rpow_add (hx1 0)]; simp
      have h5 : M ≤ M * c3 * (1 + Real.exp (2 * π * s)) ^ a := by
        calc M = M * (c3 * (1 + Real.exp (2 * π * 0)) ^ a) := by rw [h4, mul_one]
          _ ≤ M * (c3 * (1 + Real.exp (2 * π * s)) ^ a) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) hM
          _ = M * c3 * (1 + Real.exp (2 * π * s)) ^ a := by ring
      have e4 : 0 ≤ C * c2 * (1 + Real.exp (2 * π * s)) ^ a := by positivity
      nlinarith

lemma exp_weight_bound {χ : ℝ → ℝ} {b : ℝ} (hχ : IsSlopeWeight χ π b) :
    ∃ K > 0, ∀ s, Real.exp (χ s) ≤ K * (1 + Real.exp (2 * π * s)) ^ (b / (2 * π)) := by
  obtain ⟨KR, hKR, hR⟩ := QL.exists_exp_bound_right χ hχ.1.continuous b fun s hs => hχ.eq_right hs
  obtain ⟨KL, hKL, hL⟩ := QL.exists_exp_bound_left χ hχ.1.continuous π fun s hs => hχ.eq_left hs
  refine rate_bound _ (b / (2 * π)) KR KL hKR.le hKL.le (fun s hs => ?_) (fun s hs => ?_)
  · have e : 2 * π * (b / (2 * π)) * s = b * s := by field_simp
    rw [e]; exact hR s hs
  · calc Real.exp (χ s) ≤ KL * Real.exp (π * s) := hL s hs
      _ ≤ KL * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])) hKL.le
      _ = KL := mul_one _

lemma beta_weight_bound {β : ℝ → ℝ} (hβ : IsLeftCutoff β) (e : ℝ) :
    ∃ K > 0, ∀ s, |β s| ≤ K * (1 + Real.exp (2 * π * s)) ^ e := by
  obtain ⟨M, hM, hMb⟩ := QN18.beta_bdd hβ
  refine rate_bound _ e 0 M le_rfl hM (fun s hs => ?_) (fun s _ => hMb s)
  rw [hβ.2.2 s hs]; simp

lemma norm_U1_le (y : QDom) (q : ℝ × ℝ) : ‖(U y q).1‖ ≤ UK * ‖y‖ :=
  (norm_fst_le _).trans (norm_U_apply_le y q)

lemma norm_U21_le (y : QDom) (q : ℝ × ℝ) : ‖(U y q).2.1‖ ≤ UK * ‖y‖ :=
  ((norm_fst_le _).trans (norm_snd_le _)).trans (norm_U_apply_le y q)

lemma norm_U22_le (y : QDom) (q : ℝ × ℝ) : ‖(U y q).2.2‖ ≤ UK * ‖y‖ :=
  ((norm_snd_le _).trans (norm_snd_le _)).trans (norm_U_apply_le y q)

lemma norm_c_le (y : QDom) : ‖y.2.1‖ ≤ ‖y‖ := (norm_fst_le _).trans (norm_snd_le _)

/-- The scalar algebra of R1. -/
lemma pt_bound {KT Kb KN UK Y PT PN eT eN bs : ℝ} {w : ℂ × ℂ × ℂ} (heT : 0 < eT) (heN : 0 < eN)
    (hT : eT ≤ KT * PT) (hN : eN ≤ KN * PN) (hB : |bs| ≤ Kb * PN)
    (h1 : ‖w.1‖ ≤ UK * Y) (h2 : ‖w.2.1‖ ≤ UK * Y) (h3 : ‖w.2.2‖ ≤ UK * Y) (hY : 0 ≤ Y)
    (hUK : 0 < UK) (hPT : 0 ≤ PT) (hPN : 0 ≤ PN) (hKT : 0 < KT) (hKb : 0 < Kb) (hKN : 0 < KN) :
    ‖(eT : ℂ) * w.1‖ ≤ (KT * UK + (Kb + KN) * UK + 1) * Y * PT ∧
      ‖(bs : ℂ) * w.2.2 + (eN : ℂ) * w.2.1‖ ≤ (KT * UK + (Kb + KN) * UK + 1) * Y * PN := by
  refine ⟨?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heT]
    calc eT * ‖w.1‖ ≤ (KT * PT) * (UK * Y) := mul_le_mul hT h1 (norm_nonneg _) (by positivity)
      _ ≤ (KT * UK + (Kb + KN) * UK + 1) * Y * PT := by
          nlinarith [mul_nonneg (mul_nonneg hY hPT) (by positivity : (0 : ℝ) ≤ (Kb + KN) * UK + 1)]
  · have e1 : ‖(bs : ℂ) * w.2.2‖ ≤ (Kb * PN) * (UK * Y) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hB h3 (norm_nonneg _) (by positivity)
    have e2 : ‖(eN : ℂ) * w.2.1‖ ≤ (KN * PN) * (UK * Y) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heN]
      exact mul_le_mul hN h2 (norm_nonneg _) (by positivity)
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (Kb * PN) * (UK * Y) + (KN * PN) * (UK * Y) := add_le_add e1 e2
      _ ≤ (KT * UK + (Kb + KN) * UK + 1) * Y * PN := by
          nlinarith [mul_nonneg (mul_nonneg hY hPN) (by positivity : (0 : ℝ) ≤ KT * UK + 1)]

/-- R1. -/
theorem c0_bound_proof (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ K > 0, ∀ (y : QDom) (z : ℂ),
      ‖(pLc χT χN β z y).1‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(pLc χT χN β z y).2‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π)) := by
  have hπ : 0 < 2 * π := by positivity
  obtain ⟨KT, hKT, hT⟩ := exp_weight_bound hχT
  obtain ⟨KN, hKN, hN⟩ := exp_weight_bound hχN
  obtain ⟨Kb, hKb, hB⟩ := beta_weight_bound hβ (δ / (2 * π))
  have eT : (2 * π + δT) / (2 * π) = 1 + δT / (2 * π) := by field_simp
  rw [eT] at hT
  have hUK := UK_pos
  refine ⟨KT * UK + (Kb + KN) * UK + 1, by positivity, fun y z => ?_⟩
  have hy := norm_nonneg y
  have hzp : 0 < 1 + ‖z‖ := by positivity
  by_cases hz : z = 0
  · subst hz
    rw [pLc_zero]
    have hK1 : 1 ≤ KT * UK + (Kb + KN) * UK + 1 := by
      have : 0 ≤ KT * UK + (Kb + KN) * UK := by positivity
      linarith
    refine ⟨?_, ?_⟩
    · simp only [norm_zero]; positivity
    · simp only [norm_zero, add_zero, Real.one_rpow, mul_one]
      exact (norm_c_le y).trans (le_mul_of_one_le_left hy hK1)
  · rw [pLc_ne _ _ _ hz, wV_apply]
    have hx := norm_zc_exp hz
    have hT' := hT (zc z).1
    have hN' := hN (zc z).1
    have hB' := hB (zc z).1
    rw [hx] at hT' hN' hB'
    exact pt_bound (Real.exp_pos _) (Real.exp_pos _) hT' hN' hB' (norm_U1_le y (zc z))
      (norm_U21_le y (zc z)) (norm_U22_le y (zc z)) hy hUK (Real.rpow_nonneg hzp.le _)
      (Real.rpow_nonneg hzp.le _) hKT hKb hKN

end QR

end

end FiniteEnergyPlane

-- FILE: RSK_RP1.lean
namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

namespace QRB

theorem exists_norm_qMember_le_proof (δ δT : ℝ) (hδ : δ < 0)
    (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ K > 0, ∀ (y : QDom) (z : ℂ),
      ‖(qMember χT χN β y z).1 - z‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(qMember χT χN β y z).2‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π)) := by
  obtain ⟨K, hK, h⟩ := QR.c0_bound_proof δ δT hδ hδT χT χN β hχT hχN hβ
  refine ⟨K, hK, fun y z => ?_⟩
  have e : qMember χT χN β y z = (z, 0) + QR.pLc χT χN β z y := by
    rw [← pG_eq_qMember]; rfl
  rw [e]
  simpa using h y z

end QRB

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ K > 0, ∀ (y : QDom) (z : ℂ),
      ‖(qMember χT χN β y z).1 - z‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(qMember χT χN β y z).2‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π)) :=
  QRB.exists_norm_qMember_le_proof δ δT hδ hδT χT χN β hχT hχN hβ
