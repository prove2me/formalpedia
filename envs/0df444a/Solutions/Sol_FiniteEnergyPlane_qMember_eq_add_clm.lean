-- Prove2me | solution 1 for FiniteEnergyPlane.qMember_eq_add_clm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T10:25:54.239496+00:00
-- url     : https://prove2.me/submissions/6825eecc-9647-428a-87ef-87aa0a28ce5d

import Definitions.Def_FiniteEnergyPlane_QMember
import Theorems.Thm_CauchyRiemannIndex_exists_continuous_representative_of_mem_W1p
import Theorems.Thm_CauchyRiemannIndex_eq_of_continuous_periodic_ae_eq
import Definitions.Def_FiniteEnergyPlane_TubeFamily



-- FILE: _imports_RSK_RB.lean


-- FILE: QSlope.lean
/-!
# Slope weights (local helper definition, not published as a definition)

`IsSlopeWeight χ a b`: `χ` is smooth, with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`.
-/

namespace FiniteEnergyPlane

open scoped ContDiff

/-! ### Slope weights are affine near the ends -/

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

theorem qMember_eq_add_clm_proof (χT χN β : ℝ → ℝ) (z : ℂ) :
    ∃ L : QDom →L[ℝ] ℂ × ℂ, ∀ x : QDom, qMember χT χN β x z = (z, 0) + L x :=
  ⟨pLc χT χN β z, fun x => by rw [← pG_eq_qMember]; rfl⟩

end QRB

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (χT χN β : ℝ → ℝ) (z : ℂ) :
    ∃ L : QDom →L[ℝ] ℂ × ℂ, ∀ x : QDom, qMember χT χN β x z = (z, 0) + L x :=
  QRB.qMember_eq_add_clm_proof χT χN β z
