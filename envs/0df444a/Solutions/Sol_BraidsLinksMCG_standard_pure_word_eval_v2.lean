-- Prove2me | solution 1 for BraidsLinksMCG.standard_pure_word_eval_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:53:17.697715+00:00
-- url     : https://prove2.me/submissions/cb3a6506-ab5a-4213-8fa6-11799153f67d

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1

set_option autoImplicit false

open BraidsLinksMCG TarchaBraids

namespace P2Ma747

noncomputable section

abbrev OC := OrderedConfig 3
abbrev G3 := Equiv.Perm (Fin 3)

instance instMulActionOC : MulAction G3 OC where
  smul g z := ⟨z.1 ∘ ⇑g⁻¹, z.2.comp (Equiv.injective _)⟩
  one_smul z := Subtype.ext (funext fun k => by
    show z.1 ((1 : G3)⁻¹ k) = z.1 k
    simp)
  mul_smul g h z := Subtype.ext (funext fun k => by
    show z.1 ((g * h)⁻¹ k) = z.1 (h⁻¹ (g⁻¹ k))
    simp [mul_inv_rev, Equiv.Perm.mul_apply])

lemma smul_val (g : G3) (z : OC) : (g • z).1 = z.1 ∘ ⇑g⁻¹ := rfl

instance instCCS : ContinuousConstSMul G3 OC := ⟨fun g => by
  apply continuous_induced_rng.2
  show Continuous fun z : OC => z.1 ∘ ⇑g⁻¹
  exact continuous_pi fun k => (continuous_apply _).comp continuous_subtype_val⟩

instance instCancel : IsCancelSMul G3 OC where
  left_cancel' g a b h := by simpa using congrArg (g⁻¹ • ·) h
  right_cancel' g h z hz := by
    have hk : ∀ k, g⁻¹ k = h⁻¹ k := fun k => by
      have := congrFun (congrArg Subtype.val hz) k
      simp only [smul_val, Function.comp_apply] at this
      exact z.2 this
    exact inv_injective (Equiv.ext hk)

lemma isOpen_inj : IsOpen {p : Fin 3 → ℂ | Function.Injective p} := by
  have h : {p : Fin 3 → ℂ | Function.Injective p} =
      ⋂ i : Fin 3, ⋂ j : Fin 3, ⋂ (_ : i ≠ j), {p | p i ≠ p j} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun hp i j hij hpij => hij (hp hpij),
      fun hp i j hpij => by_contra fun hij => hp i j hij hpij⟩
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => isOpen_ne_fun (continuous_apply i) (continuous_apply j)

instance instLC : LocallyCompactSpace OC := isOpen_inj.locallyCompactSpace

lemma cov1 : IsCoveringMap (configProj 3 : OC → UnorderedConfig 3) := by
  have hq : Topology.IsQuotientMap (configProj 3 : OC → UnorderedConfig 3) :=
    isQuotientMap_quotient_mk'
  have hfG : ∀ {e₁ e₂ : OC}, configProj 3 e₁ = configProj 3 e₂ ↔
      e₁ ∈ MulAction.orbit G3 e₂ := by
    intro e₁ e₂
    rw [MulAction.mem_orbit_iff]
    change Quotient.mk (configSetoid 3) e₁ = Quotient.mk (configSetoid 3) e₂ ↔ _
    rw [Quotient.eq]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, Subtype.ext ?_⟩
      funext k
      simp [smul_val, hg]
    · rintro ⟨g, rfl⟩
      exact ⟨g, by funext k; simp [smul_val]⟩
  exact (hq.isQuotientCoveringMap_of_properlyDiscontinuousSMul (G := G3) hfG).isCoveringMap

def bp (g : G3) : OC := ⟨(baseOrdered 3).1 ∘ ⇑g, (baseOrdered 3).2.comp g.injective⟩

def sw (i : Fin (3 - 1)) : G3 := Equiv.swap (strandIdx i) (strandIdxSucc i)

lemma H1_eq (i : Fin (3 - 1)) : (halfTwistConfig 3 i 1).1 = (baseOrdered 3).1 ∘ ⇑(sw i) := by
  have h := halfTwistConfig_one 3 i
  rw [h]
  funext k
  simp [sw, Function.comp_apply, Equiv.swap_apply_self]

def aP (i : Fin (3 - 1)) (g : G3) : Path (bp g) (bp (sw i * g)) where
  toFun t := ⟨(halfTwistConfig 3 i t).1 ∘ ⇑g, (halfTwistConfig 3 i t).2.comp g.injective⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine continuous_pi fun k => ?_
    exact (continuous_apply (g k)).comp (continuous_subtype_val.comp
      ((continuous_halfTwistConfig 3 i).comp continuous_subtype_val))
  source' := by
    apply Subtype.ext
    simp only [Set.Icc.coe_zero, halfTwistConfig_zero]
    rfl
  target' := by
    apply Subtype.ext
    simp only [Set.Icc.coe_one, H1_eq]
    rfl

lemma proj_aP (i : Fin (3 - 1)) (g : G3) :
    (configProj 3 : OC → UnorderedConfig 3) ∘ (aP i g) = halfTwistLoop 3 i := by
  funext t
  show configProj 3 (aP i g t) = configProj 3 (halfTwistConfig 3 i t)
  exact Quotient.sound ⟨g⁻¹, by funext k; simp [aP]⟩

lemma comp_trans {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Z)
    (g : Y → Z) {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (a : Path x₀ x₁) (b : Path x₁ x₂)
    (c : Path y₀ y₁) (d : Path y₁ y₂) (h1 : f ∘ a = g ∘ c) (h2 : f ∘ b = g ∘ d) :
    f ∘ (a.trans b) = g ∘ (c.trans d) := by
  funext t
  simp only [Function.comp_apply, Path.trans_apply]
  split_ifs
  · exact congrFun h1 _
  · exact congrFun h2 _

def W (i : Fin (3 - 1)) (g : G3) (t : unitInterval) : ℂ :=
  (halfTwistConfig 3 i t).1 (g 0) - (halfTwistConfig 3 i t).1 (g 2)

lemma W_cont (i : Fin (3 - 1)) (g : G3) : Continuous (W i g) := by
  have hc : Continuous fun t : unitInterval => (halfTwistConfig 3 i t).1 :=
    continuous_subtype_val.comp ((continuous_halfTwistConfig 3 i).comp continuous_subtype_val)
  exact ((continuous_apply _).comp hc).sub ((continuous_apply _).comp hc)

def thPath (i : Fin (3 - 1)) (g : G3) (c k : ℂ) (hs : ∀ t, c * W i g t ∈ Complex.slitPlane)
    {x y : ℂ} (h0 : Complex.log (c * W i g 0) + k = x)
    (h1 : Complex.log (c * W i g 1) + k = y) : Path x y where
  toFun t := Complex.log (c * W i g t) + k
  continuous_toFun := ((continuous_const.mul (W_cont i g)).clog hs).add continuous_const
  source' := h0
  target' := h1

def expS (z : ℂ) : {z : ℂ // z ≠ 0} := ⟨Complex.exp z, Complex.exp_ne_zero z⟩

lemma cov2 : IsCoveringMap expS := Complex.isCoveringMap_exp

def dC : C(OC, {z : ℂ // z ≠ 0}) where
  toFun z := ⟨z.1 0 - z.1 2, sub_ne_zero.mpr (fun h => absurd (z.2 h) (by decide))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_apply 0).comp continuous_subtype_val).sub
      ((continuous_apply 2).comp continuous_subtype_val)

lemma thPath_spec (i : Fin (3 - 1)) (g : G3) (c k : ℂ)
    (hs : ∀ t, c * W i g t ∈ Complex.slitPlane) {x y : ℂ}
    (h0 : Complex.log (c * W i g 0) + k = x) (h1 : Complex.log (c * W i g 1) + k = y)
    (hk : c * Complex.exp k = 1) :
    expS ∘ (thPath i g c k hs h0 h1) = dC ∘ (aP i g) := by
  funext t
  apply Subtype.ext
  show Complex.exp (Complex.log (c * W i g t) + k) = W i g t
  rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hs t))]
  linear_combination (W i g t) * hk

lemma WA1 (t : unitInterval) : W 0 1 t = twistPoint (3 / 2) (-1) t - 3 := by
  simp [W, halfTwistConfig, halfTwistFun]; norm_num

lemma WA2 (t : unitInterval) : W 0 (sw 0 * 1) t = twistPoint (3 / 2) 1 t - 3 := by
  have e0 : (sw 0 * 1 : G3) 0 = 1 := by decide
  have e2 : (sw 0 * 1 : G3) 2 = 2 := by decide
  simp only [W, e0, e2]
  simp [halfTwistConfig, halfTwistFun]; norm_num

lemma WA3 (t : unitInterval) : W 1 (sw 0 * (sw 0 * 1)) t = 1 - twistPoint (5 / 2) 1 t := by
  have e0 : (sw 0 * (sw 0 * 1) : G3) 0 = 0 := by decide
  have e2 : (sw 0 * (sw 0 * 1) : G3) 2 = 2 := by decide
  simp only [W, e0, e2]
  simp [halfTwistConfig, halfTwistFun]; norm_num

lemma WB1 (t : unitInterval) : W 1 1 t = 1 - twistPoint (5 / 2) 1 t := by
  simp [W, halfTwistConfig, halfTwistFun]; norm_num

lemma WB2 (t : unitInterval) :
    W 0 (sw 1 * 1) t = twistPoint (3 / 2) (-1) t - twistPoint (3 / 2) 1 t := by
  have e0 : (sw 1 * 1 : G3) 0 = 0 := by decide
  have e2 : (sw 1 * 1 : G3) 2 = 1 := by decide
  simp only [W, e0, e2]
  simp [halfTwistConfig, halfTwistFun]

lemma WB3 (t : unitInterval) :
    W 0 (sw 0 * (sw 1 * 1)) t = twistPoint (3 / 2) 1 t - twistPoint (3 / 2) (-1) t := by
  have e0 : (sw 0 * (sw 1 * 1) : G3) 0 = 1 := by decide
  have e2 : (sw 0 * (sw 1 * 1) : G3) 2 = 0 := by decide
  simp only [W, e0, e2]
  simp [halfTwistConfig, halfTwistFun]

lemma sin_cos_slit (t : unitInterval) :
    0 < Real.sin (Real.pi * t) ∨ Real.cos (Real.pi * t) ≠ 0 := by
  by_cases hc : Real.cos (Real.pi * t) = 0
  · left
    have h1 := Real.sin_sq_add_cos_sq (Real.pi * t)
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have h2 : 0 ≤ Real.sin (Real.pi * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le ht0)
        (by nlinarith [Real.pi_pos])
    rw [hc] at h1
    rcases h2.lt_or_eq with h | h
    · exact h
    · rw [← h] at h1; norm_num at h1
  · exact Or.inr hc

lemma slitA1 : ∀ t, (-1 : ℂ) * W 0 1 t ∈ Complex.slitPlane := by
  intro t
  rw [Complex.mem_slitPlane_iff, WA1]; left
  have h1 := Real.neg_one_le_cos (Real.pi * t)
  simp [twistPoint_re]
  linarith

lemma slitA2 : ∀ t, (-1 : ℂ) * W 0 (sw 0 * 1) t ∈ Complex.slitPlane := by
  intro t
  rw [Complex.mem_slitPlane_iff, WA2]; left
  have h1 := Real.cos_le_one (Real.pi * t)
  simp [twistPoint_re]
  linarith

lemma slitA3 : ∀ t, (-1 : ℂ) * W 1 (sw 0 * (sw 0 * 1)) t ∈ Complex.slitPlane := by
  intro t
  rw [Complex.mem_slitPlane_iff, WA3]; left
  have h1 := Real.neg_one_le_cos (Real.pi * t)
  simp [twistPoint_re]
  linarith

lemma slitB1 : ∀ t, (-1 : ℂ) * W 1 1 t ∈ Complex.slitPlane := by
  intro t
  rw [Complex.mem_slitPlane_iff, WB1]; left
  have h1 := Real.neg_one_le_cos (Real.pi * t)
  simp [twistPoint_re]
  linarith

lemma slitB2 : ∀ t, Complex.I * W 0 (sw 1 * 1) t ∈ Complex.slitPlane := by
  intro t
  rw [Complex.mem_slitPlane_iff, WB2]
  rcases sin_cos_slit t with h | h
  · left
    simp [twistPoint_re, twistPoint_im]
    linarith
  · right
    simp [twistPoint_re, twistPoint_im]
    intro h'
    apply h
    linarith

lemma slitB3 : ∀ t, (-Complex.I) * W 0 (sw 0 * (sw 1 * 1)) t ∈ Complex.slitPlane := by
  intro t
  rw [Complex.mem_slitPlane_iff, WB3]
  rcases sin_cos_slit t with h | h
  · left
    simp [twistPoint_re, twistPoint_im]
    linarith
  · right
    simp [twistPoint_re, twistPoint_im]
    intro h'
    apply h
    linarith

lemma vA1_0 : (-1 : ℂ) * W 0 1 0 = 2 := by
  rw [WA1]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num
lemma vA1_1 : (-1 : ℂ) * W 0 1 1 = 1 := by
  rw [WA1]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num
lemma vA2_0 : (-1 : ℂ) * W 0 (sw 0 * 1) 0 = 1 := by
  rw [WA2]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num
lemma vA2_1 : (-1 : ℂ) * W 0 (sw 0 * 1) 1 = 2 := by
  rw [WA2]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num
lemma vA3_0 : (-1 : ℂ) * W 1 (sw 0 * (sw 0 * 1)) 0 = 2 := by
  rw [WA3]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num
lemma vA3_1 : (-1 : ℂ) * W 1 (sw 0 * (sw 0 * 1)) 1 = 1 := by
  rw [WA3]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num
lemma vB1_0 : (-1 : ℂ) * W 1 1 0 = 2 := by
  rw [WB1]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num
lemma vB1_1 : (-1 : ℂ) * W 1 1 1 = 1 := by
  rw [WB1]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num
lemma vB2_0 : Complex.I * W 0 (sw 1 * 1) 0 = -Complex.I := by
  rw [WB2]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num
lemma vB2_1 : Complex.I * W 0 (sw 1 * 1) 1 = Complex.I := by
  rw [WB2]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num
lemma vB3_0 : (-Complex.I) * W 0 (sw 0 * (sw 1 * 1)) 0 = -Complex.I := by
  rw [WB3]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num
lemma vB3_1 : (-Complex.I) * W 0 (sw 0 * (sw 1 * 1)) 1 = Complex.I := by
  rw [WB3]; apply Complex.ext <;> simp [twistPoint_re, twistPoint_im] <;> norm_num

lemma hexpI : Complex.exp (↑Real.pi / 2 * Complex.I) = Complex.I := by
  rw [← Complex.log_I, Complex.exp_log Complex.I_ne_zero]

lemma hexpNegI : Complex.exp (-(↑Real.pi / 2) * Complex.I) = -Complex.I := by
  rw [← Complex.log_neg_I, Complex.exp_log (neg_ne_zero.mpr Complex.I_ne_zero)]

lemma kA : (-1 : ℂ) * Complex.exp (↑Real.pi * Complex.I) = 1 := by
  rw [Complex.exp_pi_mul_I]; ring

lemma kB2 : Complex.I * Complex.exp (-(↑Real.pi / 2) * Complex.I + 2 * ↑Real.pi * Complex.I) = 1 := by
  rw [Complex.exp_add, hexpNegI, Complex.exp_two_pi_mul_I]
  ring_nf; rw [Complex.I_sq]; ring

lemma kB3 : (-Complex.I) * Complex.exp (↑Real.pi / 2 * Complex.I + 2 * ↑Real.pi * Complex.I) = 1 := by
  rw [Complex.exp_add, hexpI, Complex.exp_two_pi_mul_I]
  ring_nf; rw [Complex.I_sq]; ring

def thA1 : Path (Complex.log 2 + ↑Real.pi * Complex.I) (↑Real.pi * Complex.I) :=
  thPath 0 1 (-1) (↑Real.pi * Complex.I) slitA1 (by rw [vA1_0]) (by rw [vA1_1, Complex.log_one, zero_add])
def thA2 : Path (↑Real.pi * Complex.I) (Complex.log 2 + ↑Real.pi * Complex.I) :=
  thPath 0 (sw 0 * 1) (-1) (↑Real.pi * Complex.I) slitA2 (by rw [vA2_0, Complex.log_one, zero_add])
    (by rw [vA2_1])
def thA3 : Path (Complex.log 2 + ↑Real.pi * Complex.I) (↑Real.pi * Complex.I) :=
  thPath 1 (sw 0 * (sw 0 * 1)) (-1) (↑Real.pi * Complex.I) slitA3 (by rw [vA3_0])
    (by rw [vA3_1, Complex.log_one, zero_add])
def thB1 : Path (Complex.log 2 + ↑Real.pi * Complex.I) (↑Real.pi * Complex.I) :=
  thPath 1 1 (-1) (↑Real.pi * Complex.I) slitB1 (by rw [vB1_0]) (by rw [vB1_1, Complex.log_one, zero_add])
def thB2 : Path (↑Real.pi * Complex.I) (2 * ↑Real.pi * Complex.I) :=
  thPath 0 (sw 1 * 1) Complex.I (-(↑Real.pi / 2) * Complex.I + 2 * ↑Real.pi * Complex.I) slitB2
    (by rw [vB2_0, Complex.log_neg_I]; ring) (by rw [vB2_1, Complex.log_I]; ring)
def thB3 : Path (2 * ↑Real.pi * Complex.I) (3 * ↑Real.pi * Complex.I) :=
  thPath 0 (sw 0 * (sw 1 * 1)) (-Complex.I) (↑Real.pi / 2 * Complex.I + 2 * ↑Real.pi * Complex.I) slitB3
    (by rw [vB3_0, Complex.log_neg_I]; ring) (by rw [vB3_1, Complex.log_I]; ring)

lemma specA1 : expS ∘ thA1 = dC ∘ aP 0 1 := thPath_spec _ _ _ _ _ _ _ kA
lemma specA2 : expS ∘ thA2 = dC ∘ aP 0 (sw 0 * 1) := thPath_spec _ _ _ _ _ _ _ kA
lemma specA3 : expS ∘ thA3 = dC ∘ aP 1 (sw 0 * (sw 0 * 1)) := thPath_spec _ _ _ _ _ _ _ kA
lemma specB1 : expS ∘ thB1 = dC ∘ aP 1 1 := thPath_spec _ _ _ _ _ _ _ kA
lemma specB2 : expS ∘ thB2 = dC ∘ aP 0 (sw 1 * 1) := thPath_spec _ _ _ _ _ _ _ kB2
lemma specB3 : expS ∘ thB3 = dC ∘ aP 0 (sw 0 * (sw 1 * 1)) := thPath_spec _ _ _ _ _ _ _ kB3

def ΓA := ((aP 0 1).trans (aP 0 (sw 0 * 1))).trans (aP 1 (sw 0 * (sw 0 * 1)))
def ΓB := (aP 1 1).trans ((aP 0 (sw 1 * 1)).trans (aP 0 (sw 0 * (sw 1 * 1))))
def ΘA := (thA1.trans thA2).trans thA3
def ΘB := thB1.trans (thB2.trans thB3)

lemma projA : (configProj 3 : OC → UnorderedConfig 3) ∘ ΓA =
    id ∘ (((halfTwistLoop 3 0).trans (halfTwistLoop 3 0)).trans (halfTwistLoop 3 1)) :=
  comp_trans _ id _ _ _ _ (comp_trans _ id _ _ _ _ (proj_aP 0 1) (proj_aP 0 _)) (proj_aP 1 _)

lemma projB : (configProj 3 : OC → UnorderedConfig 3) ∘ ΓB =
    id ∘ ((halfTwistLoop 3 1).trans ((halfTwistLoop 3 0).trans (halfTwistLoop 3 0))) :=
  comp_trans _ id _ _ _ _ (proj_aP 1 1) (comp_trans _ id _ _ _ _ (proj_aP 0 _) (proj_aP 0 _))

lemma liftA : expS ∘ ΘA = dC ∘ ΓA :=
  comp_trans _ _ _ _ _ _ (comp_trans _ _ _ _ _ _ specA1 specA2) specA3

lemma liftB : expS ∘ ΘB = dC ∘ ΓB :=
  comp_trans _ _ _ _ _ _ specB1 (comp_trans _ _ _ _ _ _ specB2 specB3)

lemma noncomm : halfTwistBraid 3 1 * (halfTwistBraid 3 0 * halfTwistBraid 3 0) ≠
    (halfTwistBraid 3 0 * halfTwistBraid 3 0) * halfTwistBraid 3 1 := by
  intro key
  have hq : Path.Homotopic.Quotient.mk
      (((halfTwistLoop 3 0).trans (halfTwistLoop 3 0)).trans (halfTwistLoop 3 1)) =
      Path.Homotopic.Quotient.mk
      ((halfTwistLoop 3 1).trans ((halfTwistLoop 3 0).trans (halfTwistLoop 3 0))) := key
  have hhom := Path.Homotopic.Quotient.eq.mp hq
  have hrel : ΓA.toContinuousMap.HomotopicRel ΓB.toContinuousMap {0, 1} := by
    rw [cov1.homotopicRel_iff_comp ⟨0, by simp, by simp [ΓA, ΓB]⟩]
    have eA : ContinuousMap.comp ⟨configProj 3, cov1.continuous⟩ ΓA.toContinuousMap =
        (((halfTwistLoop 3 0).trans (halfTwistLoop 3 0)).trans
          (halfTwistLoop 3 1)).toContinuousMap :=
      ContinuousMap.ext (fun t => congrFun projA t)
    have eB : ContinuousMap.comp ⟨configProj 3, cov1.continuous⟩ ΓB.toContinuousMap =
        ((halfTwistLoop 3 1).trans ((halfTwistLoop 3 0).trans
          (halfTwistLoop 3 0))).toContinuousMap :=
      ContinuousMap.ext (fun t => congrFun projB t)
    rw [eA, eB]
    exact hhom
  have hrel2 : (dC.comp ΓA.toContinuousMap).HomotopicRel (dC.comp ΓB.toContinuousMap) {0, 1} :=
    hrel.map (fun F => F.compContinuousMap dC)
  have h0A : (dC.comp ΓA.toContinuousMap) 0 = expS (Complex.log 2 + ↑Real.pi * Complex.I) := by
    have := congrFun liftA 0
    simp only [Function.comp_apply, Path.source] at this
    show dC (ΓA 0) = _
    rw [Path.source]
    exact this.symm
  have h0B : (dC.comp ΓB.toContinuousMap) 0 = expS (Complex.log 2 + ↑Real.pi * Complex.I) := by
    have := congrFun liftB 0
    simp only [Function.comp_apply, Path.source] at this
    show dC (ΓB 0) = _
    rw [Path.source]
    exact this.symm
  have eA2 : ΘA.toContinuousMap = cov2.liftPath (dC.comp ΓA.toContinuousMap) _ h0A :=
    (cov2.eq_liftPath_iff' _).mpr ⟨liftA, ΘA.source⟩
  have eB2 : ΘB.toContinuousMap = cov2.liftPath (dC.comp ΓB.toContinuousMap) _ h0B :=
    (cov2.eq_liftPath_iff' _).mpr ⟨liftB, ΘB.source⟩
  have key2 := cov2.liftPath_apply_one_eq_of_homotopicRel hrel2 _ h0A h0B
  rw [← eA2, ← eB2] at key2
  have e1 : ΘA.toContinuousMap 1 = ↑Real.pi * Complex.I := ΘA.target
  have e2 : ΘB.toContinuousMap 1 = 3 * ↑Real.pi * Complex.I := ΘB.target
  rw [e1, e2] at key2
  have := congrArg Complex.im key2
  simp at this <;> linarith [Real.pi_pos]

end

end P2Ma747

open P2Ma747 in
theorem solution : ¬ (∀ (n : Nat) (i : Fin (n + 1)),
    FreeGroup.lift (fun j : Fin (n + 2 - 1) => halfTwistBraid (n + 2) j)
      (braidWordFree (standardPureBraidWord (n + 1) i))
      = (halfTwistBraid (n + 2) i) ^ 2) := by
  intro h
  have h1 := h 1 0
  have hw : standardPureBraidWord (1+1) (0 : Fin (1+1)) =
    [⟨1, .positive⟩, ⟨0, .positive⟩, ⟨0, .positive⟩, ⟨1, .negative⟩] := by decide
  rw [hw] at h1
  simp only [braidWordFree, braidLetterFree, map_mul, map_inv, FreeGroup.lift_apply_of,
    mul_one] at h1
  have h1' : halfTwistBraid 3 1 * (halfTwistBraid 3 0 * (halfTwistBraid 3 0 *
      (halfTwistBraid 3 1)⁻¹)) = halfTwistBraid 3 0 ^ 2 := h1
  apply noncomm
  calc halfTwistBraid 3 1 * (halfTwistBraid 3 0 * halfTwistBraid 3 0)
      = (halfTwistBraid 3 1 * (halfTwistBraid 3 0 * (halfTwistBraid 3 0 *
          (halfTwistBraid 3 1)⁻¹))) * halfTwistBraid 3 1 := by group
    _ = halfTwistBraid 3 0 ^ 2 * halfTwistBraid 3 1 := by rw [h1']
    _ = (halfTwistBraid 3 0 * halfTwistBraid 3 0) * halfTwistBraid 3 1 := by rw [pow_two]
