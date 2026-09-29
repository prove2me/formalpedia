-- Prove2me | solution 1 for CerednikDrinfeld.Omega.v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/732b049c-f840-5a9f-9cf8-62a6902bb124

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_CerednikDrinfeld_Omega_v_sub_eq_max_of_mem_affinoid_zero_of_not_mem
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one

set_option autoImplicit false

open scoped MatrixGroups
open Filter CerednikDrinfeld.Omega Polynomial

namespace Law3U1

theorem v_eval_eq {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [IsAlgClosed K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ₁ : PseudoUniformizer K₀ K) (p : K[X]) (hp : ∀ w ∈ affinoid ϖ₁ 0, p.eval w ≠ 0)
    {z z' : K} (hz : z ∈ affinoid ϖ₁ 0) (hz' : z' ∈ affinoid ϖ₁ 0) :
    Valued.v (p.eval z) = Valued.v (p.eval z') := by
  classical
  have hsplit := IsAlgClosed.splits p
  conv_lhs => rw [Polynomial.Splits.eq_prod_roots hsplit]
  conv_rhs => rw [Polynomial.Splits.eq_prod_roots hsplit]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod, Multiset.map_map,
    Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, map_mul, map_multiset_prod]
  congr 1
  refine congrArg _ (Multiset.map_congr rfl fun a ha => ?_)
  have haroot : p.eval a = 0 := by
    rw [Polynomial.mem_roots'] at ha; exact ha.2
  have hna : a ∉ affinoid ϖ₁ 0 := fun h => hp a h haroot
  rw [v_sub_eq_max_of_mem_affinoid_zero_of_not_mem ϖ₁ hz hna,
    v_sub_eq_max_of_mem_affinoid_zero_of_not_mem ϖ₁ hz' hna]

end Law3U1

theorem solution
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K] [IsAlgClosed K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ₁ : PseudoUniformizer K₀ K)
    {f g : ↥(affinoid ϖ₁ 0) → K} (hf : f ∈ holOn K (affinoid ϖ₁ 0)) (hg : g ∈ holOn K (affinoid ϖ₁ 0))
    (hfg : f * g = 1) (z z' : ↥(affinoid ϖ₁ 0)) :
    Valued.v (f z) = Valued.v (f z') := by
  classical

  have hfg' : ∀ w : ↥(affinoid ϖ₁ 0), f w * g w = 1 := fun w => by
    have := congrFun hfg w; simpa using this
  have hf0 : ∀ w : ↥(affinoid ϖ₁ 0), f w ≠ 0 := fun w h => by
    have := hfg' w; rw [h, zero_mul] at this; exact zero_ne_one this

  obtain ⟨B, hB⟩ := IsHolOn.bounded (show IsHolOn K (affinoid ϖ₁ 0) g from hg)
  have hB0 : B ≠ 0 := by
    intro h
    have := hB z
    rw [h, map_zero, le_zero_iff, Valuation.zero_iff] at this
    have := hfg' z; rw [‹g z = 0›, mul_zero] at this; exact zero_ne_one this
  have hlow : ∀ w : ↥(affinoid ϖ₁ 0), Valued.v B⁻¹ ≤ Valued.v (f w) := by
    intro w
    have h1 : Valued.v (f w) * Valued.v (g w) = 1 := by rw [← Valuation.map_mul, hfg' w, Valuation.map_one]
    have hg0 : Valued.v (g w) ≠ 0 := fun h => by rw [h, mul_zero] at h1; exact zero_ne_one h1
    rw [Valuation.map_inv]
    calc (Valued.v B)⁻¹ ≤ (Valued.v (g w))⁻¹ := inv_anti₀ (zero_lt_iff.2 hg0) (hB w)
      _ = (Valued.v (f w) * Valued.v (g w)) * (Valued.v (g w))⁻¹ := by rw [h1, one_mul]
      _ = Valued.v (f w) := by rw [mul_assoc, mul_inv_cancel₀ hg0, mul_one]

  obtain ⟨r, hr, -, hlim⟩ := (show IsHolOn K (affinoid ϖ₁ 0) f from hf)
  rw [tendstoUniformly_iff_vRestrict] at hlim
  have hγ0 : vRestrict K B⁻¹ ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; exact inv_ne_zero hB0
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 (hlim (Units.mk0 _ hγ0))
  have hclose : ∀ w : ↥(affinoid ϖ₁ 0), Valued.v ((r k).evalAt w - f w) < Valued.v (f w) := by
    intro w
    have := hk k le_rfl w
    rw [Units.val_mk0, ← v_lt_iff_vRestrict_lt] at this
    exact this.trans_le (hlow w)
  have hval : ∀ w : ↥(affinoid ϖ₁ 0), Valued.v ((r k).evalAt w) = Valued.v (f w) := by
    intro w
    have : (r k).evalAt w = ((r k).evalAt w - f w) + f w := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (hclose w)]

  have hden : ∀ w ∈ affinoid ϖ₁ 0, (r k).den.eval w ≠ 0 := hr k
  have hnum : ∀ w ∈ affinoid ϖ₁ 0, (r k).num.eval w ≠ 0 := by
    intro w hw h0
    have := hval ⟨w, hw⟩
    rw [RatPair.evalAt, h0, zero_div, map_zero] at this
    exact hf0 ⟨w, hw⟩ ((Valuation.zero_iff _).1 this.symm)
  rw [← hval z, ← hval z', RatPair.evalAt, RatPair.evalAt, map_div₀, map_div₀,
    Law3U1.v_eval_eq ϖ₁ _ hnum z.2 z'.2, Law3U1.v_eval_eq ϖ₁ _ hden z.2 z'.2]

end S_CerednikDrinfeld_Omega_v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one (solution)
