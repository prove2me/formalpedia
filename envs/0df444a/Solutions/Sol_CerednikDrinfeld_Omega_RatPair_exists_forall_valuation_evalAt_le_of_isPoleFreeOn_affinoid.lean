-- Prove2me | solution 1 for CerednikDrinfeld.Omega.RatPair.exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7c97a8f4-c360-5474-a0f8-000188295a83

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_RatPair_exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_RatPair_exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid.CerednikDrinfeld.Omega Polynomial"

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid RatPair RatPair.evalAt"
namespace OmegaBDD
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ K : Type} [Field K₀] [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

local notation "𝔭" => Valued.v (algebraMap K₀ K ϖ.ϖ)

theorem p_le_one : 𝔭 ≤ 1 := ϖ.lt_one.le
theorem one_le_P : 1 ≤ 𝔭⁻¹ := (one_le_inv₀ ϖ.pos).2 (p_le_one ϖ)

theorem pow_le_v_sub_of_not_mem {n : ℕ} {a z : K} (ha : a ∉ affinoid ϖ n) (hz : z ∈ affinoid ϖ n) :
    𝔭 ^ n ≤ Valued.v (z - a) := by
  obtain ⟨hz₁, hz₂⟩ := hz
  by_cases hva : Valued.v a ≤ 𝔭⁻¹ ^ n
  ·
    have : ¬ ∀ t : K₀, Valued.v (algebraMap K₀ K t) ≤ 𝔭⁻¹ ^ n → 𝔭 ^ n ≤ Valued.v (a - algebraMap K₀ K t) :=
      fun h => ha ⟨hva, h⟩
    simp only [not_forall, not_le, exists_prop] at this
    obtain ⟨t, ht, hat⟩ := this
    have hzt : 𝔭 ^ n ≤ Valued.v (z - algebraMap K₀ K t) := hz₂ t ht
    have hlt : Valued.v (-(a - algebraMap K₀ K t)) < Valued.v (z - algebraMap K₀ K t) := by
      rw [Valuation.map_neg]; exact hat.trans_le hzt
    have : z - a = (z - algebraMap K₀ K t) + -(a - algebraMap K₀ K t) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ hlt]
    exact hzt
  ·
    have hva' : 𝔭⁻¹ ^ n < Valued.v a := not_le.1 hva
    have hlt : Valued.v z < Valued.v (-a) := by rw [Valuation.map_neg]; exact hz₁.trans_lt hva'
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ hlt, Valuation.map_neg]
    exact (pow_le_one₀ zero_le' (p_le_one ϖ)).trans ((one_le_pow₀ (one_le_P ϖ)).trans hva'.le)

noncomputable def bnd (n : ℕ) (c : K) : K :=
  if Valued.v c ≤ 𝔭⁻¹ ^ n then ((algebraMap K₀ K ϖ.ϖ)⁻¹) ^ n else c

theorem v_inv_pow (n : ℕ) : Valued.v (((algebraMap K₀ K ϖ.ϖ)⁻¹) ^ n) = 𝔭⁻¹ ^ n := by
  rw [map_pow, map_inv₀]

theorem v_sub_le_v_bnd {n : ℕ} {z : K} (hz : z ∈ affinoid ϖ n) (c : K) :
    Valued.v (z - c) ≤ Valued.v (bnd ϖ n c) := by
  refine (Valuation.map_sub _ _ _).trans ?_
  unfold bnd
  split_ifs with h
  · rw [v_inv_pow]; exact max_le hz.1 h
  · exact max_le (hz.1.trans (not_le.1 h).le) le_rfl

theorem v_eval_eq [IsAlgClosed K] (p : K[X]) (z : K) :
    Valued.v (p.eval z) = Valued.v p.leadingCoeff * (p.roots.map fun a => Valued.v (z - a)).prod := by
  conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots]
  rw [eval_mul, eval_C, Valuation.map_mul, eval_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  congr 1
  exact Multiset.map_congr rfl fun a _ => by
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]

theorem main [IsAlgClosed K] (n : ℕ) (r : RatPair K) (hr : r.IsPoleFreeOn (affinoid ϖ n)) :
    ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v (r.evalAt z) ≤ Valued.v b := by
  by_cases hne : (affinoid ϖ n : Set K).Nonempty
  swap
  · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hne⟩
  obtain ⟨z₀, hz₀⟩ := hne
  have hq0 : r.den ≠ 0 := fun h => hr z₀ hz₀ (by rw [h, eval_zero])
  have hlq : r.den.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hq0
  have hϖ0 : (algebraMap K₀ K ϖ.ϖ) ≠ 0 := fun h => ϖ.pos.ne' (by rw [h, map_zero])

  have hroot : ∀ a ∈ r.den.roots, a ∉ affinoid ϖ n := fun a ha hmem =>
    hr a hmem ((mem_roots hq0).1 ha)
  set m := r.den.roots.card with hm

  refine ⟨r.num.leadingCoeff * (r.num.roots.map (bnd ϖ n)).prod /
      (r.den.leadingCoeff * (algebraMap K₀ K ϖ.ϖ) ^ (n * m)), fun z hz => ?_⟩
  have hden_lo : Valued.v (r.den.leadingCoeff * (algebraMap K₀ K ϖ.ϖ) ^ (n * m)) ≤ Valued.v (r.den.eval z) := by
    rw [Valuation.map_mul, map_pow, v_eval_eq]
    refine mul_le_mul_right ?_ _
    have : 𝔭 ^ (n * m) = (r.den.roots.map fun _ => 𝔭 ^ n).prod := by
      rw [Multiset.prod_map_pow, Multiset.map_const', Multiset.prod_replicate, ← pow_mul, mul_comm]
    rw [this]
    exact Multiset.prod_map_le_prod_map _ _ fun a ha => pow_le_v_sub_of_not_mem ϖ (hroot a ha) hz
  have hnum_up : Valued.v (r.num.eval z) ≤ Valued.v (r.num.leadingCoeff * (r.num.roots.map (bnd ϖ n)).prod) := by
    rw [Valuation.map_mul, map_multiset_prod, Multiset.map_map, v_eval_eq]
    refine mul_le_mul_right ?_ _
    exact Multiset.prod_map_le_prod_map _ _ fun a _ => v_sub_le_v_bnd ϖ hz a
  have hpos : 0 < Valued.v (r.den.leadingCoeff * (algebraMap K₀ K ϖ.ϖ) ^ (n * m)) := by
    rw [Valuation.map_mul, map_pow]
    exact mul_pos ((Valuation.pos_iff _).2 hlq) (pow_pos ϖ.pos _)
  rw [RatPair.evalAt, map_div₀, map_div₀, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul' hnum_up (inv_anti₀ hpos hden_lo)

end CerednikDrinfeld.Omega.OmegaBDD

theorem solution
    {K₀ K : Type} [Field K₀] [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (n : ℕ) (r : RatPair K) (hr : r.IsPoleFreeOn (affinoid ϖ n)) :
    ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v (r.evalAt z) ≤ Valued.v b :=
  CerednikDrinfeld.Omega.OmegaBDD.main ϖ n r hr

end S_CerednikDrinfeld_Omega_RatPair_exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_RatPair_exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid (solution)
