-- Prove2me | solution 1 for CerednikDrinfeld.Omega.inv_mem_holOn_of_forall_le_v_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9cc2f507-e00c-5079-984e-5de749b72196

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_inv_mem_holOn_of_forall_le_v_apply

set_option autoImplicit false
set_option linter.unusedVariables false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_inv_mem_holOn_of_forall_le_v_apply.CerednikDrinfeld.Omega Filter"

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "RatPair RatPair.evalAt RatPair.const RatPair.isPoleFreeOn_const RatPair.evalAt_const vRestrict v_le_iff_vRestrict_le v_lt_iff_vRestrict_lt tendstoUniformly_iff_vRestrict IsHolOn holOn"
namespace InvHol
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

def inv (r : RatPair K) : RatPair K := ⟨r.den, r.num⟩

theorem inv_evalAt (r : RatPair K) (z : K) : (inv r).evalAt z = (r.evalAt z)⁻¹ := by
  simp [inv, RatPair.evalAt, inv_div]

theorem inv_den (r : RatPair K) : (inv r).den = r.num := rfl

theorem eventually_v_sub_lt {α : Type} {F : ℕ → α → K} {f : α → K} (h : TendstoUniformly F f atTop)
    (y : K) (hy : y ≠ 0) : ∀ᶠ k in atTop, ∀ z, Valued.v (F k z - f z) < Valued.v y := by
  rw [tendstoUniformly_iff_vRestrict] at h
  have hy' : vRestrict K y ≠ 0 := by rwa [ne_eq, map_eq_zero]
  filter_upwards [h (Units.mk0 _ hy')] with k hk z
  rw [v_lt_iff_vRestrict_lt]
  exact hk z

theorem v_add_eq_of_lt {x e : K} (h : Valued.v e < Valued.v x) : Valued.v (x + e) = Valued.v x :=
  Valuation.map_add_eq_of_lt_left _ h

end CerednikDrinfeld.Omega.InvHol

open CerednikDrinfeld.Omega.InvHol in
theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (S : Set K) {g : ↥S → K} (hg : g ∈ holOn K S)
    (δ : K) (hδ : δ ≠ 0) (hb : ∀ z : ↥S, Valued.v δ ≤ Valued.v (g z)) :
    (fun z : ↥S => (g z)⁻¹) ∈ holOn K S := by
  classical
  have hg' : IsHolOn K S g := hg
  obtain ⟨r, hr, -, hlim⟩ := hg'
  have hδv : 0 < Valued.v δ := (Valuation.pos_iff _).mpr hδ

  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (eventually_v_sub_lt hlim δ hδ)
  have hval : ∀ k, N ≤ k → ∀ z : ↥S, Valued.v ((r k).evalAt z) = Valued.v (g z) := by
    intro k hk z
    have h1 := hN k hk z
    have e : (r k).evalAt z = g z + ((r k).evalAt z - g z) := by ring
    rw [e]
    exact v_add_eq_of_lt (lt_of_lt_of_le h1 (hb z))
  have hne_r : ∀ k, N ≤ k → ∀ z : ↥S, (r k).evalAt z ≠ 0 := by
    intro k hk z h0
    have := hval k hk z
    rw [h0, map_zero] at this
    exact absurd (this ▸ hδv.trans_le (hb z)) (lt_irrefl _)
  have hne_g : ∀ z : ↥S, g z ≠ 0 := fun z h0 => by
    have := hb z; rw [h0, map_zero, le_zero_iff] at this; exact hδv.ne' this

  refine ⟨fun k => if N ≤ k then inv (r k) else RatPair.const δ⁻¹, fun k => ?_, ⟨δ⁻¹, fun k z => ?_⟩, ?_⟩
  ·
    by_cases hk : N ≤ k
    · simp only [if_pos hk]
      intro z hz h0
      apply hne_r k hk ⟨z, hz⟩
      show (r k).num.eval z / (r k).den.eval z = 0
      rw [show (r k).num.eval z = 0 from h0, zero_div]
    · simp only [if_neg hk]; exact RatPair.isPoleFreeOn_const S δ⁻¹
  ·
    by_cases hk : N ≤ k
    · simp only [if_pos hk]
      rw [inv_evalAt, map_inv₀, map_inv₀]
      exact (inv_le_inv₀ (lt_of_lt_of_le hδv ((hb z).trans (hval k hk z).symm.le)) hδv).2
        ((hb z).trans (hval k hk z).symm.le)
    · simp only [if_neg hk]
      rw [RatPair.evalAt_const]
  ·
    rw [tendstoUniformly_iff_vRestrict] at hlim ⊢
    intro γ
    have hδ' : vRestrict K δ ≠ 0 := by rwa [ne_eq, map_eq_zero]
    set d : (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v (R := K))))ˣ := Units.mk0 _ hδ' with hd
    filter_upwards [hlim (γ * d * d), Filter.eventually_ge_atTop N] with k hk hkN z
    rw [if_pos hkN, inv_evalAt]
    have hr0 := hne_r k hkN z
    have hg0 := hne_g z
    have e : ((r k).evalAt z)⁻¹ - (g z)⁻¹ = (g z - (r k).evalAt z) / ((r k).evalAt z * g z) := by
      field_simp
    rw [e, map_div₀, map_mul]

    have hbz : (d : MonoidWithZeroHom.ValueGroup₀ _) ≤ vRestrict K (g z) := by
      rw [hd, Units.val_mk0]; exact (v_le_iff_vRestrict_le K _ _).1 (hb z)
    have hbr : (d : MonoidWithZeroHom.ValueGroup₀ _) ≤ vRestrict K ((r k).evalAt z) := by
      rw [hd, Units.val_mk0]; exact (v_le_iff_vRestrict_le K _ _).1 ((hb z).trans (hval k hkN z).symm.le)
    have hpos : 0 < vRestrict K ((r k).evalAt z) * vRestrict K (g z) :=
      mul_pos ((Valuation.pos_iff _).mpr hr0) ((Valuation.pos_iff _).mpr hg0)
    rw [div_lt_iff₀ hpos, Valuation.map_sub_swap]
    refine lt_of_lt_of_le (hk z) ?_
    rw [Units.val_mul, Units.val_mul, mul_assoc]
    exact mul_le_mul_right (mul_le_mul' hbr hbz) _

end S_CerednikDrinfeld_Omega_inv_mem_holOn_of_forall_le_v_apply
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_inv_mem_holOn_of_forall_le_v_apply (solution)
