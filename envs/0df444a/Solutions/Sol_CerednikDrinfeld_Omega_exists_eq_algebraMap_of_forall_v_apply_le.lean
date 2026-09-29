-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_v_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/384658c5-2eaa-5f0e-b3a6-fb98f2ecaba4

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_CerednikDrinfeld_Omega_RatPair_v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_v_apply_le

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_v_apply_le.CerednikDrinfeld.Omega Filter"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.RatPair Omega.RatPair.v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane affinoid_mono IsExhausted RatPair vRestrict v_lt_iff_vRestrict_lt tendstoUniformly_iff_vRestrict restrictAffinoid holRing mem_holRing_iff algebraMap_holRing_apply upperHalfPlane RatPair.v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid"
namespace LiouvilleBdd
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem eventually_v_sub_lt {α : Type} {F : ℕ → α → K} {f : α → K} (h : TendstoUniformly F f atTop)
    (y : K) (hy : y ≠ 0) : ∀ᶠ k in atTop, ∀ z, Valued.v (F k z - f z) < Valued.v y := by
  rw [tendstoUniformly_iff_vRestrict] at h
  have hy' : vRestrict K y ≠ 0 := by rwa [ne_eq, map_eq_zero]
  filter_upwards [h (Units.mk0 _ hy')] with k hk z
  rw [v_lt_iff_vRestrict_lt]
  exact hk z

theorem eq_zero_of_forall_v_le_pow_mul
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (x : K) (hx0 : 0 < Valued.v x) (hx : Valued.v x < 1) (b y : K)
    (h : ∀ n : ℕ, Valued.v y ≤ Valued.v x ^ n * Valued.v b) : y = 0 := by
  by_contra hy
  by_cases hb : b = 0
  · rw [hb, map_zero] at h
    have := h 0
    rw [mul_zero, le_zero_iff, map_eq_zero] at this
    exact hy this
  · have hyb : y / b ≠ 0 := div_ne_zero hy hb
    obtain ⟨n, hn⟩ := hrk x (y / b) hx hyb
    have hb' : 0 < Valued.v b := (Valuation.pos_iff _).mpr hb
    rw [map_div₀, le_div_iff₀ hb'] at hn

    have h1 := hn.trans (h (n + 1))
    rw [pow_succ, mul_assoc, mul_comm (Valued.v x) (Valued.v b), ← mul_assoc] at h1
    have hpos : 0 < Valued.v x ^ n * Valued.v b := mul_pos (pow_pos hx0 n) hb'
    have := (le_mul_iff_one_le_right hpos).mp h1
    exact absurd (lt_of_lt_of_le hx this) (lt_irrefl _)

end CerednikDrinfeld.Omega.LiouvilleBdd

open CerednikDrinfeld.Omega.LiouvilleBdd in

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (f : ↥(holRing ϖ)) (b : K)
    (hb : ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ≤ Valued.v b) :
    ∃ c : K, f = algebraMap K ↥(holRing ϖ) c := by
  classical

  by_cases hΩ : IsEmpty ↥(upperHalfPlane K₀ K)
  · exact ⟨0, Subtype.ext (funext fun z => (hΩ.false z).elim)⟩
  rw [not_isEmpty_iff] at hΩ
  obtain ⟨z₀⟩ := hΩ
  refine ⟨(f : ↥(upperHalfPlane K₀ K) → K) z₀, Subtype.ext (funext fun z => ?_)⟩
  rw [algebraMap_holRing_apply]

  by_cases hb0 : b = 0
  · have h1 : (f : ↥(upperHalfPlane K₀ K) → K) z = 0 := by
      have := hb z; rwa [hb0, map_zero, le_zero_iff, map_eq_zero] at this
    have h2 : (f : ↥(upperHalfPlane K₀ K) → K) z₀ = 0 := by
      have := hb z₀; rwa [hb0, map_zero, le_zero_iff, map_eq_zero] at this
    rw [h1, h2]

  obtain ⟨n₁, hn₁⟩ := hex z z.2
  obtain ⟨n₂, hn₂⟩ := hex z₀ z₀.2
  set n := max n₁ n₂ with hn
  have hzn : (z : K) ∈ affinoid ϖ n := affinoid_mono ϖ (le_max_left _ _) hn₁
  have hz₀n : (z₀ : K) ∈ affinoid ϖ n := affinoid_mono ϖ (le_max_right _ _) hn₂

  have key : ∀ d : ℕ, Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z - (f : ↥(upperHalfPlane K₀ K) → K) z₀) ≤
      Valued.v (algebraMap K₀ K ϖ.ϖ) ^ d * Valued.v b := by
    intro d
    set m := n + d with hm
    have hzm : (z : K) ∈ affinoid ϖ m := affinoid_mono ϖ (Nat.le_add_right n d) hzn
    have hz₀m : (z₀ : K) ∈ affinoid ϖ m := affinoid_mono ϖ (Nat.le_add_right n d) hz₀n

    obtain ⟨r, hr, -, hlim⟩ := (mem_holRing_iff ϖ _).mp f.2 m

    have hϖ0 : algebraMap K₀ K ϖ.ϖ ≠ 0 := fun h => by have := ϖ.pos; rw [h, map_zero] at this; exact lt_irrefl _ this
    set y : K := algebraMap K₀ K ϖ.ϖ ^ d * b with hy
    have hy0 : y ≠ 0 := mul_ne_zero (pow_ne_zero _ hϖ0) hb0
    have hvy : Valued.v y = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ d * Valued.v b := by rw [hy, map_mul, map_pow]
    obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 ((eventually_v_sub_lt hlim y hy0).and (eventually_v_sub_lt hlim b hb0))
    obtain ⟨hk1, hk2⟩ := hk k le_rfl

    have hbd : ∀ w : K, w ∈ affinoid ϖ m → Valued.v ((r k).evalAt w) ≤ Valued.v b := by
      intro w hw
      have h1 := hk2 ⟨w, hw⟩
      have h2 := hb ⟨w, affinoid_subset_upperHalfPlane ϖ m hw⟩
      have : (r k).evalAt w = ((r k).evalAt w - restrictAffinoid ϖ m (f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hw⟩) +
          (f : ↥(upperHalfPlane K₀ K) → K) ⟨w, affinoid_subset_upperHalfPlane ϖ m hw⟩ := by
        simp [restrictAffinoid]
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le h1.le h2)

    have hosc := CerednikDrinfeld.Omega.RatPair.v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid K₀ K ϖ n m
      (Nat.le_add_right n d) (hfin m) (r k) (hr k) b hbd hzn hz₀n
    rw [show m - n = d by omega] at hosc

    have e1 := hk1 ⟨z, hzm⟩
    have e2 := hk1 ⟨z₀, hz₀m⟩
    simp only [restrictAffinoid, Function.comp_apply] at e1 e2
    have : (f : ↥(upperHalfPlane K₀ K) → K) z - (f : ↥(upperHalfPlane K₀ K) → K) z₀ =
        ((r k).evalAt z - (r k).evalAt z₀) - ((r k).evalAt z - (f : ↥(upperHalfPlane K₀ K) → K) z) +
          ((r k).evalAt z₀ - (f : ↥(upperHalfPlane K₀ K) → K) z₀) := by ring
    rw [this]
    refine (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_sub _ _ _).trans (max_le hosc ?_)) ?_)
    · rw [← hvy]; exact le_of_lt (by
        convert e1 using 2)
    · rw [← hvy]; exact le_of_lt (by
        convert e2 using 2)

  have := eq_zero_of_forall_v_le_pow_mul hrk (algebraMap K₀ K ϖ.ϖ) ϖ.pos ϖ.lt_one b _ key
  exact sub_eq_zero.mp this

end S_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_v_apply_le
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_v_apply_le (solution)
