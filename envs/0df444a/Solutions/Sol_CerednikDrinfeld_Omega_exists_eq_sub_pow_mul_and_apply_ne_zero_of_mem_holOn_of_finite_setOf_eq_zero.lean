-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7aad9f49-7b02-5f04-88d8-158a51609196

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_holOn_eq_sub_mul_of_apply_eq_zero
import Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero.CerednikDrinfeld.Omega Polynomial Filter"

noncomputable section
open Classical

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.exists_mem_holOn_eq_sub_mul_of_apply_eq_zero Omega.exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "RatPair RatPair.evalAt vRestrict v_lt_iff_vRestrict_lt tendstoUniformly_iff_vRestrict isHolOn_ratPair holOn mem_holOn_iff exists_mem_holOn_eq_sub_mul_of_apply_eq_zero exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset"
namespace F1Aux
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "𝓋" => (Valued.v (R := K))

theorem v_sub_comm (a b : K) : 𝓋 (a - b) = 𝓋 (b - a) := Valuation.map_sub_swap _ a b

theorem v_sub_le_max (a b c : K) : 𝓋 (a - c) ≤ max (𝓋 (a - b)) (𝓋 (b - c)) := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact Valuation.map_add _ _ _

theorem v_sub_eq_of_lt {a b c : K} (h : 𝓋 (a - b) < 𝓋 (b - c)) : 𝓋 (a - c) = 𝓋 (b - c) := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact Valuation.map_add_eq_of_lt_right _ h

section Generic
variable [IsAlgClosed K]

theorem exists_unit_generic (W : Finset K) : ∃ u : K, 𝓋 u = 1 ∧ ∀ w ∈ W, 1 ≤ 𝓋 (u - w) := by
  classical
  let W₁ := W.filter fun w => 𝓋 w = 1
  let p : K[X] := X * ∏ w ∈ W₁, (X - C w)
  have hmonic : p.Monic := monic_X.mul (monic_prod_of_monic _ _ fun w _ => monic_X_sub_C w)
  have hdegp : 0 < p.degree := by
    have : p.natDegree = 1 + W₁.card := by
      rw [show p = X * ∏ w ∈ W₁, (X - C w) from rfl, natDegree_mul X_ne_zero (monic_prod_of_monic _ _ fun w _ => monic_X_sub_C w).ne_zero,
        natDegree_X, natDegree_prod_of_monic _ _ fun w _ => monic_X_sub_C w]
      simp
    exact Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [this]; omega)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root (p - C 1) (by rw [degree_sub_C hdegp]; exact hdegp.ne')
  have hu' : u * ∏ w ∈ W₁, (u - w) = 1 := by
    have := hu
    rw [IsRoot, eval_sub, eval_C, sub_eq_zero, eval_mul, eval_X, eval_prod] at this
    simpa using this
  have hv : 𝓋 u * ∏ w ∈ W₁, 𝓋 (u - w) = 1 := by
    rw [← map_prod, ← Valuation.map_mul, hu', Valuation.map_one]

  have hvu : 𝓋 u = 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    ·
      have : ∏ w ∈ W₁, 𝓋 (u - w) = 1 := by
        refine Finset.prod_eq_one fun w hw => ?_
        have hw1 : 𝓋 w = 1 := (Finset.mem_filter.mp hw).2
        rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hw1]; exact hlt), hw1]
      rw [this, mul_one] at hv
      exact hne hv
    · have : ∀ w ∈ W₁, 𝓋 (u - w) = 𝓋 u := fun w hw => by
        have hw1 : 𝓋 w = 1 := (Finset.mem_filter.mp hw).2
        exact Valuation.map_sub_eq_of_lt_left _ (by rw [hw1]; exact hgt)
      rw [Finset.prod_congr rfl this, Finset.prod_const] at hv
      have h1 : (1 : Γ₀) < 𝓋 u * 𝓋 u ^ W₁.card :=
        lt_of_lt_of_le hgt (le_mul_of_one_le_right' (one_le_pow_of_one_le' hgt.le _))
      exact absurd hv h1.ne'
  refine ⟨u, hvu, fun w hw => ?_⟩
  rcases lt_trichotomy (𝓋 w) 1 with hlt | heq | hgt
  · rw [Valuation.map_sub_eq_of_lt_left _ (by rw [hvu]; exact hlt), hvu]
  ·
    have hwW : w ∈ W₁ := Finset.mem_filter.mpr ⟨hw, heq⟩
    have hle : ∀ x ∈ W₁, 𝓋 (u - x) ≤ 1 := fun x hx => by
      have hx1 : 𝓋 x = 1 := (Finset.mem_filter.mp hx).2
      calc 𝓋 (u - x) ≤ max (𝓋 u) (𝓋 x) := Valuation.map_sub _ _ _
        _ = 1 := by rw [hvu, hx1, max_self]
    rw [hvu, one_mul] at hv
    by_contra hlt
    push_neg at hlt
    have : ∏ x ∈ W₁, 𝓋 (u - x) < 1 := by
      rw [← Finset.mul_prod_erase _ _ hwW]
      calc 𝓋 (u - w) * ∏ x ∈ W₁.erase w, 𝓋 (u - x) ≤ 𝓋 (u - w) * 1 :=
            mul_le_mul_right (Finset.prod_le_one' fun x hx => hle x (Finset.mem_of_mem_erase hx)) _
        _ < 1 := by rw [mul_one]; exact hlt
    exact absurd hv this.ne
  · rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hvu]; exact hgt)]; exact hgt.le

theorem exists_generic (a s : K) (hs : s ≠ 0) (Z : Finset K) :
    ∃ z : K, 𝓋 (z - a) = 𝓋 s ∧ ∀ ζ ∈ Z, 𝓋 s ≤ 𝓋 (z - ζ) := by
  obtain ⟨u, hu, hgen⟩ := exists_unit_generic (K := K) (Z.image fun ζ => (ζ - a) / s)
  refine ⟨a + s * u, by rw [add_sub_cancel_left, Valuation.map_mul, hu, mul_one], fun ζ hζ => ?_⟩
  have h := hgen ((ζ - a) / s) (Finset.mem_image_of_mem _ hζ)
  have e : a + s * u - ζ = s * (u - (ζ - a) / s) := by field_simp; ring
  rw [e, Valuation.map_mul]
  exact le_mul_of_one_le_right' h

end Generic

theorem unif_eps {α : Type} {F : ℕ → α → K} {φ : α → K} (h : TendstoUniformly F φ atTop) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z, Valued.v (F k z - φ z) < Valued.v e := fun e he => by
  rw [tendstoUniformly_iff_vRestrict] at h
  have hwe : vRestrict K e ≠ 0 := by rwa [ne_eq, map_eq_zero]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h (Units.mk0 _ hwe))
  exact ⟨N, fun k hk z => (v_lt_iff_vRestrict_lt K _ _).2 (hN k hk z)⟩

end CerednikDrinfeld.Omega.F1Aux

end

open CerednikDrinfeld.Omega.F1Aux in
theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (hfin : Set.Finite {z : ↥S | f z = 0})
    (p : ↥S) (r : K) (hr : r ≠ 0) (hD : ∀ w : K, Valued.v (w - (p : K)) ≤ Valued.v r → w ∈ S) :
    ∃ (k : ℕ) (g : ↥S → K), g ∈ holOn K S ∧ g p ≠ 0 ∧
      ∀ z : ↥S, f z = ((z : K) - (p : K)) ^ k * g z := by
  classical
  by_cases hnt : ∃ y : K, y ≠ 0 ∧ Valued.v y < 1
  ·
    obtain ⟨y, hy0, hy1⟩ := hnt
    have hvy : 0 < Valued.v y := (Valuation.pos_iff _).mpr hy0
    have hvr0 : 0 < Valued.v r := zero_lt_iff.2 (by rwa [ne_eq, map_eq_zero])
    by_contra hcon

    have hall : ∀ k : ℕ, ∃ g : ↥S → K, g ∈ holOn K S ∧
        ∀ z : ↥S, f z = ((z : K) - (p : K)) ^ k * g z := by
      intro k
      induction k with
      | zero => exact ⟨f, hf, fun z => by rw [pow_zero, one_mul]⟩
      | succ k ih =>
        obtain ⟨g, hg, hfg⟩ := ih
        have hgp : g p = 0 := by
          by_contra hgp
          exact hcon ⟨k, g, hg, hgp, hfg⟩
        obtain ⟨g', hg', hgg'⟩ :=
          CerednikDrinfeld.Omega.exists_mem_holOn_eq_sub_mul_of_apply_eq_zero K hg p hgp r hr hD
        refine ⟨g', hg', fun z => ?_⟩
        rw [hfg z, hgg' z, pow_succ, mul_assoc]
    obtain ⟨B, hB⟩ := ((mem_holOn_iff f).1 hf).bounded

    have hzero : ∀ w : ↥S, Valued.v ((w : K) - (p : K)) < Valued.v r → f w = 0 := by
      intro w hw
      by_cases hwp : (w : K) = (p : K)
      · obtain ⟨g, -, hfg⟩ := hall 1
        have hw' : w = p := Subtype.ext hwp
        rw [hfg w, hw', sub_self, pow_one, zero_mul]
      · by_contra hfw

        have hest : ∀ m : ℕ, Valued.v (f w) ≤ (Valued.v ((w : K) - (p : K)) / Valued.v r) ^ m * Valued.v B := by
          intro m
          obtain ⟨g, hg, hfg⟩ := hall m

          have hcirc : ∀ y : ↥S, Valued.v ((y : K) - (p : K)) = Valued.v r →
              Valued.v (g y) ≤ Valued.v B / Valued.v r ^ m := by
            intro y hy
            rw [le_div_iff₀ (pow_pos hvr0 m), ← hy]
            calc Valued.v (g y) * Valued.v ((y : K) - (p : K)) ^ m = Valued.v (f y) := by
                  rw [hfg y, map_mul, map_pow, mul_comm]
              _ ≤ Valued.v B := hB y

          have hgw : Valued.v (g w) ≤ Valued.v B / Valued.v r ^ m := by
            obtain ⟨E, hE⟩ :=
              CerednikDrinfeld.Omega.exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset
                K S (p : K) r hr hD hg
            obtain ⟨z₀, hz₀, hgen⟩ := exists_generic (K := K) (p : K) r hr E
            have hgen' : ∀ e ∈ E, Valued.v r ≤ Valued.v (z₀ - e) := hgen
            have h1 := hE z₀ hz₀ hgen' (w : K) hw.le
            exact h1.trans (hcirc ⟨z₀, hD z₀ hz₀.le⟩ hz₀)
          calc Valued.v (f w) = Valued.v ((w : K) - (p : K)) ^ m * Valued.v (g w) := by
                rw [hfg w, map_mul, map_pow]
            _ ≤ Valued.v ((w : K) - (p : K)) ^ m * (Valued.v B / Valued.v r ^ m) := mul_le_mul_right hgw _
            _ = (Valued.v ((w : K) - (p : K)) / Valued.v r) ^ m * Valued.v B := by
                rw [div_pow, div_mul_eq_mul_div, ← mul_div_assoc]

        have hvFw : 0 < Valued.v (f w) := zero_lt_iff.2 (by rwa [ne_eq, map_eq_zero])
        have hvB : 0 < Valued.v B := lt_of_lt_of_le hvFw (hB w)
        have hB0 : B ≠ 0 := fun h => by rw [h, map_zero] at hvB; exact lt_irrefl _ hvB
        set x : K := ((w : K) - (p : K)) / r with hxdef
        have hx0 : x ≠ 0 := div_ne_zero (sub_ne_zero.2 hwp) hr
        have hvx : Valued.v x = Valued.v ((w : K) - (p : K)) / Valued.v r := map_div₀ _ _ _
        have hvx1 : Valued.v x < 1 := by rw [hvx, div_lt_one₀ hvr0]; exact hw
        obtain ⟨N, hN⟩ := hrk x (f w / B * x) hvx1 (mul_ne_zero (div_ne_zero hfw hB0) hx0)
        have h1 : Valued.v x ^ N < Valued.v (f w) / Valued.v B := by
          refine lt_of_le_of_lt hN ?_
          rw [map_mul, map_div₀]
          exact mul_lt_of_lt_one_right (div_pos hvFw hvB) hvx1
        have h2 : Valued.v x ^ N * Valued.v B < Valued.v (f w) := by
          rwa [lt_div_iff₀ hvB] at h1
        have h3 := hest N
        rw [← hvx] at h3
        exact absurd (lt_of_le_of_lt h3 h2) (lt_irrefl _)

    let wn : ℕ → K := fun n => (p : K) + r * y ^ (n + 1)
    have hwnS : ∀ n, wn n ∈ S := fun n => hD _ (by
      show Valued.v ((p : K) + r * y ^ (n + 1) - (p : K)) ≤ Valued.v r
      rw [add_sub_cancel_left, Valuation.map_mul, Valuation.map_pow]
      exact mul_le_of_le_one_right' (pow_le_one₀ zero_le' hy1.le))
    have hwnlt : ∀ n, Valued.v (wn n - (p : K)) < Valued.v r := fun n => by
      show Valued.v ((p : K) + r * y ^ (n + 1) - (p : K)) < Valued.v r
      rw [add_sub_cancel_left, Valuation.map_mul, Valuation.map_pow]
      have : Valued.v r * Valued.v y ^ (n + 1) < Valued.v r * 1 :=
        mul_lt_mul_of_pos_left (pow_lt_one₀ zero_le' hy1 (Nat.succ_ne_zero n)) hvr0
      rwa [mul_one] at this
    have hinj : Function.Injective (fun n => (⟨wn n, hwnS n⟩ : ↥S)) := by
      intro a b hab
      have h1 : wn a = wn b := congrArg Subtype.val hab
      have h2 : y ^ (a + 1) = y ^ (b + 1) := by
        have := h1; simp only [wn, add_right_inj] at this
        exact mul_left_cancel₀ hr this
      have h3 : Valued.v y ^ (a + 1) = Valued.v y ^ (b + 1) := by rw [← Valuation.map_pow, ← Valuation.map_pow, h2]
      have := (pow_right_strictAnti₀ hvy hy1).injective h3
      omega
    exact absurd (Set.infinite_of_injective_forall_mem hinj (fun n => hzero _ (hwnlt n))) hfin.not_infinite
  ·
    push_neg at hnt
    have hv1 : ∀ x : K, x ≠ 0 → Valued.v x = 1 := by
      intro x hx
      apply le_antisymm _ (hnt x hx)
      have h := hnt x⁻¹ (inv_ne_zero hx)
      rw [Valuation.map_inv, one_le_inv₀ ((Valuation.pos_iff _).mpr hx)] at h
      exact h
    have hvle : ∀ x : K, Valued.v x ≤ 1 := fun x => by
      by_cases hx : x = 0
      · rw [hx, Valuation.map_zero]; exact zero_le'
      · exact (hv1 x hx).le

    have hS : ∀ w : K, w ∈ S := fun w => hD w (by rw [hv1 r hr]; exact hvle _)

    obtain ⟨rs, hpf, -, hlim⟩ := hf
    obtain ⟨N, hN⟩ := unif_eps hlim 1 one_ne_zero
    have hfeq : ∀ z : ↥S, f z = (rs N).evalAt z := by
      intro z
      have h := hN N le_rfl z
      rw [Valuation.map_one] at h
      by_contra hne
      exact absurd (hv1 _ (sub_ne_zero.mpr (Ne.symm hne))) h.ne

    set den := (rs N).den with hden
    set num := (rs N).num with hnum
    have hden0 : ∀ w : K, den.eval w ≠ 0 := fun w => hpf N w (hS w)
    have hdegden : den.degree ≤ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨w, hw⟩ := IsAlgClosed.exists_root den h.ne'
      exact hden0 w hw
    have hdenC : den = C (den.coeff 0) := eq_C_of_degree_le_zero hdegden
    set c := den.coeff 0 with hc
    have hc0 : c ≠ 0 := fun h0 => hden0 0 (by rw [hdenC, h0, map_zero, eval_zero])

    have hnum0 : num ≠ 0 := by
      intro h0
      have hall : ∀ z : ↥S, f z = 0 := fun z => by
        rw [hfeq z, RatPair.evalAt, ← hnum, h0, eval_zero, zero_div]
      have : (Set.univ : Set ↥S).Infinite := by
        haveI : Infinite ↥S := Infinite.of_injective (fun w : K => (⟨w, hS w⟩ : ↥S)) (fun a b h => congrArg Subtype.val h)
        exact Set.infinite_univ
      exact absurd (this.mono (fun z _ => hall z)) hfin.not_infinite

    set k := num.rootMultiplicity (p : K) with hk
    set q := num /ₘ (X - C (p : K)) ^ k with hq
    have hnumq : (X - C (p : K)) ^ k * q = num := pow_mul_divByMonic_rootMultiplicity_eq num (p : K)
    have hqp : q.eval (p : K) ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero (p : K) hnum0
    let Q : RatPair K := ⟨q, C c⟩
    have hQpf : Q.IsPoleFreeOn S := fun w _ => by show (C c).eval w ≠ 0; rw [eval_C]; exact hc0
    refine ⟨k, fun z => Q.evalAt z, ?_, ?_, fun z => ?_⟩
    · exact isHolOn_ratPair Q hQpf ⟨1, fun w _ => by rw [Valuation.map_one]; exact hvle _⟩
    · show q.eval (p : K) / (C c).eval (p : K) ≠ 0
      rw [eval_C]; exact div_ne_zero hqp hc0
    · rw [hfeq z]
      show num.eval (z : K) / den.eval (z : K) = ((z : K) - (p : K)) ^ k * (q.eval (z : K) / (C c).eval (z : K))
      rw [hdenC, ← hnumq]
      simp only [eval_C, eval_mul, eval_pow, eval_sub, eval_X]
      ring

end S_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero (solution)
