-- Prove2me | solution 1 for GRH.moebius_square_residual_iff_reduced_residue_bias
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T11:55:34.757936+00:00
-- url     : https://prove2.me/submissions/f3f12e12-89a7-45e7-af52-f5f3b228ef42

import Theorems.Thm_GRH_reduced_moebius_principal_bounds_of_dirichlet_prefixes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/- The square-root weight estimates are adapted from the proof at
https://prove2.me/submissions/0176d409-98bf-44bc-b6fe-85633680ae6d . -/
open scoped BigOperators

namespace GRH

lemma sqrt_rpow_weight_bound (N : ℕ) (σ : ℝ) (hone : σ < 1) :
    (N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 ≤ ((N : ℝ) + 1) ^ σ := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hU : 0 < (N.sqrt : ℝ) + 1 := by positivity
  have hX : 0 < (N : ℝ) + 1 := by positivity
  have hsqrt : (N : ℝ) + 1 ≤ ((N.sqrt : ℝ) + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' N
    have h' : N + 1 ≤ (N.sqrt + 1) ^ 2 := by simpa [Nat.succ_eq_add_one] using Nat.succ_le_iff.mpr h
    exact_mod_cast h'
  have hp : (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 ≤
      ((N : ℝ) + 1) ^ (σ - 1) := by
    have h := Real.rpow_le_rpow_of_nonpos hX hsqrt (by linarith : σ - 1 ≤ 0)
    rw [← Real.rpow_natCast_mul hU.le] at h
    rw [← Real.rpow_mul_natCast hU.le]
    convert h using 1
    congr 1
    ring
  calc
    (N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2
        ≤ (N : ℝ) * (((N : ℝ) + 1) ^ (σ - 1)) := mul_le_mul_of_nonneg_left hp hN
    _ ≤ ((N : ℝ) + 1) * (((N : ℝ) + 1) ^ (σ - 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hX.le _)
    _ = ((N : ℝ) + 1) ^ σ := by
      nth_rw 1 [← Real.rpow_one ((N : ℝ) + 1)]
      rw [← Real.rpow_add hX]
      congr 1
      ring

lemma harmonic_main_weight_bound (N : ℕ) (σ K x : ℝ) (hone : σ < 1)
    (hK : 0 ≤ K) (hx : |x| ≤ K * ((N.sqrt : ℝ) + 1) ^ (σ - 1)) :
    (N : ℝ) * x ^ 2 ≤ K ^ 2 * ((N : ℝ) + 1) ^ σ := by
  have hs : x ^ 2 ≤ K ^ 2 * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 := by
    have h := sq_le_sq₀ (abs_nonneg x) (by positivity : 0 ≤ K * ((N.sqrt : ℝ) + 1) ^ (σ - 1))
    have := h.mpr hx
    simpa only [sq_abs, mul_pow] using this
  calc
    (N : ℝ) * x ^ 2 ≤ (N : ℝ) *
        (K ^ 2 * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N)
    _ = K ^ 2 * ((N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2) := by ring
    _ ≤ K ^ 2 * ((N : ℝ) + 1) ^ σ :=
      mul_le_mul_of_nonneg_left (sqrt_rpow_weight_bound N σ hone) (sq_nonneg K)

end GRH



theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ B : ℝ)
    (hhalf : (1/2 : ℝ) < σ) (hone : σ < 1) (hB : 0 ≤ B)
    (hprefix : ∀ n : ℕ, |∑ j ∈ Finset.range n,
      (ArithmeticFunction.moebius j : ℝ) * (j : ℝ) ^ (-σ)| ≤ B) :
    (∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) +
        (u : ℝ) ^ 2 * ((1 / (q : ℝ)) * (GRH.reducedMoebiusHarmonic q u) ^ 2)| ≤
      D * ((u : ℝ) ^ 2 + 1) ^ σ) ↔
    (q.totient = 1 ∨ ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) - (∑ k ∈ Finset.range (u ^ 2 + 1),
          if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0) / (q.totient : ℝ)| ≤ D * ((u : ℝ) ^ 2 + 1) ^ σ) := by
  classical
  obtain ⟨K,hK,hH,hP⟩ := GRH.reduced_moebius_principal_bounds_of_dirichlet_prefixes
    q σ B hhalf hone hB hprefix
  let A := fun u : ℕ => ∑ k ∈ Finset.range (u^2+1),
    if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0
  let P := fun u : ℕ => ∑ k ∈ Finset.range (u^2+1),
    if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0
  let T := fun u : ℕ => (u:ℝ)^2*((1/(q:ℝ))*(GRH.reducedMoebiusHarmonic q u)^2)
  let g := fun u : ℕ => ((u:ℝ)^2+1)^σ
  let L := 3*K+K^2
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hφn := Nat.totient_pos.mpr (NeZero.pos q)
  have hφ : (1:ℝ) ≤ q.totient := by exact_mod_cast hφn
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hcommon (u : ℕ) : |P u/(q.totient:ℝ)+T u| ≤ L*g u := by
    have hp : |P u| ≤ (3*K)*g u := by
      have pp := hP (u*u)
      change |∑ k ∈ Finset.range (u*u+1), (if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0)| ≤ (3*K)*(((u*u:ℕ):ℝ)+1)^σ at pp
      rw [Nat.cast_mul] at pp
      simpa only [P,g,pow_two] using pp
    have hp' : |P u/(q.totient:ℝ)| ≤ (3*K)*g u := by
      rw [abs_div,abs_of_nonneg (Nat.cast_nonneg q.totient : 0 ≤ (q.totient:ℝ))]
      exact (div_le_self (abs_nonneg _) hφ).trans hp
    have hh := GRH.harmonic_main_weight_bound (u^2) σ K (GRH.reducedMoebiusHarmonic q u)
      hone hK (by simpa only [Nat.sqrt_eq' u] using hH u)
    simp only [Nat.cast_pow (α := ℝ) u 2] at hh
    have hq' : 1/(q:ℝ) ≤ 1 := div_le_self zero_le_one hq
    have hprod : 0 ≤ (u:ℝ)^2*(GRH.reducedMoebiusHarmonic q u)^2 := by positivity
    have ht : |T u| ≤ K^2*g u := by
      have ht0 : 0 ≤ T u := by dsimp [T]; positivity
      rw [abs_of_nonneg ht0]
      calc
        T u = (1/(q:ℝ))*((u:ℝ)^2*(GRH.reducedMoebiusHarmonic q u)^2) := by dsimp only [T]; ring
        _ ≤ 1*((u:ℝ)^2*(GRH.reducedMoebiusHarmonic q u)^2) := mul_le_mul_of_nonneg_right hq' hprod
        _ ≤ K^2*g u := by simpa only [one_mul,g] using hh
    exact (abs_add_le _ _).trans ((add_le_add hp' ht).trans_eq (by dsimp only [L]; ring))
  change (∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ, |A u+T u| ≤ D*g u) ↔
    q.totient = 1 ∨ ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ, |A u-P u/(q.totient:ℝ)| ≤ D*g u
  constructor
  · rintro ⟨D,hD,h⟩
    right
    refine ⟨D+L,add_nonneg hD hL, fun u => ?_⟩
    calc
      _ = |(A u+T u) - (P u/(q.totient:ℝ)+T u)| := by ring_nf
      _ ≤ |A u+T u|+|P u/(q.totient:ℝ)+T u| := abs_sub _ _
      _ ≤ D*g u+L*g u := add_le_add (h u) (hcommon u)
      _ = _ := (add_mul ..).symm
  · intro rhs
    have hbias : ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ, |A u-P u/(q.totient:ℝ)| ≤ D*g u := by
      rcases rhs with hcard | h
      · have single : ∀ x y : (ZMod q)ˣ, x = y :=
          Fintype.card_le_one_iff.mp (by rw [ZMod.card_units_eq_totient, hcard])
        have iff_unit (x : ZMod q) : x = a ↔ IsUnit x := by
          refine ⟨fun h => h ▸ ha, fun hx => ?_⟩
          simpa using congrArg (fun v : (ZMod q)ˣ => (v : ZMod q)) (single hx.unit ha.unit)
        have equal (u : ℕ) : A u = P u := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : (k : ZMod q) = a
          · simp only [if_pos hk, if_pos ((iff_unit _).mp hk)]
          · simp only [if_neg hk, if_neg (fun h => hk ((iff_unit _).mpr h))]
        exact ⟨0,le_rfl,fun u => by simp only [equal u,hcard,Nat.cast_one,div_one,sub_self,abs_zero,zero_mul,le_refl]⟩
      · exact h
    obtain ⟨D,hD,h⟩ := hbias
    refine ⟨D+L,add_nonneg hD hL,fun u => ?_⟩
    calc
      _ = |(A u-P u/(q.totient:ℝ))+(P u/(q.totient:ℝ)+T u)| := by ring_nf
      _ ≤ |A u-P u/(q.totient:ℝ)|+|P u/(q.totient:ℝ)+T u| := abs_add_le _ _
      _ ≤ D*g u+L*g u := add_le_add (h u) (hcommon u)
      _ = _ := (add_mul ..).symm
