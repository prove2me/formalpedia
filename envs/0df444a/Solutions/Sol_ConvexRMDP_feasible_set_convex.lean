-- Prove2me | solution 1 for ConvexRMDP.feasible_set_convex
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:47:45.830118+00:00
-- url     : https://prove2.me/submissions/43aec697-d533-48d1-b275-3332a421c860

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_tOp

namespace Aux_ConvexRMDP_fsc
open ConvexRMDP

theorem amgm_part {S : Type*} [Fintype S] (w : S → ℝ) (hw : ∀ s, 0 ≤ w s) (c : ℝ)
    (hc : c + ∑ s, w s = 1) (hc0 : 0 ≤ c) (a : ℝ) (ha : 0 < a) (x Z : S → ℝ)
    (hx : ∀ s, 0 < x s) (hZ : ∀ s, 0 < Z s) :
    a * (∏ s, x s ^ w s) / (∏ s, Z s ^ w s) ≤ c * a + ∑ s, w s * (a * x s / Z s) := by
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Option S))
    (fun o => o.elim c w) (fun o => o.elim a (fun s => a * x s / Z s))
    (by intro o _; cases o with
      | none => exact hc0
      | some s => exact hw s)
    (by rw [Fintype.sum_option]; simpa using hc)
    (by intro o _; cases o with
      | none => exact ha.le
      | some s => exact (div_pos (mul_pos ha (hx s)) (hZ s)).le)
  rw [Fintype.prod_option, Fintype.sum_option] at h
  simp only [Option.elim] at h
  have e : ∏ s, (a * x s / Z s) ^ w s = a ^ (∑ s, w s) * (∏ s, x s ^ w s) / ∏ s, Z s ^ w s := by
    rw [Real.rpow_sum_of_pos ha, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro s _
    rw [Real.div_rpow (mul_pos ha (hx s)).le (hZ s).le, Real.mul_rpow ha.le (hx s).le]
  rw [e, ← mul_div_assoc, ← mul_assoc, ← Real.rpow_add ha, hc, Real.rpow_one] at h
  exact h

theorem cobb {S : Type*} [Fintype S] (w : S → ℝ) (hw : ∀ s, 0 ≤ w s) (hsum : ∑ s, w s ≤ 1)
    (x y : S → ℝ) (hx : ∀ s, 0 < x s) (hy : ∀ s, 0 < y s) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    a * (∏ s, x s ^ w s) + b * (∏ s, y s ^ w s) ≤ ∏ s, (a * x s + b * y s) ^ w s := by
  rcases ha.eq_or_lt with ha0 | ha0
  · subst ha0
    have : b = 1 := by linarith
    subst this; simp
  rcases hb.eq_or_lt with hb0 | hb0
  · subst hb0
    have : a = 1 := by linarith
    subst this; simp
  set c := 1 - ∑ s, w s with hcdef
  have hc : c + ∑ s, w s = 1 := by rw [hcdef]; ring
  have hc0 : 0 ≤ c := by rw [hcdef]; linarith
  have hZ : ∀ s, 0 < a * x s + b * y s := fun s => by
    have := mul_pos ha0 (hx s); have := mul_pos hb0 (hy s); linarith
  have h1 := amgm_part w hw c hc hc0 a ha0 x (fun s => a * x s + b * y s) hx hZ
  have h2 := amgm_part w hw c hc hc0 b hb0 y (fun s => a * x s + b * y s) hy hZ
  have hP : 0 < ∏ s, (a * x s + b * y s) ^ w s :=
    Finset.prod_pos (fun s _ => Real.rpow_pos_of_pos (hZ s) _)
  have hsum2 : c * a + ∑ s, w s * (a * x s / (a * x s + b * y s)) +
      (c * b + ∑ s, w s * (b * y s / (a * x s + b * y s))) = 1 := by
    rw [← hc]
    have : ∑ s, w s * (a * x s / (a * x s + b * y s)) + ∑ s, w s * (b * y s / (a * x s + b * y s))
        = ∑ s, w s := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      have := (hZ s).ne'
      field_simp
    linear_combination c * hab + this
  have : (a * (∏ s, x s ^ w s) + b * (∏ s, y s ^ w s)) / ∏ s, (a * x s + b * y s) ^ w s ≤ 1 := by
    rw [add_div]; linarith
  rwa [div_le_one hP] at this

end Aux_ConvexRMDP_fsc

open ConvexRMDP Aux_ConvexRMDP_fsc in
theorem solution {S A : Type*} [Fintype S] [Fintype A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) :
    Convex ℝ {x : S → ℝ | ∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s} := by
  intro x hx y hy a c ha hc hac s
  have hxp : ∀ s, 0 < x s := fun s => by linarith [(hx s).1]
  have hyp : ∀ s, 0 < y s := fun s => by linarith [(hy s).1]
  have hz : (a • x + c • y) s = a * x s + c * y s := by simp
  have hzfun : (a • x + c • y) = fun s => a * x s + c * y s := by funext s; simp
  constructor
  · rw [hz]; nlinarith [(hx s).1, (hy s).1]
  · rw [hz]
    have hconc : a * M.tOp b x s + c * M.tOp b y s ≤ M.tOp b (a • x + c • y) s := by
      unfold RMDP.tOp
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a' _
      have hω : 0 ≤ M.omega b s a' := div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)
      have hlb : ∀ u : S → ℝ, (∀ s, 0 < u s) →
          BddBelow ((fun p : S → ℝ => ∏ s', u s' ^ (M.γ * p s')) '' M.U s a') := by
        intro u hu
        refine ⟨0, ?_⟩
        rintro _ ⟨q, _, rfl⟩
        exact Finset.prod_nonneg (fun s' _ => Real.rpow_nonneg (hu s').le _)
      have key : a * sInf ((fun p : S → ℝ => ∏ s', x s' ^ (M.γ * p s')) '' M.U s a') +
          c * sInf ((fun p : S → ℝ => ∏ s', y s' ^ (M.γ * p s')) '' M.U s a') ≤
          sInf ((fun p : S → ℝ => ∏ s', (a • x + c • y) s' ^ (M.γ * p s')) '' M.U s a') := by
        apply le_csInf ((M.U_nonempty s a').image _)
        rintro _ ⟨p, hp, rfl⟩
        have hpS := M.U_subset s a' hp
        have h1 := csInf_le (hlb x hxp) ⟨p, hp, rfl⟩
        have h2 := csInf_le (hlb y hyp) ⟨p, hp, rfl⟩
        have hcb := cobb (fun s' => M.γ * p s') (fun s' => mul_nonneg M.γ_pos.le (hpS.1 s'))
          (by rw [← Finset.mul_sum, hpS.2, mul_one]; exact M.γ_lt_one.le) x y hxp hyp a c ha hc hac
        rw [hzfun]
        simp only at h1 h2 ⊢
        nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hc]
      nlinarith [mul_le_mul_of_nonneg_left key hω]
    linarith [mul_le_mul_of_nonneg_left (hx s).2 ha, mul_le_mul_of_nonneg_left (hy s).2 hc, hconc]
