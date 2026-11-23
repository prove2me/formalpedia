-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_BoxSumLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:01.419552+00:00
-- url     : https://prove2.me/submissions/eddc7388-341c-40ab-9952-ce5c0a7727ad

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : BoxSumLattice := by
  intro hB
  obtain ⟨C0, hC0⟩ := hB
  refine ⟨|C0| + 1, by have := abs_nonneg C0; linarith, ?_⟩
  intro E _ _ _ aa L x K Θ a haa hL hx hK ha hΘ hprod
  have hf1 : 0 < Fintype.card (InfinitePlace E) := Fintype.card_pos
  have hΘ0 : 0 < Θ := by linarith
  have ha0 : 0 < a := by linarith
  have hK3 : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hp : 0 < (K : ℝ) - 5 / 2 := by linarith
  refine ⟨fun l => Finset.prod_nonneg fun w _ =>
    le_min zero_le_one (pow_nonneg (div_nonneg (hx w) (apply_nonneg w l)) K), ?_⟩
  intro S hS
  have hRHS : 0 ≤ ((|C0| + 1) * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^
      Fintype.card (InfinitePlace E) := by positivity
  by_cases hx0 : ∃ w, x w = 0
  · obtain ⟨w0, hw0⟩ := hx0
    have h0 : ∀ l ∈ S, prof x K l = 0 := by
      intro l _
      unfold prof
      apply Finset.prod_eq_zero (Finset.mem_univ w0)
      rw [hw0, zero_div, zero_pow (by omega)]; simp
    rw [Finset.sum_eq_zero h0]; exact hRHS
  · push Not at hx0
    have hxpos : ∀ w, 0 < x w := fun w => lt_of_le_of_ne (hx w) (Ne.symm (hx0 w))
    have hP : 0 < ∏ w, x w := Finset.prod_pos fun w _ => hxpos w
    have hNq : (0 : ℚ) < FractionalIdeal.absNorm aa :=
      lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg aa)
        (Ne.symm (by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]))
    have hN : 0 < √(FractionalIdeal.absNorm aa : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hNq)
    have hq : 0 < √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w := div_pos hN hP
    obtain ⟨Θ₀, hΘ₀def⟩ : ∃ Θ₀ : ℝ, Θ₀ = (√(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w) ^
        (((Fintype.card (InfinitePlace E) : ℕ) : ℝ)⁻¹) := ⟨_, rfl⟩
    have hΘ₀pos : 0 < Θ₀ := by rw [hΘ₀def]; exact Real.rpow_pos_of_pos hq _
    have hΘ₀f : Θ₀ ^ Fintype.card (InfinitePlace E) =
        √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w := by
      rw [hΘ₀def]; exact Real.rpow_inv_natCast_pow hq.le (ne_of_gt hf1)
    have hpw : (Θ / a) ^ Fintype.card (InfinitePlace E) ≤ Θ₀ ^ Fintype.card (InfinitePlace E) := by
      rw [hΘ₀f, le_div_iff₀ hP]
      calc (Θ / a) ^ Fintype.card (InfinitePlace E) * ∏ w, x w
          ≤ (Θ / a) ^ Fintype.card (InfinitePlace E) *
              ((a / Θ) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm aa : ℝ)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = √(FractionalIdeal.absNorm aa : ℝ) := by
            rw [← mul_assoc, ← mul_pow]
            have : Θ / a * (a / Θ) = 1 := by field_simp
            rw [this, one_pow, one_mul]
    have hle : Θ / a ≤ Θ₀ := le_of_pow_le_pow_left₀ (ne_of_gt hf1) hΘ₀pos.le hpw
    have h2 : 2 < Θ₀ := lt_of_lt_of_le (by rw [lt_div_iff₀ ha0]; linarith) hle
    have key := hC0 E aa haa x Θ₀ (K : ℝ) hxpos h2 hK3 hΘ₀f S
      (fun l hl => ⟨hL l (hS l hl).1, (hS l hl).2⟩)
    have hsum : ∑ l ∈ S, prof x K l = ∑ l ∈ S, ∏ w, min 1 ((x w / w l) ^ (K : ℝ)) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      unfold prof
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [Real.rpow_natCast]
    rw [hsum]
    refine key.trans ?_
    have hΘa : 0 < Θ / a := div_pos hΘ0 ha0
    have h3 : Θ₀ ^ (-((K : ℝ) - 5 / 2)) ≤ a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
      calc Θ₀ ^ (-((K : ℝ) - 5 / 2)) ≤ (Θ / a) ^ (-((K : ℝ) - 5 / 2)) :=
            (by
              rw [Real.rpow_neg hΘ₀pos.le, Real.rpow_neg hΘa.le]
              exact inv_anti₀ (Real.rpow_pos_of_pos hΘa _) (Real.rpow_le_rpow hΘa.le hle hp.le))
        _ = a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
            rw [Real.div_rpow hΘ0.le ha0.le, Real.rpow_neg ha0.le, div_inv_eq_mul, mul_comm]
    have h4 : |C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))| ≤
        (|C0| + 1) * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hΘ₀pos _), mul_assoc]
      exact mul_le_mul (by linarith) h3 (Real.rpow_pos_of_pos hΘ₀pos _).le
        (by have := abs_nonneg C0; linarith)
    calc (C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E)
        ≤ |(C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E)| := le_abs_self _
      _ = |C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))| ^ Fintype.card (InfinitePlace E) := abs_pow _ _
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h4 _
end Formalism.FourierDecayAlt.P.Jx7
