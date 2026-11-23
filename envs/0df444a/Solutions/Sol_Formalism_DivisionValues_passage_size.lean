-- Prove2me | solution 1 for Formalism.DivisionValues.passage_size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:10:26.472897+00:00
-- url     : https://prove2.me/submissions/f486917d-f9fa-4e05-bd5d-9654a3c2a372

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : PassageSize := by
  intro J Pl _ _ mu0 logκ Fo Fabs Eb logOm La W b N m f C0 xe B0 Nc pF pN x eps pq w h1 hJ hPl
    hpq hW hw hLa hFo hC0 hEb
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) hLa
  have hm0 : 0 ≤ m := by
    rw [← hJ]
    exact Nat.cast_nonneg _
  have hf0 : 0 ≤ f := le_trans (Nat.cast_nonneg _) hPl
  have hmN : 0 ≤ m * N := by
    rcases isEmpty_or_nonempty J with hJe | ⟨⟨j0⟩⟩
    · have : m = 0 := by
        rw [← hJ]
        simp
      simp [this]
    · exact mul_nonneg hm0 (le_trans (abs_nonneg _) (hpq j0))
  have hterm : ∀ j ρ, pq j * w j ρ * logOm ≤ |pq j| * W * La := by
    intro j ρ
    have e1 : pq j * w j ρ * logOm ≤ |pq j * w j ρ * logOm| := le_abs_self _
    rw [abs_mul, abs_mul, abs_of_nonneg (hw j ρ).1] at e1
    have e2 : |pq j| * w j ρ ≤ |pq j| * W := mul_le_mul_of_nonneg_left (hw j ρ).2 (abs_nonneg _)
    have e3 : |pq j| * w j ρ * |logOm| ≤ |pq j| * W * La :=
      mul_le_mul e2 hLa (abs_nonneg _) (mul_nonneg (abs_nonneg _) hW)
    linarith
  have hsum : ∑ j, ∑ ρ, pq j * w j ρ * logOm ≤ m * f * N * W * La := by
    calc ∑ j, ∑ ρ, pq j * w j ρ * logOm ≤ ∑ j : J, ∑ ρ : Pl, N * (W * La) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun ρ _ => by
            have := hterm j ρ
            have := mul_le_mul_of_nonneg_right (hpq j) (mul_nonneg hW hLa0)
            linarith
      _ = m * (Fintype.card Pl : ℝ) * (N * (W * La)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hJ]
          ring
      _ ≤ m * f * N * W * La := by
          have := mul_le_mul_of_nonneg_left hPl (mul_nonneg (mul_nonneg hmN hW) hLa0)
          nlinarith [this]
  have g1 : mu0 ≤ logκ + m * f * N * W * La + 2 * Fabs + C0 * m * xe * (B0 + Nc) := by linarith
  refine ⟨g1, fun hWb hb hF hNc hB0 hxe hxe0 => ?_⟩
  have k1 : m * f * N * W * La ≤ m * f * N * (2 * b) * La := by
    have := mul_le_mul_of_nonneg_left hWb (mul_nonneg (mul_nonneg hmN hf0) hLa0)
    linarith
  have k2 : B0 ≤ f * m * b * xe := by
    rw [hB0]
    exact mul_le_mul_of_nonneg_left hxe (mul_nonneg (mul_nonneg hf0 hm0) hb)
  have k3 : C0 * m * xe * (B0 + Nc) ≤ C0 * m * xe * (f * m * b * xe + pN * b) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hC0 hm0) hxe0)
  linarith
end Formalism.DivisionValues
