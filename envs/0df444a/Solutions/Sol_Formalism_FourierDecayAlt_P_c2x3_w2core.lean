-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x3_w2core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:06:30.265396+00:00
-- url     : https://prove2.me/submissions/836d270b-a1b8-43d6-9637-6a686d186c23

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_tel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (y : ℕ → ℝ) (hy : ∀ i, 0 < y i) (h0 : y 0 = 1) (K : ℕ) : ∀ r : ℕ,
    ∏ l ∈ Finset.range r, (y (l + 1) / y l) ^ (4 * (r - l) + K) =
      y r ^ K * ∏ l ∈ Finset.range r, y (l + 1) ^ 4 := by
  intro r
  induction r with
  | zero => simp [h0]
  | succ r ih =>
    have hsplit : ∀ l ∈ Finset.range (r + 1), (y (l + 1) / y l) ^ (4 * (r + 1 - l) + K) =
        (y (l + 1) / y l) ^ 4 * (y (l + 1) / y l) ^ (4 * (r - l) + K) := by
      intro l hl
      rw [Finset.mem_range] at hl
      rw [← pow_add]; congr 1; omega
    rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib, Finset.prod_pow,
      c2x3_tel y (fun i => (hy i).ne') (r + 1), h0, div_one,
      Finset.prod_range_succ (fun l => (y (l + 1) / y l) ^ (4 * (r - l) + K)), ih, Nat.sub_self,
      mul_zero, zero_add, Finset.prod_range_succ (fun l => y (l + 1) ^ 4)]
    have hr0 := (hy r).ne'
    have hq : y r ^ K * (y (r + 1) / y r) ^ K = y (r + 1) ^ K := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero K hr0)]
    calc y (r + 1) ^ 4 * (y r ^ K * (∏ l ∈ Finset.range r, y (l + 1) ^ 4) * (y (r + 1) / y r) ^ K)
        = y (r + 1) ^ 4 * (∏ l ∈ Finset.range r, y (l + 1) ^ 4) * (y r ^ K * (y (r + 1) / y r) ^ K) := by ring
      _ = y (r + 1) ^ K * ((∏ l ∈ Finset.range r, y (l + 1) ^ 4) * y (r + 1) ^ 4) := by rw [hq]; ring
end Formalism.FourierDecayAlt.P
