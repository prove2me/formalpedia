-- Prove2me | solution 1 for Formalism.summable_abs_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:33.055592+00:00
-- url     : https://prove2.me/submissions/f5baf68d-2e78-4efe-af6a-c6f287c11860

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section
open Formalism
variable (a : ℕ → ℝ)
namespace Formalism
theorem _root_.solution (K : ℝ) (hK : ∀ n : ℕ, |a n| ≤ K * vonMangoldt n) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => |a n| * (n : ℝ) ^ (-σ)) := by
  have hs : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun n => ?_) (hs.norm.mul_left |K|)
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
  · have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.norm_term_eq, if_neg hn.ne']
    simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg hΛ]
    rw [div_eq_mul_inv, ← Real.rpow_neg hnpos.le]
    have hK' : |a n| ≤ |K| * ArithmeticFunction.vonMangoldt n :=
      (hK n).trans (mul_le_mul_of_nonneg_right (le_abs_self K) hΛ)
    calc |a n| * (n : ℝ) ^ (-σ) ≤ |K| * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hK' (Real.rpow_nonneg hnpos.le _)
      _ = |K| * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) := by ring
end Formalism
