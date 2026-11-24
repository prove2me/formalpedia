-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.FT_pow_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:56.00781+00:00
-- url     : https://prove2.me/submissions/3895f4da-b0b9-4dfe-aaeb-a08f9163c43b

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_X_pow_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (y : σ) (T : Finset (Fin r)) (hy : ∀ c ∈ T, w c ≠ y ∧ e c ≠ y) (m b : ℕ)
    (G : MvPolynomial σ ℚ_[p]) : (FT w e T ^ b) (X y ^ m * G) = X y ^ m * (FT w e T ^ b) G := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ', Module.End.mul_apply, ih, FT_X_pow_mul w e y T hy, ← Module.End.mul_apply, ← pow_succ']
end Formalism.GM.gammaIntegralityLemmas
