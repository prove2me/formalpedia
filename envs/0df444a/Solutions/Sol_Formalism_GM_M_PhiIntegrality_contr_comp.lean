-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.contr_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:03.589988+00:00
-- url     : https://prove2.me/submissions/5a0ede3f-b702-4367-a4f1-abb9e8c36a32

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
namespace Formalism.GM.M.PhiIntegrality
theorem _root_.solution {C C' : ℝ} {T T' : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]}
    (hC : 0 ≤ C) (h : Contr C T) (h' : Contr C' T') : Contr (C * C') (T' * T) := by

  intro B hB u hu
  have h1 := h' (B * C) (mul_nonneg hB hC) (T u) (h B hB u hu)
  rw [Module.End.mul_apply, ← mul_assoc]
  exact h1
end Formalism.GM.M.PhiIntegrality
