-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.pderiv_pow_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:34.224836+00:00
-- url     : https://prove2.me/submissions/921b430e-88f3-45b2-b52f-f863f6f7277e

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
theorem _root_.solution (i : σ) (s : ℕ) (m : σ →₀ ℕ) (a : ℚ_[p]) :
    (((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ^ s)
      (monomial m a)) = monomial (m - Finsupp.single i s) (a * ((m i).descFactorial s : ℚ_[p])) := by

  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    erw [MvPolynomial.pderiv_monomial]
    congr 1
    · rw [tsub_tsub, ← Finsupp.single_add]
    · rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.descFactorial_succ]; push_cast; ring
end Formalism.GM.M.PhiIntegrality
