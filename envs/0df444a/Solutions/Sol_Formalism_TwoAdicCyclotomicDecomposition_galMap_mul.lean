-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.galMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:22.123382+00:00
-- url     : https://prove2.me/submissions/83f90d32-2cef-4227-b41a-7179a13cc941

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_pm_of_sq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ne_zero_of_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {n q d : ℕ} {ζ a b : L}
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (h : IsLayer n q d ζ a b) (hq0 : q ≠ 0) (hd0 : d ≠ 0) (σ τ : Gal(L/ℚ)) :
    galMap h.1 a b (σ * τ) = galMap h.1 a b σ * galMap h.1 a b τ :=
  Prod.ext (map_mul _ σ τ) (Prod.ext
    (sgn_mul (ne_zero_of_sq hq0 h.2.1) (pm_of_sq h.2.1) σ τ)
    (sgn_mul (ne_zero_of_sq hd0 h.2.2.1) (pm_of_sq h.2.2.1) σ τ))
end Formalism.TwoAdicCyclotomicDecomposition
