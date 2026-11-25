-- Prove2me | solution 1 for Formalism.L2.Pj.LocAlg.mem_intPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:10:13.257437+00:00
-- url     : https://prove2.me/submissions/362bae58-33a6-4fcc-8511-01d8ef391636

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
variable {Ω : Type} [Field Ω] {D N : ℕ}
variable {jc j0 : Fin (N + 1)} {x : Fin N → Ω}
namespace Formalism.L2.Pj.LocAlg
theorem _root_.solution {σ : Type} {W : Subring Ω} {P : MvPolynomial σ Ω} :
    P ∈ intPoly σ W ↔ ∀ e, P.coeff e ∈ W :=
    Iff.rfl
end Formalism.L2.Pj.LocAlg
