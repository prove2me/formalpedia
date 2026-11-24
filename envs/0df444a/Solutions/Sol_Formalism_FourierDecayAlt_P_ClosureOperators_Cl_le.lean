-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.Cl_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:55:19.517865+00:00
-- url     : https://prove2.me/submissions/3cc59cda-dd17-4b87-bd78-40808b9301a9

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.ClosureOperators
theorem _root_.solution {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} {L : Fin N → Fin N → Prop} {M : Submodule ℂ V}
    (P : Submodule ℂ V) (h1 : M ≤ P) (h2 : ∀ a b, L a b → ∀ q ∈ P, E a b q ∈ P) : Cl E L M ≤ P :=
  sInf_le ⟨h1, h2⟩
end Formalism.FourierDecayAlt.P.ClosureOperators
