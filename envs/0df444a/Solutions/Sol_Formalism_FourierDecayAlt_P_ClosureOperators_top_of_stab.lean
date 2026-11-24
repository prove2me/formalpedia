-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.top_of_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:55:21.612723+00:00
-- url     : https://prove2.me/submissions/b9e267d6-a592-4287-93d1-022053da7b7b

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hI : Irr E) (S : Submodule ℂ V) (hS : Stab E S)
    (v : V) (hv : v ∈ S) (hv0 : v ≠ 0) : S = ⊤ := by
  refine (hI.2 S hS).resolve_left (fun h => hv0 ?_)
  rw [h] at hv
  exact (Submodule.mem_bot ℂ).mp hv
end Formalism.FourierDecayAlt.P.ClosureOperators
