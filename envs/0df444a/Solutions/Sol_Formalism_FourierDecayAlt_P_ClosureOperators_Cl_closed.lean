-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.Cl_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:55:18.021799+00:00
-- url     : https://prove2.me/submissions/8e413c39-6d4f-4021-b2c7-27385be05ff7

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
theorem _root_.solution {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} {L : Fin N → Fin N → Prop} {M : Submodule ℂ V}
    (a b : Fin N) (h : L a b) (q : V) (hq : q ∈ Cl E L M) : E a b q ∈ Cl E L M := by
  unfold Cl at hq ⊢
  rw [Submodule.mem_sInf] at hq ⊢
  intro P hP
  exact hP.2 a b h q (hq P hP)
end Formalism.FourierDecayAlt.P.ClosureOperators
