-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Qr.mem_CapSp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:37:55.280274+00:00
-- url     : https://prove2.me/submissions/e1b346d3-31a1-4c4a-acc6-33217ca145ac

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.Qr
theorem _root_.solution {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {m : Fin n → ℂ} {v : V} :
    v ∈ CapSp E m ↔ ∀ w, qdet E w v = cpol m w • v := by
  simp only [CapSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]
end Formalism.FourierDecayAlt.Qr
