-- Prove2me | solution 1 for Formalism.L2.SG.Pf.AllRowsTr.pA_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:23.323426+00:00
-- url     : https://prove2.me/submissions/37389347-c36c-45b4-b0c0-7d6ed2a3a379

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsTr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MonoidAlgebra
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.AllRowsTr
open Formalism.L2.SG.Pf.AllRowsGA
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
namespace Formalism.L2.SG.Pf.AllRowsTr
theorem _root_.solution (f : ∀ i, MonoidAlgebra ℂ (G i)) (γ : ∀ i, G i) : (pA f).coeff γ = ∏ i, (f i).coeff (γ i) := by
  simp [pA, MonoidAlgebra.coeff_ofCoeff]
end Formalism.L2.SG.Pf.AllRowsTr
