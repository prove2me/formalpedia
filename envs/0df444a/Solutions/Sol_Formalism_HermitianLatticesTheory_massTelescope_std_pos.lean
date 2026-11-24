-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.massTelescope_std_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:18:38.333596+00:00
-- url     : https://prove2.me/submissions/ef41ea30-79d5-4e6b-858f-b3f095399577

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_symm
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_isLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_def
import Theorems.Thm_Formalism_HermitianLatticesTheory_massBasic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hCM : IsCMUnram K) (n : ℕ) :
    0 < mass (massTelescope_form K n) (massTelescope_lat K n) := by
  exact (massBasic K (Fin n → K) (massTelescope_form K n) (massTelescope_symm K n)
    (fun x hx => massTelescope_def K hCM n x hx) (massTelescope_lat K n)
    (massTelescope_isLattice K n)).2.2
end Formalism.HermitianLatticesTheory
