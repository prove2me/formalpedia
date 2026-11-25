-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.massTelescope_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:04:47.442641+00:00
-- url     : https://prove2.me/submissions/0bb786e5-a7ca-4c1a-8099-c912dd42f5a3

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_symm
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_ortho
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_std_pos
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hS : SiegelMassRatio) (hCM : IsCMUnram K) (r : ℕ) (hr : 2 ≤ r) :
    mass (massTelescope_form K (r + 1)) (massTelescope_lat K (r + 1)) =
      mass (massTelescope_form K r) (massTelescope_lat K r) * massRatioRightSide K (r + 1) := by
  have h := hS K hCM (r + 1) (by omega) (Fin (r + 1) → K) (Fin r → K)
    (massTelescope_form K (r + 1)) (massTelescope_form K r) (massTelescope_lat K (r + 1))
    (massTelescope_lat K r) (massTelescope_symm K (r + 1)) (massTelescope_symm K r)
    (massTelescope_ortho K (r + 1)) (by simpa using massTelescope_ortho K r)
  have hp := massTelescope_std_pos K hCM r
  rw [← h]
  field_simp
end Formalism.HermitianLatticesTheory
