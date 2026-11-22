-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.massTelescope_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:56.350393+00:00
-- url     : https://prove2.me/submissions/19f1eb4e-bbe8-4771-a0ba-1a3ee00a05b1

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_form_apply
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
theorem _root_.solution (n : ℕ) : (massTelescope_form K n).IsSymm := by
  have key : ∀ x y : Fin n → K,
      starRingEnd K (massTelescope_form K n x y) = massTelescope_form K n y x := by
    intro x y
    simp only [massTelescope_form_apply, map_sum, starRingEnd_apply, star_mul, star_star]
  first
  | exact key
  | exact ⟨key⟩
end Formalism.HermitianLatticesTheory
