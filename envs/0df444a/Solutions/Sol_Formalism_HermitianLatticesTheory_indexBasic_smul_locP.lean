-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.indexBasic_smul_locP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:20.142918+00:00
-- url     : https://prove2.me/submissions/23211812-9852-4dca-9fd8-32240666c20f

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_idem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (p : Ideal R) [p.IsPrime] (Y : Submodule R W) {s : R} (hs : s ∉ p)
    {z : W} (hz : s • z ∈ localization₂ p Y) : z ∈ localization₂ p Y := by
  have : z ∈ localization₂ p (localization₂ p Y) := ⟨s, hs, hz⟩
  unfold localization₂ at this ⊢
  rwa [locBasic_locS_idem] at this
end Formalism.HermitianLatticesTheory
