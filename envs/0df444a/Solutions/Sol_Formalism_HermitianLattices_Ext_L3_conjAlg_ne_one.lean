-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.conjAlg_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:40.821988+00:00
-- url     : https://prove2.me/submissions/874311fa-5c5e-4a20-9f1e-6dcbfd737575

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_star_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable (K : Type) [Field K] [NumberField K] [StarRing K]
variable {K}
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : conjAlg K ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := exists_star_ne hK
  apply ha
  rw [← conjAlg_apply, h, AlgEquiv.one_apply]
end Formalism.HermitianLattices.Ext.L3
