-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.finrank_cmF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:25.331154+00:00
-- url     : https://prove2.me/submissions/32ba25f3-f766-41a4-9066-4ed867fe0573

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjAlg_ne_one

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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : finrank (cmF K) K = 2 := by
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
  refine orderOf_eq_prime ?_ (conjAlg_ne_one hK)
  ext x
  rw [sq, AlgEquiv.mul_apply, conjAlg_apply, conjAlg_apply, star_star, AlgEquiv.one_apply]
end Formalism.HermitianLattices.Ext.L3
