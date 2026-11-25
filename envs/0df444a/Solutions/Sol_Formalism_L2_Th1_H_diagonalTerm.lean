-- Prove2me | solution 1 for Formalism.L2.Th1.H.diagonalTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:16:15.658696+00:00
-- url     : https://prove2.me/submissions/f1bd46b1-9b7e-437f-8ef8-4530f6f72d6d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionActionPermutesPlaces
import Theorems.Thm_Formalism_L2_Th1_H_wt_eq_cexp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : DiagTerm := by
  intro V _ _ H hH v z
  rw [opU, kerK, wt_eq_cexp H hH, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hc : H z v = conj (H v z) := hH v z
  have hw : conj (H v z) = H v z - 2 * Complex.I * ((H v z).im : ℂ) := by
    apply Complex.ext <;> simp
    all_goals ring
  simp only [map_add, LinearMap.add_apply, hc, hw, altE]
  ring
end Formalism.L2.Th1.H
