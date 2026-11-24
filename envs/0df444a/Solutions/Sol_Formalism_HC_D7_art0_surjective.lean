-- Prove2me | solution 1 for Formalism.HC.D7.art0_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:41:10.420892+00:00
-- url     : https://prove2.me/submissions/a8b22843-94d0-4da8-8eb7-cc5293e9b909

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_exists_sign
import Theorems.Thm_Formalism_HC_D7_q4
import Theorems.Thm_Formalism_HC_D7_d4
import Theorems.Thm_Formalism_HC_D7_exists_art
import Theorems.Thm_Formalism_HC_D7_exists_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH
namespace Formalism.HC.D7
theorem _root_.solution : Function.Surjective (art0 e hH) := by
  intro g
  obtain ⟨x, v, hv, hx⟩ := exists_rep e g.2
  obtain ⟨y, -, hy⟩ := exists_sign hH.1 (q4 hH) g.1.1
  obtain ⟨z, -, hz⟩ := exists_sign hH.2.1 (d4 hH) g.1.2
  obtain ⟨u, -, -, -, hu⟩ := exists_art e hH g x y z v hv hx hy.symm hz.symm
  exact ⟨u, hu.symm⟩
end Formalism.HC.D7
