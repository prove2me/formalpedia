-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.nu_of_specialization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:03:38.197844+00:00
-- url     : https://prove2.me/submissions/8d2cae6e-f493-4a8e-b2c9-cb90dc4d258b

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_strictAnti_gap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution : NuOfSpec := by
  unfold NuOfSpec
  intro r U hU h0
  have hgap := la_strictAnti_gap U hU
  have hpos : ∀ a : Fin r, (r : ℤ) - 1 - a.val ≤ U a := by
    intro a
    have ha := a.isLt
    have hlast : a.val + (r - 1 - a.val) < r := by omega
    have h3 := hgap (r - 1 - a.val) a ⟨a.val + (r - 1 - a.val), hlast⟩ rfl
    have h4 := h0 ⟨a.val + (r - 1 - a.val), hlast⟩
    omega
  constructor
  · intro a b hab
    have hab' : a.val ≤ b.val := hab
    have hb := hpos b
    have ha := hpos a
    have key : U b + ((b.val - a.val : ℕ) : ℤ) ≤ U a := hgap (b.val - a.val) a b (by omega)
    simp only [nuOf]
    omega
  · funext a
    have ha := hpos a
    have hal := a.isLt
    simp only [lamU, rowNu, hal, ↓reduceDIte, nuOf, Fin.eta]
    omega
end Formalism.CohomologicalDescent.LA
