-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.res_rowDiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:14.070855+00:00
-- url     : https://prove2.me/submissions/a46d6cfd-cd2c-4f73-a634-615283591d93

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_rowGen
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable (R : Type*) [CommRing R] (p q : ℕ)
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (b b' : Fin q) (k : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R) :
    res R p q (rowDiv R (Fin.natAdd p b) (Fin.natAdd p b') k f) = rowDiv R b b' k (res R p q f) := by
  have h := congrArg (fun φ => (φ f).coeff k) (lrb_rowGen R p q b b')
  simp only [AlgHom.comp_apply, Polynomial.coeff_mapAlgHom_apply] at h
  exact h
end Formalism.CohomologicalDescent.LR
