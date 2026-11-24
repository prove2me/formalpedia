-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.res_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:48.63042+00:00
-- url     : https://prove2.me/submissions/c5c8a62c-8c9a-4200-8a81-0fb83f3581a3

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
import Theorems.Thm_Formalism_CohomologicalDescent_LR_res_colHom
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_resO_rename
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_resO_colAdd
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowst_mem_dualWeyl_iff
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
theorem _root_.solution (w : ℕ) (lam2 : Fin q → ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R)
    (hf : f ∈ dualWeyl R (p + q) (p + q) (LD.blockWt p q w lam2)) : res R p q f ∈ dualWeyl R q q lam2 := by
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  refine ⟨?_, fun l j hlj => ?_⟩
  · have h := res_colHom R p q _ f hf.1
    have e : (fun b => LD.blockWt p q w lam2 (Fin.natAdd p b)) = lam2 := by
      funext b
      exact Fin.append_right _ _ b
    rwa [e] at h
  · have h := hf.2 (Fin.natAdd p l) (Fin.natAdd p j) (by
      rw [Fin.lt_def] at hlj ⊢
      simpa using hlj)
    have h1 := congrArg (fun φ => φ f) (lrb_resO_colAdd R p q l j)
    have h2 := congrArg (fun φ => φ f) (lrb_resO_rename R p q)
    simp only [AlgHom.comp_apply] at h1 h2
    rw [← h1, h, h2]
end Formalism.CohomologicalDescent.LR
