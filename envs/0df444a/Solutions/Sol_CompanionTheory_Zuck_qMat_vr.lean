-- Prove2me | solution 1 for CompanionTheory.Zuck.qMat_vr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:59:05.92897+00:00
-- url     : https://prove2.me/submissions/06ddfd1f-b058-4f9f-b087-3ef2e1334a83

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Theorems.Thm_CompanionTheory_Zuck_casimir_kronecker_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace CompanionTheory.Zuck
theorem _root_.solution (hS : StdD) (b : Bool) :
    qMat (vr k r b) (vr k r (!b)) = (-1 : ℂ) • ((cM _)ᵀ * cM _ : Matrix _ _ ℂ) := by
  cases b
  · refine Eq.trans ?_ (casimir_kronecker_sum _).1
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      congrArg₂ _ (hS k r _).1 (hS k r _).2
  · refine Eq.trans ?_ (casimir_kronecker_sum _).2
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      congrArg₂ _ (hS k r _).2 (hS k r _).1
end CompanionTheory.Zuck
