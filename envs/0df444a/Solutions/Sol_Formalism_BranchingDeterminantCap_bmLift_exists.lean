-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmLift_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:33.638752+00:00
-- url     : https://prove2.me/submissions/8ef59224-2e66-4bf7-b4f6-c524915d130d

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_add
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_smul
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_bidet
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpanDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (lam sg : Fin n → ℕ) (hIL : bmIL lam sg)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : f ∈ dualWeyl R n n sg) :
    ∃ G, bmLift R n lam (fun s => lam s - sg s) f G := by
  rw [standardMonomialSpanDomain R n n sg] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
    subst hsh
    exact bmG_bidet K sz hsz I lam hIL
  | zero => exact ⟨0, bmG_zero R n _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨G, hG⟩ := hx
    obtain ⟨G', hG'⟩ := hy
    exact ⟨_, bmLift_add hG hG'⟩
  | smul c x _ hx =>
    obtain ⟨G, hG⟩ := hx
    exact ⟨_, bmLift_smul c hG⟩
end Formalism.BranchingDeterminantCap
