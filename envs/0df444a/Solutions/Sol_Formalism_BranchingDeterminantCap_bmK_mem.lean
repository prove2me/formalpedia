-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:07:15.468891+00:00
-- url     : https://prove2.me/submissions/a51a06e4-198c-4794-8985-b616aaf1db81

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_ndE_eq
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_ndEul_eq
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_mem_dualWeyl_iff
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_bmE
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_bmZ

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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ) (u : ℤ) (G : BP R n)
    (hG : G ∈ dualWeyl R (n + 1) n lam) : bmCap R n u G ∈ dualWeyl R (n + 1) n lam := by
  rw [bm_mem_dualWeyl_iff] at hG ⊢
  obtain ⟨h1, h2⟩ := hG
  refine ⟨fun s => ?_, fun l j hlj => ?_⟩
  · have e : ndEul R (n + 1) n s (bmCap R n u G) = bmCap R n u (ndEul R (n + 1) n s G) := by
      rw [bm_ndEul_eq, Derivation.add_apply, Derivation.add_apply, bmK_bmE, bmK_bmZ, map_add]
    rw [e, h1 s, map_smul]
  · have e : ndE R (n + 1) n l j (bmCap R n u G) = bmCap R n u (ndE R (n + 1) n l j G) := by
      rw [bm_ndE_eq, Derivation.add_apply, Derivation.add_apply, bmK_bmE, bmK_bmZ, map_add]
    rw [e, h2 l j hlj, map_zero]
end Formalism.BranchingDeterminantCap
