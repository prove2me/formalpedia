-- Prove2me | solution 1 for Formalism.REAL.pfil_facts_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:12:17.926835+00:00
-- url     : https://prove2.me/submissions/dfbc4787-a231-4509-b46d-f24376043c79

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_P2M_Formalism_REAL_mem_kSpan_self__eef759b81251
import Theorems.Thm_Formalism_REAL_pfil_monotone_in_length
import Theorems.Thm_Formalism_REAL_pfil_compact_stable
import Theorems.Thm_Formalism_REAL_poincare_filtration_succ
import Theorems.Thm_Formalism_REAL_poincare_filtration_zero
import Theorems.Thm_Formalism_REAL_pfil_le_cyclic
import Theorems.Thm_Formalism_REAL_pfil_finite_dimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : PfilFacts := by
  intro V _ _ n ε E u hE
  refine ⟨poincare_filtration_zero ε E u, fun j => pfil_monotone_in_length ε E u (Nat.le_succ j),
    fun j => pfil_compact_stable ε E u hE j, fun j a b => poincare_filtration_succ ε E u hE j a b,
    fun j => pfil_le_cyclic ε E u j, ?_, fun h0 j => pfil_finite_dimensional ε E u h0 j⟩
  intro x hx
  have hmono : Monotone (pfil ε E u) := by
    intro i k h
    exact pfil_monotone_in_length ε E u h
  have hdir : Directed (· ≤ ·) (pfil ε E u) := hmono.directed_le
  have hle : cyc E u ≤ ⨆ j, pfil ε E u j := by
    unfold cyc
    apply sInf_le
    refine ⟨?_, ?_⟩
    · apply Submodule.mem_iSup_of_mem 0
      rw [poincare_filtration_zero]
      exact mem_kSpan_self' ε E u
    · intro a b y hy
      obtain ⟨j, hj⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hy
      exact Submodule.mem_iSup_of_mem (j + 1) (poincare_filtration_succ ε E u hE j a b y hj)
  exact (Submodule.mem_iSup_of_directed _ hdir).mp (hle hx)
end Formalism.REAL
