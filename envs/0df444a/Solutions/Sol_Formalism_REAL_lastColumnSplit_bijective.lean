-- Prove2me | solution 1 for Formalism.REAL.lastColumnSplit_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:07.878212+00:00
-- url     : https://prove2.me/submissions/3ca49e9f-6068-435f-ac47-97da254fd1ce

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Theorems.Thm_Formalism_REAL_cycleToLast_last
import Theorems.Thm_Formalism_REAL_extendLast_castSucc
import Theorems.Thm_Formalism_REAL_extendLast_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (m : ℕ) : Function.Bijective (lastColumnSplit m) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    simp only [lastColumnSplit] at h
    have hj : j = j' := by
      have h' := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ (Fin.last m)) h
      simpa [Equiv.Perm.mul_apply, extendLast_last, cycleToLast_last] using h'
    subst hj
    have he : extendLast τ = extendLast τ' := mul_left_cancel h
    have hτ : τ = τ' := by
      refine Equiv.ext (fun k => ?_)
      have h' := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ k.castSucc) he
      simpa [extendLast_castSucc] using h'
    rw [hτ]
  · simp [Fintype.card_perm, Nat.factorial_succ]
end Formalism.REAL
