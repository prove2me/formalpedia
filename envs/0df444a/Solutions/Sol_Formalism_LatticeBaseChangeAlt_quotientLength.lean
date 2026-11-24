-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.quotientLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:28:16.016489+00:00
-- url     : https://prove2.me/submissions/576d08a3-fa95-4f25-acc2-4230bc288780

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_quot_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open BQuot
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : QuotientLength := by
  intro O K V _ _ _ _ _ _ _ _ _ _ ϖ hϖ n c N hN X e be th hX hth a a' ha ha' hdet
  dsimp only
  have hq := quot_core (K := K) ϖ hϖ n c N hN X e be th hX hth a a' ha hdet
  have hva : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact ha
  have hva' : IsDiscreteValuationRing.addVal O a' ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact ha'
  lift IsDiscreteValuationRing.addVal O a to ℕ using hva with A hA
  lift IsDiscreteValuationRing.addVal O a' to ℕ using hva' with A' hA'
  have hfin : ql X ((X ⊓ N.restrictScalars O) ⊔
      Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hq
    exact (ENat.coe_ne_top _) (top_le_iff.1 (by exact_mod_cast hq))
  lift ql X ((X ⊓ N.restrictScalars O) ⊔
      Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)) to ℕ using hfin with m hm
  refine ⟨m, rfl, ?_⟩
  have hq' : m + A' ≤ A + n * be := by exact_mod_cast hq
  simp only [ENat.toNat_coe]
  have hq'' : (m : ℤ) + A' ≤ A + n * be := by exact_mod_cast hq'
  linarith
end Formalism.LatticeBaseChangeAlt
