-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.smul_mem_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:49.047466+00:00
-- url     : https://prove2.me/submissions/be1f2b3a-b5b4-4471-8258-7525da6716df

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_SmulMemOfNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (Λ : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) {s : ℚ_[p]} (hs : ‖s‖ ≤ 1)
    {v : MvPolynomial σ ℚ_[p]} (hv : v ∈ Λ) : s • v ∈ Λ := by
  have e : s • v = (show ℤ_[p] from ⟨s, hs⟩) • v := by
    rw [← algebraMap_smul ℚ_[p] (show ℤ_[p] from ⟨s, hs⟩) v]
    rfl
  rw [e]
  exact Λ.smul_mem _ hv
end Formalism.InvariantFactorPaths.KP.LL
