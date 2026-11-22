-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.span_map_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:45.244844+00:00
-- url     : https://prove2.me/submissions/147dd562-54fb-423f-89b0-0cbc1f33eff6

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
theorem _root_.solution {τ : Type} (T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial τ ℚ_[p])
    (S : Set (MvPolynomial σ ℚ_[p])) (Λ : Submodule ℤ_[p] (MvPolynomial τ ℚ_[p]))
    (h : ∀ v ∈ S, T v ∈ Λ) : ∀ v ∈ Submodule.span ℤ_[p] S, T v ∈ Λ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv => exact h v hv
  | zero => rw [map_zero]; exact Λ.zero_mem
  | add a b _ _ ha hb => rw [map_add]; exact Λ.add_mem ha hb
  | smul c a _ ha =>
    rw [← algebraMap_smul ℚ_[p] c a, map_smul, algebraMap_smul]
    exact Λ.smul_mem c ha
end Formalism.InvariantFactorPaths.KP.LL
