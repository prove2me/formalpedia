-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.intPol_iff_bnd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:47.900308+00:00
-- url     : https://prove2.me/submissions/f809cd0a-2fcb-44ce-8534-2a60a0cdcaae

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
theorem _root_.solution (x : MvPolynomial σ ℚ_[p]) : x ∈ IntPol p σ ↔ ∀ m, ‖coeff m x‖ ≤ 1 := by
  constructor
  · rintro ⟨y, rfl⟩ m
    simp only [AlgHom.toLinearMap_apply, MvPolynomial.mapAlgHom_apply, MvPolynomial.coeff_map]
    exact PadicInt.norm_le_one (coeff m y)
  · intro h
    refine ⟨∑ m ∈ x.support, MvPolynomial.monomial m (⟨coeff m x, h m⟩ : ℤ_[p]), ?_⟩
    simp only [AlgHom.toLinearMap_apply, map_sum, MvPolynomial.mapAlgHom_apply, MvPolynomial.map_monomial]
    conv_rhs => rw [x.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    erw [MvPolynomial.map_monomial]
    rfl
end Formalism.InvariantFactorPaths.KP.LL
