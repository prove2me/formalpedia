-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.Mcoord_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:26.860644+00:00
-- url     : https://prove2.me/submissions/a0f77ff2-f503-43c4-aa3c-e821a15505a4

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
theorem _root_.solution {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    Mcoord t X B ρ σ = blk (wMat n) 0 0 1 * blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ := by
  unfold Mcoord blk
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; simp [Matrix.mul_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply]
  · ext i j; simp [Matrix.mul_apply]
end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
