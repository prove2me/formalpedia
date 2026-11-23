-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.det_Mcoord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:52.645675+00:00
-- url     : https://prove2.me/submissions/8459ffee-90cd-4090-a56f-b9c45feb6116

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_sum_eq_geoS
import Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_Mcoord_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_det_blk

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
theorem _root_.solution {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (Mcoord t X B ρ σ).det = (wMat n).det *
      (t ^ n * σ - ∑ j ∈ Finset.range n, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j)) := by
  have hW : (blk (wMat n) 0 0 1).det = (wMat n).det := by
    unfold blk
    rw [Matrix.det_reindex_self]
    simp only [Pi.zero_apply]
    rw [show (Matrix.of fun _ _ => (0 : ℂ) : Matrix _ (Fin n) ℂ) = 0 from rfl, Matrix.det_fromBlocks_zero₂₁]
    simp
  rw [Mcoord_eq, Matrix.det_mul, det_blk t X hX, sum_eq_geoS, hW]
end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
