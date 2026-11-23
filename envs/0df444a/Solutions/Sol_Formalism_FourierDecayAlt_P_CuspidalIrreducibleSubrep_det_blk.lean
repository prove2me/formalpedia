-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.det_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:40.926011+00:00
-- url     : https://prove2.me/submissions/1cec2209-09ce-457a-8c74-6178f079c72b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_det_blk_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_continuous_blk_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_continuous_geoS

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
    (blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det = t ^ n * σ - ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  by_cases ht : t = 0
  swap
  · exact det_blk_ne t ht X hX B ρ σ
  have hc1 : Continuous fun s : ℂ => (blk (s • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det :=
    (continuous_blk_shift X B ρ σ).matrix_det
  have hc2 : Continuous fun s : ℂ => s ^ n * σ - ρ ⬝ᵥ (geoS X s *ᵥ B) :=
    ((continuous_pow n).mul continuous_const).sub
      (continuous_const.dotProduct ((continuous_geoS X).matrix_mulVec continuous_const))
  have heq := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc1 hc2 (fun s hs => det_blk_ne s hs X hX B ρ σ)
  exact congrFun heq t
end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
