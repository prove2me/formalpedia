-- Prove2me | solution 1 for Formalism.REAL.tendsto_slope_exp_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:27.285353+00:00
-- url     : https://prove2.me/submissions/a829bd9d-b9af-4432-a7be-98cd6cdea64a

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Theorems.Thm_Formalism_REAL_hasDerivAt_matrix_exp_smul_at_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 X) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedSpace (R := ℝ) (m := Fin n) (n := Fin n) (α := ℂ)
  exact (hasDerivAt_matrix_exp_smul_at_zero X).tendsto_slope
end Formalism.REAL
