-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.emb_closedEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:22:52.816131+00:00
-- url     : https://prove2.me/submissions/1d8f5ca0-f5ea-4c64-8125-58f7e205d516

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_linv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution :
    IsClosedEmbedding fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r) := by
  let c' : Mt k r → (Fin (k + 1) → Fin (k + 1) → ℂ) :=
    fun y => ((Em k r)ᵀ * Matrix.of y * Em k r : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
  have hc' : Continuous c' :=
    Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const
  have hli : Function.LeftInverse c' fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r) := by
    intro x
    exact emb_linv (Matrix.of x)
  exact hli.isClosedEmbedding hc' emb_cont
end Formalism.FourierDecayAlt.P.B2x3
