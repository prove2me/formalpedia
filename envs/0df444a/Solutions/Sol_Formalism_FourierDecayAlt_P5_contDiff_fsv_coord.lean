-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.contDiff_fsv_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:46:36.440213+00:00
-- url     : https://prove2.me/submissions/ed2acd73-be33-4b87-99b7-dd1b1dda520f

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermMulVecMulVec
import Theorems.Thm_P2M_RH_Formalism_FourierDecayAlt_P5_contDiff_fsv_96a9e73be49d280f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (l : Fin r) (s : ℂ) :
    ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => fsv s (x.1 l)) :=
  (contDiff_fsv s).comp (by fun_prop : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => x.1 l))
end Formalism.FourierDecayAlt.P5
