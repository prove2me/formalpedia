-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.contDiff_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:50:36.924805+00:00
-- url     : https://prove2.me/submissions/7256778d-c5bc-46c1-a5f0-ddc420d6786c

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermMulVecMulVec

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
theorem _root_.solution : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => zeta k r z z' x.2) := by
  unfold zeta zetaL
  let Lc : Mx k r →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (hermLin (Hpk k r) (fvec k r z' (Fin.last r)) (fvec k r z (Fin.last r)))
  have h1 : ContDiff ℝ ∞ (fun g : Mx k r => Lc g) := (Lc.restrictScalars ℝ).contDiff
  exact h1.comp contDiff_snd
end Formalism.FourierDecayAlt.P5
