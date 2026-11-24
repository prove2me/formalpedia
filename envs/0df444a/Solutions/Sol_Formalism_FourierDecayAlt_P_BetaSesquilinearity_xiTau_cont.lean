-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.xiTau_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:58:54.350159+00:00
-- url     : https://prove2.me/submissions/ce3ed4de-a065-460b-8225-8258a39faaed

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_ell_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) : Continuous (xiTau D τ) := by
  unfold xiTau lam
  have h1 := (ell_cont (k := k) (r := r) D.z).comp (continuous_snd.comp (continuous_fst : Continuous fun p : SS k r => p.1))
  have h2 := (ell_cont (k := k) (r := r) D.z').comp (continuous_snd.comp (continuous_snd : Continuous fun p : SS k r => p.2))
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h1))).sub
    (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h2)))
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
