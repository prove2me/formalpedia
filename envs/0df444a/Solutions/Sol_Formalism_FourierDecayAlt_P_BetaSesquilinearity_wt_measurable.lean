-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.wt_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:34:25.447447+00:00
-- url     : https://prove2.me/submissions/86f8ce82-52a9-4b3e-9cfe-b2b6e783ef63

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : Measurable (wt D) := by
  unfold wt bcWeight
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const (Complex.continuous_normSq.measurable.comp measurable_snd)
  · exact Continuous.measurable ((continuous_finset_prod _ fun a _ =>
      ((continuous_apply a).comp continuous_fst).norm.pow _).mul
      (((Complex.continuous_normSq.comp continuous_snd).sub continuous_const).pow _))
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
