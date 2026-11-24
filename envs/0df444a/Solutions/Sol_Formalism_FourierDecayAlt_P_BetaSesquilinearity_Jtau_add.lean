-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Jtau_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:44:01.241477+00:00
-- url     : https://prove2.me/submissions/e1d6ab4c-02e5-46e7-b9e6-3cabb8e79e2f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_rho_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_xi_int

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {g : Mat k r}
    (h : Integrable (fun p => rho D p F g) D.μSS) (h' : Integrable (fun p => rho D p F' g) D.μSS) :
    Jtau D τ (F + F') g = Jtau D τ F g + Jtau D τ F' g := by
  simp only [Jtau]
  rw [← integral_add (xi_int D τ h) (xi_int D τ h')]
  congr 1
  funext p
  rw [rho_add, smul_add]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
