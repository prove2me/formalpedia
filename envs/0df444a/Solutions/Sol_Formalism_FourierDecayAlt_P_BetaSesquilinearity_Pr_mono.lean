-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Pr.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:55:51.521797+00:00
-- url     : https://prove2.me/submissions/e4e64364-a5a2-4723-a073-eab0a76e1460

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono

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
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {O UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Pr
theorem _root_.solution {m m' : ℕ∞} (hm : m ≤ m') (h : Pr O UU m' a Φ) : Pr O UU m a Φ := ⟨sCkOn_mono hm h.ha, sCkOn_mono hm h.hΦ, h.hz⟩
end Pr
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
