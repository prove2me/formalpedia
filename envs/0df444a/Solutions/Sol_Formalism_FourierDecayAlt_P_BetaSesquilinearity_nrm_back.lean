-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm_back
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:02:29.649399+00:00
-- url     : https://prove2.me/submissions/953d7d4a-20a2-48b6-9aac-1bd1330a52c5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_nz_pos

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
theorem _root_.solution (X : Mat k r) : ((nz X : ℝ) : ℂ) • nrm X = X := by
  unfold nrm
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (nz_pos X).ne', Complex.ofReal_one, one_smul]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
