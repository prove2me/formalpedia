-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_Rw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:53:56.208952+00:00
-- url     : https://prove2.me/submissions/706d4f62-929c-4f1f-a307-29a0f5eadb35

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_nrm_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Rw_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_Rw

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
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {A : ℝ} {m : ℕ} {v : List (Mat k r)} (hv : ∀ X ∈ v, inLie k r X) {F : Mat k r → E}
    (hF : InCC A (m + v.length) F) : InCC A m (Rw v F) := by
  obtain ⟨c, hc⟩ := hF
  have hv' : ∀ X ∈ v.map nrm, unitLie k r X := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
    exact nrm_unit (hv Y hY)
  have h1 : CCle A (m + (v.map nrm).length) F c := by rw [List.length_map]; exact hc
  rw [Rw_scale]
  exact ⟨_, CCle_smul _ (CCle_Rw hv' h1)⟩
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
