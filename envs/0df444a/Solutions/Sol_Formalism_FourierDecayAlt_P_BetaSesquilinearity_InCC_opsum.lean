-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:11:23.47981+00:00
-- url     : https://prove2.me/submissions/afcbe32a-698a-49dc-90a0-66636f5716dd

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_add

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
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {ι : Type*} {A : ℝ} {m : ℕ} (Θ : List ι) (φ : ι → Mat k r → E)
    (h : ∀ T ∈ Θ, InCC A m (φ T)) : InCC A m (fun g => (Θ.map fun T => φ T g).sum) := by
  induction Θ with
  | nil => exact ⟨0, by simpa using (CCle_zero : CCle A m (fun _ : Mat k r => (0 : E)) 0)⟩
  | cons T Θ ih =>
    obtain ⟨c, hc⟩ := h T (by simp)
    obtain ⟨c', hc'⟩ := ih (fun T' hT' => h T' (by simp [hT']))
    exact ⟨c + c', by simpa using CCle_add hc hc'⟩
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
