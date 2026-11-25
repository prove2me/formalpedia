-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.assemble_equality_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:42:42.883386+00:00
-- url     : https://prove2.me/submissions/e0cce174-e81f-415e-9bcd-ca853a1b6a72

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_diagDom
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_InCC_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_core

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.AssembleEq := by
  intro hC hAe hFa hL hDC hJ1 k r Wp Wq _ _ _ _ _ _ D A hA hRB hRA hU hJ hDB
  have hDD : DiagDom D A := diagDom hAe hFa hRB hRA hU hJ
  have h11 : ((1, 1) : ℝ × ℝ) ∈ Quad := by simp [Quad]
  have eJ : ∀ F : Mat k r → (Wq →L[ℂ] Wp), Jtau D (1, 1) F = JF D F := fun F => funext fun g => hJ1 k r Wp Wq D F g
  have eN : ∀ F : Mat k r → (Wq →L[ℂ] Wp), normSq D F = normSqTau D (1, 1) F := fun F => by
    unfold normSq normSqTau; rw [eJ]
  have eB : ∀ F F' : Mat k r → (Wq →L[ℂ] Wp), beta D F F' = betaTau D (1, 1) F F' := fun F F' => by
    unfold beta betaTau; rw [eJ, eJ]
  have h2 : PairingEqLimitPairing D A := fun F F' hF hF' => by
    rw [eB]
    exact core hC hAe hFa hL hDC hA hRB hRA hU hJ hDB h11 F F' hF hF'
  refine ⟨?_, h2⟩
  obtain ⟨C0, U0, hU0, hC0⟩ := hRB.1 (1, 1) h11
  refine ⟨C0, fun F F' c c' hF hF' hc hc' => ⟨?_, ?_, ?_⟩⟩
  · rw [eN]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hDD F (InCC_mono (by norm_num) hF) _ h11).2
  · rw [eN]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hDD F' (InCC_mono (by norm_num) hF') _ h11).2
  · rw [h2 F F' hF hF']
    exact hC0 _ (mem_of_mem_nhds hU0) F F' c c' hc hc'
end Formalism.FourierDecayAlt.P
