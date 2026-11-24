-- Prove2me | solution 1 for Formalism.REAL.frobenius_ball_compact_pos_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:43:46.128087+00:00
-- url     : https://prove2.me/submissions/81a10cf5-bae6-447f-a5c3-d0859d9bf1a4

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionInvariants
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Theorems.Thm_Formalism_REAL_continuous_frobenius_on_group
import Theorems.Thm_Formalism_REAL_f1auxiliary_hs_one
import Theorems.Thm_Formalism_REAL_hermitian_small_ball
import Theorems.Thm_Formalism_REAL_isClosedEmbeddingMatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped NNReal ENNReal
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) :
    IsCompact {g : UJ ε | hsG g ≤ (n : ℝ) + 1} ∧ 0 < muG ε {g : UJ ε | hsG g ≤ (n : ℝ) + 1} ∧
      muG ε {g : UJ ε | hsG g ≤ (n : ℝ) + 1} < ⊤ := by
  have hc : IsCompact {g : UJ ε | hsG g ≤ (n : ℝ) + 1} := by
    have h := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage ((hermitian_small_ball n ε).1 ((n : ℝ) + 1))
    convert h using 1
    ext g
    exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩
  refine ⟨hc, ?_, hc.measure_lt_top⟩
  have hU : IsOpen {g : UJ ε | hsG g < (n : ℝ) + 1} :=
    isOpen_lt (continuous_frobenius_on_group ε) continuous_const
  have h1 : (1 : UJ ε) ∈ {g : UJ ε | hsG g < (n : ℝ) + 1} := by
    show hs (1 : Matrix (Fin n) (Fin n) ℂ) < (n : ℝ) + 1
    rw [f1auxiliary_hs_one]; linarith
  exact (hU.measure_pos (muG ε) ⟨1, h1⟩).trans_le
    (measure_mono fun g (hg : hsG g < (n : ℝ) + 1) => hg.le)
end Formalism.REAL
