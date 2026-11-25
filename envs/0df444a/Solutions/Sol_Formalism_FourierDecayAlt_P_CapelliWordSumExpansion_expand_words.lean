-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:43:33.514889+00:00
-- url     : https://prove2.me/submissions/ad7a456b-946d-444e-ba44-0b1bebbd4176

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_Xa_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_Xb_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
theorem _root_.solution (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ cw ∈ expand k r ts, (∀ X ∈ cw.2, unitLie k r X) ∧ cw.2.length ≤ ts.length := by
  induction ts with
  | nil =>
    intro cw hcw
    simp [expand] at hcw
    subst hcw
    simp
  | cons t ts ih =>
    intro cw hcw
    simp only [expand, List.mem_append, List.mem_map] at hcw
    rcases hcw with (⟨cw', hcw', rfl⟩ | ⟨cw', hcw', rfl⟩) | ⟨cw', hcw', rfl⟩
    · obtain ⟨h1, h2⟩ := ih cw' hcw'
      exact ⟨h1, by simpa using Nat.le_succ_of_le h2⟩
    · obtain ⟨h1, h2⟩ := ih cw' hcw'
      refine ⟨?_, by simpa using h2⟩
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact Xa_unit _ _
      · exact h1 X hX
    · obtain ⟨h1, h2⟩ := ih cw' hcw'
      refine ⟨?_, by simpa using h2⟩
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact Xb_unit _ _
      · exact h1 X hX
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
