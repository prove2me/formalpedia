-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.density_lemma_of_reductions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:06:31.143066+00:00
-- url     : https://prove2.me/submissions/c5321408-cc15-4158-819c-8b3f6b56e9bb

import Definitions.Def_Formalism_HermitianCurvature_LemmaDensOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensityLemmaOfReductions
import Theorems.Thm_Formalism_FourierDecayAlt_P_nonzero_minor_count_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.DensityAveraging.LemmaDensOfSteps := by
  rintro ⟨C0, hB⟩ ⟨C1, hJ⟩ ⟨C2, hT⟩
  refine ⟨max C0 (max C1 C2), ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ O hr hε hA hmm hF hsupp hbig hrel hG
  have H : Formalism.FourierDecayAlt.DensityAveraging.DensHyp (max C0 (max C1 C2)) D A ε mm F' := ⟨hr, hε, hA, hmm, hF, hsupp, hbig⟩
  have h0 : C0 ≤ max C0 (max C1 C2) := le_max_left _ _
  have h1 : C1 ≤ max C0 (max C1 C2) := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2 : C2 ≤ max C0 (max C1 C2) := le_trans (le_max_right _ _) (le_max_right _ _)
  have key : ∀ n : ℕ, ∀ γ : B.Mat k r, r + 2 - Formalism.FourierDecayAlt.DensityAveraging.nzMin D γ = n → IsRelevant D γ →
      0 < Gf k r D.z D.z' γ → Formalism.FourierDecayAlt.DensityAveraging.VanAt D F' γ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro γ hn hrelγ hGγ
      have hMore : Formalism.FourierDecayAlt.DensityAveraging.MoreBlocks D F' γ := by
        intro γ' hrel' hG' hlt
        have hle := nonzero_minor_count_le D γ'
        exact ih (r + 2 - Formalism.FourierDecayAlt.DensityAveraging.nzMin D γ') (by omega) γ' rfl hrel' hG'
      by_cases hbc : γ ∈ bigPos D
      · exact hB _ h0 k r Wp Wq D A ε mm F' γ H hbc hrelγ
      · have hz : ∃ l : Fin (r + 2), Dmin k r D.z D.z' γ l = 0 := by
          by_contra hne
          exact hbc ⟨hrelγ.1, hGγ, fun l _ hl => hne ⟨l, hl⟩⟩
        by_cases hcj : Formalism.FourierDecayAlt.DensityAveraging.CaseJ D γ
        · exact hJ _ h1 k r Wp Wq D A ε mm F' γ H hrelγ hGγ hcj hMore
        · exact hT _ h2 k r Wp Wq D A ε mm F' γ H hrelγ hGγ ⟨hz, hcj⟩ hMore
  exact key _ γ rfl hrel hG O
end Formalism.FourierDecayAlt.P
