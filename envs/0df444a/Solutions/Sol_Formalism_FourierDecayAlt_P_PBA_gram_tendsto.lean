-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.gram_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:32:27.849074+00:00
-- url     : https://prove2.me/submissions/80055027-f0d1-4331-88d0-2479cc09bf5f

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalNormNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_gram_withRR
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_gram_S

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
variable {S RR}
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) (w : S.W) (p q : TB.Pt E) :
    Tendsto (fun n => (KB.withRR S (RR n)).gram ε i w.1 p q) atTop (𝓝 (S.gram ε i w.1 p q)) := by
  simp only [gram_withRR, gram_S]
  split_ifs
  · apply tendsto_finsetProd
    intro v _
    exact tendsto_const_nhds.mul (hconv v ε hε i _ ⟨w, rfl⟩ _ _)
  · exact tendsto_const_nhds
end Formalism.FourierDecayAlt.P.PBA
