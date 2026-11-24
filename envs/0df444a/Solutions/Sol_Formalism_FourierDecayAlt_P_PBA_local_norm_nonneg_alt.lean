-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.local_norm_nonneg_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:11:51.520004+00:00
-- url     : https://prove2.me/submissions/0b101ab8-4d20-4d41-8384-65db4a110faa

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalNormNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_gram_psd
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_sum_re_nonneg


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
theorem _root_.solution {S : C.HidaSetting E Wp Wq} (hP : C.ThmPPos S) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W)
    (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (hκ : TB.PSDOn Y κ) : 0 ≤ S.base.N0 ε k w Y κ := by
  have e2 : S.base.N0 ε k w Y κ = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε k w.1 h h').re / S.base.wt w := rfl
  rw [e2]
  apply div_nonneg (BaseGramNonnegativity.sum_re_nonneg Y κ _ hκ (gram_psd hP hε k w Y))
  show 0 ≤ C.Word.size S.P w.1
  unfold C.Word.size
  exact Finset.prod_nonneg fun v _ => List.prod_nonneg fun x hx => by
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
end Formalism.FourierDecayAlt.P.PBA
