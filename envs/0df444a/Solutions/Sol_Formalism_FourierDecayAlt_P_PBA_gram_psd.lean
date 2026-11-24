-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.gram_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:11:23.371469+00:00
-- url     : https://prove2.me/submissions/6bf7be2b-388c-4d1c-8f40-31c8578ee230

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalNormNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_psd_pull
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_pull


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
    (Y : Finset (TB.Pt E)) : TB.PSDOn Y (fun h h' => S.gram ε k w.1 h h') := by
  classical
  by_cases hk : k ≤ S.G.r + 1
  · have : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y
        (fun h h' => S.gramLoc v ε k (w.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h')) := by
      intro v _
      exact JCx1.decay.psd_pull (Y.image (C.loc (S.σ v))) _ (hP v ε hε k hk w _) Y _
        (fun h hh => Finset.mem_image_of_mem _ hh)
    refine Jx7.psd_congr ?_ (Jx7.psd_prod univ _ this)
    intro x _ y _
    simp only [C.HidaSetting.gram, hk, if_true]
  · refine Jx7.psd_congr ?_ (Jx7.psd_zero (F := Y))
    intro x _ y _
    simp only [C.HidaSetting.gram, hk, if_false]
end Formalism.FourierDecayAlt.P.PBA
