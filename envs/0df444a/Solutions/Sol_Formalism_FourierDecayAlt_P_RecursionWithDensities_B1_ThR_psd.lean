-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.ThR_psd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:04.777828+00:00
-- url     : https://prove2.me/submissions/6c952e13-17ec-4e94-9bfb-8887463b0941

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_restrict
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_majorantPSD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_sel_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) (hK : KrPSD D)
    (hD : DomMin D T Th) (i s : ℕ) (t : E) (Y : Finset (Pt E)) : PSDOn Y (ThR D T Th i s t) := by
  unfold ThR
  by_cases hc : (1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1) ∧
      good (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s)
  · obtain ⟨⟨hs, hsi, hi⟩, hg⟩ := id hc
    refine psd_congr (fun x _ y _ => ?_)
      (psd_restrict Y (majorantPSD E W D T Th hK hD i s hs hsi hi _ (sel_mem hg)))
    simp only [if_pos hc]
    first
    | exact if_congr Iff.rfl rfl rfl
    | (split_ifs <;> rfl)
  · refine psd_congr (fun x _ y _ => ?_) (psd_zero Y)
    simp only [if_neg hc]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
