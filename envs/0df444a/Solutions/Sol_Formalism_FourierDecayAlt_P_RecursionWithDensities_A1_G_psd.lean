-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.G_psd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:00.186847+00:00
-- url     : https://prove2.me/submissions/3db6cab0-ef89-4cbf-9e0a-251c8c8d5469

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_G_cases
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_majorantPSDA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hNZ : NZSg Sg) (hK : AxK D)
    (hD : TC.DomMinA D Sg Th) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1)
    (c : E ⧸ D.La i s) : PSDOn (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) c) := by
  rcases G_cases (D.La i s) (Sg i s) (Th i s) c with ⟨_, h0⟩ | ⟨t₁, ht₁, _, h1⟩
  · rw [h0]
    exact psd_zero _
  · rw [h1]
    exact majorantPSDA E D Sg Th hNZ hK hD i s hs hsi hi t₁ ht₁
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
