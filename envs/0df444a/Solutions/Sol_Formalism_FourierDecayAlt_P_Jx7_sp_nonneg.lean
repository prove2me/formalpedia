-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.sp_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:44.909406+00:00
-- url     : https://prove2.me/submissions/05205a32-6cd7-49a2-a93d-09042c84259f

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_supI_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_supremum_first_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped nonZeroDivisors
variable {ι : Type} [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution (hg : 0 ≤ G.g) (hka : 0 ≤ G.ka) (p : Prop) [Decidable p] (w : ι) :
    0 ≤ sp G de de' T T' l p w := by
  unfold sp; split_ifs
  · exact supremum_first_nonneg G de de' T T' l hg hka w
  · exact supI_nonneg G de de' T T' l hg hka w
end Formalism.FourierDecayAlt.P.Jx7
