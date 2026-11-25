-- Prove2me | solution 1 for Formalism.L2.Col.GFam.ipOf_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:09:43.955118+00:00
-- url     : https://prove2.me/submissions/9a7a1c3b-74aa-4553-b977-c0ece6752ed1

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_indep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GFam
variable (F : GFam K)
namespace Formalism.L2.Col.GFam
theorem _root_.solution (h : F.Ok) (s s' : ∀ b, (F.mem b).Sec) (φ ψ : F.Forms) : F.ipOf h s φ ψ = F.ipOf h s' φ ψ := by
  unfold ipOf
  exact Finset.sum_congr rfl fun b _ => (F.mem b).ipOf_indep (h b) (s b) (s' b) (φ b) (ψ b)
end Formalism.L2.Col.GFam
