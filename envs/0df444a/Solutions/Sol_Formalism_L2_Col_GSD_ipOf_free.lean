-- Prove2me | solution 1 for Formalism.L2.Col.GSD.ipOf_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:24.459696+00:00
-- url     : https://prove2.me/submissions/8be19647-d981-45a1-bcba-5912264f4e01

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_wt_eq
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_eq_sum
import Theorems.Thm_Formalism_L2_Col_GSD_wt_eq_one

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
open Formalism.L2.Col.GSD
variable (S : GSD K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution (h : S.Ok) (s : S.Sec) (hf : S.Free) (φ ψ : S.D → S.V) :
    S.ipOf h s φ ψ = letI := h.fintypeCl
      ∑ c : S.Cl, S.pair (φ (s.rep c)) (ψ (s.rep c)) := by
  rw [S.ipOf_eq_sum h s]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← S.wt_eq h s c, S.wt_eq_one h s hf c]
  simp only [Nat.cast_one, inv_one, one_mul]
end Formalism.L2.Col.GSD
