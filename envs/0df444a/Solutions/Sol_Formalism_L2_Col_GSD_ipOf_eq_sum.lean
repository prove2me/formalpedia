-- Prove2me | solution 1 for Formalism.L2.Col.GSD.ipOf_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:15.758116+00:00
-- url     : https://prove2.me/submissions/e5073419-9b19-4c2e-a558-3e1346309697

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_wt_eq

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
theorem _root_.solution (h : S.Ok) (s : S.Sec) (φ ψ : S.D → S.V) :
    S.ipOf h s φ ψ = letI := h.fintypeCl
      ∑ c : S.Cl, ((Nat.card (MulAction.stabilizer S.G (s.rep c)) : K))⁻¹ * S.pair (φ (s.rep c)) (ψ (s.rep c)) := by
  unfold ipOf CSD.csum
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [S.wt_eq h s c]
end Formalism.L2.Col.GSD
