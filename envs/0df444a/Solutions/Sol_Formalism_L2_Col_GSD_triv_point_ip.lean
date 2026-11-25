-- Prove2me | solution 1 for Formalism.L2.Col.GSD.triv_point_ip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:07:26.087866+00:00
-- url     : https://prove2.me/submissions/a0363697-16c0-49b3-8ee3-3f2950c64da0

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_eq_sum

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
namespace Formalism.L2.Col
namespace GSD
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G]
    (h : (GSD.triv K G PUnit).Ok) :
    (GSD.triv K G PUnit).ip h (GSD.trivOne K G PUnit) (GSD.trivOne K G PUnit) = ((Nat.card G : K))⁻¹ := by
  let _ := h.fintypeCl
  unfold GSD.ip
  rw [GSD.ipOf_eq_sum]
  have hs : Subsingleton (GSD.triv K G PUnit).Cl := by
    refine ⟨fun a b => ?_⟩
    induction a using Quotient.inductionOn' with
    | h x =>
    induction b using Quotient.inductionOn' with
    | h y => rfl
  rw [Fintype.sum_subsingleton _ ((GSD.triv K G PUnit).cls PUnit.unit)]
  have h2 : ∀ x : PUnit, Nat.card (MulAction.stabilizer G x) = Nat.card G := by
    intro x
    have h1 : MulAction.stabilizer G x = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rfl
    rw [h1]
    exact Subgroup.card_top
  have h3 := h2 ((GSD.triv K G PUnit).outSec.rep ((GSD.triv K G PUnit).cls PUnit.unit))
  refine Eq.trans (congrArg (fun n : ℕ => ((n : K))⁻¹ * _) h3) ?_
  show ((Nat.card G : K))⁻¹ * (star (1 : K) * 1) = _
  simp
end GSD
end Formalism.L2.Col
