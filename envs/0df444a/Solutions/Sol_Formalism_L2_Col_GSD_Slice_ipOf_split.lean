-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Slice.ipOf_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:10:13.354311+00:00
-- url     : https://prove2.me/submissions/325b7e46-6646-4272-9ce5-94225fa6afe7

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_eq_sum
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_indep
import Theorems.Thm_Formalism_L2_Col_GSD_restr_card_stab
import Theorems.Thm_P2M_Formalism_L2_Col_GSD_Slice_card_stab_smul__ace3a7f01b1e

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
variable (A : Type) [Group A] [MulAction A S.D]
open Formalism.L2.Col.GSD.Slice
variable {S A} (σ : S.Slice A)
variable [SMulCommClass A S.G S.D]
namespace Formalism.L2.Col.GSD.Slice
theorem _root_.solution [Fintype A] (h : S.Ok) (s : S.Sec) (sT : (S.restr σ.T).Sec) (φ ψ : S.EqFun) :
    S.ipOf h s φ ψ = ∑ b : A, (S.restr σ.T).ipOf (S.restr_ok h σ.T) sT (σ.split φ b) (σ.split ψ b) := by
  let _ := h.fintypeCl
  let _ := (S.restr_ok h σ.T).fintypeCl
  rw [S.ipOf_indep h s (σ.sec sT), GSD.ipOf_eq_sum]
  simp only [GSD.ipOf_eq_sum]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (σ.clEquiv sT).symm _ _ fun c => ?_
  show ((Nat.card (MulAction.stabilizer S.G
      (((σ.clEquiv sT).symm c).1 • ((sT.rep ((σ.clEquiv sT).symm c).2 : σ.T) : S.D))) : K))⁻¹ * _ = _
  rw [card_stab_smul', ← S.restr_card_stab σ.T]
  rfl
end Formalism.L2.Col.GSD.Slice
