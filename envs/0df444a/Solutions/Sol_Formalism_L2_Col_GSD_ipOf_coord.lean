-- Prove2me | solution 1 for Formalism.L2.Col.GSD.ipOf_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:53:28.149379+00:00
-- url     : https://prove2.me/submissions/bf6c324a-6eb9-4be7-94d3-893e5fade64c

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_I_coordOf
import Theorems.Thm_Formalism_L2_DIV_CSD_csum_sum


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
theorem _root_.solution (h : S.Ok) (s : S.Sec) (φ ψ : S.EqFun) :
    S.ipOf h s φ ψ = hform (S.toCSDOf h s).H (S.coordOf h s φ) (S.coordOf h s ψ) := by
  have e := (S.toCSDOf h s).csum_sum (S.coordOf h s φ) (S.coordOf h s ψ)
  rw [S.I_coordOf, S.I_coordOf] at e
  unfold ipOf
  rw [e]
  unfold hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Formalism.L2.Col.GSD
