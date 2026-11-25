-- Prove2me | solution 1 for Formalism.L2.Col.GFam.ipOf_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:09:38.641374+00:00
-- url     : https://prove2.me/submissions/42cc0f47-1d99-4b5a-a5d6-9310178c4e3f

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_I_coordOf
import Theorems.Thm_Formalism_L2_Col_GFam_ipOf_eq_csum
import Theorems.Thm_Formalism_L2_Col_GFam_I_coordOf
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
open Formalism.L2.Col.GFam
variable (F : GFam K)
namespace Formalism.L2.Col.GFam
theorem _root_.solution (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ ψ : F.Forms) :
    F.ipOf h s φ ψ = hform (F.toCSDOf h s).H (F.coordOf h s φ) (F.coordOf h s ψ) := by
  rw [F.ipOf_eq_csum h s, ← F.I_coordOf h s φ, ← F.I_coordOf h s ψ, (F.toCSDOf h s).csum_sum]
  unfold hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Formalism.L2.Col.GFam
