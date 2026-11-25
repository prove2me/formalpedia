-- Prove2me | solution 1 for Formalism.L2.Col.GFam.Mat.resOf_opOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:07:05.956416+00:00
-- url     : https://prove2.me/submissions/94cd6ffb-9184-4cab-a8f7-c457e53c8818

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GFam_Mat_opOf_apply

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
namespace Mat
theorem _root_.solution {F F' : GFam K} (M : Mat F F') (h : F.Ok) (h' : F'.Ok) (s : ∀ b, (F.mem b).Sec)
    (s' : ∀ b', (F'.mem b').Sec) (φ : F.Forms) :
    (F'.resOf h' s' (M.opOf h s φ)).1 = letI := h.fintypeCl
      Formalism.ThetaLiftIndependence.kerOpM (fun c => (((F.toCSDOf h s).wt c : K))⁻¹) (M.atReps s s') (F.resOf h s φ).1 := by
  funext c'
  letI : ∀ b, Fintype (F.mem b).Cl := fun b => (h b).fintypeCl
  show ((M.opOf h s φ c'.1 : (F'.mem c'.1).EqFun) : (F'.mem c'.1).D → F'.V) ((s' c'.1).rep c'.2) = _
  rw [M.opOf_apply h s φ c'.1, Submodule.coe_sum, Finset.sum_apply]
  simp only [Formalism.ThetaLiftIndependence.kerOpM]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rfl
end Mat
end Formalism.L2.Col.GFam
