-- Prove2me | solution 1 for Formalism.L2.Col.GFam.ipOf_eq_csum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:49.147018+00:00
-- url     : https://prove2.me/submissions/4d7fb4cd-796d-4e25-bafc-bb275993682e

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

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
    F.ipOf h s φ ψ = (F.toCSDOf h s).csum (F.resOf h s φ).1 (F.resOf h s ψ).1 := by
  letI : ∀ b, Fintype (F.mem b).Cl := fun b => (h b).fintypeCl
  unfold ipOf CSD.csum
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rfl
end Formalism.L2.Col.GFam
