-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Slice.split_mem_intNab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:09.356965+00:00
-- url     : https://prove2.me/submissions/4dac8d35-23d7-459e-b317-2d3c44f8ff13

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_Slice_split_mem_intOf

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
theorem _root_.solution (hN : ∀ (b : A) (d : S.D), S.Nab (b • d) = S.Nab d) (φ : S.EqFun) :
    φ ∈ S.intNab ↔ ∀ b, σ.split φ b ∈ (S.restr σ.T).intNab := by
  exact σ.split_mem_intOf S.Nab hN φ
end Formalism.L2.Col.GSD.Slice
