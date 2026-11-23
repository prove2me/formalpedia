-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Slice.split_mem_intDel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:21.863904+00:00
-- url     : https://prove2.me/submissions/8c162d5a-2a30-496e-93ed-2e9f6d1b349a

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
theorem _root_.solution (hN : ∀ (b : A) (d : S.D), S.Del (b • d) = S.Del d) (φ : S.EqFun) :
    φ ∈ S.intDel ↔ ∀ b, σ.split φ b ∈ (S.restr σ.T).intDel := by
  exact σ.split_mem_intOf S.Del hN φ
end Formalism.L2.Col.GSD.Slice
