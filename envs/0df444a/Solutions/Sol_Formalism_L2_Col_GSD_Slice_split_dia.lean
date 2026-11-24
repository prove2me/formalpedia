-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Slice.split_dia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:53:28.703531+00:00
-- url     : https://prove2.me/submissions/4571d094-b093-4618-8996-a18794a28af0

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_Slice_dia_apply

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
theorem _root_.solution (b c : A) (φ : S.EqFun) : σ.split ((dia S b).op φ) c = σ.split φ (b * c) := by
  apply Subtype.ext
  funext t
  show (((dia S b).op φ : S.EqFun) : S.D → S.V) (c • (t : S.D)) = (φ : S.D → S.V) ((b * c) • (t : S.D))
  rw [dia_apply, mul_smul]
end Formalism.L2.Col.GSD.Slice
