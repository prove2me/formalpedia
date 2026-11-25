-- Prove2me | solution 1 for Formalism.L2.Col.GSD.twForm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:40.359809+00:00
-- url     : https://prove2.me/submissions/2585e7e1-bbd3-4a8b-8876-5578c7753d61

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
open Formalism.L2.Col.GSD
variable (K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution : twForm K ∈ (tw K).intDel := by
  intro d
  cases d with
  | none => exact zero_mem _
  | some g => exact Submodule.mem_one.mpr ⟨((g : ℤ) : 𝓞 K), map_intCast _ _⟩
end Formalism.L2.Col.GSD
