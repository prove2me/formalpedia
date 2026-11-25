-- Prove2me | solution 1 for Formalism.L2.Col.GSD.chgSec_nab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:08:15.506276+00:00
-- url     : https://prove2.me/submissions/febf60dc-f2cb-4a35-b9fa-b46572359e5d

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_mem_intNab_iff

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
theorem _root_.solution (h : S.Ok) (s s' : S.Sec) (f : (S.toCSDOf h s).Forms) :
    (∀ c, (S.chgSec h s s' f).1 c ∈ S.Nab (s'.rep c)) ↔ ∀ c, f.1 c ∈ S.Nab (s.rep c) := by
  have e2 : f.1 = fun c => (((S.resOf h s).symm f : S.EqFun) : S.D → S.V) (s.rep c) :=
    (congrArg Subtype.val ((S.resOf h s).apply_symm_apply f)).symm
  rw [e2]
  exact (S.mem_intNab_iff h s' ((S.resOf h s).symm f)).symm.trans (S.mem_intNab_iff h s ((S.resOf h s).symm f))
end Formalism.L2.Col.GSD
