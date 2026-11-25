-- Prove2me | solution 1 for Formalism.L2.Col.GSD.chgSec_csum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:08:11.343304+00:00
-- url     : https://prove2.me/submissions/f4828575-5a7f-4e0f-b452-69f23ce220d7

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_indep

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
theorem _root_.solution (h : S.Ok) (s s' : S.Sec) (f f' : (S.toCSDOf h s).Forms) :
    (S.toCSDOf h s').csum (S.chgSec h s s' f).1 (S.chgSec h s s' f').1 = (S.toCSDOf h s).csum f.1 f'.1 := by
  have e1 := S.ipOf_indep h s s' ((S.resOf h s).symm f) ((S.resOf h s).symm f')
  have e2 : ∀ g : (S.toCSDOf h s).Forms,
      (fun c => (((S.resOf h s).symm g : S.EqFun) : S.D → S.V) (s.rep c)) = (g : S.Cl → S.V) :=
    fun g => congrArg Subtype.val ((S.resOf h s).apply_symm_apply g)
  unfold ipOf at e1
  rw [e2 f, e2 f'] at e1
  exact e1.symm
end Formalism.L2.Col.GSD
