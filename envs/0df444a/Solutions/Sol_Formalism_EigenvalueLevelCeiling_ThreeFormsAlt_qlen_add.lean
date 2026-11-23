-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.qlen_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:37.808922+00:00
-- url     : https://prove2.me/submissions/c645d2cf-3e44-49f5-bea9-6240c9b6b4f9

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_len_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution {N M P : Submodule R W} (hNM : N ≤ M) (hMP : M ≤ P) :
    qlen P N = qlen M N + qlen P M :=
  indexBasic_len_add N M P hNM hMP
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
