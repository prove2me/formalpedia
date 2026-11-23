-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.qlen_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:46.844478+00:00
-- url     : https://prove2.me/submissions/b7b8fb15-18a0-483c-996e-a24ea043c2ff

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_DivisionValues_imageLcv_len_map


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
theorem _root_.solution (f : W ≃ₗ[R] W) (X Y : Submodule R W) :
    qlen (X.map (f : W →ₗ[R] W)) (Y.map (f : W →ₗ[R] W)) = qlen X Y :=
  imageLcv_len_map f X Y
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
