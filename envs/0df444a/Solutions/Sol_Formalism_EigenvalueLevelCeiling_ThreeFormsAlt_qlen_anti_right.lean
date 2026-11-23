-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.qlen_anti_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:46.478799+00:00
-- url     : https://prove2.me/submissions/505564ba-d317-4f1c-82ad-08fa447e4b52

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms

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
theorem _root_.solution (X : Submodule R W) {Y Y' : Submodule R W} (h : Y ≤ Y') :
    qlen X Y' ≤ qlen X Y := by
  unfold qlen
  let g : (↥X ⧸ Y.comap X.subtype) →ₗ[R] (↥X ⧸ Y'.comap X.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => h hx)
  refine Module.length_le_of_surjective g ?_
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
