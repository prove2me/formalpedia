-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.localization_sup_eq_localization_dnN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:46.134907+00:00
-- url     : https://prove2.me/submissions/c23119fc-7dca-4757-ba4f-73192a91f20d

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_algebraMap_ne_zero_of_notMem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_sup


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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution (p : Ideal (𝓞 K)) [p.IsPrime] (X Y : Submodule (𝓞 K) Z) :
    localization₂ p (X ⊔ Y) = localization₂ p X ⊔ localization₂ p Y :=
  locBasic_locS_sup (K := K) _ (fun _ hs => algebraMap_ne_zero_of_notMem p hs) X Y
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
