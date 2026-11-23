-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.split_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:31.866259+00:00
-- url     : https://prove2.me/submissions/fa2c582d-ebca-4766-a983-56f6a20a70af

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_split_of_snf

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
variable {O K Z : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [ValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup Z] [Module K Z] [Module O Z]
  [IsScalarTower O K Z]
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution (N NB : Submodule O Z) (hfg : N.FG) (hle : NB ≤ N) (a : O) (ha : a ≠ 0) :
    ∃ W : Submodule K Z,
      (∀ x ∈ N, ∃ y ∈ N, ∃ t ∈ N, y ∈ W ∧ a • t ∈ NB ∧ x = y + t) ∧
      (∀ x ∈ W, a • x ∈ NB → x ∈ N) := by
  have hfin : Module.Finite O N := Module.Finite.iff_fg.mpr hfg
  have htfZ : Module.IsTorsionFree O Z := Module.IsTorsionFree.trans_faithfulSMul O K Z
  have htf : Module.IsTorsionFree O N := inferInstance
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Module.Free.chooseBasis O N) (NB.comap N.subtype)
  obtain ⟨W, h1, h2⟩ := split_of_snf (K := K) N NB a ha snf
  exact ⟨W, h1, fun x hx hax => h2 x hx (hle hax) hax⟩
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
