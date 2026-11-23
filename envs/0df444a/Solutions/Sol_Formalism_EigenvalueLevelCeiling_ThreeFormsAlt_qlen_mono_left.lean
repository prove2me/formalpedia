-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.qlen_mono_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:58.583833+00:00
-- url     : https://prove2.me/submissions/873af6c2-206f-48fe-bf8a-6c1a3c05d360

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
theorem _root_.solution {X' X : Submodule R W} (h : X' ≤ X) (Y : Submodule R W) :
    qlen X' Y ≤ qlen X Y := by
  unfold qlen
  let f : (↥X' ⧸ Y.comap X'.subtype) →ₗ[R] (↥X ⧸ Y.comap X.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion h) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact hx)
  refine Module.length_le_of_injective f ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    rw [LinearMap.mem_ker] at hy
    dsimp only [f] at hy
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hy
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
