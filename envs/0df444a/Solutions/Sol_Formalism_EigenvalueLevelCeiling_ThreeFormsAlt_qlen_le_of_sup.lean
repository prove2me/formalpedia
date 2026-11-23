-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.qlen_le_of_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:49.887408+00:00
-- url     : https://prove2.me/submissions/546b521b-9145-4961-b944-87f59aac8cf5

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
theorem _root_.solution {X' X Y : Submodule R W} (h : X' ≤ X) (hs : X ≤ X' ⊔ (X ⊓ Y)) :
    qlen X Y ≤ qlen X' Y := by
  unfold qlen
  let f : (↥X' ⧸ Y.comap X'.subtype) →ₗ[R] (↥X ⧸ Y.comap X.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion h) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact hx)
  refine Module.length_le_of_surjective f ?_
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨x, hx⟩ := x
    obtain ⟨u, hu, t, ht, rfl⟩ := Submodule.mem_sup.mp (hs hx)
    refine ⟨Submodule.Quotient.mk ⟨u, hu⟩, ?_⟩
    dsimp only [f]
    rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
      Submodule.coe_inclusion]
    have : u - (u + t) = -t := by abel
    rw [this]
    exact Y.neg_mem ht.2
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
