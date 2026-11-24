-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.filtered_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:47.357554+00:00
-- url     : https://prove2.me/submissions/3fe76077-c98c-49ec-a428-a7b74ddd05d1

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
open CategoryTheory CategoryTheory.Limits
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution {C : Type 1} [Category.{0} C] [Abelian C] {P : C → Prop} {Y : C}
    (h : Filtered P Y) : ∀ {Y' : C} (_ : Y ≅ Y'), Filtered P Y' := by
  cases h with
  | zero _ h => intro Y' e; exact Filtered.zero _ (h.of_iso e.symm)
  | step S hS h1 h3 =>
    intro Y' e
    have w : (S.f ≫ e.hom) ≫ (e.inv ≫ S.g) = 0 := by simp
    have hiso : S ≅ ShortComplex.mk (S.f ≫ e.hom) (e.inv ≫ S.g) w :=
      ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) (by simp) (by simp)
    exact Filtered.step (ShortComplex.mk (S.f ≫ e.hom) (e.inv ≫ S.g) w)
      (ShortComplex.shortExact_of_iso hiso hS) h1 h3
end Formalism.CohomologicalDescent.DepthNonnegative
