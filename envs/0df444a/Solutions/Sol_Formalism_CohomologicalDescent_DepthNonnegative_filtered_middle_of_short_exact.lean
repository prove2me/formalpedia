-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.filtered_middle_of_short_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:50.486275+00:00
-- url     : https://prove2.me/submissions/525ad424-f238-43a4-8e8e-4a611eda68d7

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_filtered_of_iso
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
theorem _root_.solution {C : Type 1} [Category.{0} C] [Abelian C] {P : C → Prop} {Z : C}
    (hZ : Filtered P Z) : ∀ {X Y : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact → Filtered P X → Filtered P Y := by
  induction hZ with
  | zero Z h0 =>
    intro X Y f g w hS hX
    have hm : Mono f := hS.mono_f
    have he : Epi f := hS.exact.epi_f (h0.eq_of_tgt _ _)
    have : IsIso f := isIso_of_mono_of_epi f
    exact filtered_of_iso hX (asIso f)
  | step S' hS' _ h3 ih =>
    intro X Y f g w hS hX
    have hmf : Mono f := hS.mono_f
    have heg : Epi g := hS.epi_g
    have hmu : Mono S'.f := hS'.mono_f
    have hev : Epi S'.g := hS'.epi_g

    let ι : kernel (g ≫ S'.g) ⟶ Y := kernel.ι (g ≫ S'.g)
    have hι : ι ≫ g ≫ S'.g = 0 := kernel.condition _
    have htop : (ShortComplex.mk ι (g ≫ S'.g) hι).ShortExact :=
      { exact := ShortComplex.exact_kernel _
        mono_f := by dsimp; infer_instance
        epi_g := by dsimp; infer_instance }
    refine Filtered.step (ShortComplex.mk ι (g ≫ S'.g) hι) htop ?_ h3
    let f' : X ⟶ kernel (g ≫ S'.g) := kernel.lift (g ≫ S'.g) f (by rw [← Category.assoc, w, zero_comp])
    have hf' : f' ≫ ι = f := kernel.lift_ι _ _ _
    let g' : kernel (g ≫ S'.g) ⟶ S'.X₁ := hS'.exact.lift (ι ≫ g) (by rw [Category.assoc]; exact hι)
    have hg' : g' ≫ S'.f = ι ≫ g := hS'.exact.lift_f _ _
    have w' : f' ≫ g' = 0 := by
      rw [← cancel_mono S'.f, Category.assoc, hg', ← Category.assoc, hf', w, zero_comp]
    refine ih f' g' w' ?_ hX
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.exact_iff_exact_up_to_refinements]
      intro A x₂ hx₂
      dsimp at x₂ hx₂
      have h1 : (x₂ ≫ ι) ≫ g = 0 := by
        rw [Category.assoc, ← hg', ← Category.assoc, hx₂, zero_comp]
      obtain ⟨A', π, hπ, x₁, hx₁⟩ := hS.exact.exact_up_to_refinements (x₂ ≫ ι) h1
      dsimp at x₁ hx₁
      refine ⟨A', π, hπ, x₁, ?_⟩
      dsimp
      rw [← cancel_mono ι, Category.assoc, Category.assoc, hf', hx₁]
    · dsimp
      exact mono_of_mono_fac hf'
    · dsimp
      rw [epi_iff_surjective_up_to_refinements]
      intro A y
      obtain ⟨A', π, hπ, x₀, hx₀⟩ := surjective_up_to_refinements_of_epi g (y ≫ S'.f)
      have h2 : x₀ ≫ g ≫ S'.g = 0 := by
        rw [← Category.assoc, ← hx₀, Category.assoc, Category.assoc, S'.zero, comp_zero, comp_zero]
      refine ⟨A', π, hπ, kernel.lift (g ≫ S'.g) x₀ h2, ?_⟩
      have h3' : kernel.lift (g ≫ S'.g) x₀ h2 ≫ ι = x₀ := kernel.lift_ι _ _ _
      apply (cancel_mono S'.f).mp
      calc (π ≫ y) ≫ S'.f = π ≫ y ≫ S'.f := Category.assoc _ _ _
        _ = x₀ ≫ g := hx₀
        _ = (kernel.lift (g ≫ S'.g) x₀ h2 ≫ ι) ≫ g := by rw [h3']
        _ = kernel.lift (g ≫ S'.g) x₀ h2 ≫ g' ≫ S'.f := by rw [Category.assoc, hg']
        _ = (kernel.lift (g ≫ S'.g) x₀ h2 ≫ g') ≫ S'.f := (Category.assoc _ _ _).symm
end Formalism.CohomologicalDescent.DepthNonnegative
