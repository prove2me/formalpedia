-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:50.432259+00:00
-- url     : https://prove2.me/submissions/88af51c1-e56f-411a-b738-52192f1d4b2e

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_mem_sc_inv
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_split_core
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_isDVR_OO
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_mem_localization_iff_mem_span

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) Z) (hA : A.FG)
    (hBA : B ≤ A) {a : K} (ha : a ≠ 0) (hav : a ∈ OO w) :
    ∃ W : Submodule K Z,
      localization₂ w.asIdeal A ≤
        cut W (localization₂ w.asIdeal A) ⊔ (localization₂ w.asIdeal A ⊓ sc a⁻¹ (localization₂ w.asIdeal B)) ∧
      cut W (sc a⁻¹ (localization₂ w.asIdeal B)) ≤ localization₂ w.asIdeal A := by
  have hdvr := isDVR_OO w
  have htow : IsScalarTower (𝓞 K) (OO w) Z :=
    ⟨fun r c z => by rw [Subalgebra.smul_def, Subalgebra.smul_def, Subalgebra.coe_smul, smul_assoc]⟩
  have hfg : (Submodule.span (OO w) (A : Set Z)).FG := by
    obtain ⟨s, hs⟩ := hA
    exact ⟨s, by rw [← hs, Submodule.span_span_of_tower]⟩
  have ha0 : (⟨a, hav⟩ : OO w) ≠ 0 := fun h => ha (congrArg Subtype.val h)
  obtain ⟨W, h1, h2⟩ := split_core (K := K) (Submodule.span (OO w) (A : Set Z))
    (Submodule.span (OO w) (B : Set Z)) hfg (Submodule.span_mono hBA) ⟨a, hav⟩ ha0
  refine ⟨W, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, t, ht, hyW, hat, rfl⟩ := h1 x ((mem_localization_iff_mem_span w A x).mp hx)
    exact Submodule.add_mem_sup ⟨(mem_localization_iff_mem_span w A y).mpr hy, hyW⟩
      ⟨(mem_localization_iff_mem_span w A t).mpr ht,
        (mem_sc_inv ha _ _).mpr ((mem_localization_iff_mem_span w B _).mpr hat)⟩
  · rintro x ⟨hxC, hxW⟩
    exact (mem_localization_iff_mem_span w A x).mpr
      (h2 x hxW ((mem_localization_iff_mem_span w B _).mp ((mem_sc_inv ha _ _).mp hxC)))
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
