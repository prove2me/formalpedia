-- Prove2me | solution 1 for Formalism.ExtensionFiltration.span_min_slope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:52:38.529782+00:00
-- url     : https://prove2.me/submissions/308e2ea9-b2ae-4ff3-9303-91c4e1f4e011

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Theorems.Thm_Formalism_ExtensionFiltration_muDef_line
import Theorems.Thm_Formalism_ExtensionFiltration_muMin_line
import Theorems.Thm_Formalism_HN_degree_supermodular
import Theorems.Thm_Formalism_HN_finite_supremum_slopes
import Theorems.Thm_Formalism_HN_hnStep_of
import Theorems.Thm_Formalism_HN_maximal_slope_ratio
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_real_saturation_property
import Theorems.Thm_Formalism_HN_saturation_basic_properties
import Theorems.Thm_Formalism_HN_slope_characterization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
namespace Formalism.ExtensionFiltration
theorem _root_.solution : SpanMuMin := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX B Λ hB hB0 hs
  obtain ⟨s, hsB, hsn, hspan⟩ := hs
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set θ : ℝ := (-(2 * Λ) + Real.log 2 - logDisc K / (Module.finrank ℚ K : ℝ)) / 2 with hθ
  obtain ⟨hlat, hrkB, -⟩ := place_lattice_structure K V ι b X hX B hB
  obtain ⟨hsat, hmin, hcont, -⟩ :=
    hnStep_of degree_supermodular slope_characterization maximal_slope_ratio finite_supremum_slopes real_saturation_property saturation_basic_properties
      (𝓞 K) V _ ρ B hlat θ
  set S := hnStep ρ B θ with hS
  have hmem : ∀ x ∈ s, x ∈ S := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact S.zero_mem
    · have hle : Submodule.span (𝓞 K) ({x} : Set V) ≤ B :=
        (Submodule.span_singleton_le_iff_mem x B).2 (hsB hx)
      have hne : Submodule.span (𝓞 K) ({x} : Set V) ≠ ⊥ := fun h =>
        hx0 ((Submodule.span_singleton_eq_bot).1 h)
      have hmu := muDef_line b X hX x hx0 Λ (hsn x hx)
      have hsl : θ ≤ slope ρ (Submodule.span (𝓞 K) ({x} : Set V)) := by
        unfold muDef at hmu
        rw [hθ]
        linarith
      exact hcont _ hle hne (muMin_line b X hX x hx0 θ hsl) (Submodule.mem_span_singleton_self x)
  have hSfg : S.FG := Submodule.FG.of_le hB hsat.1
  have hrkS := (place_lattice_structure K V ι b X hX S hSfg).2.1
  have hspanEq : Submodule.span K (S : Set V) = Submodule.span K (B : Set V) := by
    refine le_antisymm (Submodule.span_mono hsat.1) (Submodule.span_le.2 ?_)
    intro y hy
    exact Submodule.span_mono (fun x hx => hmem x hx) (hspan hy)
  have hrkK : rkK (K := K) S = rkK (K := K) B := by
    unfold rkK
    rw [hspanEq]
  have hBS : B = S :=
    (saturation_basic_properties (𝓞 K) V _ ρ B hlat).2.2.1 S B hsat hsat.1 le_rfl (by rw [hrkB, hrkS, hrkK])
  have hfin : θ ≤ muMin ρ B := by
    have := hmin (by rw [← hBS]; exact hB0)
    rwa [← hBS] at this
  unfold muMinDef
  rw [hθ] at hfin
  linarith
end Formalism.ExtensionFiltration
