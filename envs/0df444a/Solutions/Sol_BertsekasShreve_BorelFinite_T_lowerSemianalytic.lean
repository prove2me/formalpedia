-- Prove2me | solution 1 for BertsekasShreve.BorelFinite.T_lowerSemianalytic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:05:08.523004+00:00
-- url     : https://prove2.me/submissions/021a067e-a3d1-4555-b05d-a67481896c91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators
import Theorems.Thm_BertsekasShreve_BorelFinite_H_lowerSemianalytic

namespace BertsekasShreve.BorelFinite

open MeasureTheory Set

lemma analyticSet_univ_of_isBorelSpace' {X : Type*} [TopologicalSpace X]
    [BertsekasShreve.AnalyticSelection.IsBorelSpace X] : AnalyticSet (univ : Set X) := by
  obtain ⟨Z, mZ, cZ, sZ, B, hB, ⟨e⟩⟩ :=
    BertsekasShreve.AnalyticSelection.IsBorelSpace.exists_homeomorph_borel (X := X)
  letI : MeasurableSpace Z := borel Z
  haveI : BorelSpace Z := ⟨rfl⟩
  have hBa : AnalyticSet B := MeasurableSet.analyticSet hB
  obtain ⟨β, tβ, pβ, f, hf, hrange⟩ := analyticSet_iff_exists_polishSpace_range.1 hBa
  let g : β → X := fun b => e.symm ⟨f b, hrange ▸ mem_range_self b⟩
  have hg : Continuous g := e.symm.continuous.comp (hf.subtype_mk _)
  have hr : range g = univ := by
    refine eq_univ_of_forall fun x => ?_
    have hx : (e x).1 ∈ range f := hrange ▸ (e x).2
    obtain ⟨b, hb⟩ := hx
    refine ⟨b, ?_⟩
    simp only [g]
    rw [show (⟨f b, _⟩ : B) = e x from Subtype.ext hb]
    exact e.symm_apply_apply x
  rw [← hr]
  exact analyticSet_range_of_polishSpace hg

end BertsekasShreve.BorelFinite

open BertsekasShreve.BorelFinite

theorem solution {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (J : S → EReal) (hJ : IsLowerSemianalyticOn Set.univ J) :
    IsLowerSemianalyticOn Set.univ (T M J) := by
  have hH := H_lowerSemianalytic M J hJ
  refine ⟨analyticSet_univ_of_isBorelSpace', fun c => ?_⟩
  have e : {x : S | x ∈ Set.univ ∧ T M J x < (c : EReal)} =
      Prod.fst '' {z : S × C | z ∈ M.Γ ∧ H M J z < (c : EReal)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, Set.mem_image, T, iInf_lt_iff]
    constructor
    · rintro ⟨u, hu, h⟩; exact ⟨(x, u), ⟨hu, h⟩, rfl⟩
    · rintro ⟨⟨x', u⟩, ⟨hu, h⟩, rfl⟩; exact ⟨u, hu, h⟩
  rw [e]
  exact (hH.2 c).image_of_continuous continuous_fst
