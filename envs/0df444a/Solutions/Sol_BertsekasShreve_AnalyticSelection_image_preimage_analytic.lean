-- Prove2me | solution 1 for BertsekasShreve.AnalyticSelection.image_preimage_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:25:19.393557+00:00
-- url     : https://prove2.me/submissions/03093f3e-f90d-4f3c-8617-eb961624ed64

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace

set_option autoImplicit false

open MeasureTheory

namespace P98bbd0f8

open Set BertsekasShreve.AnalyticSelection TopologicalSpace

universe u

lemma secondCountable_t2 {X : Type u} [TopologicalSpace X] [IsBorelSpace X] :
    SecondCountableTopology X ∧ T2Space X := by
  obtain ⟨Z, hm, hc, hs, B, -, ⟨e⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := X)
  have : SecondCountableTopology Z := inferInstance
  exact ⟨e.secondCountableTopology, e.isEmbedding.t2Space⟩

lemma exists_cont_surj {X : Type u} [TopologicalSpace X] [IsBorelSpace X] [Nonempty X] :
    ∃ v : (ℕ → ℕ) → X, Continuous v ∧ Function.Surjective v := by
  obtain ⟨Z, hm, hc, hs, B, hB, ⟨e⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := X)
  let : MeasurableSpace Z := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  have hA : AnalyticSet B := MeasurableSet.analyticSet hB
  have hne : B.Nonempty := ⟨(e (Classical.arbitrary X)).1, (e (Classical.arbitrary X)).2⟩
  rw [AnalyticSet] at hA
  rcases hA with h | ⟨k, hk, hkr⟩
  · exact absurd h hne.ne_empty
  · have hmem : ∀ n, k n ∈ B := fun n => hkr ▸ mem_range_self n
    refine ⟨fun n => e.symm ⟨k n, hmem n⟩, ?_, ?_⟩
    · exact e.symm.continuous.comp (hk.subtype_mk _)
    · intro x
      have hx : (e x).1 ∈ range k := hkr ▸ (e x).2
      obtain ⟨n, hn⟩ := hx
      refine ⟨n, ?_⟩
      have : (⟨k n, hmem n⟩ : B) = e x := Subtype.ext hn
      simp only [this, Homeomorph.symm_apply_apply]

end P98bbd0f8

open MeasureTheory BertsekasShreve.AnalyticSelection in
theorem solution {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    (f : X → Y) (hf : Measurable f) :
    (∀ A : Set X, AnalyticSet A → AnalyticSet (f '' A)) ∧
    (∀ B : Set Y, AnalyticSet B → AnalyticSet (f ⁻¹' B)) := by
  obtain ⟨hY2, hYT⟩ := P98bbd0f8.secondCountable_t2 (X := Y)
  have := hY2
  have := hYT
  refine ⟨fun A hA => ?_, fun B hB => ?_⟩
  · rw [AnalyticSet] at hA
    rcases hA with rfl | ⟨g, hg, rfl⟩
    · simpa using analyticSet_empty
    · rw [← Set.range_comp]
      have hm : Measurable (f ∘ g) := hf.comp hg.measurable
      have h := MeasurableSet.univ.analyticSet_image (X := ℕ → ℕ) hm
      rw [Set.image_univ] at h
      exact h
  · rcases isEmpty_or_nonempty X with hX | hX
    · rw [Set.eq_empty_of_isEmpty (f ⁻¹' B)]
      exact analyticSet_empty
    obtain ⟨v, hv, hvs⟩ := P98bbd0f8.exists_cont_surj (X := X)
    rw [AnalyticSet] at hB
    rcases hB with rfl | ⟨h, hh, rfl⟩
    · simpa using analyticSet_empty
    · let S : Set ((ℕ → ℕ) × (ℕ → ℕ)) := {p | f (v p.1) = h p.2}
      have hS : MeasurableSet S :=
        measurableSet_eq_fun (hf.comp (hv.measurable.comp measurable_fst))
          (hh.measurable.comp measurable_snd)
      have hSa : AnalyticSet S := hS.analyticSet
      have hI := hSa.image_of_continuous (hv.comp continuous_fst)
      convert hI using 1
      ext x
      constructor
      · rintro ⟨n, hn⟩
        obtain ⟨m, rfl⟩ := hvs x
        exact ⟨(m, n), hn.symm, rfl⟩
      · rintro ⟨⟨m, n⟩, hmn, rfl⟩
        exact ⟨n, hmn.symm⟩
