-- Prove2me | solution 1 for BertsekasShreve.SemicontSelection.lemma7_21_open_selector
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:14:25.740992+00:00
-- url     : https://prove2.me/submissions/36aef0b5-a722-4707-aadb-635ec7e02f76

import Mathlib

set_option autoImplicit false

open TopologicalSpace in
theorem solution {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (G : Set (X × Y)) (hG : IsOpen G) :
    IsOpen (Prod.fst '' G) ∧
      ∃ φ : (Prod.fst '' G) → Y, Measurable φ ∧ ∀ x : (Prod.fst '' G), ((x : X), φ x) ∈ G := by
  classical
  refine ⟨isOpenMap_fst G hG, ?_⟩
  by_cases hY : Nonempty Y
  · obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq Y
    have hex : ∀ x : (Prod.fst '' G), ∃ n, ((x : X), d n) ∈ G := by
      intro x
      obtain ⟨p, hp, hpx⟩ := x.2
      have hopen : IsOpen {y : Y | ((x : X), y) ∈ G} :=
        hG.preimage (Continuous.prodMk continuous_const continuous_id)
      have hne : ({y : Y | ((x : X), y) ∈ G} : Set Y).Nonempty := ⟨p.2, by
        show ((x : X), p.2) ∈ G
        rw [← hpx]; exact hp⟩
      exact hd.exists_mem_open hopen hne
    refine ⟨fun x => d (Nat.find (hex x)), ?_, fun x => Nat.find_spec (hex x)⟩
    have hm : Measurable fun x : (Prod.fst '' G) => Nat.find (hex x) := by
      apply measurable_find
      intro k
      have h1 : MeasurableSet {x : X | (x, d k) ∈ G} :=
        (hG.preimage (Continuous.prodMk continuous_id continuous_const)).measurableSet
      exact measurable_subtype_coe h1
    exact measurable_from_nat.comp hm
  · have : IsEmpty (Prod.fst '' G) := ⟨fun x => hY ⟨(x.2.choose).2⟩⟩
    exact ⟨fun x => isEmptyElim x, Subsingleton.measurable, fun x => isEmptyElim x⟩
