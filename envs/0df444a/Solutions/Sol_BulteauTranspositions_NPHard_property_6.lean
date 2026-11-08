-- Prove2me | solution 1 for BulteauTranspositions.NPHard.property_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:57:36.038616+00:00
-- url     : https://prove2.me/submissions/d2311935-4716-4fb0-a8c0-7edbb04c1867

import Mathlib
import Definitions.Def_BulteauTranspositions_NPHard_ThreeDT

open BulteauTranspositions.NPHard in
theorem solution (I : Instance) (hI : I.WF) (p : ℕ → ℕ)
    (hp : IsPermutation I.span p) (he : Equivalent I p) :
    breakpoints I.span p = I.domain.card ∧ I.domain.card = 3 * I.triples.length := by
  classical
  obtain ⟨hspan, hnd, hpos, hinj⟩ := hI
  obtain ⟨_, hbij, _, _⟩ := hp
  have hpinj : Set.InjOn p (Set.Icc 0 I.span) := hbij.injOn
  -- the three symbols of a triple are distinct
  have hdist : ∀ t ∈ I.triples, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
    intro t ht
    have h := (List.nodup_flatMap.mp hnd).1 t ht
    simp only [Triple.symbols, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at h
    push_neg at h
    exact ⟨h.1.1, h.1.2, h.2.1⟩
  have hmemsym : ∀ t ∈ I.triples, ∀ a ∈ t.symbols, a ∈ I.symbols := by
    intro t ht a ha
    exact List.mem_flatMap.mpr ⟨t, ht, ha⟩
  have hposmem : ∀ a ∈ I.symbols, I.pos a ∈ Set.Icc 0 I.span := fun a ha =>
    ⟨Nat.zero_le _, (hpos a ha).2⟩
  have hsub1 : ∀ x, x ≤ I.span → x - 1 ∈ Set.Icc 0 I.span := fun x hx =>
    ⟨Nat.zero_le _, by omega⟩
  -- the breakpoint set equals the domain
  have hset : (Finset.Icc 1 I.span).filter (fun x => p x ≠ p (x - 1) + 1) = I.domain := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hbp⟩
      by_contra hvd
      exact hbp (he.2.1 v hv hvd)
    · intro hvd
      have hvd' := hvd
      simp only [Instance.domain, List.mem_toFinset, List.mem_map] at hvd'
      obtain ⟨a, ha, rfl⟩ := hvd'
      refine ⟨Finset.mem_Icc.mpr (hpos a ha), ?_⟩
      intro hadj
      obtain ⟨t, ht, hat⟩ := List.mem_flatMap.mp ha
      obtain ⟨h1, h2, h3⟩ := he.2.2 t ht
      obtain ⟨d12, d13, d23⟩ := hdist t ht
      have hs1 : t.1 ∈ I.symbols := hmemsym t ht _ (by simp [Triple.symbols])
      have hs2 : t.2.1 ∈ I.symbols := hmemsym t ht _ (by simp [Triple.symbols])
      have hs3 : t.2.2 ∈ I.symbols := hmemsym t ht _ (by simp [Triple.symbols])
      simp only [Triple.symbols, List.mem_cons, List.not_mem_nil, or_false] at hat
      rcases hat with rfl | rfl | rfl
      · -- a = t.1 : then p (pos t.1) = p (pos t.2.1)
        have : I.pos t.1 = I.pos t.2.1 := hpinj (hposmem _ hs1) (hposmem _ hs2) (by omega)
        exact d12 (hinj hs1 hs2 this)
      · have : I.pos t.2.1 = I.pos t.2.2 := hpinj (hposmem _ hs2) (hposmem _ hs3) (by omega)
        exact d23 (hinj hs2 hs3 this)
      · have : I.pos t.2.2 = I.pos t.1 := hpinj (hposmem _ hs3) (hposmem _ hs1) (by omega)
        exact d13 (hinj hs1 hs3 this.symm)
  refine ⟨?_, ?_⟩
  · unfold breakpoints
    rw [hset]
  · unfold Instance.domain
    have hndmap : (I.symbols.map I.pos).Nodup := hnd.map_on (fun a ha b hb h => hinj ha hb h)
    rw [List.toFinset_card_of_nodup hndmap, List.length_map]
    unfold Instance.symbols
    rw [List.length_flatMap]
    simp [Triple.symbols, List.sum_replicate, mul_comm]
