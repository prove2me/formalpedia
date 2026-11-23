-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.enclosure_properties
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:32:47.630739+00:00
-- url     : https://prove2.me/submissions/1955b630-35c3-4fca-97fe-d48c250c4db7

import Definitions.Def_ChenCapacityTerminals_Exact_ExactExecution

set_option autoImplicit false

open scoped BigOperators
open ChenCapacityTerminals.Exact

theorem solution (G : Network) (r : ℕ) (J : Finset ℕ) (U : ℝ)
    (b : ℕ → ℕ) (hG : G.Valid) (hJ : J ⊆ G.vertices \ {r}) (hU : 0 < U)
    (B : Finset ℕ) (hB : Enclosure G r J U B) :
    (∀ t ∈ J \ B, ∀ X, PairSide G r t X → U ≤ cut G X) ∧
    (∀ t ∈ J ∩ B, ∃ X, OptimalPair G r t X ∧ X ⊆ B) ∧
    cut G B ≤ U * (J ∩ B).card ∧
    (∀ η : ℝ, 0 < η → Conditioned G r b η →
      (mass b B : ℝ) ≤ U / η * (J ∩ B).card) := by
  classical
  have cut_empty : cut G ∅ = 0 := by simp [cut, weight]
  have cut_nonneg (X : Finset ℕ) : 0 ≤ cut G X := by
    unfold cut weight
    apply List.sum_nonneg
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    split_ifs
    · exact (hG e he).2.2
    · exact le_rfl
  have cut_submodular (A C : Finset ℕ) :
      cut G (A ∪ C) + cut G (A ∩ C) ≤ cut G A + cut G C := by
    have arcwise : ∀ xs : List Arc,
        (∀ e ∈ xs, e.tail ∈ G.vertices ∧ e.head ∈ G.vertices) →
        (∀ e ∈ xs, 0 ≤ e.capacity) →
        (xs.map fun e => if e.tail ∈ G.vertices \ (A ∪ C) ∧ e.head ∈ A ∪ C
          then e.capacity else 0).sum +
        (xs.map fun e => if e.tail ∈ G.vertices \ (A ∩ C) ∧ e.head ∈ A ∩ C
          then e.capacity else 0).sum ≤
        (xs.map fun e => if e.tail ∈ G.vertices \ A ∧ e.head ∈ A
          then e.capacity else 0).sum +
        (xs.map fun e => if e.tail ∈ G.vertices \ C ∧ e.head ∈ C
          then e.capacity else 0).sum := by
      intro xs
      induction xs with
      | nil => intros; simp
      | cons e xs ih =>
          intro hvalid hnonneg
          simp only [List.map_cons, List.sum_cons]
          obtain ⟨hetV, hehV⟩ := hvalid e (by simp)
          have he : 0 ≤ e.capacity := hnonneg e (by simp)
          have htail : ∀ a ∈ xs, 0 ≤ a.capacity := by
            intro a ha
            exact hnonneg a (by simp [ha])
          have hvalidTail : ∀ a ∈ xs, a.tail ∈ G.vertices ∧ a.head ∈ G.vertices := by
            intro a ha
            exact hvalid a (by simp [ha])
          have hi := ih hvalidTail htail
          have hterm :
              (if e.tail ∈ G.vertices \ (A ∪ C) ∧ e.head ∈ A ∪ C
                then e.capacity else 0) +
              (if e.tail ∈ G.vertices \ (A ∩ C) ∧ e.head ∈ A ∩ C
                then e.capacity else 0) ≤
              (if e.tail ∈ G.vertices \ A ∧ e.head ∈ A
                then e.capacity else 0) +
              (if e.tail ∈ G.vertices \ C ∧ e.head ∈ C
                then e.capacity else 0) := by
            simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
            by_cases hta : e.tail ∈ A <;>
            by_cases htc : e.tail ∈ C <;>
            by_cases hha : e.head ∈ A <;>
            by_cases hhc : e.head ∈ C <;>
              simp [hta, htc, hha, hhc, hetV] <;> nlinarith
          linarith
    unfold cut weight
    exact arcwise G.arcs (fun e he => ⟨(hG e he).1, (hG e he).2.1⟩)
      (fun e he => (hG e he).2.2)
  have nonroot_of_pair {t : ℕ} {S : Finset ℕ} (hS : PairSide G r t S) :
      S ⊆ G.vertices \ {r} := by
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨hS.1.1 hv, ?_⟩
    intro hvr
    subst v
    exact hS.1.2.2 hv
  have comparison (S : Finset ℕ) (hS : S ⊆ G.vertices \ {r}) :
      U * (J ∩ (S \ B)).card ≤ cut G S - cut G (S ∩ B) := by
    have hBS : B ∪ S ⊆ G.vertices \ {r} := Finset.union_subset hB.1 hS
    have hmin := hB.2 (B ∪ S) hBS
    have hset : J ∩ (B ∪ S) = (J ∩ B) ∪ (J ∩ (S \ B)) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      tauto
    have hdisj : Disjoint (J ∩ B) (J ∩ (S \ B)) := by
      rw [Finset.disjoint_left]
      intro v hvB hvS
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hvS).2).2
        (Finset.mem_inter.mp hvB).2
    unfold enclosureObjective at hmin
    rw [hset, Finset.card_union_of_disjoint hdisj] at hmin
    push_cast at hmin
    rw [Finset.union_comm B S] at hmin
    have hsub := cut_submodular S B
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht S hS
    have htJ : t ∈ J := (Finset.mem_sdiff.mp ht).1
    have htB : t ∉ B := (Finset.mem_sdiff.mp ht).2
    have htS : t ∈ S := hS.2
    have hcmp := comparison S (nonroot_of_pair hS)
    have htmem : t ∈ J ∩ (S \ B) := by simp [htJ, htS, htB]
    have hcard : (1 : ℝ) ≤ (J ∩ (S \ B)).card := by
      exact_mod_cast (Finset.card_pos.mpr ⟨t, htmem⟩)
    calc
      U = U * 1 := by ring
      _ ≤ U * (J ∩ (S \ B)).card := mul_le_mul_of_nonneg_left hcard hU.le
      _ ≤ cut G S - cut G (S ∩ B) := hcmp
      _ ≤ cut G S := by linarith [cut_nonneg (S ∩ B)]
  · intro t ht
    have htJ : t ∈ J := (Finset.mem_inter.mp ht).1
    have htB : t ∈ B := (Finset.mem_inter.mp ht).2
    have htV : t ∈ G.vertices := (Finset.mem_sdiff.mp (hJ htJ)).1
    have htr : t ≠ r := by simpa using (Finset.mem_sdiff.mp (hJ htJ)).2
    let sides : Finset (Finset ℕ) := G.vertices.powerset.filter (PairSide G r t)
    have htSide : PairSide G r t {t} := by
      refine ⟨⟨?_, ⟨t, by simp⟩, ?_⟩, by simp⟩
      · intro v hv
        have hvt : v = t := by simpa using hv
        simpa [hvt] using htV
      · intro hrt
        have hrt' : r = t := by simpa using hrt
        exact htr hrt'.symm
    have hsides : sides.Nonempty := by
      refine ⟨{t}, ?_⟩
      simp [sides, htSide, htV]
    obtain ⟨S, hSsides, hSmin⟩ := Finset.exists_min_image sides (cut G) hsides
    have hSside : PairSide G r t S := (Finset.mem_filter.mp hSsides).2
    have hSopt : OptimalPair G r t S := by
      refine ⟨hSside, ?_⟩
      intro Y hY
      apply hSmin
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hY.1.1, hY⟩
    have hcmp := comparison S (nonroot_of_pair hSside)
    have hnonneg : 0 ≤ U * (J ∩ (S \ B)).card := by positivity
    have hle : cut G (S ∩ B) ≤ cut G S := by linarith
    have htSB : t ∈ S ∩ B := Finset.mem_inter.mpr ⟨hSside.2, htB⟩
    have hSBside : PairSide G r t (S ∩ B) := by
      refine ⟨⟨?_, ⟨t, htSB⟩, ?_⟩, htSB⟩
      · exact (Finset.inter_subset_left.trans hSside.1.1)
      · intro hrSB
        exact hSside.1.2.2 (Finset.mem_inter.mp hrSB).1
    refine ⟨S ∩ B, ⟨hSBside, ?_⟩, Finset.inter_subset_right⟩
    intro Y hY
    have hSY : cut G S ≤ cut G Y := hSopt.2 Y hY
    linarith
  · have hmin := hB.2 ∅ (by simp)
    unfold enclosureObjective at hmin
    simp [cut_empty] at hmin
    linarith
  · intro η hη hcond
    have hmb := hcond B hB.1
    have hcut := hB.2 ∅ (by simp)
    unfold enclosureObjective at hcut
    simp [cut_empty] at hcut
    have hmain : η * (mass b B : ℝ) ≤ U * (J ∩ B).card := by linarith
    calc
      (mass b B : ℝ) ≤ (U * (J ∩ B).card) / η :=
        (le_div_iff₀ hη).2 (by nlinarith [hmain])
      _ = U / η * (J ∩ B).card := by ring
