-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.optimal_augmented_projection
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:17:31.804276+00:00
-- url     : https://prove2.me/submissions/c414e6c0-d561-45a1-888b-51fe36d87870

import Definitions.Def_ChenCapacityTerminals_Exact_ExactExecution

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem solution (G : Network) (r : ℕ) (J : Finset ℕ) (U : ℝ) (z : ℕ)
    (hG : G.Valid) (hr : r ∈ G.vertices) (hJ : J ⊆ G.vertices \ {r}) (hz : z ∉ G.vertices)
    (X : Finset ℕ) (hX : OptimalPair (enclosureNetwork G J U z) r z X) :
    Enclosure G r J U (X.erase z) := by
  classical
  have hcut (S : Finset ℕ) (hS : S ⊆ G.vertices) (hzS : z ∉ S) :
      cut (enclosureNetwork G J U z) (insert z S) =
        cut G S + U * ((J \ S).card : ℝ) := by
    have hcomp : insert z G.vertices \ insert z S = G.vertices \ S := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    have horig :
        (G.arcs.map fun e => if e.tail ∈ G.vertices \ S ∧
          e.head ∈ insert z S then e.capacity else 0).sum =
        (G.arcs.map fun e => if e.tail ∈ G.vertices \ S ∧
          e.head ∈ S then e.capacity else 0).sum := by
      congr 1
      apply List.map_congr_left
      intro e he
      have he' := hG e he
      have hhead : e.head ≠ z := by
        intro heq
        apply hz
        rw [← heq]
        exact he'.2.1
      simp [hhead]
    have hadd :
        ((J.toList.map fun t => Arc.mk t z U).map fun e =>
          if e.tail ∈ G.vertices \ S ∧ e.head ∈ insert z S then e.capacity else 0).sum =
          U * ((J \ S).card : ℝ) := by
      have hmap :
          (J.toList.map fun t => Arc.mk t z U).map (fun e =>
            if e.tail ∈ G.vertices \ S ∧ e.head ∈ insert z S then e.capacity else 0) =
            J.toList.map (fun t => if t ∈ J \ S then U else 0) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro t ht
        have htJ : t ∈ J := Finset.mem_toList.mp ht
        have htG : t ∈ G.vertices := (Finset.mem_sdiff.mp (hJ htJ)).1
        have htz : t ≠ z := by
          intro heq
          apply hz
          rw [← heq]
          exact htG
        by_cases htS : t ∈ S <;>
          simp [htJ, htG, htz, htS]
      rw [hmap, ← List.sum_toFinset (fun t => if t ∈ J \ S then U else 0) J.nodup_toList]
      simp only [Finset.toList_toFinset]
      rw [Finset.sum_ite_mem]
      have hJJ : J ∩ (J \ S) = J \ S := Finset.inter_eq_right.mpr Finset.sdiff_subset
      rw [hJJ]
      simp [nsmul_eq_mul, mul_comm]
    simp only [cut, weight, enclosureNetwork, List.map_append, List.sum_append, hcomp]
    rw [horig, hadd]
  rcases hX with ⟨⟨⟨hXsub, hXne, hrX⟩, hzX⟩, hmin⟩
  have hBsub : X.erase z ⊆ G.vertices := by
    intro v hv
    have hvX : v ∈ X := Finset.mem_of_mem_erase hv
    have hvne : v ≠ z := (Finset.mem_erase.mp hv).1
    have hv' := hXsub hvX
    simpa only [enclosureNetwork, Finset.mem_insert, hvne, false_or] using hv'
  have hzB : z ∉ X.erase z := by simp
  have hXB : insert z (X.erase z) = X := Finset.insert_erase hzX
  have hrB : r ∉ X.erase z := fun h => hrX (Finset.mem_of_mem_erase h)
  refine ⟨?_, ?_⟩
  · intro v hv
    refine Finset.mem_sdiff.mpr ⟨hBsub hv, ?_⟩
    simp only [Finset.mem_singleton]
    intro hvr
    subst v
    exact hrB hv
  · intro Y hY
    have hYsub : Y ⊆ G.vertices := fun v hv => (Finset.mem_sdiff.mp (hY hv)).1
    have hzY : z ∉ Y := fun h => hz (hYsub h)
    have hrY : r ∉ Y := fun h => (Finset.mem_sdiff.mp (hY h)).2 (by simp)
    have hrz : r ≠ z := by
      intro heq
      apply hz
      rw [← heq]
      exact hr
    have hYpair : PairSide (enclosureNetwork G J U z) r z (insert z Y) := by
      refine ⟨⟨?_, ?_, ?_⟩, Finset.mem_insert_self z Y⟩
      · intro v hv
        simp only [enclosureNetwork, Finset.mem_insert] at hv ⊢
        rcases hv with rfl | hv
        · exact Or.inl rfl
        · exact Or.inr (hYsub hv)
      · exact Finset.insert_nonempty z Y
      · simp [hrY, hrz]
    have hle := hmin (insert z Y) hYpair
    rw [← hXB, hcut (X.erase z) hBsub hzB, hcut Y hYsub hzY] at hle
    have hcardB : ((J ∩ X.erase z).card : ℝ) + ((J \ X.erase z).card : ℝ) = J.card := by
      exact_mod_cast Finset.card_inter_add_card_sdiff J (X.erase z)
    have hcardY : ((J ∩ Y).card : ℝ) + ((J \ Y).card : ℝ) = J.card := by
      exact_mod_cast Finset.card_inter_add_card_sdiff J Y
    have heqB : cut G (X.erase z) + U * ((J \ X.erase z).card : ℝ) =
        enclosureObjective G J (X.erase z) U + U * J.card := by
      unfold enclosureObjective
      linear_combination U * hcardB
    have heqY : cut G Y + U * ((J \ Y).card : ℝ) =
        enclosureObjective G J Y U + U * J.card := by
      unfold enclosureObjective
      linear_combination U * hcardY
    rw [heqB, heqY] at hle
    linarith
