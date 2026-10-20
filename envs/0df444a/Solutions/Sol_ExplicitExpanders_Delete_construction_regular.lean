-- Prove2me | solution 1 for ExplicitExpanders.Delete.construction_regular
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T04:09:12.358993+00:00
-- url     : https://prove2.me/submissions/ea288677-038e-400a-a274-ad726fafd2e8

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch

set_option autoImplicit false

namespace P2MConstrReg

open ExplicitExpanders.Delete

lemma edist_cast_lt {V : Type*} (H : SimpleGraph V) {a b : V} {r k : ℕ} (hk : k < 2 * r + 3)
    (h : ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist a b) (p : H.Walk a b) (hp : p.length = k) : False := by
  have h1 := SimpleGraph.edist_le p
  rw [hp] at h1
  have := h.trans h1
  exact absurd (by exact_mod_cast this) (not_le.mpr hk)

/-- two `U`-vertices sharing a neighbour coincide -/
lemma uniq_nbr {V : Type*} (H : SimpleGraph V) (r : ℕ) (U : Finset V)
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    {z z' x : V} (hz : z ∈ U) (hz' : z' ∈ U) (h1 : H.Adj z x) (h2 : H.Adj z' x) : z = z' := by
  by_contra hne
  exact edist_cast_lt H (k := 2) (by omega) (hU3 z hz z' hz' hne)
    (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2.symm SimpleGraph.Walk.nil)) rfl

/-- a neighbour of a `U`-vertex is not in `U` -/
lemma nbr_not_mem {V : Type*} (H : SimpleGraph V) (r : ℕ) (U : Finset V)
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    {z x : V} (hz : z ∈ U) (h1 : H.Adj z x) : x ∉ U := by
  intro hx
  exact edist_cast_lt H (k := 1) (by omega) (hU3 z hz x hx h1.ne)
    (SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil) rfl

/-- matched vertices are not adjacent in `H` -/
lemma match_not_adj {V : Type*} (H : SimpleGraph V) (r : ℕ) (hr : 1 ≤ r) (U : Finset V)
    (hU2 : ∀ z ∈ U, NoCycleOn H (ball H z (r + 1)))
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    {z z' x y : V} (hz : z ∈ U) (hz' : z' ∈ U) (h1 : H.Adj z x) (h2 : H.Adj z' y) (hxy : x ≠ y) :
    ¬ H.Adj x y := by
  intro hadj
  by_cases hzz : z = z'
  · subst hzz
    have hb : ∀ w, H.Adj z w → w ∈ ball H z (r + 1) := by
      intro w hw
      show H.edist z w ≤ ((r + 1 : ℕ) : ℕ∞)
      have := SimpleGraph.edist_le (SimpleGraph.Walk.cons hw SimpleGraph.Walk.nil)
      refine this.trans ?_
      simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
      exact_mod_cast (by omega : 0 + 1 ≤ r + 1)
    have hz0 : z ∈ ball H z (r + 1) := by
      show H.edist z z ≤ ((r + 1 : ℕ) : ℕ∞)
      simp
    have e1 : (H.induce (ball H z (r + 1))).Adj ⟨z, hz0⟩ ⟨x, hb x h1⟩ := by simpa using h1
    have e2 : (H.induce (ball H z (r + 1))).Adj ⟨x, hb x h1⟩ ⟨y, hb y h2⟩ := by simpa using hadj
    have e3 : (H.induce (ball H z (r + 1))).Adj ⟨y, hb y h2⟩ ⟨z, hz0⟩ := by simpa using h2.symm
    apply hU2 z hz (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2
      (SimpleGraph.Walk.cons e3 SimpleGraph.Walk.nil)))
    have hzx : z ≠ x := h1.ne
    have hzy : z ≠ y := h2.ne
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, hxy, hzy.symm, hzx.symm]
    · simp [SimpleGraph.Walk.edges_cons, hxy, hzx, hzy]
  · exact edist_cast_lt H (k := 3) (by omega) (hU3 z hz z' hz' hzz)
      (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons hadj
        (SimpleGraph.Walk.cons h2.symm SimpleGraph.Walk.nil))) rfl

end P2MConstrReg

namespace ExplicitExpanders.Delete

open Matrix

open Classical in
theorem constr_reg_aux {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d r : ℕ) (hreg : H.IsRegularOfDegree d) (hr : 1 ≤ r)
    (U : Finset V) (hU2 : ∀ z ∈ U, NoCycleOn H (ball H z (r + 1)))
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    (m : V → V) (hm : IsMatchingOn (nbrSet H U) m) :
    (deleteAndMatch H U m).IsRegularOfDegree d ∧
      Fintype.card (Kept U) = Fintype.card V - U.card ∧
      (deleteAndMatch H U m).adjMatrix ℝ =
        (deleted H U).adjMatrix ℝ + (matchGraph H U m).adjMatrix ℝ := by
  obtain rfl : ‹DecidableRel H.Adj› = (fun a b => Classical.propDecidable (H.Adj a b)) :=
    Subsingleton.elim _ _
  classical
  have memN : ∀ x, x ∈ nbrSet H U ↔ ∃ z ∈ U, H.Adj z x := by
    intro x; simp [nbrSet]
  -- matching adjacency
  have hMadj : ∀ v w : Kept U, (matchGraph H U m).Adj v w ↔ (v.1 ∈ nbrSet H U ∧ w.1 = m v.1) := by
    intro v w
    simp only [matchGraph, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, h | ⟨hw, hv⟩⟩
      · exact h
      · refine ⟨?_, ?_⟩
        · rw [hv]; exact (hm w.1 hw).1
        · rw [hv, (hm w.1 hw).2.1]
    · rintro ⟨hv, hw⟩
      refine ⟨?_, Or.inl ⟨hv, hw⟩⟩
      intro hvw
      apply (hm v.1 hv).2.2
      rw [← hw, hvw]
  have hdisj : ∀ v w : Kept U, (matchGraph H U m).Adj v w → ¬ (deleted H U).Adj v w := by
    intro v w hvw hd
    rw [hMadj] at hvw
    obtain ⟨hv, hw⟩ := hvw
    obtain ⟨z, hz, hzv⟩ := (memN _).1 hv
    obtain ⟨z', hz', hzw⟩ := (memN _).1 ((hm v.1 hv).1)
    have hne : v.1 ≠ m v.1 := fun h => (hm v.1 hv).2.2 h.symm
    have hd' : H.Adj v.1 w.1 := hd
    rw [hw] at hd'
    exact P2MConstrReg.match_not_adj H r hr U hU2 hU3 hz hz' hzv hzw hne hd'
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hdv := hreg v.1
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdv
    -- image of the neighbour finset in V
    set T : Finset V := ((H.neighborFinset v.1).filter (fun w => w ∉ U)) ∪
      (if v.1 ∈ nbrSet H U then {m v.1} else ∅) with hT
    have hmap : ((deleteAndMatch H U m).neighborFinset v).map
        (Function.Embedding.subtype _) = T := by
      ext w
      simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Function.Embedding.coe_subtype,
        hT, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨w', hw', rfl⟩
        rcases hw' with h | h
        · exact Or.inl ⟨h, w'.2⟩
        · rw [hMadj] at h
          right; rw [if_pos h.1]; simp [h.2]
      · rintro (⟨h, hwU⟩ | h)
        · exact ⟨⟨w, hwU⟩, Or.inl h, rfl⟩
        · by_cases hv : v.1 ∈ nbrSet H U
          · rw [if_pos hv, Finset.mem_singleton] at h
            subst h
            have hmN := (hm v.1 hv).1
            have hmU : m v.1 ∉ U := by
              obtain ⟨z, hz, hzm⟩ := (memN _).1 hmN
              exact P2MConstrReg.nbr_not_mem H r U hU3 hz hzm
            exact ⟨⟨m v.1, hmU⟩, Or.inr ((hMadj _ _).2 ⟨hv, rfl⟩), rfl⟩
          · rw [if_neg hv] at h; simp at h
    rw [← Finset.card_map, hmap, hT]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := H.neighborFinset v.1) (fun w => w ∈ U)
    rw [hdv] at hsplit
    by_cases hv : v.1 ∈ nbrSet H U
    · obtain ⟨z, hz, hzv⟩ := (memN _).1 hv
      have h1 : ((H.neighborFinset v.1).filter (fun w => w ∈ U)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨z, ?_⟩
        ext w
        simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
        constructor
        · rintro ⟨hw, hwU⟩
          exact P2MConstrReg.uniq_nbr H r U hU3 hwU hz hw.symm hzv
        · rintro rfl; exact ⟨hzv.symm, hz⟩
      rw [if_pos hv, Finset.card_union_of_disjoint]
      · simp only [Finset.card_singleton]; omega
      · rw [Finset.disjoint_singleton_right]
        simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, not_and]
        intro hadj
        obtain ⟨z', hz', hzm⟩ := (memN _).1 (hm v.1 hv).1
        exact absurd hadj (P2MConstrReg.match_not_adj H r hr U hU2 hU3 hz hz' hzv hzm
          (fun h => (hm v.1 hv).2.2 h.symm))
    · have h0 : ((H.neighborFinset v.1).filter (fun w => w ∈ U)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w hw hwU
        apply hv
        rw [memN]
        exact ⟨w, hwU, ((SimpleGraph.mem_neighborFinset _ _ _).1 hw).symm⟩
      rw [if_neg hv, Finset.union_empty]
      omega
  · rw [Fintype.card_subtype_compl, Fintype.card_coe]
  · ext i j
    simp only [SimpleGraph.adjMatrix_apply, Matrix.add_apply]
    have hsup : (deleteAndMatch H U m).Adj i j ↔ (deleted H U).Adj i j ∨ (matchGraph H U m).Adj i j :=
      Iff.rfl
    by_cases h1 : (deleted H U).Adj i j
    · have h2 : ¬ (matchGraph H U m).Adj i j := fun h => hdisj i j h h1
      rw [if_pos (hsup.2 (Or.inl h1)), if_pos h1, if_neg h2]; simp
    · by_cases h2 : (matchGraph H U m).Adj i j
      · rw [if_pos (hsup.2 (Or.inr h2)), if_neg h1, if_pos h2]; simp
      · rw [if_neg (fun h => (hsup.1 h).elim h1 h2), if_neg h1, if_neg h2]; simp

end ExplicitExpanders.Delete

open Classical ExplicitExpanders.Delete Matrix in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d r : ℕ) (hreg : H.IsRegularOfDegree d) (hr : 1 ≤ r)
    (U : Finset V) (hU2 : ∀ z ∈ U, NoCycleOn H (ball H z (r + 1)))
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    (m : V → V) (hm : IsMatchingOn (nbrSet H U) m) :
    (deleteAndMatch H U m).IsRegularOfDegree d ∧
      Fintype.card (Kept U) = Fintype.card V - U.card ∧
      (deleteAndMatch H U m).adjMatrix ℝ =
        (deleted H U).adjMatrix ℝ + (matchGraph H U m).adjMatrix ℝ := by
  exact ExplicitExpanders.Delete.constr_reg_aux H d r hreg hr U hU2 hU3 m hm
