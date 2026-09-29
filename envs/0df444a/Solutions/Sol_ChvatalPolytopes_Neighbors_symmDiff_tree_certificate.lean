-- Prove2me | solution 1 for ChvatalPolytopes.Neighbors.symmDiff_tree_certificate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:16:30.59934+00:00
-- url     : https://prove2.me/submissions/875045e6-c65f-405f-b99b-784101256fba

import Mathlib
import Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope
import Definitions.Def_ChvatalPolytopes_Neighbors_IsBicoloration



namespace ChvatalPolytopes.Neighbors

lemma ct_cases {V : Type*} [DecidableEq V] (S : Finset V) (u : V) :
    incidenceVector S u = 1 ∧ u ∈ S ∨ incidenceVector S u = 0 ∧ u ∉ S := by
  unfold incidenceVector; by_cases h : u ∈ S <;> simp [h]

lemma ct_ind {V : Type*} [DecidableEq V] (Y Z : Finset V) (x : V → ℝ) :
    x = incidenceVector Y ↔ (∀ u ∈ (Y \ Z ∪ Z \ Y), x u = if u ∈ Y \ Z then 1 else 0) ∧
      (∀ u, u ∉ (Y \ Z ∪ Z \ Y) → x u = (fun u => if u ∈ Y ∩ Z then (1:ℝ) else 0) u) := by
  constructor
  · intro h
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rw [h]; simp only [incidenceVector, Finset.mem_union, Finset.mem_sdiff] at hu ⊢
      by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hy, hz] at hu ⊢
    · rw [h]; simp only [incidenceVector, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_inter] at hu ⊢
      by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hy, hz] at hu ⊢
  · rintro ⟨h, h'⟩; funext u
    by_cases hu : u ∈ (Y \ Z ∪ Z \ Y)
    · rw [h u hu]; simp only [incidenceVector, Finset.mem_union, Finset.mem_sdiff] at hu ⊢
      by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hy, hz] at hu ⊢
    · rw [h' u hu]; simp only [incidenceVector, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_inter] at hu ⊢
      by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hy, hz] at hu ⊢

theorem ct_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Y Z : Finset V)
    (hY : G.IsIndepSet (Y : Set V)) (hZ : G.IsIndepSet (Z : Set V))
    (T : SimpleGraph (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V))
    (hTsub : T ≤ G.induce (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V))
    (c' : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) → ℕ) (m : ℕ)
    (hc' : ∀ x ∈ stableVectors T,
      (∑ u, (c' u : ℝ) * x u ≤ (m : ℝ)) ∧
      (∑ u, (c' u : ℝ) * x u = (m : ℝ) ↔
        x = incidenceVector (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Y \ Z) ∨
        x = incidenceVector (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Z \ Y))) :
    let c : V → ℤ := fun u =>
      if h : u ∈ (Y \ Z) ∪ (Z \ Y) then (c' ⟨u, by simpa using h⟩ : ℤ)
      else if u ∈ Y ∩ Z then 1 else -1
    ∀ x ∈ stableVectors G,
      (∑ u, (c u : ℝ) * x u ≤ (m : ℝ) + ((Y ∩ Z).card : ℝ)) ∧
      (∑ u, (c u : ℝ) * x u = (m : ℝ) + ((Y ∩ Z).card : ℝ) ↔
        x = incidenceVector Y ∨ x = incidenceVector Z) := by
  intro c
  rintro x ⟨S, hS, rfl⟩
  set x := incidenceVector S with hx
  -- restriction
  set xr : (↑(Y \ Z ∪ Z \ Y) : Set V) → ℝ := fun a => x a.1 with hxr
  have hxr_mem : xr ∈ stableVectors T := by
    refine ⟨Finset.univ.filter fun a : (↑(Y \ Z ∪ Z \ Y) : Set V) => a.1 ∈ S, ?_, ?_⟩
    · intro a ha b hb hab hadj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have := hTsub hadj
      rw [SimpleGraph.comap_adj] at this
      exact hS ha hb (fun h => hab (Subtype.ext h)) this
    · funext a; simp [hxr, hx, incidenceVector]
  obtain ⟨h1, h2⟩ := hc' xr hxr_mem
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun u => u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V))
    (fun u => (c u : ℝ) * x u)
  have hfirst : (∑ i : {u // u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, (c i.1 : ℝ) * x i.1) = ∑ u, (c' u : ℝ) * xr u := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha : a.1 ∈ (Y \ Z ∪ Z \ Y) := by simpa using a.2
    simp only [c, dif_pos ha, hxr]
    norm_num
  -- second sum
  set g : V → ℝ := fun u => if u ∈ Y ∩ Z then 1 else 0 with hg
  have hle2 : ∀ i : {u // ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, (c i.1 : ℝ) * x i.1 ≤ g i.1 := by
    intro i
    have hi : i.1 ∉ (Y \ Z ∪ Z \ Y) := by simpa using i.2
    simp only [c, dif_neg hi, hg]
    rcases ct_cases S i.1 with ⟨hu, _⟩ | ⟨hu, _⟩ <;> rw [hx, hu] <;>
      by_cases h : i.1 ∈ Y ∩ Z <;> simp [h]
  have hg_sum : (∑ i : {u // ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, g i.1) = ((Y ∩ Z).card : ℝ) := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun u => u ∉ (Y \ Z ∪ Z \ Y)) (p := fun u => ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V))
      (by intro u; simp)]
    rw [Finset.sum_filter, hg]
    simp only
    rw [← Finset.sum_filter]
    have : (Finset.univ.filter fun u => u ∉ (Y \ Z ∪ Z \ Y) ∧ u ∈ Y ∩ Z) = Y ∩ Z := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.filter_filter, this]
  have hsecond_le : (∑ i : {u // ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, (c i.1 : ℝ) * x i.1) ≤ ((Y ∩ Z).card : ℝ) := by
    rw [← hg_sum]; exact Finset.sum_le_sum fun i _ => hle2 i
  have htot : ∑ u, (c u : ℝ) * x u = (∑ u, (c' u : ℝ) * xr u) +
      ∑ i : {u // ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, (c i.1 : ℝ) * x i.1 := by
    rw [← hsplit, ← hfirst]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext a
    simp
  refine ⟨by rw [htot]; linarith, ?_⟩
  -- outside condition
  set O : Prop := ∀ u, u ∉ (Y \ Z ∪ Z \ Y) → x u = g u with hO
  have hsecond_eq : (∑ i : {u // ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, (c i.1 : ℝ) * x i.1) = ((Y ∩ Z).card : ℝ) ↔ O := by
    rw [← hg_sum, Finset.sum_eq_sum_iff_of_le (fun i _ => hle2 i)]
    constructor
    · intro h u hu
      have := h ⟨u, by simpa using hu⟩ (Finset.mem_univ _)
      simp only [c, dif_neg hu, hg] at this ⊢
      rcases ct_cases S u with ⟨hu', _⟩ | ⟨hu', _⟩ <;> rw [hx, hu'] at this ⊢ <;>
        by_cases h : u ∈ Y ∩ Z <;> simp [h] at this ⊢
    · intro h i _
      have hi : i.1 ∉ (Y \ Z ∪ Z \ Y) := by simpa using i.2
      have := h i.1 hi
      simp only [c, dif_neg hi, hg] at this ⊢
      rw [this]; by_cases h' : i.1 ∈ Y ∩ Z <;> simp [h']
  have hTot_eq : (∑ u, (c u : ℝ) * x u = (m : ℝ) + ((Y ∩ Z).card : ℝ)) ↔
      (∑ u, (c' u : ℝ) * xr u = m) ∧ O := by
    rw [htot, ← hsecond_eq]
    constructor
    · intro h; constructor <;> linarith
    · rintro ⟨h, h'⟩; rw [h, h']
  rw [hTot_eq, h2]
  have hA : ∀ W : Finset V, xr = incidenceVector (Finset.univ.filter fun u : (↑(Y \ Z ∪ Z \ Y) : Set V) => u.1 ∈ W) ↔
      ∀ u ∈ (Y \ Z ∪ Z \ Y), x u = if u ∈ W then 1 else 0 := by
    intro W
    constructor
    · intro h u hu
      have := congrFun h ⟨u, by simpa using hu⟩
      simpa [hxr, incidenceVector] using this
    · intro h; funext a
      have ha : a.1 ∈ (Y \ Z ∪ Z \ Y) := by simpa using a.2
      simp [hxr, incidenceVector, h a.1 ha]
  have hYc := ct_ind Y Z x
  have hZc := ct_ind Z Y x
  rw [Finset.union_comm (Z \ Y), Finset.inter_comm Z Y] at hZc
  rw [hA, hA, hYc, hZc]
  constructor
  · rintro ⟨h | h, h'⟩
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact ⟨Or.inl h, h'⟩
    · exact ⟨Or.inr h, h'⟩

end ChvatalPolytopes.Neighbors

open ChvatalPolytopes.Neighbors


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Y Z : Finset V)
    (hY : G.IsIndepSet (Y : Set V)) (hZ : G.IsIndepSet (Z : Set V))
    (hH : (G.induce (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V)).Connected)
    (T : SimpleGraph (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V))
    (hTsub : T ≤ G.induce (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V)) (hT : T.IsTree)
    (c' : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) → ℕ) (m : ℕ)
    (hc' : ∀ x ∈ stableVectors T,
      (∑ u, (c' u : ℝ) * x u ≤ (m : ℝ)) ∧
      (∑ u, (c' u : ℝ) * x u = (m : ℝ) ↔
        x = incidenceVector (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Y \ Z) ∨
        x = incidenceVector (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Z \ Y))) :
    let c : V → ℤ := fun u =>
      if h : u ∈ (Y \ Z) ∪ (Z \ Y) then (c' ⟨u, by simpa using h⟩ : ℤ)
      else if u ∈ Y ∩ Z then 1 else -1
    ∀ x ∈ stableVectors G,
      (∑ u, (c u : ℝ) * x u ≤ (m : ℝ) + ((Y ∩ Z).card : ℝ)) ∧
      (∑ u, (c u : ℝ) * x u = (m : ℝ) + ((Y ∩ Z).card : ℝ) ↔
        x = incidenceVector Y ∨ x = incidenceVector Z) := by
  exact ct_core G Y Z hY hZ T hTsub c' m hc'
