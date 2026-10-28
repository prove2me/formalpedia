-- Prove2me | solution 1 for FarhiQAOA.Concentration.eq_26
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:09:57.274447+00:00
-- url     : https://prove2.me/submissions/98ea1408-12fc-43af-892b-b7858776d1a3

import Mathlib
import Definitions.Def_FarhiQAOA_Concentration_Setting

namespace Aux_FQ_eq26

variable {n : ℕ} (G : SimpleGraph (Fin n))

lemma F2 {u j : Fin n} {i : ℕ} (hu : G.edist u j = ((i + 1 : ℕ) : ℕ∞)) :
    ∃ w, G.Adj u w ∧ G.edist w j = (i : ℕ∞) := by
  have hr : G.Reachable u j :=
    SimpleGraph.edist_ne_top_iff_reachable.mp (by rw [hu]; exact ENat.coe_ne_top _)
  obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_edist
  cases q with
  | nil =>
    exfalso
    rw [SimpleGraph.edist_self] at hu
    have h0 : ((i + 1 : ℕ) : ℕ∞) = 0 := hu.symm
    simp at h0
  | @cons _ w _ h q' =>
    refine ⟨w, h, le_antisymm ?_ ?_⟩
    · have h1 := SimpleGraph.edist_le q'
      rw [SimpleGraph.Walk.length_cons, hu] at hq
      have h2 : q'.length + 1 = i + 1 := by exact_mod_cast hq
      have : q'.length = i := by omega
      rw [this] at h1
      exact h1
    · have htri := G.edist_triangle (u := u) (v := w) (w := j)
      rw [SimpleGraph.edist_eq_one_iff_adj.mpr h, hu, add_comm] at htri
      have : ((i : ℕ∞) + 1) ≤ G.edist w j + 1 := by simpa using htri
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this

noncomputable def D (j k : Fin n) (u : Fin n) : ℕ∞ := min (G.edist u j) (G.edist u k)

lemma D1 (j k : Fin n) {a b : Fin n} (h : G.Adj a b) : D G j k a ≤ D G j k b + 1 := by
  unfold D
  have h1 : ∀ c, G.edist a c ≤ G.edist b c + 1 := by
    intro c
    have := G.edist_triangle (u := a) (v := b) (w := c)
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr h, add_comm] at this
    exact this
  rw [← min_add_add_right]
  exact min_le_min (h1 j) (h1 k)

lemma D2 (j k : Fin n) {u : Fin n} {i : ℕ} (hu : D G j k u = ((i + 1 : ℕ) : ℕ∞)) :
    ∃ w, G.Adj u w ∧ D G j k w = (i : ℕ∞) := by
  have hfin : ∀ c, G.edist u c = ((i + 1 : ℕ) : ℕ∞) → (∃ w, G.Adj u w ∧ G.edist w c = (i : ℕ∞)) :=
    fun c hc => F2 G hc
  rcases min_choice (G.edist u j) (G.edist u k) with hm | hm
  · have hj : G.edist u j = ((i + 1 : ℕ) : ℕ∞) := by unfold D at hu; rw [hm] at hu; exact hu
    obtain ⟨w, hw, hwj⟩ := hfin j hj
    refine ⟨w, hw, le_antisymm ?_ ?_⟩
    · unfold D; exact (min_le_left _ _).trans hwj.le
    · have := D1 G j k hw
      rw [hu] at this
      have : ((i : ℕ∞) + 1) ≤ D G j k w + 1 := by simpa using this
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  · have hk : G.edist u k = ((i + 1 : ℕ) : ℕ∞) := by unfold D at hu; rw [hm] at hu; exact hu
    obtain ⟨w, hw, hwk⟩ := hfin k hk
    refine ⟨w, hw, le_antisymm ?_ ?_⟩
    · unfold D; exact (min_le_right _ _).trans hwk.le
    · have := D1 G j k hw
      rw [hu] at this
      have : ((i : ℕ∞) + 1) ≤ D G j k w + 1 := by simpa using this
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this

end Aux_FQ_eq26

open FarhiQAOA.Concentration Aux_FQ_eq26 in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : ℕ) (hv : 3 ≤ v)
    (hdeg : ∀ u, G.degree u ≤ v) (p : ℕ) (j k : Fin n) (hjk : G.Adj j k) :
    ((lightCone G p j k).card : ℝ) ≤
      2 * ((((v : ℝ) - 1) ^ (p + 1) - 1) / (((v : ℝ) - 1) - 1)) := by
  classical
  let L : ℕ → Finset (Fin n) := fun i => Finset.univ.filter (fun u => D G j k u = (i : ℕ∞))
  have hD0 : ∀ u, D G j k u = 0 → u = j ∨ u = k := by
    intro u hu
    unfold D at hu
    rcases min_choice (G.edist u j) (G.edist u k) with hm | hm
    · rw [hm, SimpleGraph.edist_eq_zero_iff] at hu; exact Or.inl hu
    · rw [hm, SimpleGraph.edist_eq_zero_iff] at hu; exact Or.inr hu
  have hDj : D G j k j = 0 := by
    unfold D; rw [SimpleGraph.edist_eq_zero_iff.mpr rfl]; simp
  have hDk : D G j k k = 0 := by
    unfold D; rw [SimpleGraph.edist_eq_zero_iff.mpr (rfl : k = k)]; simp
  -- every vertex at level i has a neighbour at level ≤ i
  have hback : ∀ i : ℕ, ∀ w, D G j k w = (i : ℕ∞) → ∃ w', G.Adj w w' ∧ D G j k w' ≤ (i : ℕ∞) := by
    intro i w hw
    rcases i with _ | i
    · rcases hD0 w (by simpa using hw) with rfl | rfl
      · exact ⟨k, hjk, by rw [hDk]; simp⟩
      · exact ⟨j, hjk.symm, by rw [hDj]; simp⟩
    · obtain ⟨w', hw', hD⟩ := D2 G j k hw
      refine ⟨w', hw', ?_⟩
      rw [hD]; exact_mod_cast Nat.le_succ i
  have hstep : ∀ i, (L (i + 1)).card ≤ (L i).card * (v - 1) := by
    intro i
    have hsub : L (i + 1) ⊆ (L i).biUnion
        (fun w => (G.neighborFinset w).filter (fun u => D G j k u = ((i + 1 : ℕ) : ℕ∞))) := by
      intro u hu
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨w, hw, hDw⟩ := D2 G j k hu
      rw [Finset.mem_biUnion]
      refine ⟨w, by simp [L, hDw], ?_⟩
      simp [SimpleGraph.mem_neighborFinset, hw.symm, hu]
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro w hw
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨w', hw'adj, hw'D⟩ := hback i w hw
    have hsub2 : (G.neighborFinset w).filter (fun u => D G j k u = ((i + 1 : ℕ) : ℕ∞)) ⊆
        (G.neighborFinset w).erase w' := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [Finset.mem_erase]
      refine ⟨?_, hu.1⟩
      rintro rfl
      rw [hu.2] at hw'D
      have : ((i + 1 : ℕ) : ℕ∞) ≤ (i : ℕ∞) := hw'D
      have := ENat.coe_le_coe.mp this
      omega
    have hmem : w' ∈ G.neighborFinset w := by rw [SimpleGraph.mem_neighborFinset]; exact hw'adj
    refine (Finset.card_le_card hsub2).trans ?_
    rw [Finset.card_erase_of_mem hmem, SimpleGraph.card_neighborFinset_eq_degree]
    have := hdeg w
    omega
  have hL0 : (L 0).card ≤ 2 := by
    have hsub : L 0 ⊆ {j, k} := by
      intro u hu
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases hD0 u (by simpa using hu) with rfl | rfl <;> simp
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  have hLi : ∀ i, (L i).card ≤ 2 * (v - 1) ^ i := by
    intro i
    induction i with
    | zero => simpa using hL0
    | succ i ih =>
      refine (hstep i).trans ?_
      rw [pow_succ]
      calc (L i).card * (v - 1) ≤ 2 * (v - 1) ^ i * (v - 1) := Nat.mul_le_mul_right _ ih
        _ = 2 * ((v - 1) ^ i * (v - 1)) := by ring
  -- the light cone is covered by levels 0..p
  have hcover : lightCone G p j k ⊆ (Finset.range (p + 1)).biUnion L := by
    intro u hu
    have hu' : G.edist u j ≤ (p : ℕ∞) ∨ G.edist u k ≤ (p : ℕ∞) := by
      unfold lightCone at hu; simpa using hu
    have hDle : D G j k u ≤ (p : ℕ∞) := by
      unfold D
      rcases hu' with h | h
      · exact (min_le_left _ _).trans h
      · exact (min_le_right _ _).trans h
    have hne : D G j k u ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top p) hDle
    obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.mp hne
    rw [Finset.mem_biUnion]
    refine ⟨i, ?_, ?_⟩
    · rw [Finset.mem_range]
      rw [← hi] at hDle
      have := ENat.coe_le_coe.mp hDle
      omega
    · simp [L, hi]
  have hcard : (lightCone G p j k).card ≤ ∑ i ∈ Finset.range (p + 1), 2 * (v - 1) ^ i :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum (fun i _ => hLi i)))
  have hcardR : ((lightCone G p j k).card : ℝ) ≤
      ∑ i ∈ Finset.range (p + 1), 2 * ((v : ℝ) - 1) ^ i := by
    have h := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at h
    have hv1 : ((v - 1 : ℕ) : ℝ) = (v : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    simpa [hv1] using h
  rw [← Finset.mul_sum, geom_sum_eq] at hcardR
  · exact hcardR
  · have : (3 : ℝ) ≤ v := by exact_mod_cast hv
    linarith
