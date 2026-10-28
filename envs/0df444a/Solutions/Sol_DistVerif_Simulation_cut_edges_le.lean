-- Prove2me | solution 1 for DistVerif.Simulation.cut_edges_le
-- status  : ACCEPTED   (prove)
-- author  : @rgmohan
-- created : 2026-10-27T05:15:49.862981+00:00
-- url     : https://prove2.me/submissions/a676935b-6b5c-4ac0-b32d-4af82038ef6d

import Mathlib
import Definitions.Def_DistVerif_Simulation_Network

open DistVerif.Simulation

/-! Proof of `DistVerif.Simulation.cut_edges_le` (Das Sarma et al., §3.3, sentence before
Lemma 3.4): at most `d·p` ordered edges go from `V \ R_{t-1}` into `R_t`, and likewise for `L`.

Strategy. A tree node `u^ℓ_k` sits above exactly the leaf block `[k·D, k·D + D)`, `D = d^(p-ℓ)`.
Path, spoke and parent→child edges can never cross the cut, so every crossing edge goes from a
child `u^m_c` to its parent `u^{m-1}_{c/d}`. At a fixed level all crossing children share one
parent (a crossing child's block lies strictly on one side of the threshold, a crossing parent
has a leaf on the other side), so `(w, u) ↦ (m - 1, c % d)` injects the crossing edges into
`[0, p) × [0, d)`. -/

namespace CutEdgesLeAux

/-- `j / D = k` pins `j` to the block `[k·D, k·D + D)`. -/
theorem block_bounds {D j k : ℕ} (hD : 0 < D) (h : j / D = k) : k * D ≤ j ∧ j < k * D + D := by
  have h1 := Nat.div_add_mod' j D
  have h2 := Nat.mod_lt j hD
  rw [h] at h1
  constructor <;> omega

/-- A leaf below child `c` (block size `D`) is below the parent `c / d` (block size `D·d`). -/
theorem up_div {j D c d k : ℕ} (h1 : j / D = c) (h2 : c / d = k) : j / (D * d) = k := by
  rw [← Nat.div_div_eq_div_mul, h1, h2]

/-- The leaf block of `u^ℓ_k` lies inside `[0, d^p)`. -/
theorem block_fits {d p : ℕ} (ℓ : Fin (p + 1)) (k : Fin (d ^ (ℓ : ℕ))) :
    (k : ℕ) * d ^ (p - ℓ) + d ^ (p - ℓ) ≤ d ^ p := by
  have hl : (ℓ : ℕ) ≤ p := Nat.lt_succ_iff.mp ℓ.isLt
  have hsplit : d ^ p = d ^ (ℓ : ℕ) * d ^ (p - ℓ) := by
    rw [← pow_add, Nat.add_sub_cancel' hl]
  rw [hsplit, ← Nat.succ_mul]
  exact Nat.mul_le_mul_right _ k.isLt

/-- Generic counting step shared by both halves: if every pair in `S` is a (child, parent) tree
edge, and at equal child levels the parents are ordered both ways (hence equal), then
`|S| ≤ d·p`, via the injection `(u^m_c, parent) ↦ (m - 1, c mod d)`. -/
theorem count_generic (Γ d p : ℕ) (hd : 0 < d) (S : Finset (Vtx Γ d p × Vtx Γ d p))
    (hclass : ∀ q ∈ S, ∃ (m : Fin (p + 1)) (c : Fin (d ^ (m : ℕ))) (m' : Fin (p + 1))
      (k : Fin (d ^ (m' : ℕ))),
      q = (Sum.inr ⟨m, c⟩, Sum.inr ⟨m', k⟩) ∧ (m' : ℕ) + 1 = m ∧ (c : ℕ) / d = k)
    (hcmp : ∀ (m₁ : Fin (p + 1)) (c₁ : Fin (d ^ (m₁ : ℕ))) (m₁' : Fin (p + 1))
      (k₁ : Fin (d ^ (m₁' : ℕ))) (m₂ : Fin (p + 1)) (c₂ : Fin (d ^ (m₂ : ℕ)))
      (m₂' : Fin (p + 1)) (k₂ : Fin (d ^ (m₂' : ℕ))),
      ((Sum.inr ⟨m₁, c₁⟩, Sum.inr ⟨m₁', k₁⟩) : Vtx Γ d p × Vtx Γ d p) ∈ S →
      ((Sum.inr ⟨m₂, c₂⟩, Sum.inr ⟨m₂', k₂⟩) : Vtx Γ d p × Vtx Γ d p) ∈ S →
      (m₁' : ℕ) + 1 = m₁ → (c₁ : ℕ) / d = k₁ → (m₂' : ℕ) + 1 = m₂ → (c₂ : ℕ) / d = k₂ →
      (m₁ : ℕ) = m₂ → (k₁ : ℕ) ≤ k₂) :
    S.card ≤ d * p := by
  let f : Vtx Γ d p × Vtx Γ d p → ℕ × ℕ := fun q =>
    match q.1 with
    | Sum.inr ⟨m, c⟩ => ((m : ℕ) - 1, (c : ℕ) % d)
    | Sum.inl _ => (0, 0)
  have hcard : (Finset.range p ×ˢ Finset.range d).card = d * p := by
    rw [Finset.card_product, Finset.card_range, Finset.card_range, Nat.mul_comm]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn f
  · intro q hq
    obtain ⟨m, c, m', k, rfl, hl, hk⟩ := hclass q hq
    simp only [f, Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio]
    exact ⟨by have := m'.isLt; omega, Nat.mod_lt _ hd⟩
  · intro q₁ hq₁ q₂ hq₂ hf
    obtain ⟨m₁, c₁, m₁', k₁, rfl, hl₁, hk₁⟩ := hclass q₁ hq₁
    obtain ⟨m₂, c₂, m₂', k₂, rfl, hl₂, hk₂⟩ := hclass q₂ hq₂
    simp only [f, Prod.mk.injEq] at hf
    obtain ⟨hm, hc⟩ := hf
    have hm12 : (m₁ : ℕ) = m₂ := by omega
    have hk12 : (k₁ : ℕ) = k₂ := le_antisymm
      (hcmp _ _ _ _ _ _ _ _ hq₁ hq₂ hl₁ hk₁ hl₂ hk₂ hm12)
      (hcmp _ _ _ _ _ _ _ _ hq₂ hq₁ hl₂ hk₂ hl₁ hk₁ hm12.symm)
    -- Same parent and same remainder mod `d` give the same child.
    have hcc : (c₁ : ℕ) = c₂ := by
      have e1 := Nat.div_add_mod (c₁ : ℕ) d
      have e2 := Nat.div_add_mod (c₂ : ℕ) d
      rw [hk₁, hk12] at e1
      rw [hk₂] at e2
      omega
    have hmm : m₁ = m₂ := Fin.ext hm12
    subst hmm
    have hcc' : c₁ = c₂ := Fin.ext hcc
    subst hcc'
    have hmm' : m₁' = m₂' := Fin.ext (by omega)
    subst hmm'
    have hkk : k₁ = k₂ := Fin.ext hk12
    subst hkk
    rfl

/-- The `R` half: at most `d·p` edges from `V \ R_{t-1}` into `R_t`. -/
theorem R_side (Γ d p t : ℕ) (ht0 : 0 < t) (hd : 0 < d) :
    (Finset.univ.filter fun q : Vtx Γ d p × Vtx Γ d p =>
        (graph Γ d p).Adj q.1 q.2 ∧ q.1 ∉ R Γ d p (t - 1) ∧ q.2 ∈ R Γ d p t).card ≤ d * p := by
  have hDpos : ∀ n : ℕ, 0 < d ^ n := fun n => pow_pos hd n
  have ht : t ≠ 0 := by omega
  -- Vertices outside `R_{t-1}` lie strictly left of `t` (weak form, uniform in `t`).
  have hout_path : ∀ (a : Fin Γ) (j : Fin (d ^ p)),
      (Sum.inl (a, j) : Vtx Γ d p) ∉ R Γ d p (t - 1) → (j : ℕ) + 1 < t := by
    intro a j h
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, InRight] at h
    omega
  have hout_tree : ∀ (ℓ : Fin (p + 1)) (k : Fin (d ^ (ℓ : ℕ))),
      (Sum.inr ⟨ℓ, k⟩ : Vtx Γ d p) ∉ R Γ d p (t - 1) →
        (k : ℕ) * d ^ (p - ℓ) + d ^ (p - ℓ) ≤ t := by
    intro ℓ k h
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, InRight] at h
    have hb := block_fits ℓ k
    have hp := hDpos (p - ℓ)
    split_ifs at h with h0
    · -- `t = 1`: the only vertex outside `R_0` is `s = u^p_0`.
      obtain ⟨h1, h2⟩ := not_not.mp h
      have h3 : d ^ (p - (ℓ : ℕ)) = 1 := by rw [h1, Nat.sub_self, pow_zero]
      rw [h3, h2]
      omega
    · -- otherwise the rightmost leaf of the block is `< t - 1`.
      by_contra hc
      apply h
      refine ⟨⟨(k : ℕ) * d ^ (p - ℓ) + (d ^ (p - ℓ) - 1), by omega⟩, ?_, ?_⟩
      · show t - 1 ≤ (k : ℕ) * d ^ (p - ℓ) + (d ^ (p - ℓ) - 1)
        omega
      · show ((k : ℕ) * d ^ (p - ℓ) + (d ^ (p - ℓ) - 1)) / d ^ (p - ℓ) = k
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (by omega), zero_add]
  -- Vertices inside `R_t` have a leaf `≥ t`.
  have hin_path : ∀ (a : Fin Γ) (j : Fin (d ^ p)),
      (Sum.inl (a, j) : Vtx Γ d p) ∈ R Γ d p t → t ≤ (j : ℕ) := by
    intro a j h
    simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and, InRight] using h
  have hin_tree : ∀ (ℓ : Fin (p + 1)) (k : Fin (d ^ (ℓ : ℕ))),
      (Sum.inr ⟨ℓ, k⟩ : Vtx Γ d p) ∈ R Γ d p t → ∃ j : ℕ, t ≤ j ∧ j / d ^ (p - ℓ) = k := by
    intro ℓ k h
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, InRight, if_neg ht] at h
    obtain ⟨j, h1, h2⟩ := h
    exact ⟨j, h1, h2⟩
  apply count_generic Γ d p hd
  · -- Every crossing edge is (child, parent).
    intro q hq
    obtain ⟨v, w⟩ := q
    obtain ⟨hadj, hv, hw⟩ := (Finset.mem_filter.mp hq).2
    dsimp only at hadj hv hw
    rw [graph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, hrel⟩ := hadj
    rcases v with ⟨a, j⟩ | ⟨m, c⟩ <;> rcases w with ⟨a', j'⟩ | ⟨m', k⟩
    · exfalso
      have h1 := hout_path a j hv
      have h2 := hin_path a' j' hw
      simp only [baseRel] at hrel
      rcases hrel with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    · exfalso
      have h1 := hout_path a j hv
      obtain ⟨j2, hj2, hj2'⟩ := hin_tree m' k hw
      simp only [baseRel, false_or] at hrel
      obtain ⟨hm, hk⟩ := hrel
      have h3 : d ^ (p - (m' : ℕ)) = 1 := by rw [hm, Nat.sub_self, pow_zero]
      rw [h3, Nat.div_one] at hj2'
      omega
    · exfalso
      have h1 := hout_tree m c hv
      have h2 := hin_path a' j' hw
      simp only [baseRel, or_false] at hrel
      obtain ⟨hm, hk⟩ := hrel
      have h3 : d ^ (p - (m : ℕ)) = 1 := by rw [hm, Nat.sub_self, pow_zero]
      rw [h3] at h1
      omega
    · simp only [baseRel] at hrel
      rcases hrel with ⟨hl, hk⟩ | ⟨hl, hk⟩
      · -- parent → child: the child's leaf `≥ t` is also below the parent. Impossible.
        exfalso
        have h1 := hout_tree m c hv
        obtain ⟨j2, hj2, hj2'⟩ := hin_tree m' k hw
        have hpow : d ^ (p - (m : ℕ)) = d ^ (p - (m' : ℕ)) * d := by
          rw [← pow_succ]; congr 1; have := m'.isLt; omega
        have hup : j2 / d ^ (p - (m : ℕ)) = c := by rw [hpow]; exact up_div hj2' hk
        have := (block_bounds (hDpos _) hup).2
        omega
      · exact ⟨m, c, m', k, rfl, hl, hk⟩
  · -- Parents are ordered: child 1's block is `< t`, parent 2 has a leaf `≥ t`.
    intro m₁ c₁ m₁' k₁ m₂ c₂ m₂' k₂ hq₁ hq₂ hl₁ hk₁ hl₂ hk₂ hm
    obtain ⟨-, hv₁, -⟩ := (Finset.mem_filter.mp hq₁).2
    obtain ⟨-, -, hw₂⟩ := (Finset.mem_filter.mp hq₂).2
    have h1 := hout_tree m₁ c₁ hv₁
    obtain ⟨j, hj, hj'⟩ := hin_tree m₂' k₂ hw₂
    have hD := hDpos (p - (m₁ : ℕ))
    have hE : d ^ (p - (m₂' : ℕ)) = d ^ (p - (m₁ : ℕ)) * d := by
      rw [← pow_succ]; congr 1; have := m₁.isLt; omega
    have hx : ((c₁ : ℕ) * d ^ (p - (m₁ : ℕ))) / d ^ (p - (m₂' : ℕ)) = k₁ := by
      rw [hE]; exact up_div (Nat.mul_div_cancel _ hD) hk₁
    rw [← hj', ← hx]
    exact Nat.div_le_div_right (by omega)

/-- The `L` half (mirror image): at most `d·p` edges from `V \ L_{t-1}` into `L_t`. -/
theorem L_side (Γ d p t : ℕ) (ht0 : 0 < t) (hd : 0 < d) :
    (Finset.univ.filter fun q : Vtx Γ d p × Vtx Γ d p =>
        (graph Γ d p).Adj q.1 q.2 ∧ q.1 ∉ L Γ d p (t - 1) ∧ q.2 ∈ L Γ d p t).card ≤ d * p := by
  have hDpos : ∀ n : ℕ, 0 < d ^ n := fun n => pow_pos hd n
  have ht : t ≠ 0 := by omega
  -- Vertices outside `L_{t-1}` lie far right: position `+ t ≥ d^p`.
  have hout_path : ∀ (a : Fin Γ) (j : Fin (d ^ p)),
      (Sum.inl (a, j) : Vtx Γ d p) ∉ L Γ d p (t - 1) → d ^ p < (j : ℕ) + t := by
    intro a j h
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, InLeft] at h
    omega
  have hout_tree : ∀ (ℓ : Fin (p + 1)) (k : Fin (d ^ (ℓ : ℕ))),
      (Sum.inr ⟨ℓ, k⟩ : Vtx Γ d p) ∉ L Γ d p (t - 1) → d ^ p ≤ (k : ℕ) * d ^ (p - ℓ) + t := by
    intro ℓ k h
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, InLeft] at h
    have hb := block_fits ℓ k
    have hp := hDpos (p - ℓ)
    split_ifs at h with h0
    · -- `t = 1`: the only vertex outside `L_0` is `r = u^p_{d^p-1}`.
      obtain ⟨h1, h2⟩ := not_not.mp h
      have h3 : d ^ (p - (ℓ : ℕ)) = 1 := by rw [h1, Nat.sub_self, pow_zero]
      rw [h3, h2]
      omega
    · -- otherwise the leftmost leaf of the block is `≥ d^p - (t - 1)`.
      by_contra hc
      apply h
      refine ⟨⟨(k : ℕ) * d ^ (p - ℓ), by omega⟩, ?_, ?_⟩
      · show (k : ℕ) * d ^ (p - ℓ) + (t - 1) < d ^ p
        omega
      · show ((k : ℕ) * d ^ (p - ℓ)) / d ^ (p - ℓ) = k
        exact Nat.mul_div_cancel _ hp
  -- Vertices inside `L_t` have a leaf with position `+ t < d^p`.
  have hin_path : ∀ (a : Fin Γ) (j : Fin (d ^ p)),
      (Sum.inl (a, j) : Vtx Γ d p) ∈ L Γ d p t → (j : ℕ) + t < d ^ p := by
    intro a j h
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, InLeft] at h
    omega
  have hin_tree : ∀ (ℓ : Fin (p + 1)) (k : Fin (d ^ (ℓ : ℕ))),
      (Sum.inr ⟨ℓ, k⟩ : Vtx Γ d p) ∈ L Γ d p t →
        ∃ j : ℕ, j + t < d ^ p ∧ j / d ^ (p - ℓ) = k := by
    intro ℓ k h
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, InLeft, if_neg ht] at h
    obtain ⟨j, h1, h2⟩ := h
    exact ⟨j, h1, h2⟩
  apply count_generic Γ d p hd
  · intro q hq
    obtain ⟨v, w⟩ := q
    obtain ⟨hadj, hv, hw⟩ := (Finset.mem_filter.mp hq).2
    dsimp only at hadj hv hw
    rw [graph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, hrel⟩ := hadj
    rcases v with ⟨a, j⟩ | ⟨m, c⟩ <;> rcases w with ⟨a', j'⟩ | ⟨m', k⟩
    · exfalso
      have h1 := hout_path a j hv
      have h2 := hin_path a' j' hw
      simp only [baseRel] at hrel
      rcases hrel with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    · exfalso
      have h1 := hout_path a j hv
      obtain ⟨j2, hj2, hj2'⟩ := hin_tree m' k hw
      simp only [baseRel, false_or] at hrel
      obtain ⟨hm, hk⟩ := hrel
      have h3 : d ^ (p - (m' : ℕ)) = 1 := by rw [hm, Nat.sub_self, pow_zero]
      rw [h3, Nat.div_one] at hj2'
      omega
    · exfalso
      have h1 := hout_tree m c hv
      have h2 := hin_path a' j' hw
      simp only [baseRel, or_false] at hrel
      obtain ⟨hm, hk⟩ := hrel
      have h3 : d ^ (p - (m : ℕ)) = 1 := by rw [hm, Nat.sub_self, pow_zero]
      rw [h3] at h1
      omega
    · simp only [baseRel] at hrel
      rcases hrel with ⟨hl, hk⟩ | ⟨hl, hk⟩
      · exfalso
        have h1 := hout_tree m c hv
        obtain ⟨j2, hj2, hj2'⟩ := hin_tree m' k hw
        have hpow : d ^ (p - (m : ℕ)) = d ^ (p - (m' : ℕ)) * d := by
          rw [← pow_succ]; congr 1; have := m'.isLt; omega
        have hup : j2 / d ^ (p - (m : ℕ)) = c := by rw [hpow]; exact up_div hj2' hk
        have := (block_bounds (hDpos _) hup).1
        omega
      · exact ⟨m, c, m', k, rfl, hl, hk⟩
  · -- Parents are ordered: parent 1 has a leaf left of `d^p - t`, child 2's block is right of it.
    intro m₁ c₁ m₁' k₁ m₂ c₂ m₂' k₂ hq₁ hq₂ hl₁ hk₁ hl₂ hk₂ hm
    obtain ⟨-, -, hw₁⟩ := (Finset.mem_filter.mp hq₁).2
    obtain ⟨-, hv₂, -⟩ := (Finset.mem_filter.mp hq₂).2
    obtain ⟨j, hj, hj'⟩ := hin_tree m₁' k₁ hw₁
    have h2 := hout_tree m₂ c₂ hv₂
    have hD := hDpos (p - (m₂ : ℕ))
    have hE : d ^ (p - (m₁' : ℕ)) = d ^ (p - (m₂ : ℕ)) * d := by
      rw [← pow_succ]; congr 1; have := m₂.isLt; omega
    have hx : ((c₂ : ℕ) * d ^ (p - (m₂ : ℕ))) / d ^ (p - (m₁' : ℕ)) = k₂ := by
      rw [hE]; exact up_div (Nat.mul_div_cancel _ hD) hk₂
    rw [← hj', ← hx]
    exact Nat.div_le_div_right (by omega)

end CutEdgesLeAux

theorem solution (Γ d p t : ℕ) (ht0 : 0 < t) (ht : (t : ℝ) < ((d : ℝ) ^ p - 1) / 2) :
    (Finset.univ.filter fun q : Vtx Γ d p × Vtx Γ d p =>
        (graph Γ d p).Adj q.1 q.2 ∧ q.1 ∉ R Γ d p (t - 1) ∧ q.2 ∈ R Γ d p t).card ≤ d * p ∧
    (Finset.univ.filter fun q : Vtx Γ d p × Vtx Γ d p =>
        (graph Γ d p).Adj q.1 q.2 ∧ q.1 ∉ L Γ d p (t - 1) ∧ q.2 ∈ L Γ d p t).card ≤ d * p := by
  -- The round bound only matters through `d > 0` (it forces `d^p > 1`).
  have hN : 2 * t + 1 < d ^ p := by
    have h1 : ((2 * t + 1 : ℕ) : ℝ) < ((d ^ p : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h1
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp; simp at hN
      · rw [zero_pow hp.ne'] at hN; omega
    · exact h
  exact ⟨CutEdgesLeAux.R_side Γ d p t ht0 hd, CutEdgesLeAux.L_side Γ d p t ht0 hd⟩
