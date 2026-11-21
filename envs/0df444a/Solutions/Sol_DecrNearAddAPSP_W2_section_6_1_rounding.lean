-- Prove2me | solution 1 for DecrNearAddAPSP.W2.section_6_1_rounding
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-20T08:16:44.405986+00:00
-- url     : https://prove2.me/submissions/922ecc8f-e5fd-43bd-94d2-00ba57fe3e61

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs

open DecrNearAddAPSP DecrNearAddAPSP.W2

namespace P2MHole01_6ebaf6f3
/-- `⌈x⌉ ≤ x + 1` for any real `x`. -/
lemma p2m_ceil_le_self_add_one (x : ℝ) : (⌈x⌉ : ℝ) ≤ x + 1 := by
  have h : (⌈x⌉ : ℝ) - 1 < x := by
    have hlt : (⌈x⌉ : ℤ) - 1 < ⌈x⌉ := by omega
    simpa using (Int.lt_ceil (z := ⌈x⌉ - 1) (a := x)).mp hlt
  linarith

/-- Casting a list sum of naturals to the reals commutes with casting each entry. -/
lemma p2m_nat_cast_list_sum (l : List ℕ) : (l.sum : ℝ) = (l.map (fun x => (x : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Dividing every entry `f x` of a list by `d` divides the sum by `d` (for `d = 0`
both sides are `0`). -/
lemma p2m_sum_div_distrib {d : ℝ} {β : Type} (f : β → ℝ) (l : List β) :
    (l.map (fun x => f x / d)).sum = (l.map f).sum / d := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]; ring

/-- Adding `1` to every entry of a list adds its length to the sum. -/
lemma p2m_sum_add_one (l : List ℝ) : (l.map (fun x => x + 1)).sum = l.sum + l.length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]; ring

theorem solution {α : Type} (G : WGraph α) (ε : ℝ) (h i : ℕ) {u v : α} (p : G.adj.Walk u v) :
  ↑(scaledWalkWeight G ε h i p) ≤ ↑(G.walkWeight p) / (ε * (2 : ℝ) ^ i / ↑h) + ↑p.length := by
  let d : ℝ := ε * (2 : ℝ) ^ i / ↑h
  have he (e : Sym2 α) : (scaledWeight ε h i (G.wt e) : ℝ) ≤ (G.wt e : ℝ) / d + 1 := by
    simpa [scaledWeight] using p2m_ceil_le_self_add_one ((G.wt e : ℝ) / (ε * (2 : ℝ) ^ i / ↑h))
  calc
    (scaledWalkWeight G ε h i p : ℝ)
        = (p.edges.map fun e => (scaledWeight ε h i (G.wt e) : ℝ)).sum := by
      simp [scaledWalkWeight, List.map_map]
      rfl
    _ ≤ (p.edges.map fun e => (G.wt e : ℝ) / d + 1).sum :=
      List.sum_le_sum (fun e _ => he e)
    _ = (p.edges.map fun e => (G.wt e : ℝ) / d).sum + p.length := by
      simp
    _ = (G.walkWeight p : ℝ) / d + p.length := by
      simp [p2m_sum_div_distrib (fun e => (G.wt e : ℝ)) (p.edges), WGraph.walkWeight]
      rfl
    _ = ↑(G.walkWeight p) / (ε * (2 : ℝ) ^ i / ↑h) + ↑p.length := rfl
end P2MHole01_6ebaf6f3

/-- Rounding slack, summed along a walk: `w_{G_i}(p) = Σ_e ⌈w(e)/α_i⌉` is at most the total
weight of the walk scaled by `1/α_i` plus one unit per edge, i.e.
`(scaledWalkWeight G ε h i p : ℝ) ≤ (G.walkWeight p : ℝ)/(ε·2^i/h) + p.length`.
No hypotheses are needed: the per-edge slack `⌈x⌉ ≤ x + 1` holds for every real `x`. -/
lemma scaled_walk_weight_le {α : Type} (G : WGraph α) (ε : ℝ) (h i : ℕ) {u v : α}
    (p : G.adj.Walk u v) :
    (scaledWalkWeight G ε h i p : ℝ) ≤
      (G.walkWeight p : ℝ) / (ε * (2 : ℝ) ^ i / (h : ℝ)) + (p.length : ℝ) := by
  (first | exact P2MHole01_6ebaf6f3.solution G ε h i p | (apply P2MHole01_6ebaf6f3.solution <;> assumption))

namespace P2MHole02_65334f0e
theorem solution (ε : ℝ) (h i : ℕ) (hε0 : (0 : ℝ) < ε) (hε1 : ε < (1 : ℝ)) (hh : (1 : ℕ) ≤ h) :
  (2 : ℝ) ^ (i + (1 : ℕ)) / (ε * (2 : ℝ) ^ i / ↑h) + ↑h ≤ (4 : ℝ) * ↑h / ε := by
  have hpos : 0 < (↑h : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mp hh
  have hmain : (2 : ℝ) ^ (i + (1 : ℕ)) / (ε * (2 : ℝ) ^ i / ↑h) = 2 * ↑h / ε := by
    rw [pow_succ]
    field_simp
  rw [hmain]
  have h2 : ε ≤ 2 := by linarith
  field_simp [hε0]
  nlinarith [h2, hpos]
end P2MHole02_65334f0e

/-- Arithmetic tail of the §6.1 bound: at scale `i`, a walk whose weight is at most `2^{i+1}`
and which has at most `h` edges gets scaled weight at most
`2^{i+1}/α_i + h = 2h/ε + h ≤ 4h/ε` when `0 < ε < 1`; the bound is independent of `i`. -/
lemma rounding_tail_bound (ε : ℝ) (h i : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1) (hh : 1 ≤ h) :
    (2 : ℝ) ^ (i + 1) / (ε * (2 : ℝ) ^ i / (h : ℝ)) + (h : ℝ) ≤ 4 * (h : ℝ) / ε := by
  (first | exact P2MHole02_65334f0e.solution ε h i hε0 hε1 hh | (apply P2MHole02_65334f0e.solution <;> assumption))

/-- **§6.1 rounding bound** (p. 36). Let `G` have positive integer weights, `0 < ε < 1`, `h ≥ 1` a
hop parameter, `i ∈ ℕ`, and `α_i = ε·2^i/h`. In the scaled graph `G_i` (edges of weight at most
`2^{i+1}`, weight `w` mapped to `⌈w/α_i⌉`) every edge has a positive integer weight, and every path
`p` of `G` (any walk, simple or not) with at most `h` hops and `2^i ≤ w(p) ≤ 2^{i+1}` has `w_{G_i}(p) ≤ ⌈4h/ε⌉`. -/
theorem solution {n : ℕ} (G : WGraph (Fin n)) (hpos : G.PosWeights) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (h i : ℕ) (hh : 1 ≤ h) :
    (∀ e ∈ G.adj.edgeSet, G.wt e ≤ 2 ^ (i + 1) → 0 < scaledWeight ε h i (G.wt e)) ∧
    (∀ (u v : Fin n) (p : G.adj.Walk u v), p.length ≤ h →
      2 ^ i ≤ G.walkWeight p → G.walkWeight p ≤ 2 ^ (i + 1) →
      scaledWalkWeight G ε h i p ≤ ⌈4 * (h : ℝ) / ε⌉) := by
  constructor
  · intro e he hwe
    have hw1 : 1 ≤ G.wt e := hpos e he
    have hw0 : 0 < (G.wt e : ℝ) := Nat.cast_pos.mpr (by omega)
    have hα : 0 < ε * (2 : ℝ) ^ i / (h : ℝ) := by positivity
    unfold scaledWeight
    exact Int.ceil_pos.mpr (by positivity)
  · intro u v p hlpl hwlo hwhi
    have h1 : (scaledWalkWeight G ε h i p : ℝ) ≤
        (2 : ℝ) ^ (i + 1) / (ε * (2 : ℝ) ^ i / (h : ℝ)) + (h : ℝ) := by
      calc
        _ ≤ (G.walkWeight p : ℝ) / (ε * (2 : ℝ) ^ i / (h : ℝ)) + (p.length : ℝ) :=
            scaled_walk_weight_le G ε h i p
        _ ≤ (2 : ℝ) ^ (i + 1) / (ε * (2 : ℝ) ^ i / (h : ℝ)) + (h : ℝ) := by
          gcongr
          · exact_mod_cast hwhi
    have h2 : (2 : ℝ) ^ (i + 1) / (ε * (2 : ℝ) ^ i / (h : ℝ)) + (h : ℝ) ≤
        4 * (h : ℝ) / ε := rounding_tail_bound ε h i hε0 hε1 hh
    exact Int.le_ceil_iff.2 (by linarith)
