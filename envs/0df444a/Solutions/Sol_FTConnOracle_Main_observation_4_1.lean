-- Prove2me | solution 1 for FTConnOracle.Main.observation_4_1
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-27T03:26:03.600879+00:00
-- url     : https://prove2.me/submissions/48639e48-c3ef-4904-9c84-6fc4569d210d

import Mathlib
import Definitions.Def_FTConnOracle_Main_Expander

open FTConnOracle FTConnOracle.Main

open Classical

/-- The combinatorial core of Observation 4.1, stated over the raw path predicate (no
`cutMatrix`, no `pathSet`): the number of pairs `(u, v)` with `u ∈ S`, `i ∈ B u`,
`G.Adj u v`, `v ∉ S`, `j ∈ B v` — i.e. the middle edges `u →G v` of the paths
`i →B u →G v →B j` — equals the double 0/1 sum over `u ∈ S` and the relevant `v` of the
products of the 0/1 column indicators. Each such path is determined by its middle edge,
so the two sides count the same pairs. -/
-- riskiest
lemma pathCard_eq_doubleSum {n r : ℕ} (B : Fin n → Finset (Fin r)) (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (i j : Fin r) :
    (((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p => i ∈ B p.1 ∧ p.1 ∈ S ∧ G.Adj p.1 p.2 ∧ p.2 ∉ S ∧ j ∈ B p.2)).card : ℤ) =
      (∑ u ∈ S, ∑ v ∈ (Finset.univ : Finset (Fin n)).filter (fun v => v ∉ S ∧ G.Adj u v),
        (if i ∈ B u then 1 else 0) * (if j ∈ B v then 1 else 0) : ℤ) := by
  -- The 0/1 product-sum equals the cardinality of the filtered product set.
  have h2 :
      (∑ u ∈ S, ∑ v ∈ (Finset.univ : Finset (Fin n)).filter (fun v => v ∉ S ∧ G.Adj u v),
          (if i ∈ B u then 1 else 0) * (if j ∈ B v then 1 else 0) : ℤ) =
        ((S ×ˢ (Finset.univ : Finset (Fin n))).filter
          (fun p => p.2 ∉ S ∧ G.Adj p.1 p.2 ∧ i ∈ B p.1 ∧ j ∈ B p.2)).card := by
    calc
      (∑ u ∈ S, ∑ v ∈ (Finset.univ : Finset (Fin n)).filter (fun v => v ∉ S ∧ G.Adj u v),
          (if i ∈ B u then 1 else 0) * (if j ∈ B v then 1 else 0) : ℤ)
        = ∑ u ∈ S, ∑ v ∈ (Finset.univ : Finset (Fin n)),
            (if v ∉ S ∧ G.Adj u v then (if i ∈ B u then 1 else 0) * (if j ∈ B v then 1 else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_filter]
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset (Fin n)),
            (if p.2 ∉ S ∧ G.Adj p.1 p.2 then (if i ∈ B p.1 then 1 else 0) * (if j ∈ B p.2 then 1 else 0) else 0) := by
          exact (Finset.sum_product S (Finset.univ : Finset (Fin n))
            (fun p_1 => if p_1.2 ∉ S ∧ G.Adj p_1.1 p_1.2 then
              (if i ∈ B p_1.1 then 1 else 0) * (if j ∈ B p_1.2 then 1 else 0) else 0)).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset (Fin n)),
            (if p.2 ∉ S ∧ G.Adj p.1 p.2 ∧ i ∈ B p.1 ∧ j ∈ B p.2 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro p _
          by_cases hA : p.2 ∉ S ∧ G.Adj p.1 p.2 <;>
            by_cases hC : i ∈ B p.1 <;> by_cases hD : j ∈ B p.2 <;> simp [hA, hC, hD]
      _ = ((S ×ˢ (Finset.univ : Finset (Fin n))).filter
            (fun p => p.2 ∉ S ∧ G.Adj p.1 p.2 ∧ i ∈ B p.1 ∧ j ∈ B p.2)).card := by
          rw [Finset.sum_boole]
  -- The filter of the product equals the filter of the full product.
  have h3 :
      (S ×ˢ (Finset.univ : Finset (Fin n))).filter
        (fun p => p.2 ∉ S ∧ G.Adj p.1 p.2 ∧ i ∈ B p.1 ∧ j ∈ B p.2) =
        ((Finset.univ : Finset (Fin n × Fin n)).filter
          (fun p => p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2 ∧ i ∈ B p.1 ∧ j ∈ B p.2)) := by
    apply Finset.ext
    intro p
    simp [Finset.mem_product, Finset.mem_filter]
  -- Both sides count the same pairs, reorganised.
  have h1 :
      ((Finset.univ : Finset (Fin n × Fin n)).filter
          (fun p => i ∈ B p.1 ∧ p.1 ∈ S ∧ G.Adj p.1 p.2 ∧ p.2 ∉ S ∧ j ∈ B p.2)).card =
        ((Finset.univ : Finset (Fin n × Fin n)).filter
          (fun p => p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2 ∧ i ∈ B p.1 ∧ j ∈ B p.2)).card := by
    congr
    ext p
    tauto
  rw [h1, h2, h3]

/-- Observation 4.1 (p. 16): for `i, j ∈ [r]`, the entry `Q(S)_{i,j}` of the sketched cut matrix
equals the number of paths `i →B x →G y →B j` with `x ∈ S` and `y ∈ Sᶜ`. -/
theorem solution {n r ℓ t : ℕ} (hn : 2 ≤ n) (B : Fin n → Finset (Fin r))
    (hB : IsLosslessExpander B ℓ t) (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (i j : Fin r) :
    cutMatrix B G S i j = ((pathSet B G S i j).card : ℤ) := by
  calc
    cutMatrix B G S i j
      = ∑ u ∈ S, ∑ v ∈ (Finset.univ : Finset (Fin n)).filter (fun v => v ∉ S ∧ G.Adj u v),
          (col B u i) * (col B v j) := by
        calc
          _ = (∑ u ∈ S, ∑ v ∈ (Finset.univ : Finset (Fin n)).filter (fun v => v ∉ S ∧ G.Adj u v),
                Matrix.vecMulVec (col B u) (col B v)) i j := rfl
          _ = ∑ u ∈ S, (∑ v ∈ (Finset.univ : Finset (Fin n)).filter (fun v => v ∉ S ∧ G.Adj u v),
                Matrix.vecMulVec (col B u) (col B v)) i j := by rw [Matrix.sum_apply]
          _ = ∑ u ∈ S, ∑ v ∈ (Finset.univ : Finset (Fin n)).filter (fun v => v ∉ S ∧ G.Adj u v),
                (col B u i) * (col B v j) := by simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
    _ = ∑ u ∈ S, ∑ v ∈ (Finset.univ : Finset (Fin n)).filter (fun v => v ∉ S ∧ G.Adj u v),
          (if i ∈ B u then 1 else 0) * (if j ∈ B v then 1 else 0) := by
        simp [col]
    _ = (((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p => i ∈ B p.1 ∧ p.1 ∈ S ∧ G.Adj p.1 p.2 ∧ p.2 ∉ S ∧ j ∈ B p.2)).card : ℤ) := by
        simpa using (pathCard_eq_doubleSum B G S i j).symm
    _ = ((pathSet B G S i j).card : ℤ) := by
        simp [pathSet]
