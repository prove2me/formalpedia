-- Prove2me | solution 1 for CostlySeeding.EdgeQuery.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:47:11.575986+00:00
-- url     : https://prove2.me/submissions/acc01b91-0c1b-4af6-b626-faef59a2f400

import Definitions.Def_CostlySeeding_EdgeQuery_Model

open CostlySeeding.EdgeQuery in
theorem solution (n k : ℕ) (Gd Gm : Finset (Fin n) → ℝ)
    (eps alpha beta : ℝ) (ha : 0 ≤ alpha)
    (hclose : ∀ S : Finset (Fin n), S.card = k →
      |Gd S - Gm S| ≤ eps * (n : ℝ))
    (L : Finset (Fin n)) (hL : L.card = k)
    (happrox : alpha * OPTof Gd k - beta * n ≤ Gd L) :
    alpha * OPTof Gm k - (beta + (alpha + 1) * eps) * n ≤ Gm L := by
  have hmem : L ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ L, hL⟩
  have hne : ((Finset.univ : Finset (Fin n)).powersetCard k).Nonempty := ⟨L, hmem⟩
  have hOPT : OPTof Gm k ≤ OPTof Gd k + eps * n := by
    unfold OPTof
    rw [dif_pos hne, dif_pos hne]
    apply Finset.sup'_le
    intro S hS
    have hc := hclose S (Finset.mem_powersetCard.mp hS).2
    have h1 : Gm S ≤ Gd S + eps * n := by
      have := neg_abs_le (Gd S - Gm S); linarith
    have h2 : Gd S ≤ ((Finset.univ : Finset (Fin n)).powersetCard k).sup' hne Gd :=
      Finset.le_sup' Gd hS
    linarith
  have hL1 : Gd L - eps * n ≤ Gm L := by
    have := le_abs_self (Gd L - Gm L)
    have := hclose L hL
    linarith
  have h3 : alpha * OPTof Gm k ≤ alpha * OPTof Gd k + alpha * (eps * n) := by
    have := mul_le_mul_of_nonneg_left hOPT ha
    linarith
  nlinarith
