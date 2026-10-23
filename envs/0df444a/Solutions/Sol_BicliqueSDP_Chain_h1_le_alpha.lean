-- Prove2me | solution 1 for BicliqueSDP.Chain.h1_le_alpha
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:33:26.04145+00:00
-- url     : https://prove2.me/submissions/33e31216-3e1c-4ced-bf1d-2a0c7d0eebe5

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model
import Theorems.Thm_BicliqueSDP_Chain_theta_eq_alpha_bipartite

namespace BicliqueSDP.Chain

open Matrix

noncomputable section

/-- The quadratic form at the difference of two coordinate vectors gives the
arithmetic-mean bound on a matrix entry. -/
private theorem psd_entry_le_diag_avg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (i j : ι) :
    X i j ≤ (X i i + X j j) / 2 := by
  have hs : X j i = X i j := by simpa using hX.isHermitian.apply i j
  have h := hX.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    Matrix.mulVec_single, single_dotProduct] at h
  linarith

private theorem psd_entry_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (htr : X.trace = 1) (i j : ι) :
    X i j ≤ 1 := by
  have hdiag (k : ι) : X k k ≤ 1 := by
    calc
      X k k ≤ ∑ l, X l l := Finset.single_le_sum
        (f := fun l => X l l) (fun l _ => hX.diag_nonneg) (Finset.mem_univ k)
      _ = 1 := htr
  have hpair := psd_entry_le_diag_avg hX i j
  linarith [hdiag i, hdiag j]

/-- The objective set defining theta is bounded above, including when the vertex
type is empty. A coarse entrywise bound suffices for the supremum argument. -/
theorem theta_objective_bddAbove {V : Type} [Fintype V] (G : SimpleGraph V) :
    BddAbove ((fun X : Matrix V V ℝ => ∑ i, ∑ j, X i j) ''
      {X | X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0}) := by
  classical
  refine ⟨∑ _ : V, ∑ _ : V, (1 : ℝ), ?_⟩
  rintro z ⟨X, hX, rfl⟩
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => psd_entry_le_one hX.1 hX.2.1 i j

/-- Every feasible theta objective is at most the defining supremum. -/
theorem sum_le_theta {V : Type} [Fintype V] (G : SimpleGraph V)
    (X : Matrix V V ℝ)
    (hX : X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0) :
    (∑ i, ∑ j, X i j) ≤ theta G := by
  exact le_csSup (theta_objective_bddAbove G) ⟨X, hX, rfl⟩

/-- The quadratic form at the vector which is `1` on the left side and `-1` on the
right side bounds four times the cross-block objective by the sum of all entries. -/
theorem four_frob_Cmat_le_sum {V1 V2 : Type} [Fintype V1] [Fintype V2]
    (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (hX : X.PosSemidef) :
    4 * frob Cmat X ≤ ∑ i, ∑ j, X i j := by
  have hq := hX.dotProduct_mulVec_nonneg (Sum.elim (fun _ : V1 => (1 : ℝ))
    (fun _ : V2 => (-1 : ℝ)))
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, Pi.star_apply,
    star_trivial, Sum.elim_inl, Sum.elim_inr, mul_one, mul_neg_one, one_mul,
    neg_one_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_add_rev,
    neg_neg] at hq
  simp [frob, Cmat, Fintype.sum_sum_type, Matrix.fromBlocks,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

/-- The empty biindependent pair witnesses nonnegativity of the stability number. -/
private theorem alpha_nonneg {V1 V2 : Type} [Fintype V1] [Fintype V2]
    [DecidableEq V1] [DecidableEq V2] (E : V1 → V2 → Prop)
    [∀ i j, Decidable (E i j)] : 0 ≤ alpha E := by
  simpa [alpha] using
    (Finset.le_sup' (f := fun p : Finset V1 × Finset V2 =>
      (p.1.card : ℝ) + p.2.card) (empty_mem_pairs E))

/-- The passage to suprema does not require an optimal solution or a nonempty vertex type. -/
theorem h1_le_alpha_of_objective_bound {V1 V2 : Type} [Fintype V1] [Fintype V2]
    [DecidableEq V1] [DecidableEq V2] (E : V1 → V2 → Prop)
    [∀ i j, Decidable (E i j)]
    (hbound : ∀ X, H1Feasible E X → 4 * frob Cmat X ≤ alpha E) :
    h1 E ≤ (1 / 4) * alpha E := by
  unfold h1
  by_cases hne : ((fun X => frob Cmat X) '' {X | H1Feasible E X}).Nonempty
  · apply csSup_le hne
    rintro b ⟨X, hX, rfl⟩
    have := hbound X hX
    linarith
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact mul_nonneg (by norm_num) (alpha_nonneg E)

/-- The matrix inequality in the paper's proof, applied before taking suprema. -/
theorem four_frob_le_theta {V1 V2 : Type} [Fintype V1] [Fintype V2]
    [DecidableEq V1] [DecidableEq V2] (E : V1 → V2 → Prop)
    (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (hX : H1Feasible E X) :
    4 * frob Cmat X ≤ theta (bipGraph E) := by
  exact (four_frob_Cmat_le_sum X hX.1).trans (sum_le_theta (bipGraph E) X hX)

end

end BicliqueSDP.Chain

open BicliqueSDP.Chain

/-- §3.3, p. 18: `h₁(G) ≤ ¼α(G)`. The final equality between theta and alpha is
the separately registered bipartite-theta theorem. -/
theorem solution {V1 V2 : Type} [Fintype V1] [Fintype V2]
    [DecidableEq V1] [DecidableEq V2] (E : V1 → V2 → Prop)
    [∀ i j, Decidable (E i j)] : h1 E ≤ (1 / 4) * alpha E := by
  apply h1_le_alpha_of_objective_bound E
  intro X hX
  rw [← theta_eq_alpha_bipartite E]
  exact four_frob_le_theta E X hX
