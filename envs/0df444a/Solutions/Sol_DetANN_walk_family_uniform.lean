-- Prove2me | solution 1 for DetANN.walk_family_uniform
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T01:01:46.856923+00:00
-- url     : https://prove2.me/submissions/30103fcc-6ac2-45ec-9b83-2d60f35c491d

import Mathlib
import Definitions.Def_DetANN_Multigraph
import Definitions.Def_DetANN_TupleFamily

open DetANN

namespace DetANNWalkAux

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V] {Δ : ℕ}

/-- Number of length-`ℓ` walks from `v` ending at `i`. -/
def walkCount (nbr : V → Fin Δ → V) (ℓ : ℕ) (v i : V) : ℕ :=
  (Finset.univ.filter fun w : Fin ℓ → Fin Δ => walkEnd nbr ℓ v w = i).card

/-- `∑_k f (nbr v k) = ∑_u #{k : nbr v k = u} · f u`. -/
lemma sum_nbr (nbr : V → Fin Δ → V) (v : V) (f : V → ℝ) :
    ∑ k, f (nbr v k) = ∑ u, (edgeCount nbr v u : ℝ) * f u := by
  rw [← Finset.sum_fiberwise' Finset.univ (nbr v) f]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

lemma walkCount_succ (nbr : V → Fin Δ → V) (ℓ : ℕ) (v i : V) :
    (walkCount nbr (ℓ + 1) v i : ℝ) = ∑ k, (walkCount nbr ℓ (nbr v k) i : ℝ) := by
  simp only [walkCount, Finset.card_filter]
  push_cast
  rw [← (Fin.consEquiv fun _ : Fin (ℓ + 1) => Fin Δ).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_
  simp [Fin.consEquiv, walkEnd]

lemma walkCount_eq_pow (nbr : V → Fin Δ → V) (hΔ : 1 ≤ Δ) (ℓ : ℕ) (v i : V) :
    (walkCount nbr ℓ v i : ℝ) / (Δ : ℝ) ^ ℓ = (adjMatrix nbr ^ ℓ) v i := by
  have hΔ' : (Δ : ℝ) ≠ 0 := by positivity
  induction ℓ generalizing v with
  | zero =>
    simp only [walkCount, walkEnd, pow_zero, div_one, Matrix.one_apply]
    by_cases hvi : v = i
    · subst hvi; simp
    · simp [hvi]
  | succ ℓ ih =>
    rw [walkCount_succ, pow_succ' (adjMatrix nbr) ℓ, Matrix.mul_apply, pow_succ (Δ : ℝ) ℓ]
    have : ∀ k, (walkCount nbr ℓ (nbr v k) i : ℝ) = (adjMatrix nbr ^ ℓ) (nbr v k) i * Δ ^ ℓ := by
      intro k; rw [← ih]; field_simp
    simp_rw [this]
    rw [← Finset.sum_mul, sum_nbr nbr v (fun u => (adjMatrix nbr ^ ℓ) u i)]
    simp only [adjMatrix]
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => ?_
    field_simp

lemma adj_symm (nbr : V → Fin Δ → V) (hund : IsUndirected nbr) :
    (adjMatrix nbr).transpose = adjMatrix nbr := by
  ext u v; simp [adjMatrix, hund v u]

lemma adj_rowsum (nbr : V → Fin Δ → V) (hΔ : 1 ≤ Δ) (u : V) :
    ∑ v, adjMatrix nbr u v = 1 := by
  have hΔ' : (Δ : ℝ) ≠ 0 := by positivity
  have := sum_nbr nbr u (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
  simp only [adjMatrix, ← Finset.sum_div, ← this]
  field_simp

lemma pow_rowsum (nbr : V → Fin Δ → V) (hΔ : 1 ≤ Δ) (ℓ : ℕ) (u : V) :
    ∑ v, (adjMatrix nbr ^ ℓ) u v = 1 := by
  induction ℓ generalizing u with
  | zero => simp [Matrix.one_apply]
  | succ ℓ ih =>
    rw [pow_succ']
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact adj_rowsum nbr hΔ u

end DetANNWalkAux

open DetANNWalkAux in
theorem solution {d Δ : ℕ} (nbr : Fin d → Fin Δ → Fin d) (hΔ : 1 ≤ Δ)
    (hund : IsUndirected nbr) (ℓ : ℕ) :
    (∀ i : Fin d, blockCount (walkEnd nbr ℓ) i = Δ ^ ℓ) ∧
      ∀ i v : Fin d,
        ((Finset.univ.filter fun w : Fin ℓ → Fin Δ => walkEnd nbr ℓ v w = i).card : ℝ) /
            (Δ : ℝ) ^ ℓ = (adjMatrix nbr ^ ℓ) i v := by
  have hsymm : ∀ i v : Fin d, (adjMatrix nbr ^ ℓ) v i = (adjMatrix nbr ^ ℓ) i v := by
    intro i v
    rw [← Matrix.transpose_apply (adjMatrix nbr ^ ℓ) i v, Matrix.transpose_pow, adj_symm nbr hund]
  have part2 : ∀ i v : Fin d,
      ((Finset.univ.filter fun w : Fin ℓ → Fin Δ => walkEnd nbr ℓ v w = i).card : ℝ) /
          (Δ : ℝ) ^ ℓ = (adjMatrix nbr ^ ℓ) i v := by
    intro i v
    rw [← hsymm]; exact walkCount_eq_pow nbr hΔ ℓ v i
  refine ⟨fun i => ?_, part2⟩
  have hΔ' : (Δ : ℝ) ^ ℓ ≠ 0 := by positivity
  -- blockCount = ∑_v walkCount v i
  have hbc : (blockCount (walkEnd nbr ℓ) i : ℝ) =
      ∑ v, ((Finset.univ.filter fun w : Fin ℓ → Fin Δ => walkEnd nbr ℓ v w = i).card : ℝ) := by
    simp only [blockCount, Finset.card_filter]
    push_cast
    rw [Fintype.sum_prod_type]
  have : (blockCount (walkEnd nbr ℓ) i : ℝ) = (Δ : ℝ) ^ ℓ := by
    rw [hbc]
    have h2 : ∀ v, ((Finset.univ.filter fun w : Fin ℓ → Fin Δ => walkEnd nbr ℓ v w = i).card : ℝ)
        = (adjMatrix nbr ^ ℓ) i v * (Δ : ℝ) ^ ℓ := by
      intro v; rw [← part2]; field_simp
    simp_rw [h2]
    rw [← Finset.sum_mul, pow_rowsum nbr hΔ ℓ i, one_mul]
  exact_mod_cast this
