-- Prove2me | solution 1 for FracTruthSched.symmetrizeGen_properties_type0
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:08.818802+00:00
-- url     : https://prove2.me/submissions/f7ee33bf-9c45-4b84-a7b8-19e3c2c1924c

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_PaddedConstruction

set_option autoImplicit false

namespace FracTruthSched

open Classical

private lemma relabel_nonneg_gen {n : ℕ} {τ : Type*} (π : Equiv.Perm τ)
    (s : Fin n → τ → ℝ) (h : Nonneg s) : Nonneg (relabel π s) := fun i e => h i (π e)

private lemma relabel_update_gen {n : ℕ} {τ : Type*} (π : Equiv.Perm τ)
    (s : Fin n → τ → ℝ) (i : Fin n) (b : τ → ℝ) :
    relabel π (Function.update s i b) = Function.update (relabel π s) i (fun e => b (π e)) := by
  funext k e
  by_cases hk : k = i
  · subst hk; simp [relabel]
  · simp [relabel, hk]

private lemma relabel_relabel_gen {n : ℕ} {τ : Type*} (π γ : Equiv.Perm τ)
    (s : Fin n → τ → ℝ) : relabel π (relabel γ s) = relabel (γ * π) s := by
  funext i e; simp [relabel]

private lemma card_pos_gen {τ : Type*} [Fintype τ]
    (G : Subgroup (Equiv.Perm τ)) : (0 : ℝ) < Fintype.card G := by
  exact_mod_cast Fintype.card_pos

private lemma cost_eq_gen {n : ℕ} {τ : Type*} [Fintype τ]
    (M : FracMech n τ) (G : Subgroup (Equiv.Perm τ))
    (t s : Fin n → τ → ℝ) (i : Fin n) :
    ∑ j, t i j * (symmetrizeGen M G).x s i j =
      (1 / (Fintype.card G : ℝ)) *
        ∑ π : G, ∑ e, relabel π.1 t i e * M.x (relabel π.1 s) i e := by
  classical
  simp only [symmetrizeGen, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Equiv.sum_comp π.1 (fun j => t i j * (1 / (Fintype.card G : ℝ) *
      M.x (relabel π.1 s) i (π.1⁻¹ j)))]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [relabel]; ring

end FracTruthSched

open FracTruthSched

/-- General finite-task-type form of Claim 1: averaging over a subgroup of task
permutations preserves feasibility and truthfulness and is equivariant under those permutations. -/
theorem solution {n : ℕ} {τ : Type} [Fintype τ]
    (M : FracMech n τ) (hfeas : IsFeasibleOn Nonneg M) (htruth : IsTruthfulOn Nonneg M)
    (G : Subgroup (Equiv.Perm τ)) :
    IsFeasibleOn Nonneg (symmetrizeGen M G) ∧ IsTruthfulOn Nonneg (symmetrizeGen M G) ∧
      ∀ γ ∈ G, ∀ (s : Fin n → τ → ℝ) (i : Fin n) (e : τ),
        (symmetrizeGen M G).x (relabel γ s) i e = (symmetrizeGen M G).x s i (γ e) ∧
          (symmetrizeGen M G).P (relabel γ s) i = (symmetrizeGen M G).P s i := by
  classical
  have hN := FracTruthSched.card_pos_gen G
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have h1 : ∀ π : G, ((∀ i j, 0 ≤ M.x (relabel π.1 t) i j ∧ M.x (relabel π.1 t) i j ≤ 1) ∧
        ∀ j, ∑ i, M.x (relabel π.1 t) i j = 1) := fun π =>
      hfeas _ (FracTruthSched.relabel_nonneg_gen π.1 t ht)
    refine ⟨fun i j => ⟨?_, ?_⟩, fun j => ?_⟩
    · simp only [symmetrizeGen]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun π _ => (h1 π).1 _ _ |>.1)
    · simp only [symmetrizeGen]
      calc (1 / (Fintype.card G : ℝ)) * ∑ π : G, M.x (relabel π.1 t) i (π.1⁻¹ j)
          ≤ (1 / (Fintype.card G : ℝ)) * ∑ π : G, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun π _ => (h1 π).1 _ _ |>.2)
              (by positivity)
        _ = 1 := by simp
    · simp only [symmetrizeGen]
      rw [← Finset.mul_sum, Finset.sum_comm]
      have : ∀ π : G, ∑ i, M.x (relabel π.1 t) i (π.1⁻¹ j) = 1 := fun π => (h1 π).2 _
      simp only [this]; simp
  · intro t ht i b hb
    have key : ∀ π : G, M.P (relabel π.1 (Function.update t i b)) i -
          ∑ e, relabel π.1 t i e * M.x (relabel π.1 (Function.update t i b)) i e ≤
        M.P (relabel π.1 t) i - ∑ e, relabel π.1 t i e * M.x (relabel π.1 t) i e := by
      intro π
      have := htruth (relabel π.1 t) (FracTruthSched.relabel_nonneg_gen π.1 t ht) i (fun e => b (π.1 e))
        (by rw [← FracTruthSched.relabel_update_gen]; exact FracTruthSched.relabel_nonneg_gen π.1 _ hb)
      rw [FracTruthSched.relabel_update_gen]; exact this
    rw [FracTruthSched.cost_eq_gen, FracTruthSched.cost_eq_gen]
    simp only [symmetrizeGen]
    rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun π _ => key π) (by positivity)
  · intro γ hγ s i e
    let σ : G ≃ G := (Equiv.mulLeft (⟨γ, hγ⟩ : G))
    constructor
    · simp only [symmetrizeGen]
      congr 1
      refine Fintype.sum_equiv σ _ _ fun π => ?_
      simp only [FracTruthSched.relabel_relabel_gen, σ, Equiv.coe_mulLeft, Subgroup.coe_mul]
      congr 1
      simp
    · simp only [symmetrizeGen]
      congr 1
      refine Fintype.sum_equiv σ _ _ fun π => ?_
      simp only [FracTruthSched.relabel_relabel_gen, σ, Equiv.coe_mulLeft, Subgroup.coe_mul]