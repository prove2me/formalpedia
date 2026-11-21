-- Prove2me | solution 1 for FracTruthSched.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T09:55:22.100631+00:00
-- url     : https://prove2.me/submissions/77480b01-d517-4bdd-81b6-0d642b709c38

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_symmetrize

section
set_option autoImplicit false

namespace FracTruthSched.Dev.Claim1
open FracTruthSched
open scoped Classical

lemma relabel_nonneg {n m : ℕ} (π : Equiv.Perm (Fin m)) (s : Fin n → Fin m → ℝ) (h : Nonneg s) :
    Nonneg (relabel π s) := fun i e => h i (π e)

lemma relabel_update {n m : ℕ} (π : Equiv.Perm (Fin m)) (s : Fin n → Fin m → ℝ) (i : Fin n)
    (b : Fin m → ℝ) :
    relabel π (Function.update s i b) = Function.update (relabel π s) i (fun e => b (π e)) := by
  funext k e
  by_cases hk : k = i
  · subst hk; simp [relabel]
  · simp [relabel, hk]

lemma relabel_relabel {n m : ℕ} (π γ : Equiv.Perm (Fin m)) (s : Fin n → Fin m → ℝ) :
    relabel π (relabel γ s) = relabel (γ * π) s := by
  funext i e; simp [relabel]

lemma card_pos {m : ℕ} (G : Subgroup (Equiv.Perm (Fin m))) : (0 : ℝ) < Fintype.card G := by
  exact_mod_cast Fintype.card_pos

lemma cost_eq {n m : ℕ} (M : FracMech n (Fin m)) (G : Subgroup (Equiv.Perm (Fin m)))
    (t s : Fin n → Fin m → ℝ) (i : Fin n) :
    ∑ j, t i j * (symmetrize M G).x s i j =
      (1 / (Fintype.card G : ℝ)) *
        ∑ π : G, ∑ e, relabel π.1 t i e * M.x (relabel π.1 s) i e := by
  classical
  simp only [symmetrize, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Equiv.sum_comp π.1 (fun j => t i j * (1 / (Fintype.card G : ℝ) *
      M.x (relabel π.1 s) i (π.1⁻¹ j)))]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [relabel]; ring

theorem chk_claim_1 {n m : ℕ} (M : FracMech n (Fin m)) (hfeas : IsFeasibleOn Nonneg M)
    (htruth : IsTruthfulOn Nonneg M) (G : Subgroup (Equiv.Perm (Fin m))) :
    IsFeasibleOn Nonneg (symmetrize M G) ∧ IsTruthfulOn Nonneg (symmetrize M G) ∧
      ∀ γ ∈ G, ∀ (s : Fin n → Fin m → ℝ) (i : Fin n) (e : Fin m),
        (symmetrize M G).x (relabel γ s) i e = (symmetrize M G).x s i (γ e) ∧
          (symmetrize M G).P (relabel γ s) i = (symmetrize M G).P s i := by
  classical
  have hN := card_pos G
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have h1 : ∀ π : G, ((∀ i j, 0 ≤ M.x (relabel π.1 t) i j ∧ M.x (relabel π.1 t) i j ≤ 1) ∧
        ∀ j, ∑ i, M.x (relabel π.1 t) i j = 1) := fun π =>
      hfeas _ (relabel_nonneg π.1 t ht)
    refine ⟨fun i j => ⟨?_, ?_⟩, fun j => ?_⟩
    · simp only [symmetrize]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun π _ => (h1 π).1 _ _ |>.1)
    · simp only [symmetrize]
      calc (1 / (Fintype.card G : ℝ)) * ∑ π : G, M.x (relabel π.1 t) i (π.1⁻¹ j)
          ≤ (1 / (Fintype.card G : ℝ)) * ∑ π : G, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun π _ => (h1 π).1 _ _ |>.2)
              (by positivity)
        _ = 1 := by simp
    · simp only [symmetrize]
      rw [← Finset.mul_sum, Finset.sum_comm]
      have : ∀ π : G, ∑ i, M.x (relabel π.1 t) i (π.1⁻¹ j) = 1 := fun π => (h1 π).2 _
      simp only [this]; simp
  · intro t ht i b hb
    have key : ∀ π : G, M.P (relabel π.1 (Function.update t i b)) i -
          ∑ e, relabel π.1 t i e * M.x (relabel π.1 (Function.update t i b)) i e ≤
        M.P (relabel π.1 t) i - ∑ e, relabel π.1 t i e * M.x (relabel π.1 t) i e := by
      intro π
      have := htruth (relabel π.1 t) (relabel_nonneg π.1 t ht) i (fun e => b (π.1 e))
        (by rw [← relabel_update]; exact relabel_nonneg π.1 _ hb)
      rw [relabel_update]; exact this
    rw [cost_eq, cost_eq]
    simp only [symmetrize]
    rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun π _ => key π) (by positivity)
  · intro γ hγ s i e
    let σ : G ≃ G := (Equiv.mulLeft (⟨γ, hγ⟩ : G))
    constructor
    · simp only [symmetrize]
      congr 1
      refine Fintype.sum_equiv σ _ _ fun π => ?_
      simp only [relabel_relabel, σ, Equiv.coe_mulLeft, Subgroup.coe_mul]
      congr 1
      simp
    · simp only [symmetrize]
      congr 1
      refine Fintype.sum_equiv σ _ _ fun π => ?_
      simp only [relabel_relabel, σ, Equiv.coe_mulLeft, Subgroup.coe_mul]

end FracTruthSched.Dev.Claim1

namespace FracTruthSched
open scoped Classical in
theorem chk_claim_1 {n m : ℕ} (M : FracMech n (Fin m)) (hfeas : IsFeasibleOn Nonneg M)
    (htruth : IsTruthfulOn Nonneg M) (G : Subgroup (Equiv.Perm (Fin m))) :
    IsFeasibleOn Nonneg (symmetrize M G) ∧ IsTruthfulOn Nonneg (symmetrize M G) ∧
      ∀ γ ∈ G, ∀ (s : Fin n → Fin m → ℝ) (i : Fin n) (e : Fin m),
        (symmetrize M G).x (relabel γ s) i e = (symmetrize M G).x s i (γ e) ∧
          (symmetrize M G).P (relabel γ s) i = (symmetrize M G).P s i :=
  Dev.Claim1.chk_claim_1 M hfeas htruth G
end FracTruthSched
end

theorem solution : type_of% @FracTruthSched.chk_claim_1 := @FracTruthSched.chk_claim_1
