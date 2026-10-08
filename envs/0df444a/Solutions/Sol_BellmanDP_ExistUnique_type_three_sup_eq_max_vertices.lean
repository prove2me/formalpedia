-- Prove2me | solution 1 for BellmanDP.ExistUnique.type_three_sup_eq_max_vertices
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:42:48.417136+00:00
-- url     : https://prove2.me/submissions/8724fc41-d3fc-43af-b423-e3ff86cf6cc6

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_TypeThree



namespace BellmanDP.ExistUnique

section T3

variable {n M : ℕ} {Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} {c₁ : ℝ}

theorem t3_vertex_apply (k j : Fin (n + 1)) : vertex n k j = if j = k then 1 else 0 := by
  unfold vertex; rw [Pi.single_apply]

theorem t3_vertex_mem (k : Fin (n + 1)) : vertex n k ∈ simplex n := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [t3_vertex_apply]; split_ifs <;> norm_num
  · simp [t3_vertex_apply]

theorem t3_sum_vertex (k : Fin (n + 1)) (φ : (Fin (n + 1) → ℝ) → ℝ) :
    ∑ j, vertex n k j * φ (vertex n j) = φ (vertex n k) := by
  simp [t3_vertex_apply]

theorem t3_vertex_ne {k : Fin (n + 1)} (hk : k ≠ 0) : vertex n k ≠ vertex n 0 := by
  intro h
  have := congrFun h k
  rw [t3_vertex_apply, t3_vertex_apply, if_pos rfl, if_neg hk] at this
  norm_num at this

theorem t3_inf_le (hT : TypeThreeHyp n M Tr c₁) (φ : Fin M → ℝ) (l : Fin M) :
    ⨅ l, φ l ≤ φ l := ciInf_le (Set.finite_range _).bddBelow l

theorem t3_inf_attained (hT : TypeThreeHyp n M Tr c₁) (φ : Fin M → ℝ) :
    ∃ l, φ l = ⨅ l, φ l := by
  haveI : Nonempty (Fin M) := ⟨⟨0, hT.M_pos⟩⟩
  exact exists_eq_ciInf_of_finite

/-- The chain lemma: follow the optimal continuation of `g` while it is not the stopping branch. -/
theorem t3_chain (hT : TypeThreeHyp n M Tr c₁) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf : SolvesTypeThree n M Tr f) (hg : SolvesTypeThree n M Tr g)
    (B : ℝ) (hgB : ∀ p ∈ simplex n, -B ≤ g p) (p : Fin (n + 1) → ℝ) (hp : p ∈ simplex n) :
    ∃ q ∈ simplex n, f p - g p ≤ f q - g q ∧ (q = p ∨ ∃ l r, r ∈ simplex n ∧ q = Tr l r) ∧
      (q = vertex n 0 ∨ g q = 1 + ∑ k, q k * g (vertex n k)) := by
  have main : ∀ m : ℕ, ∀ q ∈ simplex n, f p - g p ≤ f q - g q →
      (q = p ∨ ∃ l r, r ∈ simplex n ∧ q = Tr l r) → g q < m - B →
      ∃ q ∈ simplex n, f p - g p ≤ f q - g q ∧ (q = p ∨ ∃ l r, r ∈ simplex n ∧ q = Tr l r) ∧
        (q = vertex n 0 ∨ g q = 1 + ∑ k, q k * g (vertex n k)) := by
    intro m
    induction m with
    | zero =>
      intro q hq _ _ hlt
      have := hgB q hq
      simp at hlt; linarith
    | succ m ih =>
      intro q hq hd hor hlt
      by_cases h0 : q = vertex n 0
      · exact ⟨q, hq, hd, hor, Or.inl h0⟩
      by_cases hA : g q = 1 + ∑ k, q k * g (vertex n k)
      · exact ⟨q, hq, hd, hor, Or.inr hA⟩
      have hgq := hg.2 q hq h0
      have hgq' : g q = ⨅ l, (1 + g (Tr l q)) := by
        rcases min_choice (1 + ∑ k, q k * g (vertex n k)) (⨅ l, (1 + g (Tr l q))) with h | h
        · exact absurd (hgq.trans h) hA
        · exact hgq.trans h
      obtain ⟨l, hl⟩ := t3_inf_attained hT (fun l => 1 + g (Tr l q))
      have hfq : f q ≤ 1 + f (Tr l q) := by
        rw [hf.2 q hq h0]
        exact (min_le_right _ _).trans (t3_inf_le hT (fun l => 1 + f (Tr l q)) l)
      have hgl : g q = 1 + g (Tr l q) := hgq'.trans hl.symm
      apply ih (Tr l q) (hT.mapsTo l q hq) (by linarith) (Or.inr ⟨l, q, hq, rfl⟩)
      push_cast at hlt; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (g p + B)
  exact main m p hp le_rfl (Or.inl rfl) (by linarith)

theorem t3_bound (hT : TypeThreeHyp n M Tr c₁) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf_bdd : BoundedOnSimplex n f) (hf : SolvesTypeThree n M Tr f)
    (hg_bdd : BoundedOnSimplex n g) (hg : SolvesTypeThree n M Tr g)
    (p : Fin (n + 1) → ℝ) (hp : p ∈ simplex n) :
    f p - g p ≤ ⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)| := by
  set V := ⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)|
  have hV : ∀ k, |f (vertex n k) - g (vertex n k)| ≤ V := fun k =>
    le_ciSup (f := fun k : Fin (n + 1) => |f (vertex n k) - g (vertex n k)|) (Set.finite_range _).bddAbove k
  have hV0 : 0 ≤ V := le_trans (abs_nonneg _) (hV 0)
  obtain ⟨B, hB⟩ := hg_bdd
  obtain ⟨q, hq, hd, -, hend⟩ := t3_chain hT f g hf hg B (fun p hp => by
    have := hB p hp; linarith [neg_abs_le (g p)]) p hp
  refine le_trans hd ?_
  rcases hend with h0 | hA
  · rw [h0, hf.1, hg.1]; simpa using hV0
  · have hne : q ≠ vertex n 0 := by
      intro h; subst h
      rw [hg.1, t3_sum_vertex, hg.1] at hA; norm_num at hA
    have hfq : f q ≤ 1 + ∑ k, q k * f (vertex n k) := by
      rw [hf.2 q hq hne]; exact min_le_left _ _
    have : ∑ k, q k * f (vertex n k) - ∑ k, q k * g (vertex n k) ≤ V := by
      rw [← Finset.sum_sub_distrib]
      calc ∑ k, (q k * f (vertex n k) - q k * g (vertex n k)) ≤ ∑ k, q k * V := by
            apply Finset.sum_le_sum; intro k _
            rw [← mul_sub]
            exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hV k)) (hq.1 k)
        _ = V := by rw [← Finset.sum_mul, hq.2, one_mul]
    linarith

theorem t3_sup_core (n M : ℕ)
    (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (c₁ : ℝ)
    (hT : TypeThreeHyp n M Tr c₁) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf_bdd : BoundedOnSimplex n f) (hf : SolvesTypeThree n M Tr f)
    (hg_bdd : BoundedOnSimplex n g) (hg : SolvesTypeThree n M Tr g) :
    IsLUB ((fun p => |f p - g p|) '' simplex n)
      (⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)|) := by
  constructor
  · rintro _ ⟨p, hp, rfl⟩
    have h1 := t3_bound hT f g hf_bdd hf hg_bdd hg p hp
    have h2 := t3_bound hT g f hg_bdd hg hf_bdd hf p hp
    have e : (⨆ k : Fin (n + 1), |g (vertex n k) - f (vertex n k)|)
        = ⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)| := by
      congr 1; ext k; exact abs_sub_comm _ _
    rw [e] at h2
    simp only
    rw [abs_le]; constructor <;> linarith
  · intro b hb
    apply ciSup_le
    intro k
    exact hb ⟨vertex n k, t3_vertex_mem k, rfl⟩

end T3

end BellmanDP.ExistUnique

open BellmanDP.ExistUnique


theorem solution (n M : ℕ)
    (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (c₁ : ℝ)
    (hT : TypeThreeHyp n M Tr c₁) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf_bdd : BoundedOnSimplex n f) (hf : SolvesTypeThree n M Tr f)
    (hg_bdd : BoundedOnSimplex n g) (hg : SolvesTypeThree n M Tr g) :
    IsLUB ((fun p => |f p - g p|) '' simplex n)
      (⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)|) := by
  exact t3_sup_core n M Tr c₁ hT f g hf_bdd hf hg_bdd hg
