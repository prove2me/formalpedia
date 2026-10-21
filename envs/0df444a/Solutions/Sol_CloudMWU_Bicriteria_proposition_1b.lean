-- Prove2me | solution 1 for CloudMWU.Bicriteria.proposition_1b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:47:45.171426+00:00
-- url     : https://prove2.me/submissions/9dea06c0-d549-4fa5-81d6-53fa0148bc03

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

open Finset CloudMWU.Bicriteria

/-- derivative of `u ↦ u * log (u / c)` -/
theorem cloudmwu_p1b_hasDeriv (c u : ℝ) (hc : 0 < c) (hu : 0 < u) :
    HasDerivAt (fun v => v * Real.log (v / c)) (Real.log (u / c) + 1) u := by
  have h1 : HasDerivAt (fun v => v / c) (1 / c) u := (hasDerivAt_id u).div_const c
  have h2 : HasDerivAt (fun v => Real.log (v / c)) ((1 / c) / (u / c)) u :=
    h1.log (by positivity)
  have h3 := (hasDerivAt_id' u).mul h2
  have e : u * (1 / c / (u / c)) = 1 := by
    have := hc.ne'; have := hu.ne'
    field_simp
  rw [e, one_mul] at h3
  exact h3

/-- one-sided Fermat: if `g` has derivative `d` at `0` and `g 0 ≤ g t` on `[0, δ]`, `δ > 0`,
then `0 ≤ d`. -/
theorem cloudmwu_p1b_fermat (g : ℝ → ℝ) (d δ : ℝ) (hδ : 0 < δ) (hg : HasDerivAt g d 0)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) δ, g 0 ≤ g t) : 0 ≤ d := by
  have hloc : IsLocalMinOn g (Set.Icc 0 δ) 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => hmin t ht)
  have hf : HasFDerivWithinAt g (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) d)
      (Set.Icc 0 δ) 0 := hg.hasDerivWithinAt.hasFDerivWithinAt
  have hy : δ ∈ posTangentConeAt (Set.Icc (0 : ℝ) δ) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [zero_add, segment_eq_Icc hδ.le]
  have := hloc.hasFDerivWithinAt_nonneg hf hy
  simp at this
  nlinarith

/-- exchange inequality at a KL minimizer -/
theorem cloudmwu_p1b_exchange (N : ℕ) (ε : ℝ) (y x : Fin N → ℝ) (hx : IsKLProj ε y x)
    (i j : Fin N) (hij : i ≠ j) (hi : ε / (N : ℝ) < x i) (hεN : 0 < ε / (N : ℝ)) :
    Real.log (x i / y i) ≤ Real.log (x j / y j) := by
  obtain ⟨hy, ⟨hsum, hfl⟩, hmin⟩ := hx
  have hxj : 0 < x j := lt_of_lt_of_le hεN (hfl j)
  have hxi : 0 < x i := lt_trans hεN hi
  set δ := x i - ε / (N : ℝ) with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  -- perturbed point
  let x' : ℝ → Fin N → ℝ := fun t k =>
    x k + (if k = j then t else 0) - (if k = i then t else 0)
  have hfeas : ∀ t ∈ Set.Icc (0 : ℝ) δ, x' t ∈ truncSimplex N ε := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simp only [x', Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hsum]
      ring
    · intro k
      simp only [x']
      by_cases hki : k = i
      · subst hki
        rw [if_neg hij, if_pos rfl]
        have := ht.2; rw [hδ] at this; linarith
      · rw [if_neg hki]
        split_ifs <;> linarith [hfl k, ht.1]
  -- objective along the segment
  let g : ℝ → ℝ := fun t =>
    (x j + t) * Real.log ((x j + t) / y j) + (x i - t) * Real.log ((x i - t) / y i)
  have hobj : ∀ t, klObj (x' t) y = klObj x y + (g t - g 0) := by
    intro t
    unfold klObj
    have : ∑ k, x' t k * Real.log (x' t k / y k) - ∑ k, x k * Real.log (x k / y k)
        = g t - g 0 := by
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_add_of_mem j i (Finset.mem_univ _) (Finset.mem_univ _) (Ne.symm hij)]
      · simp only [x', g, if_neg hij, if_neg (Ne.symm hij), ↓reduceIte, add_zero, sub_zero]
        ring
      · intro k _ hk
        simp only [x', if_neg hk.1, if_neg hk.2, add_zero, sub_zero, sub_self]
    linarith
  have hgmin : ∀ t ∈ Set.Icc (0 : ℝ) δ, g 0 ≤ g t := by
    intro t ht
    have := hmin (x' t) (hfeas t ht)
    rw [hobj t] at this
    linarith
  -- derivative of g at 0
  have hgd : HasDerivAt g ((Real.log (x j / y j) + 1) - (Real.log (x i / y i) + 1)) 0 := by
    have hA : HasDerivAt (fun t => (x j + t) * Real.log ((x j + t) / y j))
        (Real.log ((x j + 0) / y j) + 1) 0 := by
      have := cloudmwu_p1b_hasDeriv (y j) (x j + 0) (hy j) (by linarith)
      have h2 := this.comp (0 : ℝ) ((hasDerivAt_id (0:ℝ)).const_add (x j))
      simpa only [mul_one, Function.comp_def, id] using h2
    have hB : HasDerivAt (fun t => (x i - t) * Real.log ((x i - t) / y i))
        ((Real.log ((x i - 0) / y i) + 1) * (-1)) 0 := by
      have := cloudmwu_p1b_hasDeriv (y i) (x i - 0) (hy i) (by linarith)
      have h2 := this.comp (0 : ℝ) ((hasDerivAt_id (0:ℝ)).const_sub (x i))
      simpa only [Function.comp_def, id] using h2
    have := hA.add hB
    have e : (Real.log (x j / y j) + 1) - (Real.log (x i / y i) + 1)
        = Real.log ((x j + 0) / y j) + 1 + (Real.log ((x i - 0) / y i) + 1) * -1 := by
      simp only [add_zero, sub_zero]; ring
    rw [e]; exact this
  have := cloudmwu_p1b_fermat g _ δ hδpos hgd hgmin
  linarith

theorem solution (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (y : Fin N → ℝ) (hy : ∀ i, 0 < y i) (x : Fin N → ℝ) (hx : IsKLProj ε y x) :
    ∃ μ : Fin N → ℝ, (∀ i, 0 ≤ μ i) ∧
      (∀ i, x i ≠ ε / (N : ℝ) → μ i = 0) ∧
      ∀ i, x i = y i * Real.exp (μ i) *
        ((1 - ε / (N : ℝ) * ((univ.filter (fun j => x j = ε / (N : ℝ))).card : ℝ)) /
          ∑ j ∈ univ.filter (fun j => x j ≠ ε / (N : ℝ)), y j) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hεN : 0 < ε / (N : ℝ) := by positivity
  have hx0 := hx
  obtain ⟨_, ⟨hsum, hfl⟩, _⟩ := hx0
  set S := univ.filter (fun j => x j = ε / (N : ℝ)) with hS
  set T := univ.filter (fun j => x j ≠ ε / (N : ℝ)) with hT
  have hxpos : ∀ k, 0 < x k := fun k => lt_of_lt_of_le hεN (hfl k)
  -- T is nonempty
  have hTne : T.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hall : ∀ k, x k = ε / (N : ℝ) := by
      intro k
      by_contra hk
      have : k ∈ T := by simp [hT, hk]
      rw [hne] at this; simp at this
    have : ∑ k, x k = ε := by
      simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    linarith
  obtain ⟨i₀, hi₀⟩ := hTne
  have hi₀' : ε / (N : ℝ) < x i₀ := by
    have : x i₀ ≠ ε / (N : ℝ) := by simpa [hT] using hi₀
    exact lt_of_le_of_ne (hfl i₀) (Ne.symm this)
  set C := x i₀ / y i₀ with hC
  have hCpos : 0 < C := div_pos (hxpos i₀) (hy i₀)
  -- ratios
  have hge : ∀ k, C ≤ x k / y k := by
    intro k
    by_cases hk : k = i₀
    · rw [hk]
    · have := cloudmwu_p1b_exchange N ε y x hx i₀ k (Ne.symm hk) hi₀' hεN
      exact (Real.log_le_log_iff hCpos (div_pos (hxpos k) (hy k))).mp this
  have heqT : ∀ k, x k ≠ ε / (N : ℝ) → x k / y k = C := by
    intro k hk
    have hk' : ε / (N : ℝ) < x k := lt_of_le_of_ne (hfl k) (Ne.symm hk)
    apply le_antisymm _ (hge k)
    by_cases hki : k = i₀
    · rw [hki]
    · have := cloudmwu_p1b_exchange N ε y x hx k i₀ hki hk' hεN
      exact (Real.log_le_log_iff (div_pos (hxpos k) (hy k)) hCpos).mp this
  -- the constant formula
  have hsplit : ∑ k, x k = ∑ k ∈ S, x k + ∑ k ∈ T, x k := by
    rw [hS, hT, Finset.sum_filter_add_sum_filter_not]
  have hSsum : ∑ k ∈ S, x k = ε / (N : ℝ) * (S.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun k hk => (Finset.mem_filter.mp hk).2)]
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hTsum : ∑ k ∈ T, x k = C * ∑ k ∈ T, y k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : x k ≠ ε / (N : ℝ) := (Finset.mem_filter.mp hk).2
    have := heqT k hk'
    have hyk := hy k
    field_simp at this
    linarith
  have hTy : 0 < ∑ k ∈ T, y k := Finset.sum_pos (fun k _ => hy k) ⟨i₀, hi₀⟩
  have hKC : (1 - ε / (N : ℝ) * (S.card : ℝ)) / ∑ k ∈ T, y k = C := by
    rw [div_eq_iff hTy.ne']
    linarith
  rw [hKC]
  refine ⟨fun k => Real.log (x k / (y k * C)), ?_, ?_, ?_⟩
  · intro k
    apply Real.log_nonneg
    rw [le_div_iff₀ (mul_pos (hy k) hCpos), one_mul]
    have := hge k
    rw [le_div_iff₀ (hy k)] at this
    linarith
  · intro k hk
    have := heqT k hk
    simp only
    rw [show y k * C = x k by
      have hyk := hy k
      field_simp at this; linarith]
    rw [div_self (hxpos k).ne', Real.log_one]
  · intro k
    simp only
    rw [Real.exp_log (div_pos (hxpos k) (mul_pos (hy k) hCpos))]
    have := hy k
    field_simp
