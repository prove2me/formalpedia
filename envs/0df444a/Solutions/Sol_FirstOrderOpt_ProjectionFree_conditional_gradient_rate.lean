-- Prove2me | solution 1 for FirstOrderOpt.ProjectionFree.conditional_gradient_rate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T20:52:45.169015+00:00
-- url     : https://prove2.me/submissions/4a75a059-af5e-428b-9f72-7dd94c591eb0

import Mathlib



namespace FirstOrderOpt.ProjectionFree

theorem fw_descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X)
    (f : E → ℝ) (fGrad : E → E →L[ℝ] ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (hcvx : ∀ x ∈ X, ∀ z ∈ X, f x + (fGrad x) (z - x) ≤ f z)
    (a b : E) (ha : a ∈ X) (hb : b ∈ X) :
    f b ≤ f a + (fGrad a) (b - a) + L / 2 * ‖b - a‖ ^ 2 := by
  set G := (fGrad a) (b - a) with hG
  set D := ‖b - a‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  have key : ∀ n : ℕ, 0 < n → f b - f a ≤ G + L * D ^ 2 * (((n:ℝ) + 1) / (2 * n)) := by
    intro n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    let p : ℕ → E := fun j => a + ((j:ℝ) / n) • (b - a)
    have hp : ∀ j ≤ n, p j ∈ X := by
      intro j hj
      apply hXconv.add_smul_sub_mem ha hb
      constructor
      · positivity
      · rw [div_le_one hnR]; exact_mod_cast hj
    have hstep : ∀ j, j < n → f (p (j+1)) - f (p j) ≤
        (1 / n) * G + L * D ^ 2 * (((j:ℝ) + 1) / n ^ 2) := by
      intro j hj
      have h1 := hcvx (p (j+1)) (hp _ hj) (p j) (hp _ hj.le)
      have hdiff : p j - p (j+1) = (-(1 / (n:ℝ))) • (b - a) := by
        simp only [p]; push_cast
        rw [← sub_eq_zero]
        simp only [add_sub_add_left_eq_sub, ← sub_smul]
        rw [smul_eq_zero]; left; field_simp; ring
      rw [hdiff, map_smul, smul_eq_mul] at h1
      have h2 : (fGrad (p (j+1))) (b - a) - G ≤ L * (((j:ℝ) + 1) / n) * D ^ 2 := by
        have e : (fGrad (p (j+1))) (b - a) - G = (fGrad (p (j+1)) - fGrad a) (b - a) := by
          simp [G]
        rw [e]
        have h3 := (fGrad (p (j+1)) - fGrad a).le_opNorm (b - a)
        have h4 := hSmooth _ (hp _ hj) a ha
        have h5 : ‖p (j+1) - a‖ = (((j:ℝ) + 1) / n) * D := by
          simp only [p, add_sub_cancel_left, norm_smul, D]
          push_cast
          rw [Real.norm_of_nonneg (by positivity)]
        rw [h5] at h4
        calc (fGrad (p (j+1)) - fGrad a) (b - a) ≤ ‖(fGrad (p (j+1)) - fGrad a) (b - a)‖ :=
              le_abs_self _
          _ ≤ ‖fGrad (p (j+1)) - fGrad a‖ * ‖b - a‖ := h3
          _ ≤ (L * ((((j:ℝ) + 1) / n) * D)) * D := by
              apply mul_le_mul_of_nonneg_right h4 hD0
          _ = L * (((j:ℝ) + 1) / n) * D ^ 2 := by ring
      have e2 : (1 / (n:ℝ)) * G + L * D ^ 2 * (((j:ℝ) + 1) / n ^ 2)
          = (1 / (n:ℝ)) * (G + L * (((j:ℝ) + 1) / n) * D ^ 2) := by
        field_simp
      rw [e2]
      have : (1 / (n:ℝ)) * (fGrad (p (j+1))) (b - a) ≤
          (1 / (n:ℝ)) * (G + L * (((j:ℝ) + 1) / n) * D ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      linarith
    have hind : ∀ m, m ≤ n → f (p m) - f a ≤ ((m:ℝ) / n) * G +
        L * D ^ 2 * ((m:ℝ) * ((m:ℝ) + 1) / (2 * n ^ 2)) := by
      intro m
      induction m with
      | zero => intro _; simp [p]
      | succ m ih =>
        intro hm
        have := ih (by omega)
        have hs := hstep m (by omega)
        have e : ((((m+1 : ℕ)):ℝ) / n) * G + L * D ^ 2 * ((((m+1:ℕ)):ℝ) * ((((m+1:ℕ)):ℝ) + 1) / (2 * n ^ 2))
            = (((m:ℝ) / n) * G + L * D ^ 2 * ((m:ℝ) * ((m:ℝ) + 1) / (2 * n ^ 2)))
              + ((1 / n) * G + L * D ^ 2 * (((m:ℝ) + 1) / n ^ 2)) := by
          push_cast; field_simp; ring
        rw [e]; linarith
    have hn' := hind n le_rfl
    have hpn : p n = b := by simp [p, hnR.ne']
    rw [hpn] at hn'
    have e : ((n:ℝ) / n) * G + L * D ^ 2 * ((n:ℝ) * ((n:ℝ) + 1) / (2 * n ^ 2))
        = G + L * D ^ 2 * (((n:ℝ) + 1) / (2 * n)) := by
      field_simp
    linarith
  by_contra hcon
  push_neg at hcon
  set ε := f b - (f a + G + L / 2 * D ^ 2) with hε
  have hεpos : 0 < ε := by linarith
  have hC : 0 ≤ L * D ^ 2 := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (L * D ^ 2 / (2 * ε))
  have hnpos : (0:ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hk := key n (by exact_mod_cast hnpos)
  have e : L * D ^ 2 * (((n:ℝ) + 1) / (2 * n)) = L / 2 * D ^ 2 + L * D ^ 2 / (2 * n) := by
    field_simp
  rw [e] at hk
  have : L * D ^ 2 / (2 * n) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  linarith

theorem cgr_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXcompact : IsCompact X)
    (f : E → ℝ) (fGrad : E → E →L[ℝ] ℝ) (L : ℝ) (hL : 0 < L)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (hcvx : ∀ x ∈ X, ∀ z ∈ X, f x + (fGrad x) (z - x) ≤ f z)
    (x y : ℕ → E) (hx0 : x 0 ∈ X) (hy0 : y 0 = x 0)
    (hx : ∀ k, 1 ≤ k → x k ∈ X) (hy : ∀ k, y k ∈ X)
    (hLO : ∀ k, 1 ≤ k → ∀ z ∈ X, (fGrad (y (k - 1))) (x k) ≤ (fGrad (y (k - 1))) z)
    (α : ℕ → ℝ) (hα : ∀ k, 1 ≤ k → α k ∈ Set.Icc (0 : ℝ) 1)
    (hyDef : ∀ k, 1 ≤ k → y k = (1 - α k) • y (k - 1) + (α k) • x k)
    (hyk_le : ∀ k, 1 ≤ k →
      f (y k) ≤ f ((1 - 2 / ((k : ℝ) + 1)) • y (k - 1) + (2 / ((k : ℝ) + 1)) • x k))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ z ∈ X, f xstar ≤ f z)
    (k : ℕ) (hk : 1 ≤ k) :
    f (y k) - f xstar ≤ (2 * L / ((k : ℝ) * ((k : ℝ) + 1))) *
      ∑ i ∈ Finset.Icc 1 k, ‖x i - y (i - 1)‖ ^ 2 := by
  -- one-step recursion
  have hrec : ∀ k, 1 ≤ k → f (y k) - f xstar ≤
      (1 - 2 / ((k:ℝ) + 1)) * (f (y (k-1)) - f xstar) +
      L / 2 * (2 / ((k:ℝ) + 1)) ^ 2 * ‖x k - y (k-1)‖ ^ 2 := by
    intro k hk
    set γ : ℝ := 2 / ((k:ℝ) + 1) with hγ
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hγ0 : 0 ≤ γ := by positivity
    have hγ1 : γ ≤ 1 := by rw [hγ, div_le_one (by linarith)]; linarith
    set y' := y (k-1)
    have hy' : y' ∈ X := hy _
    have hxk := hx k hk
    have hyt : (1 - γ) • y' + γ • x k = y' + γ • (x k - y') := by
      rw [smul_sub, sub_smul, one_smul]; abel
    have hytX : y' + γ • (x k - y') ∈ X := hXconv.add_smul_sub_mem hy' hxk ⟨hγ0, hγ1⟩
    have hd := fw_descent X hXconv f fGrad L hL.le hSmooth hcvx y' _ hy' hytX
    rw [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul,
      Real.norm_of_nonneg hγ0] at hd
    have hlo := hLO k hk xstar hxstar
    have hc := hcvx y' hy' xstar hxstar
    have e1 : (fGrad y') (x k - y') = (fGrad y') (x k) - (fGrad y') y' := map_sub _ _ _
    have e2 : (fGrad y') (xstar - y') = (fGrad y') xstar - (fGrad y') y' := map_sub _ _ _
    have h3 : γ * (fGrad y') (x k - y') ≤ γ * (f xstar - f y') := by
      apply mul_le_mul_of_nonneg_left _ hγ0; linarith
    have := hyk_le k hk
    rw [hyt] at this
    have e3 : L / 2 * (γ * ‖x k - y'‖) ^ 2 = L / 2 * γ ^ 2 * ‖x k - y'‖ ^ 2 := by ring
    nlinarith
  induction k, hk using Nat.le_induction with
  | base =>
    have h := hrec 1 le_rfl
    norm_num at h ⊢
    have : 0 ≤ ‖x 1 - y 0‖ ^ 2 := by positivity
    nlinarith
  | succ n hn ih =>
    have h := hrec (n+1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    set S := ∑ i ∈ Finset.Icc 1 n, ‖x i - y (i - 1)‖ ^ 2
    set d := ‖x (n+1) - y n‖ ^ 2
    have hd : 0 ≤ d := by positivity
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h ⊢
    have hc : 0 ≤ 1 - 2 / ((n:ℝ) + 1 + 1) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have h2 := mul_le_mul_of_nonneg_left ih hc
    have e : (1 - 2 / ((n:ℝ) + 1 + 1)) * (2 * L / ((n:ℝ) * ((n:ℝ) + 1)) * S)
        = 2 * L / (((n:ℝ) + 1) * ((n:ℝ) + 1 + 1)) * S := by
      field_simp; ring
    have e2 : 2 * L / (((n:ℝ) + 1) * ((n:ℝ) + 1 + 1)) * (S + d)
        = 2 * L / (((n:ℝ) + 1) * ((n:ℝ) + 1 + 1)) * S +
          2 * L / (((n:ℝ) + 1) * ((n:ℝ) + 1 + 1)) * d := by ring
    have h4 : L / 2 * (2 / ((n:ℝ) + 1 + 1)) ^ 2 * d ≤
        2 * L / (((n:ℝ) + 1) * ((n:ℝ) + 1 + 1)) * d := by
      apply mul_le_mul_of_nonneg_right _ hd
      rw [div_pow, show L / 2 * (2 ^ 2 / ((n:ℝ) + 1 + 1) ^ 2) = 2 * L / (((n:ℝ) + 1 + 1) * ((n:ℝ) + 1 + 1)) by ring]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    rw [e] at h2
    rw [e2]
    linarith

end FirstOrderOpt.ProjectionFree

open FirstOrderOpt.ProjectionFree


theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXcompact : IsCompact X)
    (f : E → ℝ) (fGrad : E → E →L[ℝ] ℝ) (L : ℝ) (hL : 0 < L)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (hcvx : ∀ x ∈ X, ∀ z ∈ X, f x + (fGrad x) (z - x) ≤ f z)
    (x y : ℕ → E) (hx0 : x 0 ∈ X) (hy0 : y 0 = x 0)
    (hx : ∀ k, 1 ≤ k → x k ∈ X) (hy : ∀ k, y k ∈ X)
    (hLO : ∀ k, 1 ≤ k → ∀ z ∈ X, (fGrad (y (k - 1))) (x k) ≤ (fGrad (y (k - 1))) z)
    (α : ℕ → ℝ) (hα : ∀ k, 1 ≤ k → α k ∈ Set.Icc (0 : ℝ) 1)
    (hyDef : ∀ k, 1 ≤ k → y k = (1 - α k) • y (k - 1) + (α k) • x k)
    (hyk_le : ∀ k, 1 ≤ k →
      f (y k) ≤ f ((1 - 2 / ((k : ℝ) + 1)) • y (k - 1) + (2 / ((k : ℝ) + 1)) • x k))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ z ∈ X, f xstar ≤ f z)
    (k : ℕ) (hk : 1 ≤ k) :
    f (y k) - f xstar ≤ (2 * L / ((k : ℝ) * ((k : ℝ) + 1))) *
      ∑ i ∈ Finset.Icc 1 k, ‖x i - y (i - 1)‖ ^ 2 := by
  exact cgr_core X hXconv hXcompact f fGrad L hL hSmooth hcvx x y hx0 hy0 hx hy hLO α hα hyDef hyk_le xstar hxstar hxstar_opt k hk
