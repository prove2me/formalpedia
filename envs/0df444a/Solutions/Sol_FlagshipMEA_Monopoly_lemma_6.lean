-- Prove2me | solution 1 for FlagshipMEA.Monopoly.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:01:39.283369+00:00
-- url     : https://prove2.me/submissions/1555677b-ed95-405b-8ac8-29a7ae5cdc37

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model
import Theorems.Thm_FlagshipMEA_Monopoly_lemma_4
import Theorems.Thm_FlagshipMEA_Monopoly_lemma_5
import Theorems.Thm_FlagshipMEA_Monopoly_index_revenue

open FlagshipMEA.Monopoly

theorem solution {n : ℕ} (D : Data n) (hS : D.Standing)
    (hfc : D.FcConcave) (hD : D.Distinct) (hn : 0 < n)
    (m : Fin n → ℝ) (hm : D.IsOptimal m) (hM : 0 < tme m) :
    ∃! i : Fin n, D.IsArgmaxR (tme m) i := by
  set M := tme m with hMdef
  have hlam : 0 < D.lam := hS.1
  have hmk : ∀ i, 0 < D.markup i := hS.2.1
  have hC1 : ContDiffOn ℝ 1 D.c (Set.Ici D.θ) := hS.2.2.2.2
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k0, hk0, hrev0, -⟩ := lemma_4 D hS hn M hM
  -- notation
  set φ : ℝ → ℝ := fun t => D.c (D.lam * Real.log (t + D.base)) with hφ
  set a : Fin n → ℝ := fun k => Real.exp (D.u k / D.lam) with ha
  set w : Fin n → ℝ := fun j => Real.exp ((D.u j + D.θ) / D.lam) with hw
  set S1 : ℝ := ∑ j, w j * D.markup j with hS1
  set S2 : ℝ := ∑ j, w j with hS2
  have ha0 : ∀ k, 0 < a k := fun k => Real.exp_pos _
  have hw0 : ∀ k, 0 < w k := fun k => Real.exp_pos _
  have hS2n : 0 ≤ S2 := Finset.sum_nonneg (fun j _ => (hw0 j).le)
  have hS1p : 0 < S1 := Finset.sum_pos (fun j _ => mul_pos (hw0 j) (hmk j))
    Finset.univ_nonempty
  have hbase : 0 < D.base := Real.exp_pos _
  -- closed form of the index
  have hR : ∀ k (t : ℝ), 0 < t →
      D.R k t = (a k * D.markup k * t + S1) / (a k * t + (S2 + 1)) := by
    intro k t ht
    have hden : 0 < a k * t + (S2 + 1) := by nlinarith [ha0 k]
    unfold Data.R Data.A Data.B
    have hB : 0 < Real.exp (D.u k / D.lam) +
        1 / t * (∑ j, Real.exp ((D.u j + D.θ) / D.lam)) + 1 / t := by
      have h1 : 0 < 1 / t := by positivity
      have := ha0 k
      have := mul_nonneg h1.le hS2n
      simp only [ha, hS2, hw] at *
      linarith
    rw [div_eq_div_iff hB.ne' hden.ne']
    simp only [ha, hS1, hS2, hw]
    field_simp
    ring
  -- cost of a concentrated allocation
  have hcost : ∀ k (t : ℝ), D.cost (fun j => if j = k then t else 0)
      = φ t - φ 0 + ∑ _j : Fin n, φ 0 := by
    intro k t
    have : ∀ j, D.c (D.lam * Real.log ((if j = k then t else 0) + D.base))
        = (if j = k then φ t - φ 0 else 0) + φ 0 := by
      intro j; split_ifs <;> simp [hφ]
    unfold Data.cost
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  -- Step 1: every concentrated allocation on an index maximizer is optimal
  have conc_opt : ∀ k, D.IsArgmaxR M k → ∀ t, 0 < t →
      D.R k t - φ t ≤ D.R k M - φ M := by
    intro k hk t ht
    have hfeas : ∀ s, 0 ≤ s → Feasible (fun j : Fin n => if j = k then s else 0) := by
      intro s hs j; dsimp only; split_ifs <;> linarith
    have h1 := hm.2 _ (hfeas t ht.le)
    -- profit m ≤ profit of the concentrated allocation at M
    have hcm : D.cost (fun j => if j = k then M else 0) ≤ D.cost m :=
      lemma_5 D hS hfc M hM.le k m hm.1 rfl
    have hrm : D.revenue m ≤ D.revenue (fun j => if j = k0 then M else 0) :=
      hrev0 m hm.1 rfl
    have e0 := index_revenue D hS k0 M hM
    have ek := index_revenue D hS k M hM
    have et := index_revenue D hS k t ht
    have hkk0 : D.R k M = D.R k0 M := le_antisymm (hk0 k) (hk k0)
    unfold Data.profit at h1
    rw [← et, hcost] at h1
    rw [hcost] at hcm
    rw [← e0, ← hkk0] at hrm
    linarith
  -- Step 2: first-order condition
  have hx0 : D.θ < D.lam * Real.log (M + D.base) := by
    have : Real.log D.base < Real.log (M + D.base) :=
      Real.log_lt_log hbase (by linarith)
    have hlb : D.lam * Real.log D.base = D.θ := by
      unfold Data.base; rw [Real.log_exp]; field_simp
    nlinarith
  have hcd : DifferentiableAt ℝ D.c (D.lam * Real.log (M + D.base)) :=
    (hC1.contDiffAt (Ici_mem_nhds hx0)).differentiableAt one_ne_zero
  have hinner : DifferentiableAt ℝ (fun t : ℝ => D.lam * Real.log (t + D.base)) M :=
    ((differentiableAt_id.add_const _).log (by simp; linarith)).const_mul _
  have hφd : DifferentiableAt ℝ φ M := hcd.comp M hinner
  have foc : ∀ k, D.IsArgmaxR M k →
      (a k * D.markup k * (S2 + 1) - a k * S1) / (a k * M + (S2 + 1)) ^ 2 = deriv φ M := by
    intro k hk
    have hden : 0 < a k * M + (S2 + 1) := by nlinarith [ha0 k]
    have hd : HasDerivAt (fun t => (a k * D.markup k * t + S1) / (a k * t + (S2 + 1)) - φ t)
        ((a k * D.markup k * (a k * M + (S2 + 1)) - (a k * D.markup k * M + S1) * a k)
            / (a k * M + (S2 + 1)) ^ 2 - deriv φ M) M := by
      have h1 : HasDerivAt (fun t => a k * D.markup k * t + S1) (a k * D.markup k) M := by
        simpa using ((hasDerivAt_id M).const_mul (a k * D.markup k)).add_const S1
      have h2 : HasDerivAt (fun t => a k * t + (S2 + 1)) (a k) M := by
        simpa using ((hasDerivAt_id M).const_mul (a k)).add_const (S2 + 1)
      exact (h1.div h2 hden.ne').sub hφd.hasDerivAt
    have hloc : IsLocalMax (fun t => (a k * D.markup k * t + S1) / (a k * t + (S2 + 1)) - φ t) M := by
      filter_upwards [Ioi_mem_nhds hM] with t ht
      rw [← hR k t ht, ← hR k M hM]
      exact conc_opt k hk t ht
    have := hloc.hasDerivAt_eq_zero hd
    have e : (a k * D.markup k * (a k * M + (S2 + 1)) - (a k * D.markup k * M + S1) * a k)
        = a k * D.markup k * (S2 + 1) - a k * S1 := by ring
    rw [e] at this
    linarith
  -- Step 3: algebra
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => D.R i M)
  have uniq : ∀ i j, D.IsArgmaxR M i → D.IsArgmaxR M j → i = j := by
    intro i j hi hj
    have hv : D.R i M = D.R j M := le_antisymm (hj i) (hi j)
    have fi := foc i hi
    have fj := foc j hj
    rw [hR i M hM, hR j M hM] at hv
    set T := S2 + 1 with hT
    set v := (a i * D.markup i * M + S1) / (a i * M + T) with hvdef
    have hDi : 0 < a i * M + T := by nlinarith [ha0 i]
    have hDj : 0 < a j * M + T := by nlinarith [ha0 j]
    have hvi : a i * D.markup i * M + S1 = v * (a i * M + T) := by
      rw [hvdef]; field_simp
    have hvj : a j * D.markup j * M + S1 = v * (a j * M + T) := by
      rw [hv]; field_simp
    by_cases hE : v * T - S1 = 0
    · exfalso
      -- every index lies below `S1 / T`, forcing `S1 ≤ 0`
      have hk : ∀ k, D.markup k * T ≤ S1 := by
        intro k
        have hle := hi k
        have hDk : 0 < a k * M + T := by nlinarith [ha0 k]
        rw [hR k M hM, hR i M hM, ← hvdef, div_le_iff₀ hDk] at hle
        have h2 : a k * M * (D.markup k * T - S1) ≤ 0 := by nlinarith
        have h3 : 0 < a k * M := mul_pos (ha0 k) hM
        nlinarith
      have hsum : ∑ k, w k * (D.markup k * T) ≤ ∑ k, w k * S1 :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hk k) (hw0 k).le)
      have e1 : ∑ k, w k * (D.markup k * T) = S1 * T := by
        rw [hS1, Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => by ring)
      have e2 : ∑ k, w k * S1 = S2 * S1 := by rw [hS2, Finset.sum_mul]
      rw [e1, e2, hT] at hsum
      nlinarith
    · have key : ∀ k, a k * D.markup k * M + S1 = v * (a k * M + T) →
          (a k * D.markup k * T - a k * S1) * M = (a k * M + T) * (v * T - S1) := by
        intro k hk; linear_combination T * hk
      have ki := key i hvi
      have kj := key j hvj
      have hdi : (a i * D.markup i * T - a i * S1) = (a i * M + T) ^ 2 * deriv φ M := by
        rw [← fi]; field_simp
      have hdj : (a j * D.markup j * T - a j * S1) = (a j * M + T) ^ 2 * deriv φ M := by
        rw [← fj]; field_simp
      rw [hdi] at ki; rw [hdj] at kj
      -- `D_k * (M * d) = E` for both, so `D_i = D_j`
      have hDeq : a i * M + T = a j * M + T := by
        have hi' : (a i * M + T) * ((a i * M + T) * deriv φ M * M) = (a i * M + T) * (v * T - S1) := by
          linear_combination ki
        have hj' : (a j * M + T) * ((a j * M + T) * deriv φ M * M) = (a j * M + T) * (v * T - S1) := by
          linear_combination kj
        have ei := mul_left_cancel₀ hDi.ne' hi'
        have ej := mul_left_cancel₀ hDj.ne' hj'
        have hdM : deriv φ M * M ≠ 0 := by
          intro h0
          apply hE
          rw [← ei]; linear_combination (a i * M + T) * h0
        have : (a i * M + T) * (deriv φ M * M) = (a j * M + T) * (deriv φ M * M) := by
          linear_combination ei - ej
        exact mul_right_cancel₀ hdM this
      have haeq : a i = a j := by
        have : a i * M = a j * M := by linarith
        exact mul_right_cancel₀ hM.ne' this
      have hpeq : D.markup i = D.markup j := by
        have h1 : a i * D.markup i * M = a j * D.markup j * M := by
          rw [hDeq] at hvi
          linarith
        rw [haeq] at h1
        have h2 : a j * M ≠ 0 := (mul_pos (ha0 j) hM).ne'
        have : D.markup i * (a j * M) = D.markup j * (a j * M) := by linear_combination h1
        exact mul_right_cancel₀ h2 this
      have hueq : D.u i = D.u j := by
        have h1 : D.u i / D.lam = D.u j / D.lam := Real.exp_injective haeq
        field_simp at h1
        exact h1
      exact hD (Prod.ext hueq hpeq)
  exact ⟨i0, hi0, fun j hj => uniq j i0 hj hi0⟩
