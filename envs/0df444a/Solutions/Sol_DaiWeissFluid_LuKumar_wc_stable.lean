-- Prove2me | solution 1 for DaiWeissFluid.LuKumar.wc_stable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:46:11.996561+00:00
-- url     : https://prove2.me/submissions/1a35dfef-54a0-4982-923e-09342ad57bf9

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network
import Theorems.Thm_DaiWeissFluid_LuKumar_lemma2_2_ii
import Theorems.Thm_DaiWeissFluid_LuKumar_lemma3_2
import Theorems.Thm_DaiWeissFluid_LuKumar_theta_choice
import Theorems.Thm_DaiWeissFluid_LuKumar_lyapunov_conditions

open DaiWeissFluid.LuKumar

theorem solution (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1)
    (h52 : m 1 + m 3 < 1) :
    DaiWeissFluid.ThreeBuffer.FluidStable (luKumar m).IsWorkConserving := by
  obtain ⟨θ1, θ2, hθ1a, hθ1b, hθ2a, hθ2b, hord⟩ : ∃ θ1 θ2 : ℝ, m 0 < θ1 ∧ θ1 < 1 - m 3 ∧
      m 1 < θ2 ∧ θ2 < 1 - m 2 ∧ θ2 ≤ θ1 := by
    have h := theta_choice m hm h51₁ h51₂ h52
    exact ⟨_, _, h.2.2.2⟩
  set e1 := min (θ1 * (m 0)⁻¹ - 1) ((1 - θ1) * (m 3)⁻¹ - 1) with he1
  set e2 := min (θ2 * (m 1)⁻¹ - 1) ((1 - θ2) * (m 2)⁻¹ - 1) with he2
  set ε := min e1 e2 with hεdef
  let c : Fin 2 → Fin 4 → ℝ := ![![1, 1 - θ1, 1 - θ1, 1 - θ1], ![1, 1, 1 - θ2, 0]]
  have hc : ∀ i k, 0 ≤ c i k := by
    intro i k
    fin_cases i <;> fin_cases k <;> simp [c] <;> linarith [hm 2, hm 3]
  have hcle : ∀ i k, c i k ≤ 1 := by
    intro i k
    fin_cases i <;> fin_cases k <;> simp [c] <;> linarith [hm 0, hm 1]
  have hG1 : ∀ (Q : ℝ → Fin 4 → ℝ) s, G1 θ1 Q s = ∑ k, c 0 k * Q s k := by
    intro Q s
    simp [G1, Qplus, Fin.sum_univ_four, Finset.sum_filter, c]
    ring
  have hG2 : ∀ (Q : ℝ → Fin 4 → ℝ) s, G2 θ2 Q s = ∑ k, c 1 k * Q s k := by
    intro Q s
    simp [G2, Qplus, Fin.sum_univ_four, Finset.sum_filter, c]
    ring
  have hfun1 : ∀ Q : ℝ → Fin 4 → ℝ, (fun s => ∑ k, c 0 k * Q s k) = G1 θ1 Q :=
    fun Q => funext fun s => (hG1 Q s).symm
  have hfun2 : ∀ Q : ℝ → Fin 4 → ℝ, (fun s => ∑ k, c 1 k * Q s k) = G2 θ2 Q :=
    fun Q => funext fun s => (hG2 Q s).symm
  have he1pos : 0 < e1 := by
    have h0 := hm 0; have h3 := hm 3
    apply lt_min
    · rw [sub_pos, ← div_eq_mul_inv, one_lt_div h0]; exact hθ1a
    · rw [sub_pos, ← div_eq_mul_inv, one_lt_div h3]; linarith
  have he2pos : 0 < e2 := by
    have h1 := hm 1; have h2 := hm 2
    apply lt_min
    · rw [sub_pos, ← div_eq_mul_inv, one_lt_div h1]; exact hθ2a
    · rw [sub_pos, ← div_eq_mul_inv, one_lt_div h2]; linarith
  have hε : 0 < ε := lt_min he1pos he2pos
  refine ⟨1 / ε, by positivity, fun Q T hP hsum t ht k => ?_⟩
  have hsol := hP.1
  obtain ⟨-, -, hd1, hd2, hb21, hb12⟩ :=
    lyapunov_conditions m hm h51₁ h51₂ h52 θ1 θ2 hθ1a hθ1b hθ2a hθ2b hord Q T hP
  have h32 := lemma3_2 (luKumar m) hm (by norm_num) Q T hsol c hc (fun _ => ε) (fun _ => hε)
    (by
      intro i t ht hv d hd
      fin_cases i
      · simp only [Fin.zero_eta] at hd ⊢
        rw [hfun1] at hd
        have := hd1 t d ht hv hd
        linarith [min_le_left e1 e2]
      · simp only [Fin.mk_one] at hd ⊢
        rw [hfun2] at hd
        have := hd2 t d ht hv hd
        linarith [min_le_right e1 e2])
    (by
      intro i t ht hv j hj
      fin_cases i <;> fin_cases j <;> simp at hj
      · change ∑ k, c 0 k * Q t k ≤ ∑ k, c 1 k * Q t k
        change (luKumar m).volume Q 0 t = 0 at hv
        rw [← hG1, ← hG2]; exact hb12 t ht hv
      · change ∑ k, c 1 k * Q t k ≤ ∑ k, c 0 k * Q t k
        change (luKumar m).volume Q 1 t = 0 at hv
        rw [← hG1, ← hG2]; exact hb21 t ht hv)
  simp only at h32
  obtain ⟨hac, hnn, hder⟩ := h32
  set G : ℝ → ℝ := fun s => ⨆ i : Fin 2, ∑ k, c i k * Q s k with hGdef
  have hTae : ∀ k, ∀ᵐ t ∂MeasureTheory.volume, DifferentiableAt ℝ (fun s => T (max s 0) k) t :=
    fun k => Monotone.ae_differentiableAt (fun a b hab =>
      hsol.T_mono k (le_max_right a 0) (le_max_right b 0) (max_le_max hab le_rfl))
  have hdrift : ∀ᵐ t : ℝ ∂MeasureTheory.volume,
      0 < t → 0 < G t → ∀ d, HasDerivAt G d t → d ≤ -ε := by
    filter_upwards [MeasureTheory.ae_all_iff.2 hTae] with t htd htpos hGpos d hd
    have hTd : ∀ k, DifferentiableAt ℝ (fun s => T s k) t := by
      intro k
      refine (htd k).congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds htpos] with s hs
      simp [max_eq_left hs.le]
    have hQd : ∀ k, DifferentiableAt ℝ (fun s => Q s k) t := by
      intro k
      have hin : DifferentiableAt ℝ (fun s => (luKumar m).inflow T k s) t := by
        by_cases h : (k : ℕ) = 0
        · simp only [ReentrantLine.inflow, h, dif_pos]
          exact differentiableAt_id
        · simp only [ReentrantLine.inflow, h, dif_neg, not_false_eq_true]
          exact (differentiableAt_const _).mul (hTd _)
      have hD : DifferentiableAt ℝ
          (fun s => Q 0 k + (luKumar m).inflow T k s - (luKumar m).μ k * T s k) t :=
        ((differentiableAt_const _).add hin).sub ((differentiableAt_const _).mul (hTd k))
      refine hD.congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds htpos] with s hs
      exact hsol.flow s hs.le k
    have hcomp : ∀ i, DifferentiableAt ℝ (fun s => ∑ k, c i k * Q s k) t := fun i =>
      DifferentiableAt.fun_sum (fun k _ => (differentiableAt_const _).mul (hQd k))
    have := hder t d htpos hGpos hd hcomp
    simpa [ciInf_const] using this
  obtain ⟨hzero, -⟩ := lemma2_2_ii G hac hnn ε hε hdrift
  have hG0 : G 0 ≤ 1 := by
    rw [← hsum]
    apply ciSup_le
    intro i
    apply Finset.sum_le_sum
    intro k _
    have := hsol.nonneg 0 le_rfl k
    nlinarith [hcle i k]
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hGt : G t = 0 := hzero t (le_trans (div_le_div_of_nonneg_right hG0 hε.le) ht)
  have hcomp0 : ∑ k, c 0 k * Q t k ≤ 0 := by
    rw [← hGt]
    exact le_ciSup (f := fun i : Fin 2 => ∑ k, c i k * Q t k) (Set.finite_range _).bddAbove 0
  have hq := hsol.nonneg t ht0
  simp [c, Fin.sum_univ_four] at hcomp0
  have hθ : 0 < 1 - θ1 := by linarith [hm 3]
  have a0 := hq 0; have a1 := hq 1; have a2 := hq 2; have a3 := hq 3
  have b1 := mul_nonneg hθ.le a1
  have b2 := mul_nonneg hθ.le a2
  have b3 := mul_nonneg hθ.le a3
  fin_cases k
  · show Q t 0 = 0
    linarith
  · show Q t 1 = 0
    have : (1 - θ1) * Q t 1 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  · show Q t 2 = 0
    have : (1 - θ1) * Q t 2 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  · show Q t 3 = 0
    have : (1 - θ1) * Q t 3 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
