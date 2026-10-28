-- Prove2me | solution 1 for CryptoMembership.PerfectInfo.proposition_1_allocation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:00:31.363143+00:00
-- url     : https://prove2.me/submissions/196eff09-ee00-415c-8ed2-3c8c03994409

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

namespace Aux_CryptoMembership_PerfectInfo_proposition_1_allocation

open CryptoMembership.PerfectInfo

lemma amgm_eq (η a b : ℝ) (h0 : 0 < η) (h1 : η < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ (1 - η) * b ^ η = (1 - η) * a + η * b) : a = b := by
  have := (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos (Finset.univ : Finset (Fin 2))
    ![1 - η, η] ![a, b] (by intro i _; fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_two]) (by intro i _; fin_cases i <;> simpa)).1
    (by simpa [Fin.prod_univ_two, Fin.sum_univ_two] using h)
  simpa using this 0 (Finset.mem_univ _) 1 (Finset.mem_univ _)

/-- Rewriting `U` in normalized coordinates. -/
lemma U_eq (η p q W x y : ℝ) (h0 : 0 < η) (h1 : η < 1) (hp : 0 < p) (hq : 0 < q) (hW : 0 < W)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    U η x y = ((W / p) ^ (1 - η) * (W / q) ^ η) *
      ((p * x / ((1 - η) * W)) ^ (1 - η) * (q * y / (η * W)) ^ η) := by
  unfold U
  have hη1 : 0 < 1 - η := by linarith
  have e1 : x / (1 - η) = (W / p) * (p * x / ((1 - η) * W)) := by field_simp
  have e2 : y / η = (W / q) * (q * y / (η * W)) := by field_simp
  rw [e1, e2, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  ring

lemma opt_bound (η p q W x y : ℝ) (h0 : 0 < η) (h1 : η < 1) (hp : 0 < p) (hq : 0 < q)
    (hW : 0 < W) (hx : 0 ≤ x) (hy : 0 ≤ y) (hbud : p * x + q * y = W) :
    U η x y ≤ (W / p) ^ (1 - η) * (W / q) ^ η := by
  have hη1 : 0 < 1 - η := by linarith
  rw [U_eq η p q W x y h0 h1 hp hq hW hx hy]
  have hK : 0 ≤ (W / p) ^ (1 - η) * (W / q) ^ η := by positivity
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hη1.le h0.le
    (by positivity : 0 ≤ p * x / ((1 - η) * W)) (by positivity : 0 ≤ q * y / (η * W))
    (by ring : 1 - η + η = 1)
  have hsum : (1 - η) * (p * x / ((1 - η) * W)) + η * (q * y / (η * W)) = 1 := by
    field_simp; linarith
  rw [hsum] at hamgm
  calc _ ≤ ((W / p) ^ (1 - η) * (W / q) ^ η) * 1 := mul_le_mul_of_nonneg_left hamgm hK
    _ = _ := mul_one _

lemma opt_value (η p q W : ℝ) (h0 : 0 < η) (h1 : η < 1) (hp : 0 < p) (hq : 0 < q)
    (hW : 0 < W) :
    U η ((1 - η) * W / p) (η * W / q) = (W / p) ^ (1 - η) * (W / q) ^ η := by
  have hη1 : 0 < 1 - η := by linarith
  unfold U
  congr 2
  · field_simp
  · field_simp

lemma opt_char (η p q W x y : ℝ) (h0 : 0 < η) (h1 : η < 1) (hp : 0 < p) (hq : 0 < q)
    (hW : 0 < W) (hx : 0 ≤ x) (hy : 0 ≤ y) (hbud : p * x + q * y = W)
    (hopt : U η ((1 - η) * W / p) (η * W / q) ≤ U η x y) :
    x = (1 - η) * W / p ∧ y = η * W / q := by
  have hη1 : 0 < 1 - η := by linarith
  have hle := opt_bound η p q W x y h0 h1 hp hq hW hx hy hbud
  rw [opt_value η p q W h0 h1 hp hq hW] at hopt
  have heq : U η x y = (W / p) ^ (1 - η) * (W / q) ^ η := le_antisymm hle hopt
  rw [U_eq η p q W x y h0 h1 hp hq hW hx hy] at heq
  have hKpos : 0 < (W / p) ^ (1 - η) * (W / q) ^ η := by positivity
  have hab : (p * x / ((1 - η) * W)) ^ (1 - η) * (q * y / (η * W)) ^ η = 1 := by
    have h2 : (W / p) ^ (1 - η) * (W / q) ^ η *
        ((p * x / ((1 - η) * W)) ^ (1 - η) * (q * y / (η * W)) ^ η) =
        (W / p) ^ (1 - η) * (W / q) ^ η * 1 := by rw [mul_one]; exact heq
    exact mul_left_cancel₀ hKpos.ne' h2
  have hsum : (1 - η) * (p * x / ((1 - η) * W)) + η * (q * y / (η * W)) = 1 := by
    field_simp; linarith
  have hab2 := amgm_eq η _ _ h0 h1 (by positivity) (by positivity) (hab.trans hsum.symm)
  have ha1 : p * x / ((1 - η) * W) = 1 := by rw [← hab2] at hsum; linarith
  have hb1 : q * y / (η * W) = 1 := by rw [← hab2]; exact ha1
  constructor
  · rw [div_eq_one_iff_eq (by positivity)] at ha1
    field_simp; linarith
  · rw [div_eq_one_iff_eq (by positivity)] at hb1
    field_simp; linarith

end Aux_CryptoMembership_PerfectInfo_proposition_1_allocation

open Aux_CryptoMembership_PerfectInfo_proposition_1_allocation in
open CryptoMembership.PerfectInfo in
theorem solution (eta Ai Aj : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (∀ pi pj cii cij cjj cji : ℝ, IsPairEquilibrium eta Ai Aj pi pj cii cij cjj cji →
      cii = (1 - eta) * Real.exp Ai ∧ cij = eta * Real.exp Aj ∧
      cjj = (1 - eta) * Real.exp Aj ∧ cji = eta * Real.exp Ai ∧
      pi / pj = Real.exp (Aj - Ai)) ∧
    (∀ pj : ℝ, 0 < pj →
      IsPairEquilibrium eta Ai Aj (pj * Real.exp (Aj - Ai)) pj
        ((1 - eta) * Real.exp Ai) (eta * Real.exp Aj) ((1 - eta) * Real.exp Aj) (eta * Real.exp Ai)) ∧
    U eta ((1 - eta) * Real.exp Ai) (eta * Real.exp Aj) = matchUtility eta Ai Aj ∧
    (1 - eta) / ((1 - eta) * Real.exp Ai) * U eta ((1 - eta) * Real.exp Ai) (eta * Real.exp Aj) =
      Real.exp (eta * (Aj - Ai)) ∧
    U eta ((1 - eta) * Real.exp Ai) (eta * Real.exp Aj) =
      Real.exp (eta * (Aj - Ai)) * Real.exp Ai := by
  have hη1 : 0 < 1 - eta := by linarith
  have heAi := Real.exp_pos Ai
  have heAj := Real.exp_pos Aj
  have hUval : U eta ((1 - eta) * Real.exp Ai) (eta * Real.exp Aj) = matchUtility eta Ai Aj := by
    unfold U matchUtility
    rw [mul_div_cancel_left₀ _ hη1.ne', mul_div_cancel_left₀ _ h0.ne', ← Real.exp_mul,
      ← Real.exp_mul, ← Real.exp_add]
    ring_nf
  refine ⟨?_, ?_, hUval, ?_, ?_⟩
  · intro pi pj cii cij cjj cji he
    have hpi := he.pi_pos
    have hpj := he.pj_pos
    obtain ⟨hcii0, hcij0, hbi⟩ := he.i_feasible
    obtain ⟨hcjj0, hcji0, hbj⟩ := he.j_feasible
    have hWi : 0 < pi * Real.exp Ai := by positivity
    have hWj : 0 < pj * Real.exp Aj := by positivity
    have ci := opt_char eta pi pj (pi * Real.exp Ai) cii cij h0 h1 hpi hpj hWi hcii0 hcij0 hbi
      (he.i_optimal _ _ (by positivity) (by positivity) (by field_simp; ring))
    have cj := opt_char eta pj pi (pj * Real.exp Aj) cjj cji h0 h1 hpj hpi hWj hcjj0 hcji0 hbj
      (he.j_optimal _ _ (by positivity) (by positivity) (by field_simp; ring))
    obtain ⟨c1, c2⟩ := ci
    obtain ⟨c3, c4⟩ := cj
    have hcl := he.clear_i
    rw [c1, c4] at hcl
    have hkey : pj * Real.exp Aj = pi * Real.exp Ai := by
      field_simp at hcl
      nlinarith
    have hratio : pi / pj = Real.exp (Aj - Ai) := by
      rw [Real.exp_sub, div_eq_div_iff hpj.ne' heAi.ne']
      linarith
    refine ⟨?_, ?_, ?_, ?_, hratio⟩
    · rw [c1]; field_simp
    · rw [c2, ← hkey]; field_simp
    · rw [c3]; field_simp
    · rw [c4, hkey]; field_simp
  · intro pj hpj
    set pi := pj * Real.exp (Aj - Ai) with hpi_def
    have hpi : 0 < pi := by positivity
    have hkey : pi * Real.exp Ai = pj * Real.exp Aj := by
      rw [hpi_def, mul_assoc, ← Real.exp_add]; ring_nf
    have hWi : 0 < pi * Real.exp Ai := by positivity
    have hWj : 0 < pj * Real.exp Aj := by positivity
    have exi : (1 - eta) * Real.exp Ai = (1 - eta) * (pi * Real.exp Ai) / pi := by
      field_simp
    have eyi : eta * Real.exp Aj = eta * (pi * Real.exp Ai) / pj := by
      rw [hkey]; field_simp
    have exj : (1 - eta) * Real.exp Aj = (1 - eta) * (pj * Real.exp Aj) / pj := by
      field_simp
    have eyj : eta * Real.exp Ai = eta * (pj * Real.exp Aj) / pi := by
      rw [← hkey]; field_simp
    refine ⟨hpi, hpj, ⟨by positivity, by positivity, ?_⟩, ?_, ⟨by positivity, by positivity, ?_⟩,
      ?_, ?_, ?_⟩
    · simp only [hpi_def] at hkey ⊢
      linear_combination (-eta) * hkey
    · intro x y hx hy hb
      rw [exi, eyi, opt_value eta pi pj _ h0 h1 hpi hpj hWi]
      exact opt_bound eta pi pj _ x y h0 h1 hpi hpj hWi hx hy hb
    · simp only [hpi_def] at hkey ⊢
      linear_combination eta * hkey
    · intro x y hx hy hb
      rw [exj, eyj, opt_value eta pj pi _ h0 h1 hpj hpi hWj]
      exact opt_bound eta pj pi _ x y h0 h1 hpj hpi hWj hx hy hb
    · ring
    · ring
  · rw [hUval]
    unfold matchUtility
    rw [div_mul_eq_mul_div, div_eq_iff (by positivity),
      show Real.exp (eta * (Aj - Ai)) * ((1 - eta) * Real.exp Ai) =
        (1 - eta) * (Real.exp (eta * (Aj - Ai)) * Real.exp Ai) by ring, ← Real.exp_add]
    ring_nf
  · rw [hUval]
    unfold matchUtility
    rw [← Real.exp_add]
    ring_nf
