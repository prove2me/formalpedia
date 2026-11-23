-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.betaFactorisation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:36.457082+00:00
-- url     : https://prove2.me/submissions/cc6853fd-43f2-4ac1-8d44-8861e1705367

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_sqrt_prod_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_prob_and_eq_mul_of_disjoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_prod_split_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_u_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_u_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Factorisation := by
  intro c de de' ka T T' Y l h hw hw' hT hT' hl hlk hne hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  have hk := h.hk
  have hk1 : 1 ≤ c.k := by omega
  have hlR : (l : ℝ) + 2 ≤ c.k := by exact_mod_cast hlk
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hvl' : c.v l = c.vlast + 4 * c.Del * ((c.k : ℝ) - 1 - l) := rfl
  have m1 : 4 * c.Del * 1 ≤ 4 * c.Del * ((c.k : ℝ) - 1 - l) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hv0 := h.hv0
  have hYneg : Y ≤ -(7 / 2 * c.Del) := by linarith
  have hvl1 : c.v l ≤ c.v 1 := by simp only [Cfg.v]; push_cast; nlinarith
  have hkD : 0 < 4 * (c.k : ℝ) * c.Del := by
    have : (0 : ℝ) < c.k := by linarith
    positivity
  have ha : 0 < Y + 1 / 2 + c.a := by have := h.ha; linarith
  have hbj : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → 1 ≤ c.b j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact h.hb1
    | succ n hn ih =>
      intro hm
      have i1 := ih (by omega)
      have i2 := h.hgap n hn (by omega)
      linarith
  have hvi : ∀ i : ℕ, c.v i + Y = (c.v l + Y) + 4 * c.Del * ((l : ℝ) - i) := by
    intro i; simp only [Cfg.v]; ring

  have hle : ∀ i : ℕ, i < l → c.v l + Y + 4 * c.Del ≤ c.v i + Y := by
    intro i hi
    have : (i : ℝ) + 1 ≤ l := by exact_mod_cast hi
    have : 4 * c.Del * 1 ≤ 4 * c.Del * ((l : ℝ) - i) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [hvi i]; linarith
  have hge : ∀ i : ℕ, l < i → c.v i + Y ≤ c.v l + Y - 4 * c.Del := by
    intro i hi
    have : (l : ℝ) + 1 ≤ i := by exact_mod_cast hi
    have : 4 * c.Del * 1 ≤ 4 * c.Del * ((i : ℝ) - l) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [hvi i]; linarith
  have hA0 : ∀ i : ℕ, Y + c.v i ≠ 0 ∧ Y + 1 + c.v i ≠ 0 := by
    intro i
    rcases lt_trichotomy i l with hi | hi | hi
    · have := hle i hi
      constructor <;> apply ne_of_gt <;> linarith
    · subst hi
      constructor <;> apply ne_of_gt <;> linarith
    · have := hge i hi
      constructor <;> apply ne_of_lt <;> linarith
  have hW : ∀ (e : ℕ → ℝ), IsWord c.k e → ∀ i : ℕ, c.v i - e i * c.Del - -Y ≠ 0 := by
    intro e he i
    rcases lt_trichotomy i l with hi | hi | hi
    · have := hle i hi
      apply ne_of_gt
      rcases he.1 i with a | a <;> rw [a] <;> linarith
    · subst hi
      rcases he.1 i with a | a <;> rw [a]
      · apply ne_of_gt; linarith
      · apply ne_of_lt; linarith
    · have := hge i hi
      apply ne_of_lt
      rcases he.1 i with a | a <;> rw [a] <;> linarith
  have hbp : c.top = true → 0 < c.bp + -Y - 1 / 2 := by
    intro ht
    obtain ⟨hb1, _⟩ := h.htop ht
    have := h.hb1
    linarith

  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ, A = fun i => (c.v i - -Y) * (c.v i + 1 - -Y) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ → ℝ,
      B = fun i => (Y + 1 / 2 + c.u de (i + 1)) * (Y + 1 / 2 + c.u de' (i + 1)) := ⟨_, rfl⟩
  obtain ⟨Nn, hNdef⟩ : ∃ Nn : ℕ → ℝ, Nn = fun j => (c.b j + -Y) * (c.b j + -Y - 1) := ⟨_, rfl⟩
  have hB : ∀ i ∈ Icc 1 (c.k - 1), B i ≠ 0 ∧
      c.rho de de' (-Y) i = Real.sqrt |A i| / Real.sqrt |B i| := by
    intro i hi
    rw [mem_Icc] at hi
    by_cases hc : c.top = true ∧ i + 1 = c.k
    · have p := hbp hc.1
      have eB : B i = (c.bp + -Y - 1 / 2) ^ 2 := by
        rw [hBdef]
        simp only [Sz6.u_top c de i hi.1 hc.1 hc.2, Sz6.u_top c de' i hi.1 hc.1 hc.2]
        ring
      refine ⟨by rw [eB]; positivity, ?_⟩
      rw [eB, abs_of_nonneg (sq_nonneg (c.bp + -Y - 1 / 2)), Real.sqrt_sq p.le, hAdef]
      simp only [Cfg.rho, if_pos hc]
    · have eB : B i = (c.v i - de i * c.Del - -Y) * (c.v i - de' i * c.Del - -Y) := by
        rw [hBdef]
        simp only [Sz6.u_succ c de hw i hi.1 hc, Sz6.u_succ c de' hw' i hi.1 hc]
        ring
      refine ⟨by rw [eB]; exact mul_ne_zero (hW de hw i) (hW de' hw' i), ?_⟩
      rw [eB, hAdef]
      simp only [Cfg.rho, if_neg hc]
  have hN : ∀ j ∈ Icc 1 c.m, 0 < Nn j := by
    intro j hj
    rw [mem_Icc] at hj
    have := hbj j hj.1 hj.2
    rw [hNdef]
    apply mul_pos <;> linarith
  have hq : c.q de de' T T' Y =
      -(T * T') * ((Y + 1 / 2 + c.a) ^ 2 * ∏ i ∈ Icc 1 (c.k - 1), B i) := by
    unfold Cfg.q
    rw [Sz6.prod_split_first c.k hk1, hBdef]
    have u1 : ∀ e : ℕ → ℝ, c.u e 1 = c.a := by intro e; simp only [Cfg.u, if_true]
    rw [u1, u1]
    ring
  have hPP : c.P Y * c.P (Y + 1) = (∏ j ∈ Icc 1 c.m, Nn j) * ∏ i ∈ Icc 1 (c.k - 1), A i := by
    rw [Sz6.prob_and_eq_mul_of_disjoint c hk1, Sz6.prob_and_eq_mul_of_disjoint c hk1, hNdef, hAdef]
    have x1 : (∏ j ∈ Icc 1 c.m, (c.b j + -Y) * (c.b j + -Y - 1)) =
        (∏ j ∈ Icc 1 c.m, (Y - c.b j)) * ∏ j ∈ Icc 1 c.m, (Y + 1 - c.b j) := by
      rw [← prod_mul_distrib]; apply prod_congr rfl; intro j _; ring
    have x2 : (∏ i ∈ Icc 1 (c.k - 1), (c.v i - -Y) * (c.v i + 1 - -Y)) =
        (∏ i ∈ Icc 1 (c.k - 1), (Y + c.v i)) * ∏ i ∈ Icc 1 (c.k - 1), (Y + 1 + c.v i) := by
      rw [← prod_mul_distrib]; apply prod_congr rfl; intro j _; ring
    rw [x1, x2]; ring
  have hbne : ∀ j ∈ Icc 1 c.m, Y - c.b j ≠ 0 ∧ Y + 1 - c.b j ≠ 0 := by
    intro j hj
    rw [mem_Icc] at hj
    have := hbj j hj.1 hj.2
    constructor <;> apply ne_of_lt <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hq]
    refine mul_ne_zero (neg_ne_zero.mpr (mul_pos hT hT').ne') (mul_ne_zero (by positivity) ?_)
    exact prod_ne_zero_iff.mpr (fun i hi => (hB i hi).1)
  · rw [Sz6.prob_and_eq_mul_of_disjoint c hk1]
    exact mul_ne_zero (prod_ne_zero_iff.mpr (fun i _ => (hA0 i).1))
      (prod_ne_zero_iff.mpr (fun j hj => (hbne j hj).1))
  · rw [Sz6.prob_and_eq_mul_of_disjoint c hk1]
    exact mul_ne_zero (prod_ne_zero_iff.mpr (fun i _ => (hA0 i).2))
      (prod_ne_zero_iff.mpr (fun j hj => (hbne j hj).2))
  · have hTT : 0 < T * T' := mul_pos hT hT'
    have hNpos : 0 ≤ ∏ j ∈ Icc 1 c.m, Nn j := prod_nonneg (fun j hj => (hN j hj).le)
    have habs : |c.P Y * c.P (Y + 1) / c.q de de' T T' Y| =
        ((∏ j ∈ Icc 1 c.m, Nn j) * ∏ i ∈ Icc 1 (c.k - 1), |A i|) /
          (T * T' * ((Y + 1 / 2 + c.a) ^ 2 * ∏ i ∈ Icc 1 (c.k - 1), |B i|)) := by
      rw [hPP, hq, abs_div, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hTT,
        abs_of_nonneg hNpos, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Y + 1 / 2 + c.a) ^ 2),
        Finset.abs_prod, Finset.abs_prod]
    have hrho : ∏ i ∈ Icc 1 (c.k - 1), c.rho de de' (-Y) i =
        (∏ i ∈ Icc 1 (c.k - 1), Real.sqrt |A i|) / ∏ i ∈ Icc 1 (c.k - 1), Real.sqrt |B i| := by
      rw [← prod_div_distrib]
      exact prod_congr rfl (fun i hi => (hB i hi).2)
    have hNd : c.Nd (-Y) = ∏ j ∈ Icc 1 c.m, Real.sqrt (Nn j) := by
      rw [hNdef]; rfl
    have hU : c.U1 (-Y) = (Y + 1 / 2 + c.a)⁻¹ := by
      simp only [Cfg.U1, one_div]; congr 1; ring
    simp only [Cfg.be, Cfg.core]
    rw [habs, hrho, hNd, hU,
      Real.sqrt_div (mul_nonneg hNpos (prod_nonneg (fun i _ => abs_nonneg _))),
      Real.sqrt_mul hNpos, Real.sqrt_mul hTT.le, Real.sqrt_mul (sq_nonneg (Y + 1 / 2 + c.a)),
      Real.sqrt_sq ha.le, Sz6.sqrt_prod_nonneg _ _ (fun j hj => (hN j hj).le),
      Sz6.sqrt_prod_nonneg _ _ (fun i _ => abs_nonneg _),
      Sz6.sqrt_prod_nonneg _ _ (fun i _ => abs_nonneg _)]
    generalize Y + 1 / 2 + c.a = W
    ring
end Formalism.FourierDecayAlt.P
