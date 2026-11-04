-- Prove2me | solution 1 for CryptoMembership.PerfectInfo.eq15_equilibrium_iff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:11:47.955025+00:00
-- url     : https://prove2.me/submissions/ae0ee41d-a7ee-4e1e-babb-23d2b8b43e26

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model
import Theorems.Thm_CryptoMembership_PerfectInfo_proposition_1_exp_utility
import Theorems.Thm_CryptoMembership_PerfectInfo_eq13_market_clearing

open CryptoMembership.PerfectInfo MeasureTheory ProbabilityTheory Filter Topology

namespace Eq15IffAux

theorem Phi_pos (x : ℝ) : 0 < Phi x := by
  have hmono : Phi (x - 1) < Phi x := by
    rw [Phi, Phi, cdf_eq_real, cdf_eq_real, ← Set.Iic_union_Ioc_eq_Iic (by linarith : x - 1 ≤ x),
      measureReal_union (Set.disjoint_left.2 fun t ht ht' => by
        simp only [Set.mem_Iic, Set.mem_Ioc] at ht ht'; linarith) measurableSet_Ioc]
    have : 0 < (gaussianReal 0 1).real (Set.Ioc (x - 1) x) := by
      rw [measureReal_def]
      apply ENNReal.toReal_pos _ (measure_ne_top _ _)
      intro h0
      have := gaussianReal_absolutelyContinuous' 0 (one_ne_zero) h0
      rw [Real.volume_Ioc] at this
      simp at this
    linarith
  have h0 : 0 ≤ Phi (x - 1) := cdf_nonneg _ _
  linarith

end Eq15IffAux

open Eq15IffAux in
theorem solution (P : Params) (hP : P.Standing) (A xi a price : ℝ) :
    IsEquilibrium P A xi (Set.Ici a) price ↔
      0 < price ∧ lhs15 P (a - A) = rhs15 P A xi ∧
        Real.log price = Real.sqrt (P.tauEps / P.tauE) * (A - a) - xi - Real.log (1 - P.rho) := by
  set c := Real.sqrt (P.tauEps / P.tauE)
  set L := Real.log (1 - P.rho)
  set q := P.eta ^ 2 / (2 * P.tauEps)
  set u := P.eta / Real.sqrt P.tauEps + Real.sqrt P.tauEps * (A - a)
  set K1 := (1 - P.eta) * a + P.eta * A + q
  set K2 := (1 - P.eta + c) * (a - A)
  have hEU : ∀ x, expUtility P A (Set.Ici a) x = Real.exp ((1 - P.eta) * (x - a)) *
      (Real.exp K1 * Phi u) := by
    intro x
    rw [proposition_1_exp_utility P hP A x a, ← mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hEUa : Real.exp K1 * Phi u = Real.exp (K1 - K2) * lhs15 P (a - A) := by
    unfold lhs15
    have harg : P.eta / Real.sqrt P.tauEps - Real.sqrt P.tauEps * (a - A) = u := by
      simp only [u]; ring
    rw [harg, ← mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hp0 : Real.exp (c * (A - a) - xi - L) = Real.exp (K1 - K2) * rhs15 P A xi := by
    unfold rhs15
    rw [← Real.exp_add]
    congr 1
    simp only [K1, K2, q, L]; ring
  have h1η : 0 < 1 - P.eta := by linarith [hP.2.1]
  have hcont : Continuous (fun x => expUtility P A (Set.Ici a) x) := by
    simp_rw [hEU]; fun_prop
  constructor
  · intro heq
    have hp := heq.price_pos
    have hlog := (eq13_market_clearing P hP A xi a price hp).1 heq.clearing
    refine ⟨hp, ?_, hlog⟩
    -- indifference of the marginal buyer
    have hle : price ≤ expUtility P A (Set.Ici a) a := (heq.household a).1 (Set.mem_Ici.2 le_rfl)
    have hge : expUtility P A (Set.Ici a) a ≤ price := by
      by_contra hlt
      push Not at hlt
      have hev : ∀ᶠ x in 𝓝[<] a, price < expUtility P A (Set.Ici a) x :=
        ((hcont.tendsto a).eventually (lt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds
      obtain ⟨x, hx1, hx2⟩ := (hev.and self_mem_nhdsWithin).exists
      have := (heq.household x).2 hx1.le
      rw [Set.mem_Ici] at this
      exact absurd hx2 (not_lt.2 this)
    have hEq : expUtility P A (Set.Ici a) a = price := le_antisymm hge hle
    rw [hEU, sub_self, mul_zero, Real.exp_zero, one_mul, hEUa] at hEq
    have : price = Real.exp (K1 - K2) * rhs15 P A xi := by
      rw [← hp0, ← hlog, Real.exp_log hp]
    rw [this] at hEq
    exact mul_left_cancel₀ (Real.exp_pos _).ne' hEq
  · rintro ⟨hp, hl, hlog⟩
    have hEa : Real.exp K1 * Phi u = price := by
      rw [hEUa, hl, ← hp0, ← hlog, Real.exp_log hp]
    refine ⟨measurableSet_Ici, hp, fun x => ?_,
      (eq13_market_clearing P hP A xi a price hp).2 hlog⟩
    rw [hEU, hEa, Set.mem_Ici]
    constructor
    · intro hx
      have : 1 ≤ Real.exp ((1 - P.eta) * (x - a)) :=
        Real.one_le_exp (mul_nonneg h1η.le (by linarith))
      nlinarith
    · intro hx
      by_contra hxa
      push Not at hxa
      have : Real.exp ((1 - P.eta) * (x - a)) < 1 :=
        lt_of_lt_of_eq (Real.exp_lt_exp.2 (mul_neg_of_pos_of_neg h1η (by linarith))) Real.exp_zero
      nlinarith
