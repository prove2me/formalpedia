-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.Supplement.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:49.956501+00:00
-- url     : https://prove2.me/submissions/0f5eaceb-ea0c-4539-8ff1-f11c2f673eed

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

open DriftVarCtrl
open DriftVarCtrl.FixedLB
open DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 14 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-22). Suppose `(h₁, h₂)` satisfies (27),
`(σ₂²/σ₁²) h₁ < h₂ < ĥ₂(h₁)`. Let `S* = −(1/v₁) ln w` with
`w = v₂(μ₂h₁ − h₂μ₁)/(h₁μ₂(v₂ − v₁))`, and `Ṽ₁₂^{[0,S*]}(x) = −h₁x/μ₁ − h₁e^{−v₁x}/(v₁μ₁) + h₁/(v₁μ₁)`
(172). Then `S* > 0` and `M < Ṽ₁₂^{[0,S*]}(S*) < 0`.

Formalization Note: `S*` is `Sstar p` and `Ṽ₁₂^{[0,S*]}` is `Vtil p`. The standing `v₁ < v₂`
is `hv`. -/
theorem solution (p : Params) (hv : v p .one < v p .two) (h27 : cond27 p) :
    0 < Sstar p ∧ p.M < Vtil p (Sstar p) ∧ Vtil p (Sstar p) < 0 := by
      let a := v p .one
      let b := v p .two
      have ha : 0 < a := by
        dsimp [a, v, Params.mu, Params.sig]
        exact div_pos (mul_pos (by norm_num) p.hμ₁) (sq_pos_of_pos p.hσ₁)
      have hb : 0 < b := lt_trans ha hv
      have hab : 0 < b - a := sub_pos.mpr hv
      have hμ := p.hμ₁
      have hh := p.hh₁
      have ha0 := ne_of_gt ha
      have hb0 := ne_of_gt hb
      have hμ0 := ne_of_gt hμ
      have hh0 := ne_of_gt hh
      have hμ20 := ne_of_gt p.hμ₂
      let k := (-p.M) * p.μ₁ * a / p.h₁
      have hk : 0 < k := div_pos (mul_pos (mul_pos (neg_pos.mpr p.hM) hμ) ha) hh
      let z := -Real.exp (-1 - k)
      have hzneg : z < 0 := neg_neg_of_pos (Real.exp_pos _)
      have hzlo : -Real.exp (-1) < z := by
        dsimp [z]
        exact neg_lt_neg (Real.exp_lt_exp.mpr (by linarith))
      have hex : ∃ y : ℝ, -1 ≤ y ∧ y * Real.exp y = z := by
        have hc : ContinuousOn (fun y : ℝ => y * Real.exp y) (Set.Icc (-1) 0) :=
          (continuous_id.mul Real.continuous_exp).continuousOn
        have hzmem : z ∈ Set.Icc ((-1 : ℝ) * Real.exp (-1)) (0 * Real.exp 0) := by
          constructor <;> nlinarith
        obtain ⟨y, hy, heq⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 0) hc hzmem
        exact ⟨y, hy.1, heq⟩
      let L := LiquidWelfareFPA.lambertW z
      have hL : -1 ≤ L ∧ L * Real.exp L = z := by
        dsimp [L]
        rw [LiquidWelfareFPA.lambertW, dif_pos hex]
        exact Classical.choose_spec hex
      have hLneg : L < 0 := by
        nlinarith [Real.exp_pos L]
      have hLlo : -1 < L := by
        by_contra h
        have heq : L = -1 := le_antisymm (le_of_not_gt h) hL.1
        have he := hL.2
        rw [heq] at he
        nlinarith
      let t := -L
      have ht : 0 < t := neg_pos.mpr hLneg
      have ht1 : t < 1 := by dsimp [t]; linarith
      have hteq : t * Real.exp (-t) = Real.exp (-1 - k) := by
        dsimp [t]
        simp only [neg_neg]
        have he := hL.2
        dsimp [z] at he
        nlinarith
      have htlog : Real.log t - t + 1 = -k := by
        have he := congrArg Real.log hteq
        rw [Real.log_mul (ne_of_gt ht) (ne_of_gt (Real.exp_pos _)),
          Real.log_exp, Real.log_exp] at he
        linarith
      let w := wFB p p.h₁ p.h₂
      have hd : 0 < p.h₁ * p.μ₂ * (b - a) := mul_pos (mul_pos hh p.hμ₂) hab
      have hratio : a * p.μ₂ = b * p.μ₁ * (p.σ₂ ^ 2 / p.σ₁ ^ 2) := by
        dsimp [a, b, v, Params.mu, Params.sig]
        field_simp [ne_of_gt p.hσ₁, ne_of_gt p.hσ₂]
      have hcross : a * p.μ₂ * p.h₁ < b * p.μ₁ * p.h₂ := by
        calc
          a * p.μ₂ * p.h₁ = (b * p.μ₁) * ((p.σ₂ ^ 2 / p.σ₁ ^ 2) * p.h₁) := by
            rw [hratio]; ring
          _ < (b * p.μ₁) * p.h₂ := mul_lt_mul_of_pos_left h27.1 (mul_pos hb p.hμ₁)
          _ = b * p.μ₁ * p.h₂ := by ring
      have hw1 : w < 1 := by
        dsimp [w, wFB]
        change b * (p.μ₂ * p.h₁ - p.h₂ * p.μ₁) / (p.h₁ * p.μ₂ * (b - a)) < 1
        apply (div_lt_iff₀ hd).mpr
        nlinarith
      have hu : p.h₂ < p.μ₂ / p.μ₁ * p.h₁ * (1 - (b - a) / b * t) := by
        have hu := h27.2
        change p.h₂ < p.μ₂ / p.μ₁ * p.h₁ * (1 + (b - a) / b * L) at hu
        dsimp [t]
        nlinarith [hu]
      have htw : t < w := by
        dsimp [w, wFB]
        change t < b * (p.μ₂ * p.h₁ - p.h₂ * p.μ₁) / (p.h₁ * p.μ₂ * (b - a))
        apply (lt_div_iff₀ hd).mpr
        have hu' := mul_lt_mul_of_pos_left hu (mul_pos hb hμ)
        field_simp [ha0, hb0, hμ0] at hu'
        nlinarith
      have hw : 0 < w := lt_trans ht htw
      have hwlog : Real.log w < 0 := Real.log_neg hw hw1
      have hS : 0 < Sstar p := by
        change 0 < -(1 / a) * Real.log w
        exact mul_pos_of_neg_of_neg (neg_neg_of_pos (div_pos (by norm_num) ha)) hwlog
      have hexp : Real.exp (-a * Sstar p) = w := by
        have he : -a * Sstar p = Real.log w := by
          change -a * (-(1 / a) * Real.log w) = Real.log w
          field_simp
        rw [he, Real.exp_log hw]
      have hV : Vtil p (Sstar p) = p.h₁ / (a * p.μ₁) * (Real.log w - w + 1) := by
        unfold Vtil
        change -p.h₁ * Sstar p / p.μ₁ - p.h₁ * Real.exp (-a * Sstar p) / (a * p.μ₁) +
          p.h₁ / (a * p.μ₁) = _
        rw [hexp]
        change -p.h₁ * (-(1 / a) * Real.log w) / p.μ₁ - p.h₁ * w / (a * p.μ₁) +
          p.h₁ / (a * p.μ₁) = _
        field_simp
      have hcoeff : 0 < p.h₁ / (a * p.μ₁) := div_pos hh (mul_pos ha hμ)
      have hM : p.M = p.h₁ / (a * p.μ₁) * (-k) := by
        dsimp [k]
        field_simp
      have hlogdiff : Real.log t - Real.log w < t - w := by
        have hlog := Real.log_le_sub_one_of_pos (div_pos ht hw)
        rw [Real.log_div (ne_of_gt ht) (ne_of_gt hw)] at hlog
        have hdiv : t / w - 1 < t - w := by
          apply (sub_lt_iff_lt_add).mpr
          apply (div_lt_iff₀ hw).mpr
          nlinarith
        exact lt_of_le_of_lt hlog hdiv
      have hVlo : p.M < Vtil p (Sstar p) := by
        rw [hM, hV]
        apply mul_lt_mul_of_pos_left _ hcoeff
        linarith
      have hVhi : Vtil p (Sstar p) < 0 := by
        rw [hV]
        have hlog := Real.log_lt_sub_one_of_pos hw (ne_of_lt hw1)
        exact mul_neg_of_pos_of_neg hcoeff (by linarith)
      exact ⟨hS, hVlo, hVhi⟩
