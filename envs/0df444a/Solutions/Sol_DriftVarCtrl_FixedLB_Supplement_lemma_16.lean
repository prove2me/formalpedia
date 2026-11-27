-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.Supplement.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:38:53.84884+00:00
-- url     : https://prove2.me/submissions/478edf15-3a27-41f1-ab06-91ea47154ffc

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_FreeModel
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

open DriftVarCtrl
open DriftVarCtrl.FixedLB
open DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 16 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-28, (175)). When `Ũ > 0` satisfies `h⁺₁(Ũ) = h₁`,
`dᵁ₁(Ũ)(h₁ − h*₁(Ũ)) + h*₂(Ũ) = (μ₂/μ₁) h₁ [1 + ((v₂ − v₁)/v₂) LW(−e^{−1−(−M)μ₁v₁/h₁})]`;
in other words `hᵀ₂(Ũ)` (the threshold (20) of the model with upper boundary `Ũ`) equals the
upper curve (28) at `h₁`.

Formalization Note: `dᵁ₁(Ũ)`, `h*ᵢ(Ũ)`, `hᵀ₂(Ũ)` are those of `withU p Ũ hŨ` (same drifts,
volatilities, costs and `M`, upper boundary `Ũ`). The standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem solution (p : Params) (hv : v p .one < v p .two) (Ũ : ℝ) (hŨ : 0 < Ũ)
    (hplus_eq : hplusU p .one Ũ = p.h₁) :
    dU1 (withU p Ũ hŨ) * (p.h₁ - hstar (withU p Ũ hŨ) .one) + hstar (withU p Ũ hŨ) .two
        = upperCurve p p.h₁ ∧
      hT2 (withU p Ũ hŨ) = upperCurve p p.h₁ := by
        -- uniqueness on the principal branch
        have hlt : ∀ y z : ℝ, -1 ≤ y → y < z → y * Real.exp y < z * Real.exp z := by
          intro y z hy hyz
          have ht : 0 < z - y := sub_pos.mpr hyz
          have h1 : -(z - y) + 1 < Real.exp (-(z - y)) := Real.add_one_lt_exp (by linarith)
          have h2 : Real.exp (-(z - y)) < 1 := by
            rw [Real.exp_lt_one_iff]; linarith
          have h3 : y * Real.exp (-(z - y)) < z := by
            rcases le_or_gt 0 y with h0 | h0
            · nlinarith
            · nlinarith
          have h4 : Real.exp y = Real.exp (-(z - y)) * Real.exp z := by
            rw [← Real.exp_add]; congr 1; ring
          rw [h4, ← mul_assoc]
          exact mul_lt_mul_of_pos_right h3 (Real.exp_pos z)
        have hLW : ∀ y : ℝ, -1 ≤ y → LiquidWelfareFPA.lambertW (y * Real.exp y) = y := by
          intro y hy
          have hex : ∃ z : ℝ, -1 ≤ z ∧ z * Real.exp z = y * Real.exp y := ⟨y, hy, rfl⟩
          unfold LiquidWelfareFPA.lambertW
          rw [dif_pos hex]
          obtain ⟨ha, hb⟩ := Classical.choose_spec hex
          rcases lt_trichotomy (Classical.choose hex) y with h | h | h
          · exact absurd hb (hlt _ _ ha h).ne
          · exact h
          · exact absurd hb (hlt _ _ hy h).ne'
        have hμ₁ := p.hμ₁
        have hμ₂ := p.hμ₂
        have hσ₁ := p.hσ₁
        have hσ₂ := p.hσ₂
        have hh₁ := p.hh₁
        have hv1 : 0 < v p .one := by
          simp only [v, Params.mu, Params.sig]; positivity
        have hv2 : 0 < v p .two := by
          simp only [v, Params.mu, Params.sig]; positivity
        have hσ : p.σ₂ ^ 2 / p.σ₁ ^ 2 = p.μ₂ / p.μ₁ * (v p .one / v p .two) := by
          simp only [v, Params.mu, Params.sig]; field_simp
        have hx : 0 < v p .one * Ũ := mul_pos hv1 hŨ
        have hEpos : 0 < Real.exp (-v p .one * Ũ) := Real.exp_pos _
        have hE1 : Real.exp (-v p .one * Ũ) < 1 := by
          rw [Real.exp_lt_one_iff]; linarith
        have hElow : 1 - v p .one * Ũ < Real.exp (-v p .one * Ũ) := by
          have := Real.add_one_lt_exp (x := -v p .one * Ũ) (by linarith)
          linarith
        have hD : 0 < v p .one * Ũ - 1 + Real.exp (-v p .one * Ũ) := by linarith
        have hM : -p.M * p.μ₁ * v p .one
            = p.h₁ * (v p .one * Ũ - 1 + Real.exp (-v p .one * Ũ)) := by
          rw [← hplus_eq]
          simp only [hplusU, Params.mu]
          have e : Ũ * (1 - (1 - Real.exp (-v p .one * Ũ)) / (v p .one * Ũ))
              = (v p .one * Ũ - 1 + Real.exp (-v p .one * Ũ)) / v p .one := by
            field_simp; ring
          rw [e]
          have hDne := hD.ne'
          generalize v p .one * Ũ - 1 + Real.exp (-v p .one * Ũ) = D at hDne ⊢
          field_simp
        have hLWv : LiquidWelfareFPA.lambertW (-Real.exp (-1 - (-p.M) * p.μ₁ * v p .one / p.h₁))
            = -Real.exp (-v p .one * Ũ) := by
          rw [← hLW (-Real.exp (-v p .one * Ũ)) (by linarith)]
          congr 1
          rw [hM, mul_div_cancel_left₀ _ hh₁.ne', neg_mul (Real.exp _), ← Real.exp_add]
          congr 2
          ring
        have hup : upperCurve p p.h₁ = p.μ₂ / p.μ₁ * p.h₁ * (1 + (v p .two - v p .one) / v p .two
            * (-Real.exp (-v p .one * Ũ))) := by
          simp only [upperCurve]; rw [hLWv]
        have hMe : -p.M = p.h₁ * (v p .one * Ũ - 1 + Real.exp (-v p .one * Ũ))
            / (p.μ₁ * v p .one) := by
          rw [← hM]; field_simp
        have hd : dU1 (withU p Ũ hŨ) = -(p.σ₂ ^ 2 / p.σ₁ ^ 2) * (v p .two - v p .one)
            * (Ũ * Real.exp (-v p .one * Ũ) / (1 - Real.exp (-v p .one * Ũ)))
            + p.μ₂ / p.μ₁ := rfl
        have hs1 : hstar (withU p Ũ hŨ) .one = -p.M * p.μ₁ / Ũ := rfl
        have hs2 : hstar (withU p Ũ hŨ) .two = -p.M * p.μ₂ / Ũ := rfl
        have key : dU1 (withU p Ũ hŨ) * (p.h₁ - hstar (withU p Ũ hŨ) .one)
            + hstar (withU p Ũ hŨ) .two = upperCurve p p.h₁ := by
          rw [hup, hd, hs1, hs2, hMe, hσ]
          generalize Real.exp (-v p .one * Ũ) = E at *
          have hne : (1 - E) ≠ 0 := by linarith
          field_simp
          ring
        have hplus' : hplus (withU p Ũ hŨ) .one = p.h₁ := hplus_eq
        refine ⟨key, ?_⟩
        unfold hT2
        rw [hplus', key]
