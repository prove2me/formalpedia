-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.Supplement.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:02.18475+00:00
-- url     : https://prove2.me/submissions/fda4dac3-a165-43e2-bf06-190433b1c6ba

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_FreeModel
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

open DriftVarCtrl
open DriftVarCtrl.FixedLB
open DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 17 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. EC-28–EC-29, (180)). When `Ũ > 0` satisfies `h⁺₂(Ũ) = h₂`,
`(1/dᴸ₂(Ũ))(h₂ − h*₂(Ũ)) + h*₁(Ũ) = (σ₁²/σ₂²) h₂`; in other words `(hᵀ₁(Ũ), h₂)` lies on the
lower curve (29) `h₂ = (σ₂²/σ₁²) h₁`.

Formalization Note: `dᴸ₂(Ũ)`, `h*ᵢ(Ũ)`, `hᵀ₁(Ũ)` are those of `withU p Ũ hŨ` (upper boundary
`Ũ`). The standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem solution (p : Params) (hv : v p .one < v p .two) (Ũ : ℝ) (hŨ : 0 < Ũ)
    (hplus_eq : hplusU p .two Ũ = p.h₂) :
    1 / dL2 (withU p Ũ hŨ) * (p.h₂ - hstar (withU p Ũ hŨ) .two) + hstar (withU p Ũ hŨ) .one
        = p.σ₁ ^ 2 / p.σ₂ ^ 2 * p.h₂ ∧
      hT1 (withU p Ũ hŨ) = p.σ₁ ^ 2 / p.σ₂ ^ 2 * p.h₂ := by
        have hσ₁ : p.σ₁ ≠ 0 := ne_of_gt p.hσ₁
        have hσ₂ : p.σ₂ ≠ 0 := ne_of_gt p.hσ₂
        have hμ₂ : p.μ₂ ≠ 0 := ne_of_gt p.hμ₂
        have hUne : Ũ ≠ 0 := ne_of_gt hŨ
        have hv₂ : 0 < v p .two := by
          dsimp [v, Params.mu, Params.sig]
          exact div_pos (mul_pos (by norm_num) p.hμ₂) (sq_pos_of_pos p.hσ₂)
        have hv₂ne : v p .two ≠ 0 := ne_of_gt hv₂
        have hD : 1 - Real.exp (-v p .two * Ũ) ≠ 0 := by
          apply ne_of_gt
          apply sub_pos.mpr
          apply Real.exp_lt_one_iff.mpr
          nlinarith [mul_pos hv₂ hŨ]
        have hD' : 1 - Real.exp (-(Ũ * v p .two)) ≠ 0 := by
          simpa only [neg_mul, mul_comm (v p .two) Ũ] using hD
        have hDen : Ũ * (1 - (1 - Real.exp (-v p .two * Ũ)) / (v p .two * Ũ)) ≠ 0 := by
          intro hz
          have hh : p.h₂ = 0 := by
            rw [← hplus_eq]
            unfold hplusU
            rw [hz]
            exact div_zero _
          exact (ne_of_gt p.hh₂) hh
        have hcost : p.h₂ * (Ũ * (1 - (1 - Real.exp (-v p .two * Ũ)) / (v p .two * Ũ))) =
            -p.M * p.μ₂ := by
          exact ((div_eq_iff hDen).mp hplus_eq).symm
        have hratio : p.μ₁ / p.μ₂ * v p .two = p.σ₁ ^ 2 / p.σ₂ ^ 2 * v p .one := by
          dsimp [v, Params.mu, Params.sig]
          field_simp
          <;> ring
        have hratio_div : p.μ₁ / p.μ₂ = (p.σ₁ ^ 2 / p.σ₂ ^ 2 * v p .one) / v p .two := by
          exact (eq_div_iff hv₂ne).mpr hratio
        have hkey : (p.h₂ - -p.M * p.μ₂ / Ũ) *
            (Ũ / (1 - Real.exp (-v p .two * Ũ))) = p.h₂ / v p .two := by
          field_simp [hv₂ne, hUne, hD, hD'] at hcost ⊢
          nlinarith [hcost]
        have hmain : 1 / dL2 (withU p Ũ hŨ) *
            (p.h₂ - hstar (withU p Ũ hŨ) .two) + hstar (withU p Ũ hŨ) .one =
            p.σ₁ ^ 2 / p.σ₂ ^ 2 * p.h₂ := by
          change (1 / (1 / (p.μ₁ / p.μ₂ +
            (p.σ₁ ^ 2 / p.σ₂ ^ 2) * (v p .two - v p .one) *
              (Ũ / (1 - Real.exp (-v p .two * Ũ)))))) *
            (p.h₂ - -p.M * p.μ₂ / Ũ) + -p.M * p.μ₁ / Ũ = _
          rw [one_div_one_div]
          calc
            _ = p.μ₁ / p.μ₂ * p.h₂ + (p.σ₁ ^ 2 / p.σ₂ ^ 2) * (v p .two - v p .one) *
                ((p.h₂ - -p.M * p.μ₂ / Ũ) * (Ũ / (1 - Real.exp (-v p .two * Ũ)))) := by
              field_simp [hμ₂, hUne, hD, hD', hσ₂]
              <;> ring
            _ = p.μ₁ / p.μ₂ * p.h₂ + (p.σ₁ ^ 2 / p.σ₂ ^ 2) *
                (v p .two - v p .one) * (p.h₂ / v p .two) := by rw [hkey]
            _ = _ := by
              rw [hratio_div]
              field_simp [hv₂ne]
              <;> ring
        refine ⟨hmain, ?_⟩
        have hp : hplus (withU p Ũ hŨ) .two = p.h₂ := by
          simpa [hplus, hplusU, withU, v, Params.mu, Params.sig] using hplus_eq
        simpa [hT1, hp] using hmain
