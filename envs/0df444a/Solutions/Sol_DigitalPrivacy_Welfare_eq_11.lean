-- Prove2me | solution 1 for DigitalPrivacy.Welfare.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T16:55:31.604998+00:00
-- url     : https://prove2.me/submissions/43f42b70-b713-47de-9961-d8276367cfbd

import Definitions.Def_DigitalPrivacy_Welfare_Setting

open DigitalPrivacy.Welfare
open DigitalPrivacy.Strategy (abar)

private lemma priv_nonneg {β ρ ξ C : ℝ} (hb : β < 1) (hr : 0 ≤ ρ)
    (hx : 0 ≤ ξ) (hC : 0 ≤ C) : 0 ≤ abar β ρ ξ C := by
  have hb' : 0 < 1 - β := sub_pos.mpr hb
  unfold abar
  split_ifs <;> positivity

private lemma priv_activity (β ρ ψ P α : ℝ) (h : Standing β ρ ψ P α)
    (ξs Cs ξW CW : ℝ)
    (hs : DigitalPrivacy.Strategy.IsBusinessOpt β ρ ψ P ξs Cs)
    (hW : IsSocialOpt β ρ ψ P α ξW CW) :
    abar β ρ ξs Cs ≤ abar β ρ ξW CW := by
  have hp : Pi β ρ ψ P ξW CW ≤ Pi β ρ ψ P ξs Cs := hs.2 ξW CW hW.1
  have hw := hW.2 ξs Cs hs.1
  have hcs : DigitalPrivacy.Strategy.CS β ρ ξs Cs ≤
      DigitalPrivacy.Strategy.CS β ρ ξW CW := by
    apply (mul_le_mul_iff_right₀ h.2.2).mp
    have hm := mul_nonneg (sub_nonneg.mpr h.1.2.2.2.2.2.2.2.2)
      (sub_nonneg.mpr hp)
    dsimp [W] at hw
    nlinarith
  have has := priv_nonneg h.1.2.1 h.1.2.2.1 hs.1.1.1 hs.1.2
  have haw := priv_nonneg h.1.2.1 h.1.2.2.1 hW.1.1.1 hW.1.2
  apply (sq_le_sq₀ has haw).mp
  dsimp [DigitalPrivacy.Strategy.CS] at hcs
  linarith

theorem solution (β ρ ψ P α : ℝ) (h : Standing β ρ ψ P α) (ξs Cs ξW CW : ℝ)
    (hs : DigitalPrivacy.Strategy.IsBusinessOpt β ρ ψ P ξs Cs) (hW : IsSocialOpt β ρ ψ P α ξW CW)
    (hξ : ξs ≤ ξW) (hC : CW ≤ Cs) :
    DigitalPrivacy.Strategy.abar β ρ ξs Cs ≤ DigitalPrivacy.Strategy.abar β ρ ξW CW := by
  exact priv_activity β ρ ψ P α h ξs Cs ξW CW hs hW
