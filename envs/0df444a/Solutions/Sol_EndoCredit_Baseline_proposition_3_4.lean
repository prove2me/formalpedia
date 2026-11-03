-- Prove2me | solution 1 for EndoCredit.Baseline.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:44:50.219215+00:00
-- url     : https://prove2.me/submissions/886ff184-efc7-4466-9454-cffd6ccd9605

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Model

namespace ECDev
open EndoCredit.Baseline

theorem alpha_gt_one (p : Params) (hp : p.Core) : 1 < alphaPlus p := by
  obtain ⟨hsig, hmuI, hsigI, hrho1, hrho2, hgam, hgam1, hrI, hK, hbh, hqa, hIbar⟩ := id hp
  unfold alphaPlus
  simp only []
  rw [lt_div_iff₀ (by positivity)]
  by_cases h : 2 * quadA p + (betaHat p - rI p - quadA p) < 0
  · have := Real.sqrt_nonneg ((betaHat p - rI p - quadA p) ^ 2 + 4 * quadA p * betaHat p)
    linarith
  · push_neg at h
    have : 2 * quadA p + (betaHat p - rI p - quadA p) <
        Real.sqrt ((betaHat p - rI p - quadA p) ^ 2 + 4 * quadA p * betaHat p) := by
      apply (Real.lt_sqrt h).mpr
      nlinarith [mul_pos hqa hrI]
    linarith

theorem alpha_root (p : Params) (hp : p.Core) :
    quadA p * alphaPlus p * (alphaPlus p - 1) +
      (betaHat p - rI p) * alphaPlus p - betaHat p = 0 := by
  obtain ⟨_, _, _, _, _, _, _, hR, _, hB, hA, _⟩ := id hp
  have hap : alphaPlus p = (-(betaHat p - rI p - quadA p) +
      Real.sqrt ((betaHat p - rI p - quadA p) ^ 2 + 4 * quadA p * betaHat p)) /
      (2 * quadA p) := rfl
  have hD : 0 ≤ (betaHat p - rI p - quadA p) ^ 2 + 4 * quadA p * betaHat p := by positivity
  have hs2 := Real.sq_sqrt hD
  set s := Real.sqrt ((betaHat p - rI p - quadA p) ^ 2 + 4 * quadA p * betaHat p)
  have hx : 2 * quadA p * alphaPlus p = s - (betaHat p - rI p - quadA p) := by
    rw [hap]; field_simp; ring
  have h4 : (4 * quadA p) * (quadA p * alphaPlus p * (alphaPlus p - 1) +
      (betaHat p - rI p) * alphaPlus p - betaHat p) = 0 := by
    linear_combination (2 * quadA p * alphaPlus p + s + (betaHat p - rI p - quadA p)) * hx + hs2
  exact (mul_eq_zero.mp h4).resolve_left (by positivity)

/-- Key identity: γ K (α-1) = W (rI - (α-1) a / γ) with W = 1 - γ + αγ. -/
theorem key_identity (p : Params) (hp : p.Core) :
    p.gam * K p * (alphaPlus p - 1) =
      (1 - p.gam + alphaPlus p * p.gam) * (rI p - (alphaPlus p - 1) * quadA p / p.gam) := by
  have hf := alpha_root p hp
  have hg : p.gam ≠ 0 := hp.2.2.2.2.2.1.ne'
  unfold K quadA betaHat rI at *
  generalize theta p = th at *
  generalize alphaPlus p = al at *
  field_simp
  linear_combination (2 * p.gam) * hf


theorem W_pos (p : Params) (hp : p.Core) : 0 < 1 - p.gam + alphaPlus p * p.gam := by
  have hα := alpha_gt_one p hp
  have hgam : 0 < p.gam := hp.2.2.2.2.2.1
  nlinarith [mul_pos hgam (sub_pos.mpr hα)]

theorem Cq_pos (p : Params) (hp : p.Core) : 0 < Cq p := by
  have hα := alpha_gt_one p hp
  obtain ⟨_, _, _, _, _, hgam, _, _, hK, hbh, _, _⟩ := id hp
  unfold Cq
  exact div_pos (mul_pos (mul_pos hK (by linarith)) hgam) (mul_pos (W_pos p hp) hbh)

theorem deltaBar_mul (p : Params) (hp : p.Core) :
    deltaBar p * Cq p ^ (1 / (1 - p.gam)) =
      p.gam * K p * (alphaPlus p - 1) / (rI p * (1 - p.gam + alphaPlus p * p.gam)) := by
  have hce : 0 < Cq p ^ (1 / (1 - p.gam)) := Real.rpow_pos_of_pos (Cq_pos p hp) _
  unfold deltaBar
  rw [Real.rpow_neg (Cq_pos p hp).le]
  have := hce.ne'
  have := (W_pos p hp).ne'
  have := hp.2.2.2.2.2.2.2.1.ne'
  field_simp

theorem deltaBar_pos (p : Params) (hp : p.Core) : 0 < deltaBar p := by
  have hα := alpha_gt_one p hp
  obtain ⟨_, _, _, _, _, hgam, _, hrI, hK, hbh, _, _⟩ := id hp
  have hce : 0 < Cq p ^ (-(1 / (1 - p.gam))) := Real.rpow_pos_of_pos (Cq_pos p hp) _
  have hW := W_pos p hp
  unfold deltaBar
  have : 0 < p.gam * K p * (alphaPlus p - 1) := mul_pos (mul_pos hgam hK) (by linarith)
  positivity

theorem bound_lt_one (p : Params) (hp : p.Core) :
    p.gam * K p * (alphaPlus p - 1) / (rI p * (1 - p.gam + alphaPlus p * p.gam)) < 1 := by
  have hα := alpha_gt_one p hp
  have hW := W_pos p hp
  obtain ⟨_, _, _, _, _, hgam, _, hrI, hK, hbh, hqa, _⟩ := id hp
  rw [key_identity p hp, div_lt_one (by positivity)]
  have : 0 < (alphaPlus p - 1) * quadA p / p.gam := by
    have := mul_pos (sub_pos.mpr hα) hqa
    positivity
  nlinarith

end ECDev

open EndoCredit.Baseline in
theorem solution (p : Params) (hp : p.Core) :
    (∀ d ∈ Set.Icc (0 : ℝ) (deltaBar p),
      mStar {p with delta := d} = (1 - d / deltaBar p) / rI p) ∧
    StrictAntiOn (fun d : ℝ => mStar {p with delta := d})
      (Set.Icc 0 (deltaBar p)) ∧
    mStar {p with delta := deltaBar p} = 0 := by
  have hdb := ECDev.deltaBar_pos p hp
  have hrI : 0 < rI p := hp.2.2.2.2.2.2.2.1
  have hmul := ECDev.deltaBar_mul p hp
  have hW := ECDev.W_pos p hp
  have hα := ECDev.alpha_gt_one p hp
  have hden : 0 < p.gam * K p * (alphaPlus p - 1) :=
    mul_pos (mul_pos hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.1) (by linarith)
  have formula : ∀ d : ℝ, mStar {p with delta := d} = (1 - d / deltaBar p) / rI p := by
    intro d
    have e : (1 - p.gam + alphaPlus p * p.gam) / (p.gam * K p * (alphaPlus p - 1)) *
        Cq p ^ (1 / (1 - p.gam)) = 1 / (rI p * deltaBar p) := by
      have hce : 0 < Cq p ^ (1 / (1 - p.gam)) := Real.rpow_pos_of_pos (ECDev.Cq_pos p hp) _
      rw [eq_div_iff (by positivity)]
      calc (1 - p.gam + alphaPlus p * p.gam) / (p.gam * K p * (alphaPlus p - 1)) *
            Cq p ^ (1 / (1 - p.gam)) * (rI p * deltaBar p)
          = (1 - p.gam + alphaPlus p * p.gam) / (p.gam * K p * (alphaPlus p - 1)) * rI p *
            (deltaBar p * Cq p ^ (1 / (1 - p.gam))) := by ring
        _ = 1 := by
          rw [hmul]
          have h1 : (alphaPlus p - 1) ≠ 0 := by linarith
          have := hW.ne'; have := hrI.ne'; have := hden.ne'
          field_simp
          apply div_self
          exact mul_ne_zero (mul_ne_zero hp.2.2.2.2.2.1.ne' (by rw [mul_comm p.gam]; exact hW.ne'))
            hp.2.2.2.2.2.2.2.2.1.ne'
    show 1 / rI p - (1 - p.gam + alphaPlus p * p.gam) /
      (p.gam * K p * (alphaPlus p - 1)) * (d * Cq p ^ (1 / (1 - p.gam))) = _
    rw [show (1 - p.gam + alphaPlus p * p.gam) / (p.gam * K p * (alphaPlus p - 1)) *
        (d * Cq p ^ (1 / (1 - p.gam))) = d * ((1 - p.gam + alphaPlus p * p.gam) /
        (p.gam * K p * (alphaPlus p - 1)) * Cq p ^ (1 / (1 - p.gam))) by ring, e]
    field_simp
  refine ⟨fun d _ => formula d, ?_, ?_⟩
  · intro a _ b _ hab
    simp only [formula]
    apply div_lt_div_of_pos_right _ hrI
    have : a / deltaBar p < b / deltaBar p := div_lt_div_of_pos_right hab hdb
    linarith
  · rw [formula, div_self hdb.ne']; simp
