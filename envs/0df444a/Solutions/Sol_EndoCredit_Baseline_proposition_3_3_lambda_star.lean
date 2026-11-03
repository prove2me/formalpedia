-- Prove2me | solution 1 for EndoCredit.Baseline.proposition_3_3_lambda_star
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:47:42.009286+00:00
-- url     : https://prove2.me/submissions/81ea292e-017e-4bfa-b830-9528bc686880

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


theorem Q_pos (p : Params) (hp : p.Standing) : 0 < Q p :=
  mul_pos hp.2.1 (Real.rpow_pos_of_pos (Cq_pos p hp.1) _)

theorem ybar_pos (p : Params) (hp : p.Standing) : 0 < ybar p :=
  Real.rpow_pos_of_pos (Q_pos p hp) _

theorem ybar_rpow (p : Params) (hp : p.Standing) : ybar p ^ (-(1 / p.gam)) = Q p := by
  have hg : p.gam ≠ 0 := hp.1.2.2.2.2.2.1.ne'
  unfold ybar
  rw [← Real.rpow_mul (Q_pos p hp).le]
  have : -p.gam * -(1 / p.gam) = 1 := by field_simp
  rw [this, Real.rpow_one]

theorem delta_rpow (p : Params) (hp : p.Standing) :
    p.delta ^ (1 - p.gam) * Cq p = Q p ^ (1 - p.gam) := by
  have hg1 : 1 - p.gam ≠ 0 := sub_ne_zero.mpr (Ne.symm hp.1.2.2.2.2.2.2.1)
  have hC := Cq_pos p hp.1
  unfold Q
  rw [Real.mul_rpow hp.2.1.le (Real.rpow_pos_of_pos hC _).le, ← Real.rpow_mul hC.le]
  have : 1 / (1 - p.gam) * (1 - p.gam) = 1 := by field_simp
  rw [this, Real.rpow_one]

theorem coefA_ybar (p : Params) (hp : p.Standing) :
    coefA p * ybar p ^ (alphaPlus p - 1) = Q p / (K p * p.gam * (alphaPlus p - 1)) := by
  have hQ := Q_pos p hp
  have hc := hp.1
  have hα := alpha_gt_one p hc
  have hW := W_pos p hc
  have hC := Cq_pos p hc
  obtain ⟨_, _, _, _, _, hgam, _, hrI, hK, hbh, _, _⟩ := id hc
  have hd := delta_rpow p hp
  have e1 : Q p ^ (p.gam * alphaPlus p) * ybar p ^ (alphaPlus p - 1) = Q p ^ p.gam := by
    unfold ybar
    rw [← Real.rpow_mul hQ.le, ← Real.rpow_add hQ]
    congr 1; ring
  have e2 : Q p ^ (1 - p.gam) * Q p ^ p.gam = Q p := by
    rw [← Real.rpow_add hQ]; simp
  have hdelta : p.delta ^ (1 - p.gam) = Q p ^ (1 - p.gam) / Cq p := by
    rw [← hd]; field_simp
  calc coefA p * ybar p ^ (alphaPlus p - 1)
      = p.delta ^ (1 - p.gam) * alphaPlus p *
          (Q p ^ (p.gam * alphaPlus p) * ybar p ^ (alphaPlus p - 1)) /
        (betaHat p * (alphaPlus p - 1) * (1 - p.gam + alphaPlus p * p.gam)) := by
          unfold coefA; ring
    _ = Q p ^ (1 - p.gam) * Q p ^ p.gam * alphaPlus p /
        (Cq p * betaHat p * (alphaPlus p - 1) * (1 - p.gam + alphaPlus p * p.gam)) := by
          rw [e1, hdelta]; field_simp
    _ = Q p / (K p * p.gam * (alphaPlus p - 1)) := by
          rw [e2]; unfold Cq
          have : alphaPlus p - 1 ≠ 0 := by linarith
          have := hW.ne'; have := hbh.ne'; have := hK.ne'; have := hgam.ne'
          have : alphaPlus p ≠ 0 := by linarith
          field_simp

theorem phi_hasDeriv (p : Params) (w : ℝ) (hw : 0 < w) :
    HasDerivAt (phi p)
      ((-(1 / p.gam)) * w ^ (-(1 / p.gam) - 1) / K p +
        coefA p * ((alphaPlus p - 1) * w ^ (alphaPlus p - 1 - 1))) w := by
  have h1 := Real.hasDerivAt_rpow_const (p := -(1 / p.gam)) (Or.inl hw.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := alphaPlus p - 1) (Or.inl hw.ne')
  have := ((h1.div_const (K p)).sub_const (1 / rI p)).add (h2.const_mul (coefA p))
  have e : phi p = ((fun x => x ^ (-(1 / p.gam)) / K p - 1 / rI p) +
      fun y => coefA p * y ^ (alphaPlus p - 1)) := by
    funext x; simp only [phi, Pi.add_apply]
  rw [e]; exact this

theorem phi_antiOn (p : Params) (hp : p.Standing) : StrictAntiOn (phi p) (Set.Ioc 0 (ybar p)) := by
  have hc := hp.1
  have hα := alpha_gt_one p hc
  have hQ := Q_pos p hp
  obtain ⟨_, _, _, _, _, hgam, _, hrI, hK, hbh, _, _⟩ := id hc
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (ybar p))
  · intro w hw
    exact (phi_hasDeriv p w hw.1).continuousAt.continuousWithinAt
  · intro w hw
    rw [interior_Ioc] at hw
    obtain ⟨hw0, hwy⟩ := hw
    rw [(phi_hasDeriv p w hw0).deriv, Real.rpow_sub_one hw0.ne', Real.rpow_sub_one hw0.ne']
    -- coefA (α-1) w^{α-1} < Q/(γK) < w^{-1/γ}/(γK)
    have hA : coefA p * ((alphaPlus p - 1) * w ^ (alphaPlus p - 1)) < Q p / (K p * p.gam) := by
      have hlt : w ^ (alphaPlus p - 1) < ybar p ^ (alphaPlus p - 1) :=
        Real.rpow_lt_rpow hw0.le hwy (by linarith)
      have hcA : 0 < coefA p := by
        unfold coefA
        have := W_pos p hc
        have : 0 < p.delta ^ (1 - p.gam) := Real.rpow_pos_of_pos hp.2.1 _
        have : 0 < Q p ^ (p.gam * alphaPlus p) := Real.rpow_pos_of_pos hQ _
        have : 0 < alphaPlus p - 1 := by linarith
        have : 0 < alphaPlus p := by linarith
        positivity
      have := coefA_ybar p hp
      have e : coefA p * ((alphaPlus p - 1) * ybar p ^ (alphaPlus p - 1)) = Q p / (K p * p.gam) := by
        rw [show coefA p * ((alphaPlus p - 1) * ybar p ^ (alphaPlus p - 1)) =
          (alphaPlus p - 1) * (coefA p * ybar p ^ (alphaPlus p - 1)) by ring, this]
        have : alphaPlus p - 1 ≠ 0 := by linarith
        field_simp
      rw [← e]
      have : 0 < alphaPlus p - 1 := by linarith
      gcongr
    have hB : Q p < w ^ (-(1 / p.gam)) := by
      rw [← ybar_rpow p hp]
      exact Real.rpow_lt_rpow_of_neg hw0 hwy (by have := one_div_pos.mpr hgam; linarith)
    have hB' : Q p / (K p * p.gam) < w ^ (-(1 / p.gam)) / (K p * p.gam) :=
      div_lt_div_of_pos_right hB (by positivity)
    have key : -(1 / p.gam) * (w ^ (-(1 / p.gam)) / w) / K p +
        coefA p * ((alphaPlus p - 1) * (w ^ (alphaPlus p - 1) / w)) =
        (coefA p * ((alphaPlus p - 1) * w ^ (alphaPlus p - 1)) -
          w ^ (-(1 / p.gam)) / (K p * p.gam)) / w := by
      field_simp
      ring
    rw [key]
    apply div_neg_of_neg_of_pos _ hw0
    linarith

theorem phi_ybar (p : Params) (hp : p.Standing) : phi p (ybar p) = -(mStar p) := by
  have hc := hp.1
  have hα := alpha_gt_one p hc
  obtain ⟨_, _, _, _, _, hgam, _, hrI, hK, hbh, _, _⟩ := id hc
  unfold phi
  rw [ybar_rpow p hp, coefA_ybar p hp]
  unfold mStar
  have : alphaPlus p - 1 ≠ 0 := by linarith
  have := hgam.ne'; have := hK.ne'; have := hrI.ne'
  field_simp
  ring

end ECDev

open EndoCredit.Baseline in
theorem solution (p : Params) (hp : p.Standing) (x : ℝ) :
    (-(mStar p) * p.Ibar ≤ x →
      ∃! y0 : ℝ, y0 ∈ Set.Ioc 0 (ybar p) ∧ x / p.Ibar = phi p y0) ∧
    (x < -(mStar p) * p.Ibar →
      ¬∃ y0 : ℝ, y0 ∈ Set.Ioc 0 (ybar p) ∧ x / p.Ibar = phi p y0) := by
  have hanti := ECDev.phi_antiOn p hp
  have hy := ECDev.ybar_pos p hp
  have hQ := ECDev.Q_pos p hp
  have hc := hp.1
  have hα := ECDev.alpha_gt_one p hc
  obtain ⟨_, _, _, _, _, hgam, _, hrI, hK, hbh, _, hI⟩ := id hc
  have hlow : ∀ w ∈ Set.Ioc (0 : ℝ) (ybar p), -(mStar p) ≤ phi p w := by
    intro w hw
    rw [← ECDev.phi_ybar p hp]
    exact hanti.antitoneOn hw ⟨hy, le_rfl⟩ hw.2
  have hcA : 0 < coefA p := by
    unfold coefA
    have := ECDev.W_pos p hc
    have : 0 < p.delta ^ (1 - p.gam) := Real.rpow_pos_of_pos hp.2.1 _
    have : 0 < Q p ^ (p.gam * alphaPlus p) := Real.rpow_pos_of_pos hQ _
    have : 0 < alphaPlus p - 1 := by linarith
    have : 0 < alphaPlus p := by linarith
    positivity
  constructor
  · intro hx
    have ht : -(mStar p) ≤ x / p.Ibar := by rw [le_div_iff₀ hI]; exact hx
    set t := x / p.Ibar
    set M := max (K p * (t + 1 / rI p)) (Q p)
    have hM : 0 < M := lt_of_lt_of_le hQ (le_max_right _ _)
    set w1 := M ^ (-p.gam)
    have hw1 : 0 < w1 := Real.rpow_pos_of_pos hM _
    have hw1y : w1 ≤ ybar p :=
      Real.rpow_le_rpow_of_nonpos hQ (le_max_right _ _) (by linarith)
    have hw1r : w1 ^ (-(1 / p.gam)) = M := by
      rw [← Real.rpow_mul hM.le]
      have : -p.gam * -(1 / p.gam) = 1 := by field_simp
      rw [this, Real.rpow_one]
    have hphi1 : t ≤ phi p w1 := by
      unfold phi
      rw [hw1r]
      have : 0 < coefA p * w1 ^ (alphaPlus p - 1) := mul_pos hcA (Real.rpow_pos_of_pos hw1 _)
      have : t + 1 / rI p ≤ M / K p := by
        rw [le_div_iff₀ hK]; nlinarith [le_max_left (K p * (t + 1 / rI p)) (Q p)]
      linarith
    have hcont : ContinuousOn (phi p) (Set.Icc w1 (ybar p)) := by
      intro w hw
      exact (ECDev.phi_hasDeriv p w (lt_of_lt_of_le hw1 hw.1)).continuousAt.continuousWithinAt
    have hmem : t ∈ Set.Icc (phi p (ybar p)) (phi p w1) := by
      rw [ECDev.phi_ybar p hp]; exact ⟨ht, hphi1⟩
    obtain ⟨y0, hy0, hy0e⟩ := intermediate_value_Icc' hw1y hcont hmem
    refine ⟨y0, ⟨⟨lt_of_lt_of_le hw1 hy0.1, hy0.2⟩, hy0e.symm⟩, ?_⟩
    rintro z ⟨hz, hze⟩
    exact hanti.injOn hz ⟨lt_of_lt_of_le hw1 hy0.1, hy0.2⟩ (by rw [← hze, hy0e])
  · intro hx ⟨y0, hy0, he⟩
    have : x / p.Ibar < -(mStar p) := by rw [div_lt_iff₀ hI]; exact hx
    have := hlow y0 hy0
    linarith
