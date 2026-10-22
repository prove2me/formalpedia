-- Prove2me | solution 1 for CostlyShort.ShortMarket.eq15_eq16_shorting_cost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T06:51:37.297613+00:00
-- url     : https://prove2.me/submissions/4349f3fc-c8a9-4d35-b3bd-550efa032c94

import Mathlib
import Definitions.Def_CostlyShort_ShortMarket_Setting

set_option autoImplicit false

namespace CostlyShort.ShortMarket

lemma a9888_lf_nonneg (Φ Γ m : ℝ) (hm : 0 ≤ m) : lendingFlow Φ Γ m = m * Γ := by
  unfold lendingFlow
  rw [max_eq_left hm, max_eq_right (show -m ≤ 0 by linarith)]; ring

lemma a9888_lf_nonpos (Φ Γ m : ℝ) (hm : m ≤ 0) : lendingFlow Φ Γ m = m * Φ := by
  unfold lendingFlow
  rw [max_eq_right hm, max_eq_left (show (0:ℝ) ≤ -m by linarith)]; ring

lemma a9888_lf_eq (Γ m : ℝ) : lendingFlow Γ Γ m = m * Γ := by
  rcases le_total 0 m with h | h
  · exact a9888_lf_nonneg _ _ _ h
  · exact a9888_lf_nonpos _ _ _ h

lemma a9888_obj_long (σ₁ σ₂ φ γ θ₁ θ₂ : ℝ) (p : ℝ × ℝ) (h2 : θ₂ = θ₁ + γ) (hσ₁ : 0 < σ₁)
    (hp : 0 ≤ p.1) :
    mvObjective σ₁ σ₂ (φ * σ₁) (γ * σ₁) θ₁ θ₂ p
      = (p.1 * σ₁ + p.2 * σ₂) * θ₂ - (p.1 * σ₁ + p.2 * σ₂) ^ 2 / 2 := by
  unfold mvObjective
  rw [a9888_lf_nonneg _ _ _ hp, h2]; ring

lemma a9888_obj_short (σ₁ σ₂ φ γ θ₁ θ₂ : ℝ) (p : ℝ × ℝ) (hp : p.1 ≤ 0) :
    mvObjective σ₁ σ₂ (φ * σ₁) (γ * σ₁) θ₁ θ₂ p
      = p.1 * σ₁ * (θ₁ + φ) + p.2 * σ₂ * θ₂ - (p.1 * σ₁ + p.2 * σ₂) ^ 2 / 2 := by
  unfold mvObjective
  rw [a9888_lf_nonpos _ _ _ hp]; ring

lemma a9888_obj_zero (σ₁ σ₂ Φ Γ θ₁ θ₂ : ℝ) : mvObjective σ₁ σ₂ Φ Γ θ₁ θ₂ (0, 0) = 0 := by
  simp [mvObjective, lendingFlow]

/-- An agent with nonpositive net Sharpe ratio `θ₂ ≤ 0` never holds a long position. -/
lemma a9888_opt_nonpos {σ₁ σ₂ φ γ θ₁ θ₂ : ℝ} {p : ℝ × ℝ} (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (h2 : θ₂ = θ₁ + γ) (hθ : θ₂ ≤ 0)
    (hp : IsOptimalFractions σ₁ σ₂ (φ * σ₁) (γ * σ₁) θ₁ θ₂ p) : p.1 ≤ 0 := by
  by_contra h
  push_neg at h
  have h0 := hp.2 (0, 0) (le_refl _)
  rw [a9888_obj_zero, a9888_obj_long σ₁ σ₂ φ γ θ₁ θ₂ p h2 hσ₁ h.le] at h0
  have hc : 0 < p.1 * σ₁ + p.2 * σ₂ := by
    nlinarith [hp.1, mul_pos h hσ₁, mul_nonneg hp.1 hσ₂.le]
  nlinarith [mul_nonpos_iff.mpr (Or.inl ⟨hc.le, hθ⟩), mul_pos hc hc]

end CostlyShort.ShortMarket

set_option maxHeartbeats 1000000 in
open CostlyShort.ShortMarket in
theorem solution {σ₁ σ₂ S₁ Wo Wp θ₁o θ₁p θ₂o θ₂p γ φ : ℝ} {po pp : ℝ × ℝ}
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hS₁ : 0 < S₁) (hWo : 0 < Wo) (hWp : 0 < Wp)
    (hΔ : θ₁p ≤ θ₁o)
    (heq : IsShortMarketEquilibrium σ₁ σ₂ S₁ Wo Wp θ₁o θ₁p θ₂o θ₂p γ φ po pp) :
    (γ = 0 ↔ 0 ≤ θ₂p) ∧ φ = (if θ₂p < 0 then -θ₁p / 2 else 0) := by
  obtain ⟨e7o, e7p, opto, optp, clr, clrL, cost⟩ := heq
  have hφγ : γ ≤ φ := cost.1.1
  have hmax := cost.1.2
  have hleast := cost.2
  -- if φ = γ, lending clearing forces γ = 0
  have hγ0 : φ = γ → γ = 0 := by
    intro h
    rw [h, a9888_lf_eq, a9888_lf_eq] at clrL
    have h1 : (Wo * po.1 + Wp * pp.1) * (γ * σ₁) = 0 := by linarith
    rw [clr] at h1
    rcases mul_eq_zero.mp h1 with h1 | h1
    · linarith
    · rcases mul_eq_zero.mp h1 with h1 | h1
      · exact h1
      · linarith
  by_cases hθ : 0 ≤ θ₂p
  · -- inactive case: the revenue vanishes on `[γ, ∞)`, so `φ = γ = 0`
    have hφ : φ = γ := by
      apply le_antisymm _ hφγ
      apply hleast
      refine ⟨le_rfl, fun z hz => ?_⟩
      have h1 : max (-(θ₁o + z)) 0 = 0 := max_eq_right (by linarith)
      have h2 : max (-(θ₁p + z)) 0 = 0 := max_eq_right (by linarith)
      have h3 : max (-(θ₁o + γ)) 0 = 0 := max_eq_right (by linarith)
      have h4 : max (-(θ₁p + γ)) 0 = 0 := max_eq_right (by linarith)
      unfold lendingRevenue
      rw [h1, h2, h3, h4]
      simp
    have hg : γ = 0 := hγ0 hφ
    refine ⟨⟨fun _ => hθ, fun _ => hg⟩, ?_⟩
    rw [if_neg (not_lt.mpr hθ), hφ, hg]
  · push_neg at hθ
    have hKγ : θ₁p + γ < 0 := by linarith
    have hpp : pp.1 ≤ 0 := a9888_opt_nonpos hσ₁ hσ₂ e7p hθ.le optp
    have hWpp : Wp * pp.1 ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_left hpp hWp.le]
    have hWpo : 0 < Wo * po.1 := by linarith
    have hpo : 0 < po.1 := by
      by_contra h
      push_neg at h
      nlinarith [mul_le_mul_of_nonneg_left h hWo.le]
    have hθ2o : 0 < θ₂o := by
      by_contra h
      push_neg at h
      have := a9888_opt_nonpos hσ₁ hσ₂ e7o h opto
      linarith
    -- the revenue on `[γ, ∞)` only involves the pessimist
    have hR : ∀ y, γ ≤ y →
        lendingRevenue θ₁o θ₁p Wo Wp y = y * max (-(θ₁p + y)) 0 * Wp := by
      intro y hy
      unfold lendingRevenue
      rw [max_eq_right (show -(θ₁o + y) ≤ 0 by linarith)]
      ring
    -- main claim: `φ = -θ₁p / 2` and `γ ≠ 0`
    have hmain : φ = -θ₁p / 2 ∧ γ ≠ 0 := by
      rcases le_or_gt 0 θ₁p with hK | hK
      · -- `K = -θ₁p ≤ 0`: impossible
        exfalso
        have hγneg : γ < 0 := by linarith
        have hRK : lendingRevenue θ₁o θ₁p Wo Wp (-θ₁p) = 0 := by
          rw [hR _ (by linarith)]
          have : max (-(θ₁p + -θ₁p)) 0 = 0 := by simp
          rw [this]; ring
        have hφle : φ ≤ -θ₁p := by
          apply hleast
          refine ⟨by linarith, fun z hz => ?_⟩
          rw [hRK, hR z hz]
          rcases le_total (-(θ₁p + z)) 0 with h | h
          · rw [max_eq_right h]; simp
          · rw [max_eq_left h]
            have hz0 : z ≤ 0 := by linarith
            have h5 : z * -(θ₁p + z) ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨hz0, h⟩)
            exact mul_nonpos_iff.mpr (Or.inr ⟨h5, hWp.le⟩)
        have hφge : -θ₁p ≤ φ := by
          by_contra h
          push_neg at h
          have h1 := hmax (-θ₁p) (by linarith)
          rw [hRK, hR φ hφγ, max_eq_left (show (0:ℝ) ≤ -(θ₁p + φ) by linarith)] at h1
          have hφneg : φ < 0 := by linarith
          have hpos : 0 < -(θ₁p + φ) := by linarith
          nlinarith [mul_pos (mul_pos (neg_pos.mpr hφneg) hpos) hWp]
        have hφK : θ₁p + φ = 0 := by linarith
        -- the pessimist does not trade asset 1
        have hpp0 : pp.1 = 0 := by
          by_contra hne
          have hlt : pp.1 < 0 := lt_of_le_of_ne hpp hne
          have h0 := optp.2 (0, 0) (le_refl _)
          rw [a9888_obj_zero, a9888_obj_short σ₁ σ₂ φ γ θ₁p θ₂p pp hpp, hφK] at h0
          have hb : 0 ≤ pp.2 * σ₂ := mul_nonneg optp.1 hσ₂.le
          have hbθ : pp.2 * σ₂ * θ₂p ≤ 0 := mul_nonpos_iff.mpr (Or.inl ⟨hb, hθ.le⟩)
          have hc2 : (pp.1 * σ₁ + pp.2 * σ₂) ^ 2 ≤ 0 := by nlinarith
          have hc : pp.1 * σ₁ + pp.2 * σ₂ = 0 := by nlinarith [sq_nonneg (pp.1 * σ₁ + pp.2 * σ₂)]
          have hbθ0 : pp.2 * σ₂ * θ₂p = 0 := by nlinarith
          have hb0 : pp.2 * σ₂ = 0 := by
            rcases mul_eq_zero.mp hbθ0 with h | h
            · exact h
            · linarith
          have : pp.1 * σ₁ < 0 := mul_neg_of_neg_of_pos hlt hσ₁
          linarith
        rw [hpp0, mul_zero, a9888_lf_nonneg _ _ _ hWpo.le, a9888_lf_nonneg _ _ _ le_rfl] at clrL
        have h1 : Wo * po.1 * (γ * σ₁) = 0 := by linarith
        have : Wo * po.1 * (γ * σ₁) < 0 :=
          mul_neg_of_pos_of_neg hWpo (mul_neg_of_neg_of_pos hγneg hσ₁)
        linarith
      · -- `K = -θ₁p > 0`
        have hKpos : 0 < -θ₁p := by linarith
        have hR2 : ∀ z, γ ≤ z → lendingRevenue θ₁o θ₁p Wo Wp z ≤ (-θ₁p / 2) ^ 2 * Wp := by
          intro z hz
          rw [hR z hz]
          rcases le_total (-(θ₁p + z)) 0 with h | h
          · rw [max_eq_right h]
            have : 0 ≤ (-θ₁p / 2) ^ 2 * Wp := mul_nonneg (sq_nonneg _) hWp.le
            simpa using this
          · rw [max_eq_left h]
            have h5 : z * -(θ₁p + z) ≤ (-θ₁p / 2) ^ 2 := by nlinarith [sq_nonneg (z + θ₁p / 2)]
            exact mul_le_mul_of_nonneg_right h5 hWp.le
        have hφneγ : φ ≠ γ := by
          intro h
          have hg := hγ0 h
          have h1 := hmax (-θ₁p / 2) (by linarith)
          rw [hR _ (by linarith), hR φ hφγ, h, hg, zero_mul, zero_mul,
            max_eq_left (show (0:ℝ) ≤ -(θ₁p + -θ₁p / 2) by linarith)] at h1
          nlinarith [mul_pos (mul_pos hKpos hKpos) hWp]
        have hγle : γ ≤ -θ₁p / 2 := by
          by_contra hlt
          push_neg at hlt
          apply hφneγ
          apply le_antisymm _ hφγ
          apply hleast
          refine ⟨le_rfl, fun z hz => ?_⟩
          rw [hR z hz, hR γ le_rfl, max_eq_left (show (0:ℝ) ≤ -(θ₁p + γ) by linarith)]
          have hγK : 0 ≤ γ * -(θ₁p + γ) := mul_nonneg (by linarith) (by linarith)
          rcases le_total (-(θ₁p + z)) 0 with h | h
          · rw [max_eq_right h]
            have : 0 ≤ γ * -(θ₁p + γ) * Wp := mul_nonneg hγK hWp.le
            simpa using this
          · rw [max_eq_left h]
            have h5 : z * -(θ₁p + z) ≤ γ * -(θ₁p + γ) := by
              nlinarith [mul_nonpos_iff.mpr
                (Or.inl ⟨sub_nonneg.mpr hz, (show -θ₁p - z - γ ≤ 0 by linarith)⟩)]
            exact mul_le_mul_of_nonneg_right h5 hWp.le
        have hRK2 : lendingRevenue θ₁o θ₁p Wo Wp (-θ₁p / 2) = (-θ₁p / 2) ^ 2 * Wp := by
          rw [hR _ hγle, max_eq_left (show (0:ℝ) ≤ -(θ₁p + -θ₁p / 2) by linarith)]
          ring
        have hφeq : φ = -θ₁p / 2 := by
          have h1 := hmax (-θ₁p / 2) hγle
          rw [hRK2, hR φ hφγ] at h1
          rcases le_total (-(θ₁p + φ)) 0 with h | h
          · rw [max_eq_right h] at h1
            nlinarith [mul_pos (mul_pos hKpos hKpos) hWp]
          · rw [max_eq_left h] at h1
            have h2 : (-θ₁p / 2) ^ 2 ≤ φ * -(θ₁p + φ) := le_of_mul_le_mul_right h1 hWp
            have h3 : (φ + θ₁p / 2) ^ 2 = 0 :=
              le_antisymm (by nlinarith) (sq_nonneg _)
            have h4 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
            linarith
        refine ⟨hφeq, fun hg => ?_⟩
        -- with `γ = 0` the pessimist shorts strictly, so the lending market cannot clear
        have hs : θ₁p + φ < 0 := by rw [hφeq]; linarith
        have hq := optp.2 ((θ₁p + φ) / σ₁, 0) (le_refl _)
        have hq1 : ((θ₁p + φ) / σ₁, (0:ℝ)).1 ≤ 0 := (div_neg_of_neg_of_pos hs hσ₁).le
        rw [a9888_obj_short σ₁ σ₂ φ γ θ₁p θ₂p _ hq1] at hq
        dsimp only at hq
        have hx : (θ₁p + φ) / σ₁ * σ₁ = θ₁p + φ := by field_simp
        rw [hx] at hq
        have hpplt : pp.1 < 0 := by
          rcases lt_or_eq_of_le hpp with h | h
          · exact h
          · exfalso
            rw [a9888_obj_long σ₁ σ₂ φ γ θ₁p θ₂p pp e7p hσ₁ h.ge] at hq
            have hb : 0 ≤ pp.1 * σ₁ + pp.2 * σ₂ := by
              rw [h, zero_mul, zero_add]; exact mul_nonneg optp.1 hσ₂.le
            have hc1 : (pp.1 * σ₁ + pp.2 * σ₂) * θ₂p ≤ 0 :=
              mul_nonpos_iff.mpr (Or.inl ⟨hb, hθ.le⟩)
            have hc2 := sq_nonneg (pp.1 * σ₁ + pp.2 * σ₂)
            have hp2 : 0 < (θ₁p + φ) * (θ₁p + φ) := mul_pos_of_neg_of_neg hs hs
            have hq' : (θ₁p + φ) * (θ₁p + φ) / 2 ≤ (pp.1 * σ₁ + pp.2 * σ₂) * θ₂p
                - (pp.1 * σ₁ + pp.2 * σ₂) ^ 2 / 2 := by
              convert hq using 1; ring
            linarith
        have hWpp' : Wp * pp.1 < 0 := mul_neg_of_pos_of_neg hWp hpplt
        rw [a9888_lf_nonneg _ _ _ hWpo.le, a9888_lf_nonpos _ _ _ hWpp, hg] at clrL
        have hφpos : 0 < φ * σ₁ := mul_pos (by rw [hφeq]; linarith) hσ₁
        have : Wp * pp.1 * (φ * σ₁) < 0 := mul_neg_of_neg_of_pos hWpp' hφpos
        rw [zero_mul, mul_zero, zero_add] at clrL
        linarith
    obtain ⟨hφeq, hγne⟩ := hmain
    refine ⟨⟨fun h => absurd h hγne, fun h => absurd h (not_le.mpr hθ)⟩, ?_⟩
    rw [if_pos hθ, hφeq]
