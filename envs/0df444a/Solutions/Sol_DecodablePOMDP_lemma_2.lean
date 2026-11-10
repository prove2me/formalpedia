-- Prove2me | solution 1 for DecodablePOMDP.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T02:11:48.080728+00:00
-- url     : https://prove2.me/submissions/4c2afaf3-dd07-45a6-86ee-63de2ba7c15f

import Mathlib
import Definitions.Def_DecodablePOMDP_RevealResidual

open CalibratedCE.Forecast

open DecodablePOMDP in
theorem solution {S A O : Type} [Fintype S] [Fintype O] [DecidableEq S]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (hP : P.IsValid)
    (hD : IsRhoDecoderFamily P D ρ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∀ h, 2 ≤ h → h ≤ P.H → ∀ s : S,
      IsDist (reveal P D h s) ∧ IsDist (residual P D ρ h s) ∧
      (∀ z, (augmented P D).K h s z = ρ / 2 * reveal P D h s z + (1 - ρ / 2) * residual P D ρ h s z) ∧
      (∀ z, 0 < reveal P D h s z → z.2 = s) := by
  intro h h2 hH s
  have hK := hP.2.2.2.1 h h2 hH s
  have hDd := hD.1 h h2 hH
  have hd := hD.2 h h2 hH s
  have hdpos : 0 < decodeProb P D h s := lt_of_lt_of_le hρ hd
  have hc : 0 < 1 - ρ / 2 := by linarith
  have h2ρ : (2 : ℝ) - ρ ≠ 0 := by intro h; linarith
  have haugK : ∀ z, (augmented P D).K h s z = P.K h s z.1 * D h z.1 z.2 := fun z => rfl
  have hrev_nn : ∀ z, 0 ≤ reveal P D h s z := by
    intro z
    unfold reveal
    split_ifs
    · exact div_nonneg (mul_nonneg (hK.1 _) ((hDd _).1 _)) hdpos.le
    · exact le_refl _
  have hrev_sum : ∑ z, reveal P D h s z = 1 := by
    rw [Fintype.sum_prod_type]
    have : ∀ y, ∑ s', reveal P D h s (y, s') = P.K h s y * D h y s / decodeProb P D h s := by
      intro y
      unfold reveal
      simp only
      rw [Finset.sum_ite_eq' Finset.univ s, if_pos (Finset.mem_univ _)]
    simp only [this]
    rw [← Finset.sum_div]
    exact div_self hdpos.ne'
  have haug_sum : ∑ z, (augmented P D).K h s z = 1 := by
    simp only [haugK]
    rw [Fintype.sum_prod_type]
    have : ∀ y, ∑ s', P.K h s (y, s').1 * D h (y, s').1 (y, s').2 = P.K h s y := by
      intro y
      simp only
      rw [← Finset.mul_sum, (hDd y).2, mul_one]
    simp only [this]
    exact hK.2
  have hdecomp : ∀ z, (augmented P D).K h s z =
      ρ / 2 * reveal P D h s z + (1 - ρ / 2) * residual P D ρ h s z := by
    intro z
    unfold DecodablePOMDP.residual
    field_simp
    ring
  refine ⟨⟨hrev_nn, hrev_sum⟩, ⟨fun z => ?_, ?_⟩, hdecomp, fun z hz => ?_⟩
  · unfold DecodablePOMDP.residual
    apply div_nonneg _ hc.le
    rw [haugK]
    unfold reveal
    split_ifs with hz
    · rw [hz]
      have h1 : 0 ≤ P.K h s z.1 * D h z.1 s := mul_nonneg (hK.1 _) ((hDd _).1 _)
      have h2 : ρ / 2 * (P.K h s z.1 * D h z.1 s / decodeProb P D h s) ≤
          P.K h s z.1 * D h z.1 s := by
        rw [mul_div_assoc', div_le_iff₀ hdpos]
        nlinarith
      linarith
    · have := mul_nonneg (hK.1 z.1) ((hDd z.1).1 z.2)
      linarith
  · unfold DecodablePOMDP.residual
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, haug_sum, hrev_sum]
    field_simp
  · by_contra hne
    unfold reveal at hz
    rw [if_neg hne] at hz
    exact lt_irrefl _ hz
