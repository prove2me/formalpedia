-- Prove2me | solution 1 for FlexLearning.Threshold.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:50:48.220907+00:00
-- url     : https://prove2.me/submissions/c69ddbcf-261f-4cc4-8bac-47c4bb0807fa

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model
import Theorems.Thm_FlexLearning_Threshold_VN_eq
import Theorems.Thm_FlexLearning_Threshold_piBarF_eq
import Theorems.Thm_FlexLearning_Threshold_piBarN_eq
import Theorems.Thm_FlexLearning_Threshold_vF_closed_form_x0
import Theorems.Thm_FlexLearning_Threshold_threshold_algebra

open FlexLearning.Threshold

namespace FlexMainAux

/-- the normalised flexible objective. -/
noncomputable def phi (m f q : ℝ) : ℝ :=
  if q ≤ 1 then m ^ 2 + q * ((1 + m - m ^ 2) - f) - (1 + m - m ^ 2) * q ^ 3 / 6
  else if q ≤ 2 then 1 + m - 2 * f + f * (2 - q) - (1 + m - m ^ 2) * (2 - q) ^ 3 / 6
  else 1 + m - 2 * f - f * (q - 2)

lemma phi_le (m f q : ℝ) (hm0 : 0 < m) (hm1 : m ≤ 1) (hf0 : 0 ≤ f) (hf1 : f < 1) (hq : 0 ≤ q) :
    phi m f q ≤ 4 := by
  have hA1 : 0 ≤ m * (1 - m) := mul_nonneg hm0.le (by linarith)
  have hA2 : m * (1 - m) ≤ 1 := by
    have : m * (1 - m) ≤ 1 * 1 := mul_le_mul hm1 (by linarith) (by linarith) (by norm_num)
    linarith
  have eA : 1 + m - m ^ 2 = 1 + m * (1 - m) := by ring
  unfold phi
  rw [eA]
  split_ifs with h1 h2
  · have : 0 ≤ (1 + m * (1 - m)) * q ^ 3 / 6 := by positivity
    have : q * ((1 + m * (1 - m)) - f) ≤ 1 * 2 :=
      mul_le_mul h1 (by linarith) (by linarith) (by norm_num)
    have : m ^ 2 ≤ 1 := pow_le_one₀ hm0.le hm1
    linarith
  · have : 0 ≤ (1 + m * (1 - m)) * (2 - q) ^ 3 / 6 := by
      have : 0 ≤ 2 - q := by linarith
      positivity
    have : f * (2 - q) ≤ 1 * 1 := mul_le_mul hf1.le (by linarith) (by linarith) (by norm_num)
    linarith
  · have : 0 ≤ f * (q - 2) := mul_nonneg hf0 (by linarith)
    linarith

lemma vF_phi (p c U cF Q : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hU : 0 < U) (hQ : 0 ≤ Q) :
    vF p c 0 U cF Q = p * U * phi ((p - c) / p) (cF / p) (Q / U) := by
  have hp : 0 < p := by linarith
  obtain ⟨hL, hG, h3⟩ := FlexLearning.Threshold.vF_closed_form_x0 p c U cF Q hc hcp hU
  unfold phi
  split_ifs with h1 h2
  · rw [div_le_one hU] at h1
    rw [hL hQ h1]
    field_simp; ring
  · push Not at h1
    rw [one_lt_div hU] at h1
    rw [div_le_iff₀ hU] at h2
    rw [hG (by linarith) (by linarith)]
    field_simp; ring
  · push Not at h2
    rw [lt_div_iff₀ hU] at h2
    rw [h3 (by linarith)]
    field_simp; ring

end FlexMainAux

open FlexMainAux

theorem solution :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧
      ∀ p c U cF : ℝ, 0 ≤ c → c < p → 0 < U → c ≤ cF → cF < p →
        IsBreakEven p c 0 U cF →
        ((p - c) / p ≤ ζ → VN p c 0 U ≤ VF p c 0 U cF) ∧
        (ζ < (p - c) / p → VF p c 0 U cF ≤ VN p c 0 U) := by
  obtain ⟨ζ, hζ0, hζ1, H⟩ := FlexLearning.Threshold.threshold_algebra
  refine ⟨ζ, hζ0, hζ1, ?_⟩
  intro p c U cF hc hcp hU hccF hcFp hBE
  have hp : 0 < p := by linarith
  set m := (p - c) / p with hm
  set f := cF / p with hf
  have hm0 : 0 < m := div_pos (by linarith) hp
  have hm1 : m ≤ 1 := by rw [hm, div_le_one hp]; linarith
  have hf0 : 0 ≤ f := div_nonneg (by linarith) hp.le
  have hf1 : f < 1 := by rw [hf, div_lt_one hp]; exact hcFp
  have hpU : 0 < p * U := mul_pos hp hU
  unfold IsBreakEven at hBE
  have hN := FlexLearning.Threshold.piBarN_eq p c 0 U hc hcp le_rfl hU
  have hF := FlexLearning.Threshold.piBarF_eq p 0 U cF (by linarith) hcFp le_rfl hU
  rw [hN] at hBE
  have e2 : 2 * cF / p = 2 * f := by rw [hf]; ring
  have hg1 : 2 * f ≤ 1 → 2 / 3 * f * (Real.sqrt (2 * f) - 3) + 1 = m ^ 2 := by
    intro h
    have h' : 2 * cF ≤ p := by
      have : 2 * f * p ≤ p := by nlinarith
      rw [hf] at this; field_simp at this; linarith
    have := (hF.1 h').2
    rw [hBE, e2] at this
    have e : 2 / 3 * f * (Real.sqrt (2 * f) - 3) + 1 =
        (2 * (p - cF) * 0 + 2 / 3 * cF * (Real.sqrt (2 * f) - 3) * U + p * U) / (p * U) := by
      rw [hf]; field_simp; ring
    rw [e, ← this, hm]; field_simp; ring
  have hg2 : 1 < 2 * f → 2 / 3 * (1 - f) * Real.sqrt (2 - 2 * f) = m ^ 2 := by
    intro h
    have h' : p < 2 * cF := by
      have : p < 2 * f * p := by nlinarith
      rw [hf] at this; field_simp at this; linarith
    have := (hF.2 h').2
    have e3 : 2 - 2 * cF / p = 2 - 2 * f := by rw [e2]
    rw [hBE, e3] at this
    have e : 2 / 3 * (1 - f) * Real.sqrt (2 - 2 * f) =
        (2 * (p - cF) * 0 + 2 / 3 * (p - cF) * Real.sqrt (2 - 2 * f) * U) / (p * U) := by
      rw [hf]; field_simp; ring
    rw [e, ← this, hm]; field_simp; ring
  have hVN : VN p c 0 U = p * U * (m ^ 2 * (5 - 3 * m) / (1 + m - m ^ 2)) := by
    rw [(FlexLearning.Threshold.VN_eq p c 0 U hc hcp le_rfl hU).2]
    have hΔ : 0 < (p - c) * (p + c) + c * p := by nlinarith
    rw [hm]; field_simp; ring
  have hvF : ∀ Q, 0 ≤ Q → vF p c 0 U cF Q = p * U * phi m f (Q / U) :=
    fun Q hQ => vF_phi p c U cF Q hc hcp hU hQ
  have hne : (vF p c 0 U cF '' Set.Ici 0).Nonempty := ⟨_, 0, le_refl (0:ℝ), rfl⟩
  have hbdd : BddAbove (vF p c 0 U cF '' Set.Ici 0) := by
    refine ⟨p * U * 4, ?_⟩
    rintro _ ⟨Q, hQ, rfl⟩
    rw [hvF Q hQ]
    exact mul_le_mul_of_nonneg_left (phi_le m f _ hm0 hm1 hf0 hf1 (div_nonneg hQ hU.le)) hpU.le
  obtain ⟨Hlo, Hhi⟩ := H m f hm0 hm1 hf0 hf1 hg1 hg2
  constructor
  · intro hmz
    obtain ⟨q, hq0, hq⟩ := Hlo hmz
    have hQ : 0 ≤ q * U := mul_nonneg hq0 hU.le
    have hv : vF p c 0 U cF (q * U) = p * U * phi m f q := by
      rw [hvF _ hQ]; congr 2; field_simp
    unfold VF
    rw [hVN]
    calc p * U * (m ^ 2 * (5 - 3 * m) / (1 + m - m ^ 2)) ≤ p * U * phi m f q :=
          mul_le_mul_of_nonneg_left hq hpU.le
      _ = vF p c 0 U cF (q * U) := hv.symm
      _ ≤ _ := le_csSup hbdd ⟨q * U, hQ, rfl⟩
  · intro hmz
    unfold VF
    rw [hVN]
    apply csSup_le hne
    rintro _ ⟨Q, hQ, rfl⟩
    rw [hvF Q hQ]
    exact mul_le_mul_of_nonneg_left (Hhi hmz _ (div_nonneg hQ hU.le)) hpU.le
