-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.bracketBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:38.562788+00:00
-- url     : https://prove2.me/submissions/e1ce20b3-7445-475a-ad4c-b24cdf452b90

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution : BracketBound := by
  intro k r m ka rd g VV Vu hm hk hrd hka hg hVV hVu om
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hrd0 : 0 < rd := by linarith
  have hka0 : 0 < ka := by rw [hka]; positivity
  have hg0 : 0 < g := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = m * (m - 1) / 2 := ⟨_, rfl⟩
  have he2 : e = (r + 1) * (2 * r + 1) := by
    rw [he, hm]
    have : (2 * r + 2) * (2 * r + 2 - 1) = 2 * ((r + 1) * (2 * r + 1)) := by
      have : 2 * r + 2 - 1 = 2 * r + 1 := by omega
      rw [this]; ring
    rw [this]; simp
  have hmR : (m : ℝ) = 2 * r + 2 := by rw [hm]; push_cast; ring
  have heR : (e : ℝ) = ((r : ℝ) + 1) * (2 * r + 1) := by rw [he2]; push_cast; ring
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (ka ^ e)⁻¹ * rd ^ (-(((m : ℝ) - 1) / 2)) * g ^ e := ⟨_, rfl⟩
  have hom : om = B ^ ((1 : ℝ) / (k : ℝ)) := by rw [hB, he]
  have hB0 : 0 < B := by rw [hB]; positivity
  have hlogka : Real.log ka = Real.log (2 * Real.pi) - Real.log rd := by
    rw [hka, Real.log_div (by positivity) hrd0.ne']
  have hlogB : Real.log B = e * (Real.log g + Real.log rd - Real.log (2 * Real.pi)) -
      ((m : ℝ) - 1) / 2 * Real.log rd := by
    rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_inv, Real.log_pow, Real.log_pow, Real.log_rpow hrd0, hlogka]
    ring
  have hl1 : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hl2 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg h2pi
  have hl3 : Real.log (2 * Real.pi) ≤ Real.log g := Real.log_le_log (by positivity) hg
  have hlow : 0 ≤ Real.log B := by
    rw [hlogB, heR, hmR]
    have t1 : 0 ≤ ((r : ℝ) + 1) * (2 * r + 1) * (Real.log g - Real.log (2 * Real.pi)) := by
      apply mul_nonneg (by positivity); linarith
    have t2 : 0 ≤ (((r : ℝ) + 1) * (2 * r + 1) - (2 * r + 2 - 1) / 2) * Real.log rd := by
      apply mul_nonneg _ hl1
      nlinarith
    nlinarith
  have hup : Real.log B ≤ (m : ℝ) ^ 2 * (Real.log g + Real.log rd) / 2 := by
    rw [hlogB, heR, hmR]
    have t1 : 0 ≤ ((r : ℝ) + 1) * (2 * r + 1) * Real.log (2 * Real.pi) := by positivity
    have t2 : 0 ≤ ((2 * (r : ℝ) + 2 - 1) / 2) * Real.log rd := by
      apply mul_nonneg _ hl1
      linarith
    have t3 : 0 ≤ ((2 * (r : ℝ) + 2) ^ 2 / 2 - ((r : ℝ) + 1) * (2 * r + 1)) *
        (Real.log g + Real.log rd) := by
      apply mul_nonneg
      · nlinarith
      · linarith
    nlinarith
  have hB1 : 1 ≤ B := (Real.log_nonneg_iff hB0).mp hlow
  refine ⟨?_, ?_, ?_⟩
  · rw [hom]
    exact Real.one_le_rpow hB1 (by positivity)
  · rw [hom, Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.mpr
    have : (m : ℝ) ^ 2 * (Real.log g + Real.log rd) / (2 * k) =
        (m : ℝ) ^ 2 * (Real.log g + Real.log rd) / 2 * (1 / k) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hup (by positivity)
  · have hX : 0 ≤ (ka ^ (m - 1))⁻¹ * g ^ m := by positivity
    have hP : TcritPow k m ka rd g VV Vu = ((ka ^ (m - 1))⁻¹ * g ^ m) ^ k * B * (VV / Vu) := by
      unfold TcritPow
      rw [hB, ← he, pow_add, pow_add, pow_mul, mul_comm k m, pow_mul, mul_pow, inv_pow, mul_inv]
      ring
    unfold Tcrit
    rw [hP, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hB0.le,
      one_div, Real.pow_rpow_inv_natCast hX (by omega), hom, one_div]
end Formalism.FourierDecayAlt.P.Sz2
