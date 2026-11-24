-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cutoff_phase_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:58.423478+00:00
-- url     : https://prove2.me/submissions/9aef1281-4e26-45ad-bea4-0de9a3bd5cda

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_deriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_norm_iteratedFDeriv_smul_le_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6 Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.CutPhiBound := by
  intro s k
  obtain ⟨C0, hC0, hcut⟩ := cutM_deriv s k
  refine ⟨1 + 2 ^ k * C0, ?_⟩
  intro V _ _ Φ Kd bd τ hτ hΦ
  have hτ0 : 0 < τ := lt_of_lt_of_le one_pos hτ
  have e1 : cutPhi τ Φ = fun Z => cutM τ Z • Φ Z := by
    funext Z
    exact Complex.coe_smul _ _
  have e2 : cutPhiC τ Φ = Φ - cutPhi τ Φ := by
    funext Z
    simp only [cutPhiC, cutPhi, Pi.sub_apply]
    push_cast
    rw [sub_smul, one_smul]
  have hbd : ∀ Z, detM Z ∈ Kd → 0 ≤ bd Z := fun Z hZ =>
    (norm_nonneg _).trans ((hΦ Z hZ).2 0 (Nat.zero_le _))
  have hsm : ∀ Z, detM Z ∈ Kd → ContDiffAt ℝ k (cutPhi τ Φ) Z := by
    intro Z hZ
    rw [e1]
    exact (cutM_contDiff τ (n := k)).contDiffAt.smul (hΦ Z hZ).1
  have key : ∀ Z, detM Z ∈ Kd → ∀ j ≤ k, ‖iteratedFDeriv ℝ j (cutPhi τ Φ) Z‖ ≤ 2 ^ k * C0 * bd Z := by
    intro Z hZ j hj
    have hjk : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((k : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj
    rw [e1]
    refine (norm_iteratedFDeriv_smul_le_at (cutM_contDiff τ (n := j)) ((hΦ Z hZ).1.of_le hjk)).trans ?_
    calc ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutM τ) Z‖ * ‖iteratedFDeriv ℝ (j - i) Φ Z‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (C0 * bd Z) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ k := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hj
          have h1 : ‖iteratedFDeriv ℝ i (cutM τ) Z‖ ≤ C0 := by
            refine (hcut τ hτ0 i hi' Z).trans ?_
            have : (τ ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hτ)
            nlinarith
          have h2 : ‖iteratedFDeriv ℝ (j - i) Φ Z‖ ≤ bd Z := (hΦ Z hZ).2 _ ((Nat.sub_le _ _).trans hj)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hC0) (Nat.cast_nonneg _)
      _ = 2 ^ j * (C0 * bd Z) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ k * (C0 * bd Z) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hj) (mul_nonneg hC0 (hbd Z hZ))
      _ = 2 ^ k * C0 * bd Z := by ring
  constructor
  · intro Z hZ
    refine ⟨hsm Z hZ, fun j hj => (key Z hZ j hj).trans ?_⟩
    have := hbd Z hZ
    nlinarith
  · intro Z hZ
    rw [e2]
    refine ⟨(hΦ Z hZ).1.sub (hsm Z hZ), fun j hj => ?_⟩
    have hjk : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((k : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj
    rw [iteratedFDeriv_sub_apply ((hΦ Z hZ).1.of_le hjk) ((hsm Z hZ).of_le hjk)]
    refine (norm_sub_le _ _).trans ?_
    have h1 := (hΦ Z hZ).2 j hj
    have h2 := key Z hZ j hj
    linarith
end Formalism.FourierDecayAlt.P
