-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.non_top_final_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:16.604299+00:00
-- url     : https://prove2.me/submissions/97c7779c-cd73-4246-8162-2c846f9c12da

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_E_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_nontop_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) (e B α Vv Vu : ℝ) (hα : 1 ≤ α) (he : 0 ≤ e) (hB : 1 ≤ B)
    (hVv : 0 < Vv) (hs : e ^ k * B ≤ 1)
    (hVu : Vu ≤ (2 * α) ^ (k - 1) * (Real.exp (1/4) ^ k * Vv)) :
    (0.38 * e / (1 + 0) * B / α) ^ k * Vu ≤ Vv * B ^ (k - 1) / 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [show n + 1 - 1 = n by omega] at hVu ⊢
  have hα0 : 0 < α := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hbase : 0 ≤ 0.38 * e / (1 + 0) * B / α := by positivity
  have key3 : ∀ x y z w : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 → 0 ≤ w →
      x * y * z * w ≤ w := by
    intro x y z w hx hx1 hy hy1 hz hz1 hw
    have h1 : x * y ≤ 1 := by nlinarith
    have h1' : 0 ≤ x * y := mul_nonneg hx hy
    have h2 : x * y * z ≤ 1 := by nlinarith
    have h2' : 0 ≤ x * y * z := mul_nonneg h1' hz
    nlinarith
  have hE1 : 2 * 0.38 * Real.exp (1/4) ≤ 1 := by linarith [E_le]
  have hE0 : 0 ≤ 2 * 0.38 * Real.exp (1/4) := by positivity
  have hA1 : (2 * 0.38 * Real.exp (1/4)) ^ (n + 1) ≤ 1 := by
    calc (2 * 0.38 * Real.exp (1/4)) ^ (n + 1) ≤ 1 ^ (n + 1) := by
          first
          | exact pow_le_pow_left₀ hE0 hE1 (n + 1)
          | exact pow_le_pow_left hE0 hE1 (n + 1)
          | gcongr
      _ = 1 := one_pow _
  have hA0 : 0 ≤ (2 * 0.38 * Real.exp (1/4)) ^ (n + 1) := pow_nonneg hE0 _
  have hC1 : 1 / α ≤ 1 := by
    first
    | (rw [div_le_one hα0]; linarith)
    | (rw [div_le_one₀ hα0]; linarith)
    | (rw [div_le_iff₀ hα0]; linarith)
    | (rw [div_le_iff hα0]; linarith)
  have hC0 : 0 ≤ 1 / α := by positivity
  have hS0 : 0 ≤ e ^ (n + 1) * B := by positivity
  have hR : 0 ≤ Vv * B ^ n / 2 := by positivity
  calc (0.38 * e / (1 + 0) * B / α) ^ (n + 1) * Vu
      ≤ (0.38 * e / (1 + 0) * B / α) ^ (n + 1) * ((2 * α) ^ n * (Real.exp (1/4) ^ (n + 1) * Vv)) :=
        mul_le_mul_of_nonneg_left hVu (pow_nonneg hbase _)
    _ = (2 * 0.38 * Real.exp (1/4)) ^ (n + 1) * (e ^ (n + 1) * B) * (1 / α) * (Vv * B ^ n / 2) :=
        nontop_alg n 0.38 e B α (Real.exp (1/4)) Vv hα0.ne'
    _ ≤ Vv * B ^ n / 2 := key3 _ _ _ _ hA0 hA1 hS0 hs hC0 hC1 hR
end Formalism.FourierDecayAlt.P.Sz5
