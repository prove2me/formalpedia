-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.top_final_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:39.398926+00:00
-- url     : https://prove2.me/submissions/4c8b08db-b590-4dba-a8e6-bc5b65888e61

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_fac_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_top_alg

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
theorem _root_.solution (k : ℕ) (hk : 4 ≤ k) (e B a b Del θ W Vu : ℝ) (he : 0 ≤ e) (hB : 1 ≤ B)
    (hW : 0 < W) (hs : e ^ k * B ≤ 1) (hθ : 1 ≤ θ) (ha : 0 < a) (hb : 0 < b) (hDel : 0 < Del)
    (hq : ((k:ℝ) * Del) ^ 2 * (a + b) ≤ a ^ 2 * b ^ 2)
    (hVu : Vu ≤ (a ^ (k - 2) * (a + b)) * ((Real.exp (1/4) ^ (k - 1) * W) * (b * θ) ^ (k - 2))) :
    (0.38 * e / θ * B / (a * b / ((k:ℝ) * Del))) ^ k * Vu ≤
      (W * (4 * Del) ^ (k - 2) * ((k - 2).factorial : ℝ)) * B ^ (k - 1) / 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hn : 2 ≤ n := by omega
  rw [show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega] at hVu ⊢
  push_cast at hq ⊢
  have hθ0 : 0 < θ := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hK0 : 0 < ((n:ℝ) + 2) * Del := by positivity
  have hbase : 0 ≤ 0.38 * e / θ * B / (a * b / (((n:ℝ) + 2) * Del)) := by positivity
  have key3 : ∀ x y z w : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 → 0 ≤ w →
      x * y * z * w ≤ w := by
    intro x y z w hx hx1 hy hy1 hz hz1 hw
    have h1 : x * y ≤ 1 := by nlinarith
    have h1' : 0 ≤ x * y := mul_nonneg hx hy
    have h2 : x * y * z ≤ 1 := by nlinarith
    have h2' : 0 ≤ x * y * z := mul_nonneg h1' hz
    nlinarith
  have hX2 : (((n:ℝ) + 2) * Del) ^ 2 * (a + b) / (a ^ 2 * b ^ 2) ≤ 1 := by
    have hd : 0 < a ^ 2 * b ^ 2 := by positivity
    first
    | (rw [div_le_one hd]; linarith)
    | (rw [div_le_one₀ hd]; linarith)
    | (rw [div_le_iff₀ hd]; linarith)
    | (rw [div_le_iff hd]; linarith)
  have hX2' : 0 ≤ (((n:ℝ) + 2) * Del) ^ 2 * (a + b) / (a ^ 2 * b ^ 2) := by positivity
  have hX3 : 1 / θ ^ 2 ≤ 1 := by
    have hd : 0 < θ ^ 2 := by positivity
    first
    | (rw [div_le_one hd]; nlinarith)
    | (rw [div_le_one₀ hd]; nlinarith)
    | (rw [div_le_iff₀ hd]; nlinarith)
    | (rw [div_le_iff hd]; nlinarith)
  have hX3' : 0 ≤ 1 / θ ^ 2 := by positivity
  have hX1' : 0 ≤ e ^ (n + 2) * B := by positivity
  have hfb := fac_bound n hn
  have hD : 0 ≤ Del ^ n * W * B ^ (n + 1) / 2 := by positivity
  have hYZ : (0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) * (W * B ^ (n + 1))
      ≤ (W * (4 * Del) ^ n * (n.factorial : ℝ)) * B ^ (n + 1) / 2 := by
    calc (0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) * (W * B ^ (n + 1))
        = (2 * (0.38:ℝ) ^ (n + 2) * ((n:ℝ) + 2) ^ n * Real.exp (1/4) ^ (n + 1)) *
            (Del ^ n * W * B ^ (n + 1) / 2) := by simp only [mul_pow]; ring
      _ ≤ (4 ^ n * (n.factorial : ℝ)) * (Del ^ n * W * B ^ (n + 1) / 2) :=
          mul_le_mul_of_nonneg_right hfb hD
      _ = (W * (4 * Del) ^ n * (n.factorial : ℝ)) * B ^ (n + 1) / 2 := by simp only [mul_pow]; ring
  have hYZ0 : 0 ≤ (0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) *
      (W * B ^ (n + 1)) := by positivity
  calc (0.38 * e / θ * B / (a * b / (((n:ℝ) + 2) * Del))) ^ (n + 2) * Vu
      ≤ (0.38 * e / θ * B / (a * b / (((n:ℝ) + 2) * Del))) ^ (n + 2) *
          ((a ^ n * (a + b)) * ((Real.exp (1/4) ^ (n + 1) * W) * (b * θ) ^ n)) :=
        mul_le_mul_of_nonneg_left hVu (pow_nonneg hbase _)
    _ = (e ^ (n + 2) * B) * ((((n:ℝ) + 2) * Del) ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
          ((0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1)) * (W * B ^ (n + 1)) :=
        top_alg n 0.38 e B a b (((n:ℝ) + 2) * Del) θ (Real.exp (1/4)) W ha.ne' hb.ne' hθ0.ne'
    _ = (e ^ (n + 2) * B) * ((((n:ℝ) + 2) * Del) ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
          ((0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) * (W * B ^ (n + 1))) := by
        ring
    _ ≤ (0.38:ℝ) ^ (n + 2) * (((n:ℝ) + 2) * Del) ^ n * Real.exp (1/4) ^ (n + 1) * (W * B ^ (n + 1)) :=
        key3 _ _ _ _ hX1' hs hX2' hX2 hX3' hX3 hYZ0
    _ ≤ (W * (4 * Del) ^ n * (n.factorial : ℝ)) * B ^ (n + 1) / 2 := hYZ
end Formalism.FourierDecayAlt.P.Sz5
