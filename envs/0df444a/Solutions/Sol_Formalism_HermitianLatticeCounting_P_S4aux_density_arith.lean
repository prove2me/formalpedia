-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.density_arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:21.869615+00:00
-- url     : https://prove2.me/submissions/f4597471-ae06-4acf-87f3-6b83c7aa7571

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (Q : ℝ) (hQ : 2 ≤ Q) (n m : ℕ) (hn : 2 * m + 3 ≤ n) (c NX tot : ℝ)
    (hc : c * Q ^ m = Q ^ n)
    (hX1 : NX ≤ (Q ^ n) ^ m) (hX2 : (Q ^ n) ^ m - Q ^ m * (Q ^ n) ^ m / Q ^ n ≤ NX)
    (ht1 : tot ≤ NX * c ^ m) (ht2 : NX * (c ^ m - Q ^ m * c ^ m / c) ≤ tot) :
    Q ^ (2 * n * m) / Q ^ (m ^ 2) / 2 ≤ tot ∧ tot ≤ 2 * (Q ^ (2 * n * m) / Q ^ (m ^ 2)) := by
  have hQ0 : 0 < Q := by linarith
  have hQm : 0 < Q ^ m := by positivity
  have hQn : 0 < Q ^ n := by positivity
  have hc0 : 0 < c := by
    by_contra h
    push Not at h
    have : c * Q ^ m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hQm.le
    linarith
  have hcm : 0 < c ^ m := by positivity
  have hA : 0 < (Q ^ n) ^ m := by positivity
  have hmain : Q ^ (2 * n * m) / Q ^ (m ^ 2) = (Q ^ n) ^ m * c ^ m := by
    rw [div_eq_iff (by positivity)]
    have : c ^ m * Q ^ (m ^ 2) = (Q ^ n) ^ m := by
      rw [← hc, mul_pow, ← pow_mul, sq]
    calc Q ^ (2 * n * m) = (Q ^ n) ^ m * (Q ^ n) ^ m := by
          rw [← pow_mul, ← pow_add]; congr 1; ring
      _ = _ := by rw [← this]; ring
  have h8 : (8 : ℝ) ≤ Q ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ Q ^ 3 := by gcongr
  have e1 : Q ^ m / Q ^ n ≤ 1 / 8 := by
    rw [div_le_iff₀ hQn]
    have : Q ^ n = Q ^ m * Q ^ (n - m) := by rw [← pow_add]; congr 1; omega
    have h3 : Q ^ 3 ≤ Q ^ (n - m) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [this]
    nlinarith
  have e2 : Q ^ m / c ≤ 1 / 8 := by
    rw [div_le_iff₀ hc0]
    have h4 : Q ^ n = Q ^ m * Q ^ m * Q ^ (n - 2 * m) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have h3 : Q ^ 3 ≤ Q ^ (n - 2 * m) := pow_le_pow_right₀ (by linarith) (by omega)
    have h5 : c = Q ^ m * Q ^ (n - 2 * m) := by
      have : c * Q ^ m = (Q ^ m * Q ^ (n - 2 * m)) * Q ^ m := by rw [hc, h4]; ring
      exact mul_right_cancel₀ hQm.ne' this
    rw [h5]
    nlinarith
  rw [hmain]
  have hX2' : (Q ^ n) ^ m * (7 / 8) ≤ NX := by
    have : Q ^ m * (Q ^ n) ^ m / Q ^ n = (Q ^ n) ^ m * (Q ^ m / Q ^ n) := by ring
    rw [this] at hX2
    nlinarith
  have hY2 : c ^ m * (7 / 8) ≤ c ^ m - Q ^ m * c ^ m / c := by
    have : Q ^ m * c ^ m / c = c ^ m * (Q ^ m / c) := by ring
    rw [this]
    nlinarith
  have hNX0 : 0 ≤ NX := by nlinarith
  constructor
  · calc (Q ^ n) ^ m * c ^ m / 2 ≤ ((Q ^ n) ^ m * (7 / 8)) * (c ^ m * (7 / 8)) := by nlinarith [mul_pos hA hcm]
      _ ≤ NX * (c ^ m - Q ^ m * c ^ m / c) := by
          apply mul_le_mul hX2' hY2 (by positivity) hNX0
      _ ≤ tot := ht2
  · calc tot ≤ NX * c ^ m := ht1
      _ ≤ (Q ^ n) ^ m * c ^ m := by gcongr
      _ ≤ _ := by nlinarith [mul_pos hA hcm]
end Formalism.HermitianLatticeCounting.P.S4aux
