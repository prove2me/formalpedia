-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.step_arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:39.031663+00:00
-- url     : https://prove2.me/submissions/b14bfe02-c931-41ec-a53c-b18f4d4886f4

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
theorem _root_.solution (q N a W Qj Cj C' lo hi : ℝ) (hq : 2 ≤ q) (hN : 0 < N) (ha : 0 < a)
    (hWa : W * a = N ^ 2) (hsmall : q ^ 2 * a * 8 ≤ N) (hQ : 0 ≤ Qj)
    (h1 : (1 - a / N) * Qj ≤ Cj) (h2 : Cj ≤ (1 + a / N) * Qj)
    (hlo : lo = (W - q * N - q * a) / q) (hhi : hi = (W + q * N) / q)
    (hC1 : Cj * lo ≤ C') (hC2 : C' ≤ Cj * hi) :
    (1 - q ^ 2 * a / N) * (Qj * W / q) ≤ C' ∧ C' ≤ (1 + q ^ 2 * a / N) * (Qj * W / q) := by
  obtain ⟨d, hd⟩ : ∃ d, d = a / N := ⟨_, rfl⟩
  have hq0 : 0 < q := by linarith
  have hd0 : 0 < d := by rw [hd]; positivity
  have haN : a = N * d := by rw [hd]; field_simp
  have hW0 : 0 < W := by
    by_contra h
    push Not at h
    have : W * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h ha.le
    have : 0 < N ^ 2 := by positivity
    linarith
  have hNW : N = W * d := by
    have : W * d * N = N * N := by rw [mul_assoc, mul_comm d N, ← haN, hWa]; ring
    exact (mul_right_cancel₀ hN.ne' this).symm
  have hqd : q ^ 2 * d ≤ 1 / 8 := by
    have : q ^ 2 * (N * d) * 8 ≤ N := by rw [← haN]; exact hsmall
    have h3 : N * (q ^ 2 * d * 8) ≤ N * 1 := by nlinarith
    have := le_of_mul_le_mul_left h3 hN
    linarith
  have hqd1 : q * d ≤ 1 / 8 := by nlinarith
  have hd1 : d ≤ 1 / 8 := by nlinarith
  have e1 : q ^ 2 * a / N = q ^ 2 * d := by rw [hd]; ring
  rw [e1]
  rw [← hd] at h1 h2
  have hlo' : lo = (1 - q * d - q * d ^ 2) * (W / q) := by
    rw [hlo, haN, hNW]; field_simp
  have hhi' : hi = (1 + q * d) * (W / q) := by
    rw [hhi, hNW]; field_simp
  have hWq : 0 < W / q := by positivity
  have hCj0 : 0 ≤ Cj := le_trans (mul_nonneg (by linarith) hQ) h1
  have hA : 0 ≤ q ^ 2 - q - 2 := by nlinarith
  have key1 : (1 + d) * (1 + q * d) ≤ 1 + q ^ 2 * d := by
    nlinarith [mul_nonneg hd0.le hA, mul_nonneg hd0.le (sub_nonneg.2 hqd1)]
  have key2 : 1 - q ^ 2 * d ≤ (1 - d) * (1 - q * d - q * d ^ 2) := by
    nlinarith [mul_nonneg hd0.le hA, mul_pos hq0 (pow_pos hd0 3)]
  have hl0 : 0 ≤ 1 - q * d - q * d ^ 2 := by nlinarith
  have hP : 0 ≤ Qj * (W / q) := mul_nonneg hQ hWq.le
  have eP : Qj * W / q = Qj * (W / q) := by ring
  rw [eP]
  constructor
  · calc (1 - q ^ 2 * d) * (Qj * (W / q)) ≤ ((1 - d) * (1 - q * d - q * d ^ 2)) * (Qj * (W / q)) :=
          mul_le_mul_of_nonneg_right key2 hP
      _ = ((1 - d) * Qj) * lo := by rw [hlo']; ring
      _ ≤ Cj * lo := by
          apply mul_le_mul_of_nonneg_right h1
          rw [hlo']; positivity
      _ ≤ C' := hC1
  · calc C' ≤ Cj * hi := hC2
      _ ≤ ((1 + d) * Qj) * hi := by
          apply mul_le_mul_of_nonneg_right h2
          rw [hhi']; positivity
      _ = ((1 + d) * (1 + q * d)) * (Qj * (W / q)) := by rw [hhi']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right key1 hP
end Formalism.HermitianLatticeCounting.P.S4aux
