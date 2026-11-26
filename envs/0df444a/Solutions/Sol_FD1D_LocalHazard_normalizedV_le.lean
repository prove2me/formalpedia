-- Prove2me | solution 1 for FD1D.LocalHazard.normalizedV_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:10.872488+00:00
-- url     : https://prove2.me/submissions/ad03c4d8-8ddf-49ec-954a-9a214a0155f7

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_N_pos
import Theorems.Thm_FD1D_LocalHazard_D_pos
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a : ℝ} {x y : ℕ} (ha : 0 < a) :
    ((x : ℝ) - (y : ℝ)) ^ 2 / (2 * D a x y) ≤ N x y / (2 * a) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [D, N]
  · have hx : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
    have hy : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
    have hN : 0 < N x y := N_pos hne
    have hD : 0 < D a x y := D_pos ha hne
    have hxy : 0 ≤ (x : ℝ) * (y : ℝ) := mul_nonneg hx hy
    have hdelta : ((x : ℝ) - (y : ℝ)) ^ 2 ≤ N x y ^ 2 := by
      simp only [N]
      nlinarith
    have haDelta :
        a * ((x : ℝ) - (y : ℝ)) ^ 2 ≤ a * N x y ^ 2 :=
      mul_le_mul_of_nonneg_left hdelta ha.le
    have hDlower : a * N x y ≤ D a x y := by
      simp only [D]
      nlinarith
    have hND : N x y * (a * N x y) ≤ N x y * D a x y :=
      mul_le_mul_of_nonneg_left hDlower hN.le
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * D a x y)
      (by positivity : 0 < 2 * a)).2
    nlinarith [haDelta, hND]
end FD1D.LocalHazard
