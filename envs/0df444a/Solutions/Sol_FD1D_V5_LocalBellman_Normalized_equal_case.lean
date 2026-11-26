-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.equal_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:51.736948+00:00
-- url     : https://prove2.me/submissions/d0e642a2-242b-410f-80c1-b681509e3557

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_g_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_d_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_residual_eq_common
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution
    {s r : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2) :
    residual s r 0 0 ≥
      (rateIncrement s 0 0 + 0 ^ 2) / 1000 := by
  have hcommon :=
    residual_eq_common
      (s := s) (r := r) (ρ := 0) (k := 0)
      hs (by norm_num) (by norm_num)
  have hcommon' :
      residual s r 0 0 =
        r ^ 2 / 8 +
          g s r * (1 / 2 - r) * (s + 1) /
            (2 * d s 0 * (s + 1 / 2)) := by
    simpa [lambda] using hcommon
  have hres :
      0 ≤ residual s r 0 0 := by
    rw [hcommon']
    have hg : 0 < g s r := g_pos hr0
    have hd : 0 < d s 0 := d_pos hs (by norm_num) (by norm_num)
    have hterm :
        0 ≤ g s r * (1 / 2 - r) * (s + 1) /
          (2 * d s 0 * (s + 1 / 2)) := by
      positivity
    exact add_nonneg (by positivity) hterm
  have hrate : rateIncrement s 0 0 = 0 := by
    unfold rateIncrement hPlus hMinus
    field_simp [hs.ne']
    ring
  simpa [hrate] using hres
end FD1D.V5.LocalBellman.Normalized
