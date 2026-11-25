-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.log_pow_seven_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:21:10.052897+00:00
-- url     : https://prove2.me/submissions/8136147d-da86-4e00-b5fa-8da48a626f3b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_OneLeLogOfThreeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution (c : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → c * Real.log q ^ 7 ≤ Real.sqrt q := by
  have h := isLittleO_log_rpow_rpow_atTop (7 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have hb := h.bound (show (0 : ℝ) < 1 / (|c| + 1) by positivity)
  have hn := tendsto_natCast_atTop_atTop.eventually hb
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp (hn.and (Filter.eventually_ge_atTop 1))
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨h1, h2⟩ := hq₀ q hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h2
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at h1
  have e7 : Real.log q ^ (7 : ℝ) = Real.log q ^ 7 := by
    exact_mod_cast Real.rpow_natCast (Real.log q) 7
  rw [e7, ← Real.sqrt_eq_rpow] at h1
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  calc c * Real.log q ^ 7 ≤ |c| * Real.log q ^ 7 :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    _ ≤ |c| * (1 / (|c| + 1) * Real.sqrt q) := by gcongr
    _ ≤ Real.sqrt q := by
        rw [← mul_assoc]
        apply mul_le_of_le_one_left hs
        rw [mul_one_div, div_le_one (by positivity)]
        linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
