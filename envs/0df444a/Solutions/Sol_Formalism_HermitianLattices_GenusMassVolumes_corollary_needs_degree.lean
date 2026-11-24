-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.corollary_needs_degree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:45.527976+00:00
-- url     : https://prove2.me/submissions/d7345fad-fb52-4d71-9aa2-cdde4b63f761

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_OneAddInvPowLeExpOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : MeanSquareRequiresDegreeBound := by
  intro c hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
  have h1 : ((1:ℝ) / 2) ^ (n + 1) < c :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)) hn
  have h2 : ((1:ℝ) / 2) ^ (n + 1) * 2 ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
  have h3 := mul_lt_mul_of_pos_right h1 (pow_pos (by norm_num : (0:ℝ) < 2) (n + 1))
  rw [h2] at h3
  have h4 : (0:ℝ) ≤ 1 / (((n + 1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) := by positivity
  refine ⟨n + 1, 1, 2, 2, 1, 2 ^ (n + 1), 1, by omega, le_rfl, le_rfl, by norm_num, le_rfl, by positivity,
    one_pos, by simp, by simp, ?_, ?_⟩
  · rw [Real.one_rpow, mul_one]
    linarith
  · norm_num
    linarith
end Formalism.HermitianLattices.GenusMassVolumes
