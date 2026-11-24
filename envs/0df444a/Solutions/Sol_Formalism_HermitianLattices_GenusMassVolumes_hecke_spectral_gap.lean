-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.hecke_spectral_gap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:47.954943+00:00
-- url     : https://prove2.me/submissions/1fd9b41e-ec95-49ee-ba05-c2f89d4615d2

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CardUnitsZmodPrimeSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : SW_hecke_gap := by
  intro q M hq hM
  have hq0 : (0 : ℝ) < q := by linarith
  have h1 : q ^ 3 ≤ q ^ M := pow_le_pow_right₀ (by linarith) hM
  have h2 : 0 < q ^ (2 - (M : ℤ)) := zpow_pos hq0 _
  have h3 : q ^ 2 + 1 < q ^ 3 := by nlinarith [sq_nonneg q, mul_pos hq0 hq0]
  have hgap : q ^ 2 + q < q ^ M + q - 1 + q ^ (2 - (M : ℤ)) := by linarith
  refine ⟨hgap, ?_⟩
  intro S hS hle
  by_contra hne
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hne)
  have := mul_lt_mul_of_pos_right hgap hSpos
  linarith
end Formalism.HermitianLattices.GenusMassVolumes
