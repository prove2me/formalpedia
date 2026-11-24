-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.dimension_mass_joint_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:46.439657+00:00
-- url     : https://prove2.me/submissions/d464e1cf-4d0a-4128-9960-ac9250640d66

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound

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
theorem _root_.solution : DimensionMassJointBound := by
  intro f Dstar volY massr Isig dsig dimV hm hI hv h2 h3 hD
  rw [hD, h2]
  have hp : ∏ ρ ∈ range f, ((1 - 1 / 3 : ℝ) * dimV ρ) ≤ ∏ ρ ∈ range f, dsig ρ :=
    Finset.prod_le_prod (fun ρ hρ => mul_nonneg (by norm_num) (hv ρ (Finset.mem_range.1 hρ)))
      (fun ρ hρ => h3 ρ (Finset.mem_range.1 hρ))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hp
  have e : (1 - 1 / 3 : ℝ) = 2 / 3 := by norm_num
  rw [e] at hp
  calc (2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimV ρ
      = massr * Isig * ((2 / 3 : ℝ) ^ f * ∏ ρ ∈ range f, dimV ρ) := by ring
    _ ≤ massr * Isig * ∏ ρ ∈ range f, dsig ρ := mul_le_mul_of_nonneg_left hp (mul_pos hm hI).le
end Formalism.HermitianLattices.GenusMassVolumes
