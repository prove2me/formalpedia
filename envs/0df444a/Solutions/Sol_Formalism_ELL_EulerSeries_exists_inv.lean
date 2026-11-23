-- Prove2me | solution 1 for Formalism.ELL.EulerSeries.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:16.304269+00:00
-- url     : https://prove2.me/submissions/31724a9f-23d8-4a1b-9ccb-62ca7f234a3e

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus
import Theorems.Thm_Formalism_ELL_EulerSeries_integral_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.EulerSeries
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]
variable [IsUltrametricDist K]
namespace Formalism.ELL.EulerSeries
theorem _root_.solution {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0)
    (hf : IntegralMv f) :
    ∃ h : MvPowerSeries σ K, MvPowerSeries.constantCoeff h = 0 ∧ IntegralMv h ∧
      f + h + f * h = 0 := by
  have hf' : ∀ n, MvPowerSeries.coeff n f ∈ unitBall K := fun n => hf n
  set f' := f.toSubring _ hf' with hf'def
  have hc : MvPowerSeries.constantCoeff f' = 0 := by
    apply Subtype.ext
    rw [hf'def, MvPowerSeries.constantCoeff_toSubring, hf0]
    rfl
  have hu : IsUnit (1 + f') := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add, hc, map_one, add_zero]
    exact isUnit_one
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨MvPowerSeries.map (unitBall K).subtype (v - 1), ?_, integral_map _, ?_⟩
  · have hprod := congrArg (MvPowerSeries.map (unitBall K).subtype) hv
    rw [map_mul, map_add, map_one, MvPowerSeries.map_toSubring] at hprod
    have h2 := congrArg MvPowerSeries.constantCoeff hprod
    simp only [map_mul, map_add, map_one, hf0, add_zero, one_mul] at h2
    simp only [map_sub, h2, map_one, sub_self]
  · have hprod := congrArg (MvPowerSeries.map (unitBall K).subtype) hv
    rw [map_mul, map_add, map_one, MvPowerSeries.map_toSubring] at hprod
    rw [map_sub, map_one]
    linear_combination hprod
end Formalism.ELL.EulerSeries
