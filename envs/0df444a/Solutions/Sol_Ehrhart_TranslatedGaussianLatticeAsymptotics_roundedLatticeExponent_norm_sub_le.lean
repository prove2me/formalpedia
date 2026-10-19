-- Prove2me | solution 1 for Ehrhart.TranslatedGaussianLatticeAsymptotics.roundedLatticeExponent_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/6a171599-5387-46c0-9cff-fae1e670f80b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TranslatedGaussianLatticeAsymptotics_roundedLatticeExponent_coordinate_error

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TranslatedGaussianLatticeAsymptotics
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
namespace Ehrhart.TranslatedGaussianLatticeAsymptotics
theorem _root_.solution {n : ℕ}
    {k : ℕ} (hk : 0 < k) (u : Space n) :
    ‖roundedLatticeExponent k u - u‖ ≤ 1 / (k : ℝ) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 1 / (k : ℝ))).mpr
  intro i
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have h := roundedLatticeExponent_coordinate_error hk u i
  rw [abs_of_nonpos (sub_nonpos.mpr h.1)]
  linarith [h.2]
end Ehrhart.TranslatedGaussianLatticeAsymptotics
