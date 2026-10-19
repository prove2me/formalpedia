-- Prove2me | solution 1 for Ehrhart.TranslatedGaussianLatticeAsymptotics.roundedLatticeExponent_coordinate_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/4ad82373-f141-405c-be72-15a2f5e470dc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    {k : ℕ} (hk : 0 < k)
    (u : Space n) (i : Fin n) :
    roundedLatticeExponent k u i ≤ u i ∧
      u i - roundedLatticeExponent k u i < 1 / (k : ℝ) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hfloor := Int.floor_le ((k : ℝ) * u i)
  have hnext := Int.lt_floor_add_one ((k : ℝ) * u i)
  constructor
  · apply (div_le_iff₀ hkreal).mpr
    change (⌊(k : ℝ) * u i⌋ : ℝ) ≤ u i * (k : ℝ)
    nlinarith
  · change u i - (⌊(k : ℝ) * u i⌋ : ℝ) / (k : ℝ) <
      1 / (k : ℝ)
    have heq :
        u i - (⌊(k : ℝ) * u i⌋ : ℝ) / (k : ℝ) =
          ((k : ℝ) * u i - (⌊(k : ℝ) * u i⌋ : ℝ)) /
            (k : ℝ) := by
      field_simp
    rw [heq]
    apply (div_lt_div_iff_of_pos_right hkreal).mpr
    linarith
end Ehrhart.TranslatedGaussianLatticeAsymptotics
