-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_real_mesh_ceiling_cell_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:47:14.311267+00:00
-- url     : https://prove2.me/submissions/ecc552bc-190f-46d8-aec6-97c4ad7ec777

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (u T : ℝ) (hT : 0 < T) (k i : ℕ) (hk : 0 < k) :
    Nat.ceil (u * (k : ℝ) / T) = i + 1 ↔
      (i : ℝ) * T / (k : ℝ) < u ∧
      u ≤ ((i + 1 : ℕ) : ℝ) * T / (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  constructor
  · intro hc
    have hil : i < Nat.ceil (u * (k : ℝ) / T) := by omega
    have hle : Nat.ceil (u * (k : ℝ) / T) ≤ i + 1 := le_of_eq hc
    constructor
    · apply (div_lt_iff₀ hkR).mpr
      exact (lt_div_iff₀ hT).mp ((Nat.lt_ceil).mp hil)
    · apply (le_div_iff₀ hkR).mpr
      exact (div_le_iff₀ hT).mp ((Nat.ceil_le).mp hle)
  · rintro ⟨hlow, hupp⟩
    have hlt : (i : ℝ) < u * (k : ℝ) / T :=
      (lt_div_iff₀ hT).mpr ((div_lt_iff₀ hkR).mp hlow)
    have hle : u * (k : ℝ) / T ≤ ((i + 1 : ℕ) : ℝ) :=
      (div_le_iff₀ hT).mpr ((le_div_iff₀ hkR).mp hupp)
    have hil : i < Nat.ceil (u * (k : ℝ) / T) :=
      (Nat.lt_ceil).mpr hlt
    have hir : Nat.ceil (u * (k : ℝ) / T) ≤ i + 1 :=
      (Nat.ceil_le).mpr hle
    omega
