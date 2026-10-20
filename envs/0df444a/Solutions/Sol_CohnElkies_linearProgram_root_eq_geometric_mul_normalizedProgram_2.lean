-- Prove2me | solution 2 for CohnElkies.linearProgram_root_eq_geometric_mul_normalizedProgram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:31:37.026658+00:00
-- url     : https://prove2.me/submissions/6a77ae63-bfbe-4ba6-8425-0f09252607d3

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Set


theorem solution
    {d : ℕ} (hd : 0 < d) (hadmissible : Nonempty (Admissible d)) :
    (linearProgram d) ^ ((d : ℝ)⁻¹) =
      packingGeometricRoot d * normalizedProgram d := by
  obtain ⟨f0⟩ := hadmissible
  have hpos : ∀ q ∈ quotientSet d, 0 < q := by
    rintro _ ⟨f, rfl⟩; exact div_pos (admissible_zero_pos f) f.fourier_zero_pos
  have hne : (quotientSet d).Nonempty := ⟨_, f0, rfl⟩
  have hbdd : BddBelow (quotientSet d) := ⟨0, fun q hq => (hpos q hq).le⟩
  have hinf0 : 0 ≤ sInf (quotientSet d) := le_csInf hne (fun q hq => (hpos q hq).le)
  have hmono : MonotoneOn (fun x : ℝ => x ^ ((d:ℝ)⁻¹) / Real.sqrt d) (quotientSet d) := by
    intro a ha b hb hab
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (hpos a ha).le hab (by positivity)) (Real.sqrt_nonneg _)
  have hcont : Continuous (fun x : ℝ => x ^ ((d:ℝ)⁻¹) / Real.sqrt d) :=
    (Real.continuous_rpow_const (by positivity)).div_const _
  have hmap := hmono.map_csInf_of_continuousWithinAt hcont.continuousAt.continuousWithinAt hne hbdd
  have hnorm : normalizedProgram d = sInf (quotientSet d) ^ ((d:ℝ)⁻¹) / Real.sqrt d := by
    rw [hmap]; unfold normalizedProgram quotientSet; rw [← Set.range_comp]; rfl
  have hsq : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hV : 0 ≤ unitBallVolume d / (2:ℝ) ^ d := (div_pos (unitBallVolume_pos d) (by positivity)).le
  unfold linearProgram packingGeometricRoot
  rw [hnorm, Real.mul_rpow hV hinf0]
  field_simp

