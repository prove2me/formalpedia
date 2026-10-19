-- Prove2me | solution 1 for CohnElkies.linearProgram_root_eq_geometric_mul_normalizedProgram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/ac0ebdcf-721b-41c4-8981-211c02e83845

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_geometricFactor_pos
import Theorems.Thm_CohnElkies_normalizedProgram_eq_quotientInf_root
import Theorems.Thm_CohnElkies_quotientInf_nonneg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Set
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (hadmissible : Nonempty (Admissible d)) :
    (linearProgram d) ^ ((d : ℝ)⁻¹) =
      packingGeometricRoot d * normalizedProgram d := by
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'
  rw [normalizedProgram_eq_quotientInf_root d hadmissible]
  unfold linearProgram packingGeometricRoot quotientRootMap
  rw [Real.mul_rpow (geometricFactor_pos d).le
    (quotientInf_nonneg d hadmissible)]
  field_simp
end CohnElkies
