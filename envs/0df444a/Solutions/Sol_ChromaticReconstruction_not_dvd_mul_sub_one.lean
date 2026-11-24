-- Prove2me | solution 1 for ChromaticReconstruction.not_dvd_mul_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:07:59.601474+00:00
-- url     : https://prove2.me/submissions/3fa2ec5c-8d03-403e-8eef-2c4b32a8b1ed

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {q r : ℕ} (hq : 2 ≤ q) (hr : 1 ≤ r) (x : ℕ) : q * x ≠ q * r - 1 := by
  intro h
  have h1 : q * x + 1 = q * r := by
    have : 1 ≤ q * r := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have : q ∣ 1 := (Nat.dvd_add_right (dvd_mul_right q x)).mp (h1 ▸ dvd_mul_right q r)
  have := Nat.le_of_dvd one_pos this
  omega
end ChromaticReconstruction
