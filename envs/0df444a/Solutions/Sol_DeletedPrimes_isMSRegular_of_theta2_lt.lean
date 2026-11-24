-- Prove2me | solution 1 for DeletedPrimes.isMSRegular_of_theta2_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:10:06.659713+00:00
-- url     : https://prove2.me/submissions/d2833967-495e-49bb-acf2-bd969f47a7fd

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_IsRegular_mono
import Theorems.Thm_DeletedPrimes_IsMSRegular_mono
import Theorems.Thm_DeletedPrimes_theta2_set_one_mem

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {θ : ℝ} (h : theta2 S < θ) : IsMSRegular S θ := by
  obtain ⟨θ₀, hθ₀, hlt⟩ := exists_lt_of_csInf_lt ⟨1, theta2_set_one_mem S⟩ h
  exact hθ₀.2.mono hlt.le
end DeletedPrimes
