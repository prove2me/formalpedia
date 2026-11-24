-- Prove2me | solution 1 for DeletedPrimes.isRegular_of_theta_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:06:38.920802+00:00
-- url     : https://prove2.me/submissions/1172c071-971e-45e3-bd79-5fb18acc3447

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_IsRegular_mono
import Theorems.Thm_DeletedPrimes_theta_set_one_mem

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {θ : ℝ} (h : theta S < θ) : IsRegular S θ := by
  obtain ⟨θ₀, hθ₀, hlt⟩ := exists_lt_of_csInf_lt ⟨1, theta_set_one_mem S⟩ h
  exact hθ₀.2.mono hlt.le
end DeletedPrimes
