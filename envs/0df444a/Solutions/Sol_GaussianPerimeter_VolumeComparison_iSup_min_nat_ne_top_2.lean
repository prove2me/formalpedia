-- Prove2me | solution 2 for GaussianPerimeter.VolumeComparison.iSup_min_nat_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:19:24.012712+00:00
-- url     : https://prove2.me/submissions/16b6df15-f7b2-4ac0-bb2c-700ccb9d2ed0

module
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution {ι : Sort*} (n : ℕ) (f : ι → ENNReal) :
    iSup (fun x ↦ min (f x) n) ≠ ⊤ := by
  apply ne_of_lt
  rw [iSup_lt_iff]
  use n
  exact ⟨ENNReal.natCast_lt_top n, fun x ↦ min_le_right (f x) ↑n⟩
end GaussianPerimeter.VolumeComparison
