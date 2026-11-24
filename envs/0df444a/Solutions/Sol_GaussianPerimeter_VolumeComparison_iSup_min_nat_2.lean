-- Prove2me | solution 2 for GaussianPerimeter.VolumeComparison.iSup_min_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:19:13.382913+00:00
-- url     : https://prove2.me/submissions/a472bc24-54d6-4f18-883d-675b9a36bba2

module
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution (a : ENNReal) : ⨆ (n : ℕ), min a n = a := by
  apply iSup_eq_of_forall_le_of_forall_lt_exists_gt (by simp)
  intro w hw
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hw.trans_le le_top).ne
  exact ⟨n, by simp_all⟩
end GaussianPerimeter.VolumeComparison
