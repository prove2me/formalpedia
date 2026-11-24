-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.biSup_add_biSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:17:47.42636+00:00
-- url     : https://prove2.me/submissions/6961491d-f121-4d6b-ae4d-8d79c72508a2

module
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution
    {ι κ : Sort*}
    {p : ι → Prop} {q : κ → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {f : ι → ENNReal} {g : κ → ENNReal} :
    (⨆ i, ⨆ _ : p i, f i) + (⨆ j, ⨆ _ : q j, g j) =
    (⨆ i, ⨆ j, ⨆ _ : p i, ⨆ _ : q j, f i + g j) := by
  apply le_antisymm
  · calc
      (⨆ x, ⨆ _ : p x, f x) + (⨆ y, ⨆ _ : q y, g y)
          = ⨆ x, ⨆ _ : p x, (f x + (⨆ y, ⨆ _ : q y, g y)) := by apply ENNReal.biSup_add' hp
      _ ≤ (⨆ x, ⨆ y, ⨆ _ : p x, ⨆ _ : q y, f x + g y) := by
        apply iSup₂_le
        intro x hx
        calc
          f x + (⨆ y, ⨆ _ : q y, g y) = ⨆ y, ⨆ _ : q y, (f x + g y) := by
            apply ENNReal.add_biSup' hq
          _ ≤ ⨆ x, ⨆ _ : p x, (⨆ y, ⨆ _ : q y, (f x + g y)) := by
            apply le_iSup₂ x hx
          _ = ⨆ x, ⨆ y, ⨆ _ : p x, ⨆ _ : q y, (f x + g y) := by
            apply iSup_congr; intro; exact iSup_comm
  simp only [iSup_le_iff]
  intro i j hi hj
  calc
    f i + g j ≤ (⨆ i, ⨆ (_ : p i), f i) + g j := by gcongr; apply le_iSup₂ i hi
    _ ≤ (⨆ i, ⨆ (_ : p i), f i) + ⨆ j, ⨆ (_ : q j), g j := by gcongr; apply le_iSup₂ j hj
end GaussianPerimeter.VolumeComparison
