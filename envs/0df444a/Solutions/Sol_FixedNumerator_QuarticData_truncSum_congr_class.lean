-- Prove2me | solution 1 for FixedNumerator.QuarticData.truncSum_congr_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:37:23.007132+00:00
-- url     : https://prove2.me/submissions/afe91eb6-03dd-4d8b-aeba-d06eff6da7f1

module
public import Definitions.Def_FixedNumerator_Split
public import Definitions.Def_FixedNumerator_Cases

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (W : GaussianInt → ℂ) (μ γ : GaussianInt) {β β' : GaussianInt}
    (h : (4 : GaussianInt) ∣ β - β') (X : ℕ) :
    truncSum D W μ β γ X = truncSum D W μ β' γ X := by
  classical
  unfold truncSum
  congr 1
  apply Finset.filter_congr
  intro c _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have : c - β' = (c - β) + (β - β') := by ring
    rw [this]; exact dvd_add h1 h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have : c - β = (c - β') - (β - β') := by ring
    rw [this]; exact dvd_sub h1 h
end FixedNumerator.QuarticData
