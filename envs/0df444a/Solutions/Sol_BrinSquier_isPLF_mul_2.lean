-- Prove2me | solution 2 for BrinSquier.isPLF_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-14T11:46:27.939485+00:00
-- url     : https://prove2.me/submissions/1cb16bc0-bf8b-4ed1-b7ca-bd7e3627e4c9

import Theorems.Thm_LocallyAffine_affineAt_comp
import Definitions.Def_BrinSquier
import Mathlib

open BrinSquier

/-- Closure of `PLF(ℝ)` under composition, with the ε-δ work delegated to the general fact
that local affineness composes. -/
theorem solution {f g : ℝ ≃o ℝ} (hf : IsPLF f) (hg : IsPLF g) : IsPLF (f * g) := by
  classical
  obtain ⟨Bf, hBf⟩ := hf
  obtain ⟨Bg, hBg⟩ := hg
  refine ⟨Bg ∪ Bf.image (fun z => g⁻¹ z), ?_⟩
  intro x hx
  simp only [Finset.coe_union, Set.mem_union, Finset.coe_image, Set.mem_image,
    Finset.mem_coe, not_or, not_exists, not_and] at hx
  obtain ⟨hxg, hxf⟩ := hx
  -- `g x` is not a breakpoint of `f`, since `x` is not the `g`-preimage of one
  have hgx : (g x) ∉ (Bf : Set ℝ) := fun hmem =>
    absurd (RelIso.inv_apply_self g x) (hxf _ (Finset.mem_coe.1 hmem))
  -- the lemma's inner map is our `g`, its outer map our `f`
  exact LocallyAffine.affineAt_comp (f := (g : ℝ → ℝ)) (g := (f : ℝ → ℝ)) (x := x)
    (hBg x hxg) (hBf (g x) hgx)
