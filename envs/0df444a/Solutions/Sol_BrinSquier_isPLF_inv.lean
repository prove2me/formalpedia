-- Prove2me | solution 1 for BrinSquier.isPLF_inv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-12T22:13:22.963334+00:00
-- url     : https://prove2.me/submissions/681a2bd9-3bd3-491d-8d73-0984866af878

import Definitions.Def_BrinSquier
import Mathlib

open BrinSquier

theorem solution {f : ℝ ≃o ℝ} (hf : IsPLF f) : IsPLF f⁻¹ := by
  classical
  obtain ⟨B, hB⟩ := hf
  refine ⟨B.image (fun t => f t), ?_⟩
  intro z hz
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, not_exists, not_and] at hz
  have hfx : f (f⁻¹ z) = z := RelIso.apply_inv_self f z
  set x : ℝ := f⁻¹ z with hxdef
  have hxB : x ∉ (B : Set ℝ) := fun hmem => absurd hfx (hz x (Finset.mem_coe.1 hmem))
  obtain ⟨e, he, a, b, h⟩ := hB x hxB
  have hm1 : x - e/2 ∈ Set.Ioo (x - e) (x + e) := ⟨by linarith, by linarith⟩
  have hm2 : x + e/2 ∈ Set.Ioo (x - e) (x + e) := ⟨by linarith, by linarith⟩
  -- the local slope is positive, because `f` is strictly increasing
  have hlt : f (x - e/2) < f (x + e/2) := f.strictMono (by linarith)
  have ha : 0 < a := by
    rw [h _ hm1, h _ hm2] at hlt; nlinarith [hlt, he]
  have hane : a ≠ 0 := ne_of_gt ha
  -- an interval around `z` whose preimage lands in the affine window
  have hu : f (x - e/2) < z := by rw [← hfx]; exact f.strictMono (by linarith)
  have hv : z < f (x + e/2) := by rw [← hfx]; exact f.strictMono (by linarith)
  refine ⟨min (z - f (x - e/2)) (f (x + e/2) - z), lt_min (by linarith) (by linarith),
          1/a, -b/a, ?_⟩
  intro w hw
  have hle1 := min_le_left (z - f (x - e/2)) (f (x + e/2) - z)
  have hle2 := min_le_right (z - f (x - e/2)) (f (x + e/2) - z)
  have hw1 : f (x - e/2) < w := by linarith [hw.1]
  have hw2 : w < f (x + e/2) := by linarith [hw.2]
  have hlo : x - e/2 < f⁻¹ w := by
    apply f.lt_iff_lt.mp; rw [RelIso.apply_inv_self]; exact hw1
  have hhi : f⁻¹ w < x + e/2 := by
    apply f.lt_iff_lt.mp; rw [RelIso.apply_inv_self]; exact hw2
  have hmem : f⁻¹ w ∈ Set.Ioo (x - e) (x + e) := ⟨by linarith, by linarith⟩
  have hval : a * (f⁻¹ w) + b = w := by
    have := h (f⁻¹ w) hmem
    rw [RelIso.apply_inv_self] at this
    linarith [this]
  show f⁻¹ w = 1/a * w + -b/a
  field_simp
  linarith [hval]
