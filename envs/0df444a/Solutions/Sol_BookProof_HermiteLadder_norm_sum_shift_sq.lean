-- Prove2me | solution 1 for BookProof.HermiteLadder.norm_sum_shift_sq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:22:21.412926+00:00
-- url     : https://prove2.me/submissions/1346d1af-f695-4b76-8451-200f6acb38f6

import Mathlib.Analysis.InnerProductSpace.Subspace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

theorem solution (v : ι → E) (hv : Orthonormal ℂ v) (σ : ι → ι) (S : Finset ι)
    (hinj : ∀ a ∈ S, ∀ b ∈ S, σ a = σ b → a = b) (g : ι → ℂ) :
    ‖∑ a ∈ S, g a • v (σ a)‖ ^ 2 = ∑ a ∈ S, ‖g a‖ ^ 2 := by
  classical
  have hσ : Function.Injective (fun a : S => σ a.1) := by
    intro a b hab
    apply Subtype.ext
    exact hinj a.1 a.2 b.1 b.2 hab
  have h := (hv.orthogonalFamily.comp hσ).norm_sum (fun a : S => g a.1) Finset.univ
  rw [← Finset.sum_attach S (fun a => g a • v (σ a)),
    ← Finset.sum_attach S (fun a => ‖g a‖ ^ 2)]
  simpa only [Function.comp_apply, LinearIsometry.toSpanSingleton_apply,
    Finset.univ_eq_attach] using h
