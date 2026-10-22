-- Prove2me | solution 1 for FrieszDUE.FIFO.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:29:10.512318+00:00
-- url     : https://prove2.me/submissions/2b333ddf-00df-4665-955d-2e231ccba90c

import Mathlib
set_option autoImplicit false

theorem solution (f g : ℝ → ℝ) (hgf : Function.LeftInverse g f)
    (hfg : Function.RightInverse g f) (hf : Differentiable ℝ f) (z : ℝ)
    (hz : deriv f (g z) ≠ 0) :
    HasDerivAt g (1 / deriv f (g z)) z := by
  have hcont : Continuous f := hf.continuous
  have hinj : Function.Injective f := hgf.injective
  have hsurj : Function.Surjective f := hfg.surjective
  have hg : Continuous g := by
    rcases hcont.strictMono_of_inj hinj with hm | ha
    · let o : ℝ ≃o ℝ := hm.orderIsoOfSurjective f hsurj
      have : g = o.symm := by
        funext y
        apply hinj
        rw [hfg y]
        exact (o.apply_symm_apply y).symm
      rw [this]; exact o.symm.continuous
    · have hm : StrictMono (fun x => -f x) := fun a b hab => by simpa using ha hab
      have hs : Function.Surjective (fun x => -f x) := fun y => by
        obtain ⟨x, hx⟩ := hsurj (-y); exact ⟨x, by simp [hx]⟩
      let o : ℝ ≃o ℝ := hm.orderIsoOfSurjective _ hs
      have : g = fun y => o.symm (-y) := by
        funext y
        apply hinj
        rw [hfg y]
        have := o.apply_symm_apply (-y)
        change -f (o.symm (-y)) = -y at this
        linarith
      rw [this]; exact o.symm.continuous.comp continuous_neg
  have h := HasDerivAt.of_local_left_inverse hg.continuousAt (hf (g z)).hasDerivAt hz
    (Filter.Eventually.of_forall hfg)
  simpa [one_div] using h
