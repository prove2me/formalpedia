-- Prove2me | solution 1 for BB6Kit.card_box
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T22:22:04.13246+00:00
-- url     : https://prove2.me/submissions/4330fb2e-066e-424d-8e00-14af34b181de

import Mathlib
import Definitions.Def_BB6Kit

theorem solution (α1 α2 α3 X Y Z : ℕ) (h1 : 0 < α1) (h2 : 0 < α2) (h3 : 0 < α3)
    (hind : BB6Kit.MultIndep α1 α2 α3) :
    ((Finset.range (X + 1) ×ˢ Finset.range (Y + 1) ×ˢ Finset.range (Z + 1)).image
      (fun x => α1 ^ x.1 * α2 ^ x.2.1 * α3 ^ x.2.2)).card = (X + 1) * (Y + 1) * (Z + 1) := by
  rw [Finset.card_image_of_injOn]
  · simp only [Finset.card_product, Finset.card_range]
    ring
  · intro a _ b _ hab
    simp only at hab
    have hR : ((α1 : ℝ) ^ a.1 * (α2 : ℝ) ^ a.2.1 * (α3 : ℝ) ^ a.2.2) =
        (α1 : ℝ) ^ b.1 * (α2 : ℝ) ^ b.2.1 * (α3 : ℝ) ^ b.2.2 := by exact_mod_cast hab
    have h1' : (α1 : ℝ) ≠ 0 := by exact_mod_cast h1.ne'
    have h2' : (α2 : ℝ) ≠ 0 := by exact_mod_cast h2.ne'
    have h3' : (α3 : ℝ) ≠ 0 := by exact_mod_cast h3.ne'
    have hB : (α1 : ℝ) ^ b.1 * (α2 : ℝ) ^ b.2.1 * (α3 : ℝ) ^ b.2.2 ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (pow_ne_zero _ h1') (pow_ne_zero _ h2')) (pow_ne_zero _ h3')
    have key := hind ((a.1 : ℤ) - b.1) ((a.2.1 : ℤ) - b.2.1) ((a.2.2 : ℤ) - b.2.2) (by
      rw [zpow_sub₀ h1', zpow_sub₀ h2', zpow_sub₀ h3']
      simp only [zpow_natCast]
      rw [div_mul_div_comm, div_mul_div_comm, hR, div_self hB])
    obtain ⟨e1, e2, e3⟩ := key
    exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))
