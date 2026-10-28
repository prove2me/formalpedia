-- Prove2me | solution 1 for BitDFT.multiplier_time_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:41:29.867441+00:00
-- url     : https://prove2.me/submissions/6980d69f-a085-4629-bda3-fac6b357386f

import Theorems.Thm_BitDFT_output_length_le_time
set_option autoImplicit false
open IntMul
theorem solution (M : MultitapeTM) (s : ℕ) (T : ℝ)
    (h : MultipliesAt M s T) : (2 * s : ℕ) ≤ T := by
  obtain ⟨t, ht, hout⟩ := h (List.replicate s false) (List.replicate s false) (by simp) (by simp)
  have hb := BitDFT.output_length_le_time M _ _ _ t hout
  simp only [bin, List.length_ofFn] at hb
  exact (by exact_mod_cast hb : ((2 * s : ℕ) : ℝ) ≤ t).trans ht
