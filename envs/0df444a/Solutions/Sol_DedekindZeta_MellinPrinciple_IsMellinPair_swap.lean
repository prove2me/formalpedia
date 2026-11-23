-- Prove2me | solution 1 for DedekindZeta.MellinPrinciple.IsMellinPair.swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:21:15.376209+00:00
-- url     : https://prove2.me/submissions/d1677d1b-2bc9-4c72-878d-89d644eda080

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple

set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
namespace DedekindZeta.MellinPrinciple
namespace IsMellinPair
theorem _root_.solution (h : IsMellinPair f g a₀ b₀ C k c α) :
    IsMellinPair g f b₀ a₀ C⁻¹ k c α where
  hf_cont := h.hg_cont
  hg_cont := h.hf_cont
  hk := h.hk
  hc := h.hc
  hα := h.hα
  hC := inv_ne_zero h.hC
  hf_decay := h.hg_decay
  hg_decay := h.hf_decay
  hfe := by
    intro y hy
    have hy' : (0 : ℝ) < 1 / y := by positivity
    have h1 := h.hfe (1 / y) hy'
    rw [one_div_one_div] at h1
    -- h1 : f y = C * (((1/y) ^ k : ℝ) : ℂ) * g (1/y)
    have hr : ((1 : ℝ) / y) ^ k = (y ^ k)⁻¹ := by
      rw [one_div, Real.inv_rpow hy.le]
    rw [hr, Complex.ofReal_inv] at h1
    -- h1 : f y = C * ((y ^ k : ℝ) : ℂ)⁻¹ * g (1/y)
    have hyk : (0 : ℝ) < y ^ k := Real.rpow_pos_of_pos hy k
    have hA : ((y ^ k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hyk
    rw [h1]
    field_simp
    rw [mul_div_assoc, div_self h.hC, mul_one]
end IsMellinPair
end DedekindZeta.MellinPrinciple
