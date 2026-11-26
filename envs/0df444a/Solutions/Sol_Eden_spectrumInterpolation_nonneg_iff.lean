-- Prove2me | solution 1 for Eden.spectrumInterpolation_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:10:45.122264+00:00
-- url     : https://prove2.me/submissions/ad3fe34f-bb10-4dde-bb55-08ccfd15327c

import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_InterpolationSign
import Theorems.Thm_Eden_spectrumEntry_antitone
import Theorems.Thm_Eden_spectrumPartialSum_nonneg_of_le
import Theorems.Thm_Eden_kaplanYorkeIndex_le_dimension
import Theorems.Thm_Eden_kaplanYorkeDimension_lt_succ_index
import Theorems.Thm_Eden_spectrumInterpolation_index_criterion
import Theorems.Thm_Eden_exists_dimension_segment
import Theorems.Thm_Eden_kaplanYorkeIndex_mem
import Theorems.Thm_Eden_spectrumEntry_at_kaplanYorkeIndex_neg
import Theorems.Thm_Eden_spectrumInterpolation_interpolate
import Theorems.Thm_Eden_spectrumPartialSum_after_index_neg
import Theorems.Thm_Eden_spectrumPartialSum_succ


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {a : Fin 5 → ℝ} (ha : Antitone a)
    {d : ℝ} (hd : d ∈ Icc 0 5) :
    0 ≤ spectrumInterpolation a d ↔ d ≤ kaplanYorkeDimension a := by
  obtain ⟨k, hk, α, hα, rfl⟩ := exists_dimension_segment hd
  rw [spectrumInterpolation_interpolate a hk hα.1 hα.2]
  rcases lt_trichotomy k (kaplanYorkeIndex a) with hkj | hkj | hjk
  · have hs := kaplanYorkeIndex_mem a
    have hsk := spectrumPartialSum_nonneg_of_le ha hkj.le hs.1 hs.2
    have hsk₁ := spectrumPartialSum_nonneg_of_le ha
      (show k + 1 ≤ kaplanYorkeIndex a by omega) hs.1 hs.2
    have h₀ := mul_nonneg (sub_nonneg.mpr hα.2) hsk
    have h₁ := mul_nonneg hα.1 hsk₁
    rw [spectrumPartialSum_succ] at h₁
    have hn : 0 ≤ spectrumPartialSum a k + α * spectrumEntry a k := by nlinarith
    have hkreal : (k : ℝ) + 1 ≤ kaplanYorkeIndex a := by exact_mod_cast hkj
    have hle := kaplanYorkeIndex_le_dimension a
    exact iff_of_true hn (by linarith [hα.2])
  · subst k
    exact spectrumInterpolation_index_criterion hk α
  · have hsneg := spectrumPartialSum_after_index_neg hjk hk.le
    have hj₅ : kaplanYorkeIndex a < 5 := lt_trans hjk hk
    have haneg := (spectrumEntry_antitone ha hjk.le hk).trans_lt
      (spectrumEntry_at_kaplanYorkeIndex_neg hj₅)
    have hmul := mul_nonpos_of_nonneg_of_nonpos hα.1 haneg.le
    have hn : spectrumPartialSum a k + α * spectrumEntry a k < 0 := by linarith
    have hkreal : (kaplanYorkeIndex a : ℝ) + 1 ≤ k := by exact_mod_cast hjk
    have hdim := kaplanYorkeDimension_lt_succ_index hj₅
    exact iff_of_false (not_le_of_gt hn) (not_le_of_gt (by linarith [hα.1]))
end Eden
