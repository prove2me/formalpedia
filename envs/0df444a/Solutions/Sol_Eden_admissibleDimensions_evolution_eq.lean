-- Prove2me | solution 1 for Eden.admissibleDimensions_evolution_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:13.732316+00:00
-- url     : https://prove2.me/submissions/9b0c863a-a2c2-4a4c-bb44-e412bbd24b28

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Theorems.Thm_Eden_one_le_singularValueFunction_iff_interpolation
import Theorems.Thm_Eden_kaplanYorkeDimension_mem_interval
import Theorems.Thm_Eden_normalizedLogSingularValues_antitone
import Theorems.Thm_Eden_spectrumInterpolation_nonneg_iff


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) :
    admissibleDimensions (fderiv ℝ (evolution c t) p).toLinearMap =
      Icc 0 (kaplanYorkeDimension (normalizedLogSingularValues c t p)) := by
  ext d
  constructor
  · rintro ⟨hd, hω⟩
    exact ⟨hd.1, (spectrumInterpolation_nonneg_iff
      (normalizedLogSingularValues_antitone c ht p) hd).mp
      ((one_le_singularValueFunction_iff_interpolation c ht p d).mp hω)⟩
  · intro hd
    have hd₅ : d ∈ Icc 0 5 := ⟨hd.1, hd.2.trans
      (kaplanYorkeDimension_mem_interval (normalizedLogSingularValues c t p)).2⟩
    exact ⟨hd₅, (one_le_singularValueFunction_iff_interpolation c ht p d).mpr
      ((spectrumInterpolation_nonneg_iff
        (normalizedLogSingularValues_antitone c ht p) hd₅).mpr hd.2)⟩
end Eden
