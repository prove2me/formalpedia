-- Prove2me | solution 1 for ConnesRZ.spectral_weil_pair_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T15:05:44.974617+00:00
-- url     : https://prove2.me/submissions/115ab315-5bfd-40ea-afe9-a25e32a5b7c3

import Theorems.Thm_ConnesRZ_explicit_formula_C2
import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv_pair
import Definitions.Def_ConnesRZ_weil_defs
import Definitions.Def_Zeta23_ExplicitFormula
set_option autoImplicit false
open Complex MeasureTheory Set Filter
open scoped ComplexConjugate Convolution
noncomputable section
namespace Zeta23.EF
theorem continuous_tilde {g : ℝ → ℂ} (hg : Continuous g) : Continuous (tilde g) :=
  Complex.continuous_conj.comp (hg.comp continuous_neg)
theorem hasCompactSupport_tilde {g : ℝ → ℂ} (hgs : HasCompactSupport g) :
    HasCompactSupport (tilde g) :=
  (hgs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun w : ℂ => conj w) (map_zero _)
theorem weilTest_contDiff {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hfs : HasCompactSupport f) :
    ContDiff ℝ 2 (weilTest f g) := by
  have := hfs.contDiff_convolution_left (n := 2) (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
    hf (continuous_tilde hg).locallyIntegrable
  simpa [weilTest] using this
theorem weilTest_hasCompactSupport {f g : ℝ → ℂ}
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    HasCompactSupport (weilTest f g) :=
  hfs.convolution _ (hasCompactSupport_tilde hgs)



end Zeta23.EF
namespace ConnesRZArithmetic
lemma conv_starInv_eq_weilTest (f g : ℝ → ℂ) :
    ConnesRZ.conv f (ConnesRZ.starInv g) = Zeta23.EF.weilTest f g := by
  funext t
  rfl
lemma conv_starInv_contDiff_two (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hg : Continuous g) (hfs : HasCompactSupport f) :
    ContDiff ℝ 2 (ConnesRZ.conv f (ConnesRZ.starInv g)) := by
  rw [conv_starInv_eq_weilTest]
  exact Zeta23.EF.weilTest_contDiff hf hg hfs
lemma conv_starInv_hasCompactSupport (f g : ℝ → ℂ)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    HasCompactSupport (ConnesRZ.conv f (ConnesRZ.starInv g)) := by
  rw [conv_starInv_eq_weilTest]
  exact Zeta23.EF.weilTest_hasCompactSupport hfs hgs

end ConnesRZArithmetic
open ConnesRZ
theorem solution (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hg : Continuous g) (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    HasSum (fun ρ : {s : ℂ // IsCriticalZero s} =>
      (zeroMult ρ.1 : ℂ) * (mellinHat f ρ.1 *
        (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1))))
      (weilDistribution (conv f (starInv g))) := by
  have h := explicit_formula_C2 (conv f (starInv g))
    (ConnesRZArithmetic.conv_starInv_contDiff_two f g hf hg hfs)
    (ConnesRZArithmetic.conv_starInv_hasCompactSupport f g hfs hgs)
  simpa only [mellinHat_conv_starInv_pair f g hf.continuous hg hfs hgs] using h
