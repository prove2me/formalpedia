-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.absdisc_rpow_mul_I_eq_ZInfty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:27.946941+00:00
-- url     : https://prove2.me/submissions/1d8cc756-1988-4127-bdcb-c80bcb05ed2f

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_GammaIntegral_gammaIntegral_gaussian_eq

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open Classical
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.GammaIntegral
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) :
    ((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) * I K s = DedekindZeta.ZInfty K s := by
  rw [I, gammaIntegral_gaussian_eq K hs, DedekindZeta.ZInfty, mul_assoc]
end DedekindZeta.GammaIntegral
