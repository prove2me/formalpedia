-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedGaussian_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:32:55.067496+00:00
-- url     : https://prove2.me/submissions/a97c6400-456e-4852-bc34-109be9055288

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_eq_exp_quadForm

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (y : mixedSpace K) : 0 ≤ Theta.mixedGaussian K y := by
  rw [mixedGaussian_eq_exp_quadForm]; positivity
end DedekindZeta.ConeRadialReduction
