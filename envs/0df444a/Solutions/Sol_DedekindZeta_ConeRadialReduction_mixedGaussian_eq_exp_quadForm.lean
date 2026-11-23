-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedGaussian_eq_exp_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:28:59.336251+00:00
-- url     : https://prove2.me/submissions/fea64da9-5d54-43d5-8f85-6a5285812b5d

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (y : mixedSpace K) :
    Theta.mixedGaussian K y = Real.exp (-Real.pi * mixedQuadForm K y) := rfl
end DedekindZeta.ConeRadialReduction
