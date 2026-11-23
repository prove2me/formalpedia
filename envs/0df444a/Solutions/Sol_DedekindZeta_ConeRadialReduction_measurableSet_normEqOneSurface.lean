-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.measurableSet_normEqOneSurface
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:59.327488+00:00
-- url     : https://prove2.me/submissions/7420859f-b85f-4bdf-a015-fd02344afc31

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
theorem _root_.solution :
    MeasurableSet (normEqOneSurface K) :=
  (measurableSet_fundamentalCone K).inter <|
    measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const
end DedekindZeta.ConeRadialReduction
