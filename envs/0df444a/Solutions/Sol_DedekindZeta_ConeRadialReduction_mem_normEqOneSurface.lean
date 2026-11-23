-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:26.720769+00:00
-- url     : https://prove2.me/submissions/65486c62-090e-4b19-be09-326efb95de94

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
theorem _root_.solution {x : mixedSpace K} :
    x ∈ normEqOneSurface K ↔
      x ∈ mixedEmbedding.fundamentalCone K ∧ mixedEmbedding.norm x = 1 :=
  Set.mem_sep_iff
end DedekindZeta.ConeRadialReduction
