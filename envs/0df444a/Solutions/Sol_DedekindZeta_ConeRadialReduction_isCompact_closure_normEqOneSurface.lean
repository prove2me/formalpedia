-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.isCompact_closure_normEqOneSurface
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:34:09.674992+00:00
-- url     : https://prove2.me/submissions/7943e7e6-fb40-4c43-a608-91a0b72d5196

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
theorem _root_.solution : IsCompact (closure (normEqOneSurface K)) := by
  classical
  refine Bornology.IsBounded.isCompact_closure ?_
  exact (fundamentalCone.isBounded_normLeOne K).subset fun x hx => ⟨hx.1, hx.2.le⟩
end DedekindZeta.ConeRadialReduction
