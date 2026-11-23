-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.mixedEmbedding_norm_eq_absNorm_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:32:03.052933+00:00
-- url     : https://prove2.me/submissions/1eb72f39-153e-4494-9db3-7eec8b5e8ab9

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (a : 𝓞 K) :
    mixedEmbedding.norm (mixedEmbedding K ((a : 𝓞 K) : K))
      = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs,
    Algebra.coe_norm_int, ← norm_eq_norm]
end DedekindZeta.GammaIntegral
