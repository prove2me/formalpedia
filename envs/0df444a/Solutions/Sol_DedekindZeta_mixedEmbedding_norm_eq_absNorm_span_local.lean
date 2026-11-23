-- Prove2me | solution 1 for DedekindZeta.mixedEmbedding_norm_eq_absNorm_span_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:23:41.955896+00:00
-- url     : https://prove2.me/submissions/c2c3aab8-8bf1-4612-a0b8-9285c6be858a

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements

set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
variable {K}
namespace DedekindZeta
theorem _root_.solution (b : 𝓞 K) :
    mixedEmbedding.norm (mixedEmbedding K ((b : 𝓞 K) : K))
      = (Ideal.absNorm (Ideal.span {b}) : ℝ) := by
  rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs,
    Algebra.coe_norm_int, ← mixedEmbedding.norm_eq_norm]
end DedekindZeta
