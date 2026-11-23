-- Prove2me | solution 1 for DedekindZeta.tsum_orbit_ofReal_norm_neg_re_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:34:00.347393+00:00
-- url     : https://prove2.me/submissions/913f018c-88d8-4946-b7db-bdb114f37e96

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_summable_orbit_norm_neg_re

set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
namespace DedekindZeta
theorem _root_.solution
    (I : FractionalIdeal (𝓞 K)⁰ K) {t : ℂ} (ht : 1 < t.re) :
    (∑' o : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
        ENNReal.ofReal
          (mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)))
      ≠ ∞ := by
  -- Reduce the `ℝ≥0∞`-valued series to a nonnegative real `Summable` family:
  -- the summands are `ENNReal.ofReal` of `N(σ a₀)^{-Re t} ≥ 0`, so once the real
  -- family is summable, `ENNReal.ofReal_tsum_of_nonneg` collapses the `tsum` to
  -- `ENNReal.ofReal (∑' …)`, which is never `∞`. The genuine `1 < Re t`
  -- convergence input is `summable_orbit_norm_neg_re`.
  have hnn : ∀ o : Quotient (MulAction.orbitRel
        (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
        {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
      0 ≤ mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re) :=
    fun o => Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn (summable_orbit_norm_neg_re K I ht)]
  exact ENNReal.ofReal_ne_top
end DedekindZeta
