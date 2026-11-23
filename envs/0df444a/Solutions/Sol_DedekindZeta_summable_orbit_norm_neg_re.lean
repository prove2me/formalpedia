-- Prove2me | solution 1 for DedekindZeta.summable_orbit_norm_neg_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:30:33.234514+00:00
-- url     : https://prove2.me/submissions/63a671a3-8b1e-4400-845a-6282f3daed06

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_summable_absNorm_neg_cpow
import Theorems.Thm_DedekindZeta_summable_of_bounded_fiber
import Theorems.Thm_DedekindZeta_exists_orbitIdeal_norm_eq

set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000
namespace DedekindZeta
theorem _root_.solution
    (I : FractionalIdeal (𝓞 K)⁰ K) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun o : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) =>
        mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)) := by
  classical
  -- The genuine convergence content is packaged into two helper lemmas: the
  -- orbit principal-ideal representative with its norm identity and bounded
  -- finite fibres (`exists_orbitIdeal_norm_eq`), and the abstract bounded-fibre
  -- summability comparison (`summable_of_bounded_fiber`).
  obtain ⟨ψ, hval, hfin, hcard⟩ := exists_orbitIdeal_norm_eq K I (t := t)
  -- Summability of the real ideal-norm series `J ↦ 𝔑(J)^{-Re t}` for `1 < Re t`.
  have hh : Summable (fun J : NonzeroIdeal K =>
      (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (-t.re)) := by
    have hc := summable_absNorm_neg_cpow K (s := t) ht
    refine (summable_norm_iff.mpr hc).congr (fun J => ?_)
    have hpos : 0 < Ideal.absNorm (J : Ideal (𝓞 K)) :=
      Nat.pos_of_ne_zero (fun hz => J.2 ((Ideal.absNorm_eq_zero_iff).mp hz))
    rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
  refine summable_of_bounded_fiber
    (c := mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)) ^ t.re)
    (h := fun J : NonzeroIdeal K => (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (-t.re))
    (ψ := ψ) (N := NumberField.Units.torsionOrder K)
    hval ?_ hh ?_ hfin hcard
  · exact Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _
  · exact fun _ => Real.rpow_nonneg (by positivity) _
end DedekindZeta
