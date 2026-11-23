-- Prove2me | solution 1 for DedekindZeta.tsum_lintegral_enorm_cone_mixedThetaKernel_summand_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:38:23.357577+00:00
-- url     : https://prove2.me/submissions/82b52178-46d8-4307-baca-f2b0c105bd22

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_lintegral_enorm_mixedGaussian_mul_norm_cpow_ne_top
import Theorems.Thm_DedekindZeta_tsum_cone_lintegral_enorm_eq_mul_tsum_orbit
import Theorems.Thm_DedekindZeta_tsum_orbit_ofReal_norm_neg_re_ne_top

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
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) (ht : 1 < t.re) :
    (∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K a.1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K))
      ≠ ∞ := by
  -- Orbit-collapse reduction: the per-element series equals the base
  -- whole-space Gaussian Mellin `enorm`-lintegral `M` times the orbit-indexed
  -- norm-power series. `M ≠ ∞` (helper -3) and the orbit-indexed series is finite
  -- (the genuine `1 < Re t` convergence input), so the product is
  -- finite by `ENNReal.mul_ne_top`.
  rw [tsum_cone_lintegral_enorm_eq_mul_tsum_orbit K I t]
  exact ENNReal.mul_ne_top
    (lintegral_enorm_mixedGaussian_mul_norm_cpow_ne_top K ht)
    (tsum_orbit_ofReal_norm_neg_re_ne_top K I ht)
end DedekindZeta
