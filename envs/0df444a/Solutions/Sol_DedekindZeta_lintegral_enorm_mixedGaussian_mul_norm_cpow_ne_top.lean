-- Prove2me | solution 1 for DedekindZeta.lintegral_enorm_mixedGaussian_mul_norm_cpow_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:35:01.87685+00:00
-- url     : https://prove2.me/submissions/f3951a0a-bf5a-4ff5-82ea-c9c382e777ea

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_integrable_mixedGaussian_mellin

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
    {t : ℂ} (ht : 1 < t.re) :
    ∫⁻ x, ‖(Theta.mixedGaussian K x : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K) ≠ ∞ := by
  -- `1 < Re t ⇒ 0 < Re t`, the convergence threshold for whole-space
  -- integrability; finiteness of `∫⁻ ‖·‖ₑ` is exactly `HasFiniteIntegral`.
  have ht0 : (0 : ℝ) < t.re := lt_trans one_pos ht
  exact (integrable_mixedGaussian_mellin K ht0).hasFiniteIntegral.ne
end DedekindZeta
