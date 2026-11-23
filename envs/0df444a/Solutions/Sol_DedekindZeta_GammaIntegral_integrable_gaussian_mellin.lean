-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.integrable_gaussian_mellin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:20.788801+00:00
-- url     : https://prove2.me/submissions/0df997a5-5f37-4454-a063-deee4b77a06d

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_integrable_mixedGaussian_mellin


set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open Classical
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.GammaIntegral
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) :
    Integrable
      (fun x : mixedEmbedding.mixedSpace K => gaussian K x * (mixedEmbedding.norm x : ℂ) ^ s)
      (mulHaar K) :=
  -- Single source of truth: the whole-space Gaussian-Mellin convergence and its
  -- `withDensity`/product-measure reduction live upstream in `DedekindZeta`
  -- (Statements.lean), stated against the canonical `Theta.mixedGaussian` /
  -- `mixedMulHaar`. The legacy `gaussian` (GammaIntegral:83) and `mulHaar`
  -- (GammaIntegral:72) defs are *definitionally equal* to `Theta.mixedGaussian`
  -- (Theta.lean) and `mixedMulHaar` (Statements.lean) respectively, so the
  -- upstream lemma typechecks here through defeq; we consume it rather than
  -- redoing the ~110-line per-place reduction.
  DedekindZeta.integrable_mixedGaussian_mellin K hs
end DedekindZeta.GammaIntegral
