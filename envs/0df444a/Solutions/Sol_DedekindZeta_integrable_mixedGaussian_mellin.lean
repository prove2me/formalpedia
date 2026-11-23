-- Prove2me | solution 1 for DedekindZeta.integrable_mixedGaussian_mellin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:31:13.109819+00:00
-- url     : https://prove2.me/submissions/af97e543-8130-4a7f-affd-91fd13ec726d

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_integrable_real_gaussian_mul_abs_rpow
import Theorems.Thm_DedekindZeta_integrable_complexPlace_gaussian_rpow
import Theorems.Thm_DedekindZeta_integrable_mixedGaussian_mellin_of_perPlace

set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
open MeasureTheory NumberField.mixedEmbedding
namespace DedekindZeta
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.Integrable
      (fun x : mixedEmbedding.mixedSpace K =>
        (Theta.mixedGaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedMulHaar K) :=
  integrable_mixedGaussian_mellin_of_perPlace K hs
    (integrable_real_gaussian_mul_abs_rpow hs)
    (integrable_complexPlace_gaussian_rpow hs)
end DedekindZeta
