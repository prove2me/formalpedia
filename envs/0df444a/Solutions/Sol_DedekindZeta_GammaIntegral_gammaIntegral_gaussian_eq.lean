-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.gammaIntegral_gaussian_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:33:35.209801+00:00
-- url     : https://prove2.me/submissions/d7c0194a-df38-4e69-b5ea-53ffe84a777a

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_GammaIntegral_gammaReal_eq
import Theorems.Thm_DedekindZeta_GammaIntegral_gammaComplex_eq
import Theorems.Thm_DedekindZeta_GammaIntegral_gammaIntegral_gaussian_factor

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
    gammaIntegral K (fun x => (gaussian K x : ℂ)) s =
      DedekindZeta.LReal s ^ nrRealPlaces K *
        DedekindZeta.LComplex s ^ nrComplexPlaces K := by
  rw [gammaIntegral_gaussian_factor, gammaReal_eq hs, gammaComplex_eq hs]
end DedekindZeta.GammaIntegral
