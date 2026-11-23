-- Prove2me | solution 1 for DedekindZeta.mixedEmbedding_norm_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:30:30.224989+00:00
-- url     : https://prove2.me/submissions/47c1dfac-aab5-4ffa-8cb6-879864b4deb1

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_normAtPlace_inv

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta
theorem _root_.solution (x : mixedEmbedding.mixedSpace K) :
    mixedEmbedding.norm x⁻¹ = (mixedEmbedding.norm x)⁻¹ := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_inv, inv_pow,
    ← Finset.prod_inv_distrib]
end DedekindZeta
