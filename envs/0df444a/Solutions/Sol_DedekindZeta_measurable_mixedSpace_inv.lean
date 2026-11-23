-- Prove2me | solution 1 for DedekindZeta.measurable_mixedSpace_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:27:44.737805+00:00
-- url     : https://prove2.me/submissions/cbb8fbe7-56f7-454f-b1fe-5a7cb097f3ba

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral

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
theorem _root_.solution :
    Measurable (fun x : mixedEmbedding.mixedSpace K => x⁻¹) :=
  measurable_fst.inv.prodMk measurable_snd.inv
end DedekindZeta
