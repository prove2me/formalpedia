-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.isWH_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:55.229801+00:00
-- url     : https://prove2.me/submissions/9f40a399-a814-4163-a043-d30573a6250e

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_mapDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution {σ τ M : Type} [AddCommMonoid M] {K : Type} [CommSemiring K] (w : τ → M) (f : σ → τ)
    (hf : Function.Injective f) {F : MvPolynomial σ K} {ν : M} (hF : IsWeightedHomogeneous (w ∘ f) F ν) :
    IsWeightedHomogeneous w (rename f F) ν := by
  intro d hd
  by_contra hne
  apply hd
  apply coeff_rename_eq_zero
  intro u hu
  by_contra hu0
  apply hne
  rw [← hu, weight_mapDomain]
  exact hF hu0
end Formalism.GM.DimensionMonotonicity
