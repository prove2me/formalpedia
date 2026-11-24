-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.coeff_swap2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:13.231099+00:00
-- url     : https://prove2.me/submissions/ff61c54a-caf6-4de0-9fe7-c41a77afb9e8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_swap_two_eq_rename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace LemTwo
section Slice
variable {K : Type} [Field K]
private theorem coeff_rename_map_lemma {σ τ : Type} (f : σ → τ) [Filter.TendstoCofinite f]
    (hf : Function.Injective f) (g : MvPowerSeries σ K) (u : σ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.mapDomain f u) (MvPowerSeries.rename f g) = MvPowerSeries.coeff u g := by
  classical
  rw [MvPowerSeries.coeff_rename, Finset.sum_eq_single_of_mem u]
  · simp
  · intro b hb hne
    exfalso
    apply hne
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hb
    exact Finsupp.mapDomain_injective hf hb
end Slice
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Norm
section Top
variable {K : Type} [Field K]
end Top
section Additive
variable {K : Type} [Field K]
end Additive
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Norm
end LemTwo
end Formalism.InvariantFactorPaths.G7
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemTwo
theorem _root_.solution (H : MvPowerSeries (Fin 2) K) (i k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) (swap2 H) =
      MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 i) H := by
  rw [swap_two_eq_rename]
  have hu : Finsupp.mapDomain (⇑(Equiv.swap (0 : Fin 2) 1).toEmbedding)
      (Finsupp.single 0 k + Finsupp.single 1 i) = Finsupp.single 0 i + Finsupp.single 1 k := by
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact add_comm _ _
  rw [← hu, coeff_rename_map_lemma _ (Equiv.swap (0 : Fin 2) 1).toEmbedding.injective]
end Formalism.InvariantFactorPaths.G7.LemTwo
