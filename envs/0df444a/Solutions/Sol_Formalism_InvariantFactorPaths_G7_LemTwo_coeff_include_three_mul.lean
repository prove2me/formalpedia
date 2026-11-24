-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.coeff_include_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:58.363824+00:00
-- url     : https://prove2.me/submissions/b9286e28-8088-432a-a5af-f7f12fd7166b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_include_three_eq_rename
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_embDomain_two
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
theorem _root_.solution (g : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m j : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (in3 g * MvPowerSeries.X 2 ^ j) =
      if j = m then MvPowerSeries.coeff e g else 0 := by
  classical
  rw [include_three_eq_rename]
  by_cases h : j = m
  · subst h
    rw [if_pos rfl, MvPowerSeries.X_pow_eq, ext3, MvPowerSeries.coeff_add_mul_monomial, mul_one,
      Finsupp.embDomain_eq_mapDomain]
    exact coeff_rename_map_lemma _ (Fin.castSuccEmb (n := 2)).injective g e
  · rw [if_neg h, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    replace hab : a + b = ext3 e m := by simpa using hab
    rw [MvPowerSeries.coeff_X_pow]
    split_ifs with hb
    · rw [mul_one]
      apply MvPowerSeries.coeff_rename_eq_zero
      rintro ⟨u, hu⟩
      simp only at hb hu
      have h2 := congrArg (fun d : Fin 3 →₀ ℕ => d 2) hab
      simp only [Finsupp.add_apply, hb, ext3] at h2
      rw [← hu, Finsupp.mapDomain_notin_range, embDomain_two] at h2
      · simp at h2
        omega
      · rintro ⟨i, hi⟩
        have h1 := congrArg Fin.val hi
        have h3 := i.isLt
        simp at h1
        omega
    · rw [mul_zero]
end Formalism.InvariantFactorPaths.G7.LemTwo
