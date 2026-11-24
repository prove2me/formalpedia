-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.coeff_subst_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:53:25.21353+00:00
-- url     : https://prove2.me/submissions/a02b082e-b4b9-4515-a449-73532cab5ec9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_include_three_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_constantCoeff_law_first_two_of_three
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_include_three_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_fin_two_vector_eq_matrixVecCons
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_pow_high

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemTwo
theorem _root_.solution {f : MvPowerSeries (Fin 2) K} (hf : MvPowerSeries.constantCoeff f = 0)
    (G : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (MvPowerSeries.subst ![in3 f, MvPowerSeries.X 2] G) =
      MvPowerSeries.coeff e (PowerSeries.subst f (sl G m)) := by
  classical
  have ha : MvPowerSeries.HasSubst ![in3 f, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      fin_cases s
      · exact constantCoeff_law_first_two_of_three hf
      · simp)
  have hb : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  rw [MvPowerSeries.coeff_subst ha, PowerSeries.coeff_subst hb]
  have hterm : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff (ext3 e m)
      (d.prod fun s k => (![in3 f, MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) K) s ^ k) =
        if d 1 = m then MvPowerSeries.coeff e (f ^ d 0) else 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [include_three_pow, coeff_include_three_mul]
  simp_rw [hterm]
  rw [finsum_eq_sum_of_support_subset _
      (s := (Finset.range (e.degree + 1)).image (fun i => Finsupp.single (0 : Fin 2) i + Finsupp.single 1 m)),
    finsum_eq_sum_of_support_subset _ (s := Finset.range (e.degree + 1))]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i _
      simp [sl]
    · intro x _ y _ hxy
      have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) hxy
      simpa using this
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact hi (by rw [coeff_pow_high hf (by omega), smul_zero])
  · intro d hd
    rw [Function.mem_support] at hd
    split_ifs at hd with h1
    · simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      refine ⟨d 0, ?_, ?_⟩
      · by_contra hc
        exact hd (by rw [coeff_pow_high hf (by omega), smul_zero])
      · rw [← h1]
        exact (fin_two_vector_eq_matrixVecCons d).symm
    · exact absurd (smul_zero _) hd
end Formalism.InvariantFactorPaths.G7.LemTwo
