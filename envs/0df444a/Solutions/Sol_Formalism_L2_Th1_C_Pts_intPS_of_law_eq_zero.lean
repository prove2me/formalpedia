-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.intPS_of_law_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:22:07.175122+00:00
-- url     : https://prove2.me/submissions/13ec9563-e532-469b-a6e2-c1090d7ef1d1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intMv_X
import Theorems.Thm_Formalism_L2_Th1_C_Pts_coeff_substMv_two
import Theorems.Thm_Formalism_L2_Th1_C_Pts_coeff_pow_mem

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Pts
open IntegralMvPolynomialLemmas
variable {K : Type} [Field K] {σ : Type} {R : Subring K} {l linv : PowerSeries K}
namespace Formalism.L2.Th1.C.Pts
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : IntMv R F)
    (hF0 : ∀ d : Fin 2 →₀ ℕ, d 0 = 0 → MvPowerSeries.coeff d F =
      MvPowerSeries.coeff d (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))
    {i : PowerSeries K} (hi : PowerSeries.constantCoeff i = 0)
    (hz : MvPowerSeries.subst (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) F = 0) :
    IntPS R i := by
  have ha : ∀ s : Fin 2, MvPowerSeries.constantCoeff
      ((![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) s) = 0 := by
    intro s
    fin_cases s
    · exact PowerSeries.constantCoeff_X
    · exact hi
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hi' : i = - MvPowerSeries.subst (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K)
      (F - MvPowerSeries.X (1 : Fin 2)) := by
    rw [MvPowerSeries.subst_sub hs, hz, MvPowerSeries.subst_X hs, zero_sub, neg_neg]
    rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc : PowerSeries.coeff n i = - MvPowerSeries.coeff (Finsupp.single () n)
        (MvPowerSeries.subst (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K)
          (F - MvPowerSeries.X (1 : Fin 2))) := by
      conv_lhs => rw [hi']
      exact map_neg _ _
    rw [hc, coeff_substMv_two _ ha]
    refine R.neg_mem (finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun d => ?_)
    by_cases h0 : d 0 = 0
    · rw [map_sub, hF0 d h0, sub_self, zero_mul]
      exact R.zero_mem
    · refine R.mul_mem ?_ ?_
      · rw [map_sub]
        exact R.sub_mem (hF d) (intMv_X 1 d)
      · have e1 : MvPowerSeries.coeff (Finsupp.single () n)
            ((![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) 0 ^ d 0 *
              (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) 1 ^ d 1) =
            if d 0 ≤ n then PowerSeries.coeff (n - d 0) (i ^ d 1) else 0 :=
          PowerSeries.coeff_X_pow_mul' (i ^ d 1) (d 0) n
        rw [e1]
        split_ifs with hle
        · exact coeff_pow_mem ih (d 1) _ (by omega)
        · exact R.zero_mem
end Formalism.L2.Th1.C.Pts
