-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideA.intPS_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:22:12.670079+00:00
-- url     : https://prove2.me/submissions/037727be-a807-4f0a-97e9-bb827017711e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideA

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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.USideA
variable {K : Type} [Field K] {R : Subring K}
namespace Formalism.L2.Th1.C.USideA
theorem _root_.solution {U V : PowerSeries K} (hU : IntPS R U)
    (hU0 : PowerSeries.constantCoeff U = 1) (hUV : U * V = 1) : IntPS R V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h := congrArg (PowerSeries.coeff n) hUV
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at h
    have hmem0 : ((0, n) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
    rw [← Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal n)
      (fun p : ℕ × ℕ => PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V)
      hmem0] at h
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0, one_mul] at h
    have hrest : (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
        PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V) ∈ R := by
      refine R.sum_mem (fun p hp => R.mul_mem (hU _) (ih _ ?_))
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
      by_contra hle
      apply hne
      obtain ⟨a, b⟩ := p
      simp only [Prod.mk.injEq] at hmem hle ⊢
      refine ⟨?_, ?_⟩ <;> omega
    have h' : PowerSeries.coeff n V = (if n = 0 then 1 else 0) -
        ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
          PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V := by
      linear_combination h
    rw [h']
    refine R.sub_mem ?_ hrest
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
end Formalism.L2.Th1.C.USideA
