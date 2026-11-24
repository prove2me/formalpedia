-- Prove2me | solution 1 for Formalism.L2.Th1.C.CompactOperatorsAlt.coeff_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:22:07.35479+00:00
-- url     : https://prove2.me/submissions/7949d084-f638-478b-88cf-34ac160f02a9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_X_pow


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
open Formalism.L2.Th1.C.CompactOperatorsAlt
variable {K : Type} [Field K] {R : Subring K}
namespace Formalism.L2.Th1.C.CompactOperatorsAlt
theorem _root_.solution {n : ℕ} {g : PowerSeries K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hg0 : constantCoeff g = 1) (hg : ∀ m < n, coeff m g ∈ R) (hgg : coeff n (g * g) ∈ R) :
    coeff n g ∈ R := by
  have h1 : IntPS R (1 : PowerSeries K) := by simpa using USideA.intPS_X_pow (R := R) (K := K) 0
  have hh0 : coeff 0 (g - 1) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, hg0, map_one, sub_self]
  have hh : ∀ m < n, coeff m (g - 1) ∈ R := fun m hm => by
    rw [map_sub]; exact R.sub_mem (hg m hm) (h1 m)
  have hid : coeff n (g - 1) = (2 : K)⁻¹ * (coeff n (g * g) - coeff n (1 : PowerSeries K)
      - coeff n ((g - 1) * (g - 1))) := by
    have : g * g - 1 - (g - 1) * (g - 1) = (g - 1) + (g - 1) := by ring
    rw [← map_sub, ← map_sub, this, map_add]
    field_simp
    ring
  have hk : coeff n (g - 1) ∈ R := by
    rw [hid, PowerSeries.coeff_mul n (g - 1)]
    refine R.mul_mem h2 (R.sub_mem (R.sub_mem hgg (h1 n)) (Subring.sum_mem _ fun p hp => ?_))
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    by_cases hp1 : p.1 = 0
    · rw [hp1, hh0, zero_mul]; exact R.zero_mem
    by_cases hp2 : p.2 = 0
    · rw [hp2, hh0, mul_zero]; exact R.zero_mem
    exact R.mul_mem (hh _ (by omega)) (hh _ (by omega))
  have : g = (g - 1) + 1 := by ring
  rw [this, map_add]
  exact R.add_mem hk (h1 n)
end Formalism.L2.Th1.C.CompactOperatorsAlt
