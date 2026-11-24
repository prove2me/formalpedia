-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.coeff_law_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:33:43.447298+00:00
-- url     : https://prove2.me/submissions/275cbf77-f0d6-47c1-88a0-7d38085ced82

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_zero_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fadd_eq_substMv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_coeff_substMv_two

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
theorem _root_.solution (h : IsLogPair l linv) (d : Fin 2 →₀ ℕ) (hd : d 0 = 0) :
    MvPowerSeries.coeff d
        (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) =
      MvPowerSeries.coeff d (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) := by
  classical
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have ha : ∀ s : Fin 2, MvPowerSeries.constantCoeff
      ((![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) s) = 0 := by
    intro s
    fin_cases s
    · exact map_zero _
    · exact hX
  have key := coeff_substMv_two
    (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) ha
    (Finsupp.single () (d 1))
  rw [← fadd_eq_substMv h (map_zero _) hX, zero_fadd h hX, finsum_eq_single _ d] at key
  · have e1 : MvPowerSeries.coeff (Finsupp.single () (d 1))
        ((![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 0 ^ d 0 *
          (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 1 ^ d 1) = 1 := by
      rw [hd, pow_zero, one_mul]
      exact PowerSeries.coeff_X_pow_self (d 1)
    rw [e1, mul_one] at key
    rw [← key, MvPowerSeries.coeff_X]
    have e2 : MvPowerSeries.coeff (Finsupp.single () (d 1)) (PowerSeries.X : MvPowerSeries Unit K) =
        if d 1 = 1 then 1 else 0 := PowerSeries.coeff_X (d 1)
    rw [e2]
    congr 1
    apply propext
    constructor
    · intro h1
      ext s
      fin_cases s
      · simpa using hd
      · simpa using h1
    · intro h1
      rw [h1]
      simp
  · intro d' hd'
    by_cases h0 : d' 0 = 0
    · have h1 : d' 1 ≠ d 1 := by
        intro h1
        apply hd'
        ext s
        fin_cases s
        · simpa [hd] using h0
        · simpa using h1
      have e1 : MvPowerSeries.coeff (Finsupp.single () (d 1))
          ((![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 0 ^ d' 0 *
            (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 1 ^ d' 1) = 0 := by
        rw [h0, pow_zero, one_mul]
        have := PowerSeries.coeff_X_pow (R := K) (d 1) (d' 1)
        rw [if_neg (fun hh => h1 hh.symm)] at this
        exact this
      rw [e1, mul_zero]
    · have : (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 0 ^ d' 0 = 0 := zero_pow h0
      rw [this, zero_mul, map_zero, mul_zero]
end Formalism.L2.Th1.C.Pts
