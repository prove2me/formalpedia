-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.cc_pderiv_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:49:38.677439+00:00
-- url     : https://prove2.me/submissions/2e65732c-671e-477a-9d8a-382a0ce0d28e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_subst
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_subst_zero
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_pderiv_subst


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open JetSubstitutionLemmas
open Formalism.L2.Th1.C.JetSubstitutionLemmas
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {l : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (hl1 : PowerSeries.constantCoeff (PowerSeries.derivative K l) = 1) (ψ : PowerSeries K)
    (α β : K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K 0 (MvPowerSeries.pderiv K 1 (Q l ψ α β))) =
      α * β * PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K ψ)) := by
  have hX : ∀ j : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  have hdv : ∀ (i j : Fin 2) (g : PowerSeries K),
      MvPowerSeries.pderiv K i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) g) =
        PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) (PowerSeries.derivative K g) *
          (Pi.single i (1 : MvPowerSeries (Fin 2) K) : Fin 2 → MvPowerSeries (Fin 2) K) j := by
    intro i j g
    rw [IntegralMvPolynomialLemmas.pderiv_subst g (hX j) i, MvPowerSeries.pderiv_X]
  have hv : ∀ j : Fin 2,
      MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) l) = 0 :=
    fun j => cc_subst_zero (hX j) hl0
  unfold Q
  have hu : MvPowerSeries.constantCoeff (MvPowerSeries.C α * PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) l +
      MvPowerSeries.C β * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) l : MvPowerSeries (Fin 2) K) = 0 := by
    rw [map_add, map_mul, map_mul, hv 0, hv 1]
    simp
  generalize hU : (MvPowerSeries.C α * PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) l +
      MvPowerSeries.C β * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) l : MvPowerSeries (Fin 2) K) = u at hu ⊢
  have hd1 : MvPowerSeries.pderiv K 1 u =
      MvPowerSeries.C β * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)
        (PowerSeries.derivative K l) := by
    rw [← hU, map_add, Derivation.leibniz, Derivation.leibniz, MvPowerSeries.pderiv_C,
      MvPowerSeries.pderiv_C, hdv, hdv]
    simp
  have hd0 : MvPowerSeries.pderiv K 0 u =
      MvPowerSeries.C α * PowerSeries.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)
        (PowerSeries.derivative K l) := by
    rw [← hU, map_add, Derivation.leibniz, Derivation.leibniz, MvPowerSeries.pderiv_C,
      MvPowerSeries.pderiv_C, hdv, hdv]
    simp
  have hd01 : MvPowerSeries.pderiv K 0 (MvPowerSeries.pderiv K 1 u) = 0 := by
    rw [hd1, Derivation.leibniz, MvPowerSeries.pderiv_C, hdv]
    simp
  rw [IntegralMvPolynomialLemmas.pderiv_subst ψ hu 1, Derivation.leibniz, hd01, IntegralMvPolynomialLemmas.pderiv_subst _ hu 0, hd0, hd1]
  simp only [smul_zero, smul_eq_mul, mul_zero, zero_add, map_mul]
  rw [cc_subst hu, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_C, cc_subst (hX 0),
    cc_subst (hX 1), hl1]
  ring
end Formalism.L2.Th1.C.JetSubstitutionLemmas
