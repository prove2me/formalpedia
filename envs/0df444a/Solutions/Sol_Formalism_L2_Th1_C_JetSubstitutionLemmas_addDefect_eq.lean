-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.addDefect_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:33:31.502361+00:00
-- url     : https://prove2.me/submissions/48c9d3f6-c2cb-41a6-a497-4aaf8f3eb41d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_subst_zero
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_subst_subst_linv
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_subst_ph_linv

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
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (ph : PowerSeries K) (a b : K) :
    be0 l linv ph (fmul l linv a (MvPowerSeries.X (0 : Fin 2)))
        (fmul l linv b (MvPowerSeries.X (1 : Fin 2))) =
      Q l (PowerSeries.subst linv ph) a b - Q l (PowerSeries.subst linv ph) a 0 -
        Q l (PowerSeries.subst linv ph) 0 b := by
  have hX : ∀ j : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  have hv : ∀ (j : Fin 2) (c : K), MvPowerSeries.constantCoeff
      (MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) l) = 0 := by
    intro j c
    rw [map_mul, cc_subst_zero (hX j) h.1, mul_zero]
  have hsum : MvPowerSeries.constantCoeff
      (MvPowerSeries.C a * PowerSeries.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) l +
        MvPowerSeries.C b * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) l) = 0 := by
    rw [map_add, hv, hv, add_zero]
  unfold be0 fadd fmul Q
  rw [subst_subst_linv h (hv 0 a), subst_subst_linv h (hv 1 b), subst_ph_linv h ph hsum,
    subst_ph_linv h ph (hv 0 a), subst_ph_linv h ph (hv 1 b)]
  simp only [map_zero, zero_mul, add_zero, zero_add]
end Formalism.L2.Th1.C.JetSubstitutionLemmas
