-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.subst_Dinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:22:14.822502+00:00
-- url     : https://prove2.me/submissions/1811d6e9-dfc9-42b8-9fc0-f6c8db8215c7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hs1
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_derivative_log
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
namespace Formalism.L2.Th1.C
namespace JetSubstitutionLemmas
section Field
variable {K : Type} [Field K]
private theorem powerSeries_subst_mul {τ : Type} {a : MvPowerSeries τ K} (ha : PowerSeries.HasSubst a)
    (f g : PowerSeries K) :
    PowerSeries.subst a (f * g) = PowerSeries.subst a f * PowerSeries.subst a g := by
  rw [← PowerSeries.coe_substAlgHom ha, map_mul]
variable {R : Subring K}
end Field
section CharZero
variable {K : Type} [Field K] [CharZero K] {R : Subring K}
end CharZero
end JetSubstitutionLemmas
open JetSubstitutionLemmas
namespace JetSubstitutionLemmas
section Norm
variable {K : Type} [Field K]
end Norm
end JetSubstitutionLemmas
namespace JetSubstitutionLemmas
section Adj
variable {K : Type} [Field K] {σ : Type}
end Adj
end JetSubstitutionLemmas
namespace JetSubstitutionLemmas
section Hurwitz
variable {K : Type} [Field K] {R : Subring K}
variable [CharZero K]
end Hurwitz
end JetSubstitutionLemmas
end Formalism.L2.Th1.C
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.JetSubstitutionLemmas
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (g : PowerSeries K) :
    PowerSeries.subst linv (Dinv l g) =
      PowerSeries.derivative K (PowerSeries.subst linv g) := by
  obtain ⟨_, _, hi0, _, hil⟩ := h
  have hsl : PowerSeries.HasSubst linv := hs1 hi0
  have hd : PowerSeries.subst linv (PowerSeries.derivative K l) * PowerSeries.derivative K linv = 1 := by
    rw [← PowerSeries.derivative_subst hsl, hil, PowerSeries.derivative_X]
  have hc : PowerSeries.constantCoeff (PowerSeries.derivative K l) = 1 :=
    cc_derivative_log ⟨by assumption, by assumption, hi0, by assumption, hil⟩
  have hinv : (PowerSeries.derivative K l)⁻¹ * PowerSeries.derivative K l = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hc]; exact one_ne_zero)
  have hsubinv : PowerSeries.subst linv ((PowerSeries.derivative K l)⁻¹) *
      PowerSeries.subst linv (PowerSeries.derivative K l) = 1 := by
    rw [← powerSeries_subst_mul hsl, hinv, ← PowerSeries.coe_substAlgHom hsl, map_one]
  have key : PowerSeries.subst linv ((PowerSeries.derivative K l)⁻¹) = PowerSeries.derivative K linv := by
    calc PowerSeries.subst linv ((PowerSeries.derivative K l)⁻¹)
        = PowerSeries.subst linv ((PowerSeries.derivative K l)⁻¹) *
          (PowerSeries.subst linv (PowerSeries.derivative K l) * PowerSeries.derivative K linv) := by
          rw [hd, mul_one]
      _ = (PowerSeries.subst linv ((PowerSeries.derivative K l)⁻¹) *
          PowerSeries.subst linv (PowerSeries.derivative K l)) * PowerSeries.derivative K linv := by ring
      _ = PowerSeries.derivative K linv := by rw [hsubinv, one_mul]
  unfold Dinv
  rw [powerSeries_subst_mul hsl, key, PowerSeries.derivative_subst hsl, mul_comm]
end Formalism.L2.Th1.C.JetSubstitutionLemmas
