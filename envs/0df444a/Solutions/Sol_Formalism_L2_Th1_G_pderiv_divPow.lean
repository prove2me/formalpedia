-- Prove2me | solution 1 for Formalism.L2.Th1.G.pderiv_divPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:37.25764+00:00
-- url     : https://prove2.me/submissions/765b7491-76a5-4824-821c-22b0bd2a1d8d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_add_single
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral mfact_add_single)
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {ι : Type}
namespace Formalism.L2.Th1.G
theorem _root_.solution (a : MvPowerSeries ι K) (i : ι) (m : ℕ) :
    MvPowerSeries.pderiv K i (MvPowerSeries.C (((m + 1).factorial : K)⁻¹) * a ^ (m + 1)) =
      (MvPowerSeries.C ((m.factorial : K)⁻¹) * a ^ m) * MvPowerSeries.pderiv K i a := by
  have hC : ∀ c : K, MvPowerSeries.pderiv K i (MvPowerSeries.C c : MvPowerSeries ι K) = 0 := by
    intro c
    have h := (MvPowerSeries.pderiv K i : Derivation K (MvPowerSeries ι K) (MvPowerSeries ι K)).map_algebraMap c
    simpa [MvPowerSeries.algebraMap_apply] using h
  have hN : ((m + 1 : ℕ) : MvPowerSeries ι K) = MvPowerSeries.C ((m + 1 : ℕ) : K) :=
    (map_natCast _ _).symm
  have h1 : ((m : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  have h2 : ((m.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have key : (((m + 1).factorial : K))⁻¹ * ((m + 1 : ℕ) : K) = ((m.factorial : K))⁻¹ := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [Derivation.leibniz, hC, smul_zero, add_zero, Derivation.leibniz_pow, Nat.add_sub_cancel,
    smul_eq_mul, nsmul_eq_mul, smul_eq_mul, hN, ← key, map_mul]
  ring
end Formalism.L2.Th1.G
