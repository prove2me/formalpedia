-- Prove2me | solution 1 for Formalism.L2.Th1.D.ip_lgF_funEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:35:20.861424+00:00
-- url     : https://prove2.me/submissions/cb14976d-1ca3-4b71-9e37-f496c9401e6b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Lemmata_GeneralBFactUpper_Imports
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Theorems.Thm_Formalism_L2_Th1_D_ip_expand_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_g_zero_relation_holds


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF UnrOK frobVar frobVar_eq_expand)
namespace Formalism.L2.Th1.D
theorem _root_.solution {K : Type} [Field K] {l : ℕ} (hl : 2 ≤ l) (hlK : (l : K) ≠ 0)
    (hq : l ^ 2 ≠ 0) :
    (lgF K l : MvPowerSeries Unit K) -
      (l : K)⁻¹ • MvPowerSeries.expand (l ^ 2) hq (lgF K l : MvPowerSeries Unit K) =
      MvPowerSeries.X () := by
  have hl0 : l ≠ 0 := by omega
  obtain ⟨h1, h2⟩ := Formalism.InvariantFactorPaths.G7.g_zero_relation_holds K l hl hlK
  have e : ∀ f : PowerSeries K, (PowerSeries.subst (PowerSeries.X ^ l : PowerSeries K) f :
      PowerSeries K) = MvPowerSeries.expand l hl0 (f : MvPowerSeries Unit K) :=
    fun f => frobVar_eq_expand hl0 (f : MvPowerSeries Unit K)
  rw [h1, e, e] at h2
  have h3 : MvPowerSeries.expand l hl0 ((MvPowerSeries.C ((l : K)⁻¹) : MvPowerSeries Unit K) *
      MvPowerSeries.expand l hl0 (lgF K l : MvPowerSeries Unit K)) =
      (lgF K l : MvPowerSeries Unit K) - MvPowerSeries.X () := h2
  rw [map_mul, MvPowerSeries.expand_C, ← MvPowerSeries.expand_mul,
    ip_expand_congr (Nat.mul_ne_zero hl0 hl0) hq (pow_two l).symm,
    ← MvPowerSeries.smul_eq_C_mul] at h3
  rw [h3]
  ring
end Formalism.L2.Th1.D
