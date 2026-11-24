-- Prove2me | solution 1 for Formalism.LT.CoeffP.pow_sub_pow_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:41.251246+00:00
-- url     : https://prove2.me/submissions/d5dca692-7943-42fa-b009-d8b934fcffd2

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mul
import Theorems.Thm_Formalism_LT_CoeffP_Bd_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries
universe u v
namespace Formalism.LT.CoeffP
open Formalism.G
section Ball
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Ball
section Bd
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
private lemma bd_add' {c : ℝ} {F G : MvPowerSeries ι K} (hF : Bd c F) (hG : Bd c G) :
    Bd c (F + G) := by
  intro d
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF d) (hG d))
end Bd
end Formalism.LT.CoeffP
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
namespace Formalism.LT.CoeffP
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) {A B : MvPowerSeries ι K} (hA : Bd 1 A) (hB : Bd 1 B)
    (hD : Bd c (A - B)) (m : ℕ) : Bd c (A ^ m - B ^ m) := by
  induction m with
  | zero =>
    intro d
    simp [hc]
  | succ m ih =>
    have hAm : Bd 1 (A ^ m) := by simpa using Bd.pow hA zero_le_one m
    have e : A ^ (m + 1) - B ^ (m + 1) = A ^ m * (A - B) + (A ^ m - B ^ m) * B := by ring
    rw [e]
    have h1 : Bd c (A ^ m * (A - B)) := by simpa using Bd.mul hAm hD zero_le_one hc
    have h2 : Bd c ((A ^ m - B ^ m) * B) := by simpa using Bd.mul ih hB hc zero_le_one
    exact bd_add' h1 h2
end Formalism.LT.CoeffP
