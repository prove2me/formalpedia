-- Prove2me | solution 1 for Formalism.LT.CongrP.fwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:49:43.984741+00:00
-- url     : https://prove2.me/submissions/cd5d44ad-ea59-4d84-b767-e17232f577cd

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
import Theorems.Thm_Formalism_LT_CongrP_coeff_subst_range
import Theorems.Thm_Formalism_LT_CongrP_mv_coeff_eq
import Theorems.Thm_Formalism_LT_CongrP_integralMv_of
import Theorems.Thm_Formalism_LT_CongrP_divByMv_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.CongrP
theorem _root_.solution (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) [CharZero K]
    {p q : ℕ} {σ : K →+* K} (hS : FunctionalEquationSetting K p q σ) {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hfe : IsFunEqType p q σ f) {α β : PowerSeries K}
    (hα0 : constantCoeff α = 0) (hβ0 : constantCoeff β = 0) (hα : IntegralPS α)
    (hβ : IntegralPS β) {r : ℕ} (hr : 1 ≤ r) (hd : DivBy ((p : K) ^ r) (α - β)) :
    DivBy ((p : K) ^ r) (f.subst α - f.subst β) := by
  intro N
  rw [map_sub, coeff_subst_range f α hα0, coeff_subst_range f β hβ0, ← Finset.sum_sub_distrib]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
  intro n _
  rw [← mul_sub, ← map_sub, norm_mul]
  obtain ⟨k, ⟨m, hm⟩, hk⟩ := h5 K p q σ hS f hf0 hfe n
  obtain ⟨h, hh0, hq⟩ := hS.2.1
  have hp1 : ‖(p : K)‖ ≤ 1 := hS.2.2.1.le
  have hpc := h6 K Unit p hS.1 α β (integralMv_of α hα) (integralMv_of β hβ) r hr
    (divByMv_of _ _ hd) (h * k) m (Finsupp.single () N)
  have hn : n = p ^ (h * k) * m := by rw [hm, hq, pow_mul]
  rw [mv_coeff_eq, ← hn] at hpc
  simp only [Finsupp.single_eq_same, norm_pow] at hpc
  have hkk : ‖(p : K)‖ ^ (r + h * k) ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ ^ r := by
    rw [pow_add, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
    exact pow_le_pow_of_le_one (norm_nonneg _) hp1 (Nat.le_mul_of_pos_left k hh0)
  calc ‖coeff n f‖ * ‖coeff N (α ^ n - β ^ n)‖
      ≤ ‖coeff n f‖ * (‖(p : K)‖ ^ k * ‖(p : K)‖ ^ r) :=
        mul_le_mul_of_nonneg_left (hpc.trans hkk) (norm_nonneg _)
    _ = (‖coeff n f‖ * ‖(p : K)‖ ^ k) * ‖(p : K)‖ ^ r := by ring
    _ ≤ 1 * ‖(p : K)‖ ^ r := mul_le_mul_of_nonneg_right hk (pow_nonneg (norm_nonneg _) _)
    _ = ‖(p : K) ^ r‖ := by rw [one_mul, norm_pow]
end Formalism.LT.CongrP
