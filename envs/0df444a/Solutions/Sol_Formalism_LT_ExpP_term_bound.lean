-- Prove2me | solution 1 for Formalism.LT.ExpP.term_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:49:18.871783+00:00
-- url     : https://prove2.me/submissions/89c504f5-5388-4b53-904f-974e59fee1a1

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
import Theorems.Thm_Formalism_LT_ExpP_scalar_bound
import Theorems.Thm_Formalism_LT_ExpP_norm_coeff_monomial_le
import Theorems.Thm_Formalism_LT_ExpP_term_eq

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
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.ExpP
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (z : PowerSeries K)
    (hdz : IntegralPS (PowerSeries.derivative K z)) (d : ℕ) (e : Fin 2 →₀ ℕ) :
    ‖coeff d z • MvPowerSeries.coeff e
      (((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) + (p : K) • MvPowerSeries.X 1) ^ d -
        MvPowerSeries.X 0 ^ d)‖ ≤
        ‖(p : K)‖ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hc : ‖(d : K) * coeff d z‖ ≤ 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    have h := hdz n
    rw [PowerSeries.coeff_derivative] at h
    push_cast
    rw [mul_comm]
    exact h
  rw [add_pow, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, add_sub_cancel_right, map_sum,
    Finset.smul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun m hm => ?_
  have hmd : m < d := Finset.mem_range.1 hm
  rw [← map_smul (MvPowerSeries.coeff e), term_eq, map_smul, smul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (norm_coeff_monomial_le _ _ _)).trans
    (scalar_bound hp hp1 _ d m hmd hc)
end Formalism.LT.ExpP
