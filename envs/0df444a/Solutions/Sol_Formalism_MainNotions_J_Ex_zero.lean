-- Prove2me | solution 1 for Formalism.MainNotions.J.Ex_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:42:48.559248+00:00
-- url     : https://prove2.me/submissions/5655f3b6-1426-4649-9e73-a21edd4d3872

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
import Theorems.Thm_Formalism_MainNotions_J_coeff_pow_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.J
open MvPowerSeries
section AlgebraTools
variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]
private theorem powerSeries_hasSubst_of_constantCoeff_eq_zero {τ : Type} {f : MvPowerSeries τ R} (hf : constantCoeff f = 0) :
    PowerSeries.HasSubst f := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero hf
  | (show IsNilpotent _; rw [hf]; exact IsNilpotent.zero)
end AlgebraTools
section Exp
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
private theorem coeff_Ex_eq_sum_inv_factorial_coeff_pow {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) (n : ι →₀ ℕ) :
    coeff n (Ex f) =
      ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K))⁻¹ * coeff n (f ^ k) := by
  unfold Ex
  rw [PowerSeries.coeff_subst (powerSeries_hasSubst_of_constantCoeff_eq_zero hf)]
  have key : ∀ k, k ∉ Finset.range (n.degree + 1) →
      PowerSeries.coeff k (PowerSeries.exp K) • coeff n (f ^ k) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [coeff_pow_zero hf k n (by omega), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n.degree + 1))
    (fun k hk => by
      by_contra h
      exact hk (key k h))]
  apply Finset.sum_congr rfl
  intro k _
  simp [PowerSeries.coeff_exp, smul_eq_mul]
end Exp
section Int
variable {ι κ : Type} {K : Type} [Field K]
end Int
end Formalism.MainNotions.J
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
namespace Formalism.MainNotions.J
theorem _root_.solution : Ex (0 : MvPowerSeries ι K) = 1 := by
  ext n
  rw [coeff_Ex_eq_sum_inv_factorial_coeff_pow (f := (0 : MvPowerSeries ι K)) (by simp), Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [zero_pow hk, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
end Formalism.MainNotions.J
