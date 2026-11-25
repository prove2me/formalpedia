-- Prove2me | solution 1 for DiscrNeWork.eisG_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:21:07.015974+00:00
-- url     : https://prove2.me/submissions/297b8bfa-5dda-46ca-a8db-ba54a385aa0f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscLat
import Theorems.Thm_DiscrNeWork_toLat_bij

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ModularForm EisensteinSeries UpperHalfPlane
noncomputable section
open DiscrNeWork
namespace DiscrNeWork
theorem _root_.solution (a : ℂ) (ha : a ≠ 0) (τ : ℍ) (k : ℕ) (hk : 1 ≤ k) :
    PI.eisG (PI.lat2 a (a * τ)) k =
      (a ^ (2 * k))⁻¹ * ∑' v : Fin 2 → ℤ, eisSummand ((2 * k : ℕ) : ℤ) v τ := by
  have hk2 : 2 * k ≠ 0 := by omega
  let e := Equiv.ofBijective _ (toLat_bij a ha τ)
  have hterm : ∀ v : nz, 1 / ((e v : ℂ)) ^ (2 * k) =
      (a ^ (2 * k))⁻¹ * eisSummand ((2 * k : ℕ) : ℤ) v.1 τ := by
    intro v
    have hX : eisSummand ((2 * k : ℕ) : ℤ) v.1 τ =
        1 / ((v.1 0 : ℂ) * (τ : ℂ) + (v.1 1 : ℂ)) ^ (2 * k) := by
      first
        | ((simp only [eisSummand, zpow_neg, zpow_natCast, one_div]) <;> rfl)
        | (simp [eisSummand, zpow_natCast, one_div])
        | (rw [eisSummand, zpow_neg, zpow_natCast, one_div])
        | (unfold eisSummand; done)
    show 1 / (a * ((v.1 0 : ℂ) * (τ : ℂ) + (v.1 1 : ℂ))) ^ (2 * k) = _
    rw [hX]
    first
      | (rw [mul_pow, one_div, one_div, mul_inv])
      | ring
  have hsupp : Function.support (fun v : Fin 2 → ℤ => eisSummand ((2 * k : ℕ) : ℤ) v τ) ⊆
      nz := by
    intro v hv
    show v ≠ 0
    rintro rfl
    apply hv
    first
      | (simp only [eisSummand, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, zpow_neg,
          zpow_natCast, zero_pow hk2, inv_zero, one_div])
      | (simp [eisSummand, hk2])
      | (unfold eisSummand; done)
  calc PI.eisG (PI.lat2 a (a * τ)) k
      = ∑' w : {w : ℂ // w ∈ PI.lat2 a (a * τ) ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k) := rfl
    _ = ∑' v : nz, 1 / ((e v : ℂ)) ^ (2 * k) :=
        (e.tsum_eq (fun w : {w : ℂ // w ∈ PI.lat2 a (a * τ) ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k))).symm
    _ = ∑' v : nz, (a ^ (2 * k))⁻¹ * eisSummand ((2 * k : ℕ) : ℤ) v.1 τ :=
        tsum_congr hterm
    _ = (a ^ (2 * k))⁻¹ * ∑' v : nz, eisSummand ((2 * k : ℕ) : ℤ) v.1 τ :=
        tsum_mul_left
    _ = (a ^ (2 * k))⁻¹ * ∑' v : Fin 2 → ℤ, eisSummand ((2 * k : ℕ) : ℤ) v τ := by
        rw [tsum_subtype_eq_of_support_subset
          (f := fun v : Fin 2 → ℤ => eisSummand ((2 * k : ℕ) : ℤ) v τ) hsupp]
end DiscrNeWork
