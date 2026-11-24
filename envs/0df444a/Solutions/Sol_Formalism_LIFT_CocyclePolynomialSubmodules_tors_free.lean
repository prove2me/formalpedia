-- Prove2me | solution 1 for Formalism.LIFT.CocyclePolynomialSubmodules.tors_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:57.771906+00:00
-- url     : https://prove2.me/submissions/45607750-5c8b-4e37-b872-03a6caaab295

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_mem_QS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Formalism.LIFT.CocyclePolynomialSubmodules
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℓ A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
  [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D)
namespace Formalism.LIFT.CocyclePolynomialSubmodules
theorem _root_.solution (h4 : ∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N)
    {c : ℤ_[ℓ]} (hc : c ≠ 0) {y : D} (hy : y ∈ QS W) (hcy : c • y ∈ W.N) : y ∈ W.N := by
  have key : ∀ k : ℕ, ∀ z ∈ QS W, ((ℓ : ℤ_[ℓ]) ^ k) • z ∈ W.N → z ∈ W.N := by
    intro k
    induction k with
    | zero =>
      intro z _ hz
      simpa using hz
    | succ k ih =>
      intro z hz hkz
      apply ih z hz
      apply h4 _ ((mem_QS W).mp ((QS W).smul_of_tower_mem _ hz))
      rwa [smul_smul, ← pow_succ']
  obtain ⟨k, u, hcu⟩ : ∃ (k : ℕ) (u : ℤ_[ℓ]ˣ), c = u * (ℓ : ℤ_[ℓ]) ^ k := by
    first
      | exact IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc PadicInt.irreducible_p
      | exact DiscreteValuationRing.eq_unit_mul_pow_irreducible hc PadicInt.irreducible_p
      | exact ⟨_, _, PadicInt.unitCoeff_spec hc⟩
  rw [hcu, mul_comm, mul_smul] at hcy
  have h5 := key k _ ((QS W).smul_of_tower_mem (u : ℤ_[ℓ]) hy) hcy
  have h6 := W.N.smul_of_tower_mem (↑u⁻¹ : ℤ_[ℓ]) h5
  rwa [smul_smul, Units.inv_mul, one_smul] at h6
end Formalism.LIFT.CocyclePolynomialSubmodules
