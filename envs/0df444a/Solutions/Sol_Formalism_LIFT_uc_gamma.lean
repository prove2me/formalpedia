-- Prove2me | solution 1 for Formalism.LIFT.uc_gamma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:32:02.792123+00:00
-- url     : https://prove2.me/submissions/7c4d5570-f68b-4347-8fa3-0204d3fa357d

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
import Theorems.Thm_Formalism_LIFT_uc_bij
import Theorems.Thm_Formalism_LIFT_uc_smul_comm_A

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
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}
variable {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
namespace Formalism.LIFT
theorem _root_.solution (W : WD B M D) {y : D} (hy : W.QInv y) :
    ∃ a, W.QInv a ∧ W.γ y - y = B.X • a := by
  obtain ⟨t, hu, hγQ⟩ := B.γQ
  have hn : B.Q ^ M • y ∈ W.N := hy
  obtain ⟨n', hn', he⟩ := W.γ_N _ hn
  rw [W.γ_smul, map_pow, hγQ, mul_pow] at he
  obtain ⟨w, hw⟩ := (uc_bij W M).2 n'
  have hw' : B.Q ^ M • w = n' := hw
  have h1 : (1 + B.X * t) ^ M • W.γ y - y = B.X • w := by
    apply (uc_bij W M).1
    show B.Q ^ M • ((1 + B.X * t) ^ M • W.γ y - y) = B.Q ^ M • (B.X • w)
    rw [smul_sub, smul_smul, he, ← hw', uc_smul_comm_A]
  obtain ⟨s', hs'⟩ : B.X * t ∣ (1 + B.X * t) ^ M - 1 := by
    have h2 := sub_dvd_pow_sub_pow (1 + B.X * t) 1 M
    rwa [one_pow, add_sub_cancel_left] at h2
  obtain ⟨v, hv⟩ := (hu.pow M).exists_left_inv
  refine ⟨v • w - (v * (t * s')) • y, ?_, ?_⟩
  · unfold WD.QInv
    rw [smul_sub, uc_smul_comm_A, hw', uc_smul_comm_A]
    exact W.N.sub_mem (W.N.smul_mem _ hn') (W.N.smul_mem _ hn)
  · calc W.γ y - y = (v * (1 + B.X * t) ^ M) • W.γ y - (v * (1 + B.X * t) ^ M) • y := by
          rw [hv, one_smul, one_smul]
      _ = v • ((1 + B.X * t) ^ M • W.γ y - y) - v • (((1 + B.X * t) ^ M - 1) • y) := by
          rw [smul_sub, sub_smul, one_smul, smul_sub, smul_smul, smul_smul]
          abel
      _ = v • (B.X • w) - v • ((B.X * (t * s')) • y) := by
          rw [h1, hs', mul_assoc]
      _ = B.X • (v • w - (v * (t * s')) • y) := by
          rw [smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, mul_comm v B.X, mul_left_comm v B.X]
end Formalism.LIFT
