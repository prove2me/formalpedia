-- Prove2me | solution 1 for Formalism.LIFT.CocyclePolynomialSubmodules.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:09:56.113341+00:00
-- url     : https://prove2.me/submissions/98ba9df3-b232-4700-8bc7-0085d525c182

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_N_le_QS
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_CS_le_QS
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_aeval_mem_N
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_aeval_mem_QS
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_aeval_mem_CS
import Theorems.Thm_P2M_Formalism_LIFT_CocyclePolynomialSubmodules_cocyclePolynomialDivision___mem_fact_66937407d807
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_tors_free

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
theorem _root_.solution (P : Polynomial ℤ_[ℓ]) (cG : ℤ_[ℓ]) (hcG : cG ≠ 0)
    (hU : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ n' ∈ W.N,
      cG • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (M + 1) • n')
    (h1 : ∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (M + 1) • n = B.X ^ (M + 1) • z - W.φ (B.X ^ (M + 1) • z))
    (h2 : ∀ y, W.QInv y → B.X • y ∈ W.N → y ∈ W.N)
    (h3 : ∀ y, W.QInv y → Polynomial.aeval W.γ ((Polynomial.X - 1) * P) y ∈ W.N)
    (h4 : ∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N) :
    W.TorsKilled (P.eval 1 * cG) := by
  rintro ω hω ⟨k, y, z, ⟨hyQ, n, hn, rfl⟩, hk⟩
  obtain ⟨x, hx, n', hn', hxe⟩ := hU n hn
  have hm : B.X ^ (M + 1) • n' ∈ W.N := W.N.smul_mem _ hn'
  have hφm : W.φ (B.X ^ (M + 1) • n') - B.X ^ (M + 1) • n' ∈ W.N :=
    W.N.sub_mem (cocyclePolynomialDivision_φ_mem_fact W hn') hm
  have hXx : B.X • x ∈ W.N := W.N.smul_mem _ hx
  have hYQ : cG • y - (W.φ (B.X • x) - B.X • x) ∈ QS W :=
    (QS W).sub_mem ((QS W).smul_of_tower_mem _ hyQ)
      ((QS W).sub_mem (W.φ_N _ hXx) (N_le_QS W hXx))
  have key : (cG * (ℓ : ℤ_[ℓ]) ^ k) • ω =
      (W.γ (cG • y - (W.φ (B.X • x) - B.X • x)) - (cG • y - (W.φ (B.X • x) - B.X • x))) -
        (W.φ (B.X ^ (M + 1) • n') - B.X ^ (M + 1) • n') := by
    rw [mul_smul, hk, WD.d1]
    have e1 : cG • W.φ (B.X • n) = W.φ (cG • (B.X • n)) := (map_smul _ _ _).symm
    have e2 : cG • W.γ y = W.γ (cG • y) := (map_smul _ _ _).symm
    rw [smul_sub, smul_sub, smul_sub, e1, e2, hxe]
    simp only [map_sub, map_add, W.comm]
    abel
  have hω' : ω ∈ CS W := hω
  set p := Polynomial.aeval W.γ P with hp
  have hpQ : p ω ∈ QS W := aeval_mem_QS W P (CS_le_QS W hω')
  have hγ1 : ∀ Y : D, p (W.γ Y - Y) = Polynomial.aeval W.γ ((Polynomial.X - 1) * P) Y := by
    intro Y
    rw [mul_comm, map_mul, Module.End.mul_apply]
    congr 1
    simp
  have hcp : (cG * (ℓ : ℤ_[ℓ]) ^ k) • p ω ∈ W.N := by
    rw [← map_smul, key, map_sub, hγ1]
    exact W.N.sub_mem (h3 _ hYQ) (aeval_mem_N W P hφm)
  have hn0 : p ω ∈ W.N :=
    tors_free W h4 (mul_ne_zero hcG (pow_ne_zero _ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero))) hpQ hcp
  obtain ⟨y₀, hy₀Q, hy₀e⟩ : p ω ∈ CS W := aeval_mem_CS W P hω'
  have hy₀ : y₀ ∈ W.N := h2 y₀ hy₀Q (hy₀e ▸ hn0)
  obtain ⟨x₀, hx₀, n₀', hn₀', e0⟩ := hU y₀ hy₀
  obtain ⟨z₀, hz₀, e1⟩ := h1 n₀' hn₀'
  obtain ⟨S, hS⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := P) (a := 1)
  have eS : P.eval 1 • ω = p ω - (W.γ (Polynomial.aeval W.γ S ω) - Polynomial.aeval W.γ S ω) := by
    have := congrArg (fun q => Polynomial.aeval W.γ q ω) hS
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_one,
      LinearMap.sub_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.End.one_apply] at this
    rw [← hp] at this
    rw [← this]
    abel
  have hSQ : Polynomial.aeval W.γ S ω ∈ QS W := aeval_mem_QS W S (CS_le_QS W hω')
  refine ⟨cG • (-(Polynomial.aeval W.γ S ω)) + B.X • x₀, B.X ^ (M + 1) • z₀,
    ⟨(QS W).add_mem ((QS W).smul_of_tower_mem _ ((QS W).neg_mem hSQ))
      (N_le_QS W (W.N.smul_mem _ hx₀)),
      ⟨B.X ^ M • z₀, W.N.smul_mem _ hz₀, by rw [pow_succ', mul_smul]⟩⟩, ?_⟩
  rw [mul_comm, mul_smul, eS, hy₀e, smul_sub, e0, e1, WD.d1]
  simp only [map_add, map_neg, map_smul, smul_sub, smul_neg]
  abel
end Formalism.LIFT.CocyclePolynomialSubmodules
