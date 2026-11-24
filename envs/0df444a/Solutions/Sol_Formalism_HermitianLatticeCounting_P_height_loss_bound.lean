-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.height_loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:04.677932+00:00
-- url     : https://prove2.me/submissions/ccf4b2c4-f134-40bb-9acf-c34fb26c59a5

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_relIndex_ideal_smul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_card_quot_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : QuotCard := by
  intro E _ _ M _ _ _ _ I
  have htf : ∀ a : 𝓞 E, a ≠ 0 → ∀ x : M, a • x = 0 → x = 0 := fun a ha x hx => by
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := M)
      (mem_nonZeroDivisors_of_ne_zero ha)
    exact h (hx.trans (smul_zero a).symm)
  have hidx : ∀ S : Submodule (𝓞 E) M, Nat.card (M ⧸ S) = S.toAddSubgroup.index := fun S => rfl
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    have hb : ((0 : Ideal (𝓞 E)) • (⊤ : Submodule (𝓞 E) M)) = ⊥ := by
      rw [Ideal.zero_eq_bot, Submodule.bot_smul]
    rw [hb, Nat.card_congr (Submodule.quotEquivOfEqBot ⊥ rfl).toEquiv, Ideal.zero_eq_bot, Ideal.absNorm_bot]
    rcases Nat.eq_zero_or_pos (Module.finrank (𝓞 E) M) with h0 | h0
    · rw [h0, pow_zero]
      have htor := Module.finrank_eq_zero_iff_isTorsion.mp h0
      have : Subsingleton M := by
        refine ⟨fun x y => ?_⟩
        have hz : ∀ z : M, z = 0 := by
          intro z
          obtain ⟨a, ha⟩ := @htor z
          exact htf a (nonZeroDivisors.ne_zero a.2) z ha
        rw [hz x, hz y]
      exact Nat.card_unique
    · rw [zero_pow h0.ne']
      have hnt : Nontrivial M := by
        by_contra hn
        rw [not_nontrivial_iff_subsingleton] at hn
        rw [Module.finrank_zero_of_subsingleton] at h0
        omega
      obtain ⟨x, hx⟩ := exists_ne (0 : M)
      have hinj : Function.Injective (fun a : 𝓞 E => a • x) := by
        intro a b hab
        by_contra hne
        have h1 : (a - b) • x = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr hab
        exact hx (htf _ (sub_ne_zero.mpr hne) x h1)
      have : Infinite M := Infinite.of_injective _ hinj
      exact Nat.card_eq_zero_of_infinite
  | h₂ I hI =>
    rw [Ideal.isUnit_iff] at hI
    subst hI
    simp
  | h₃ I P hI hP ih =>
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have hPm : P.IsMaximal := (Ideal.prime_iff_isPrime hP0).mp hP |>.isMaximal hP0
    rw [hidx] at ih ⊢
    have hle : ((P * I) • (⊤ : Submodule (𝓞 E) M)) ≤ I • ⊤ := Submodule.smul_mono_left Ideal.mul_le_right
    rw [← AddSubgroup.relIndex_mul_index (H := ((P * I) • (⊤ : Submodule (𝓞 E) M)).toAddSubgroup)
      (K := (I • (⊤ : Submodule (𝓞 E) M)).toAddSubgroup) hle, ih, mul_comm P I, Submodule.mul_smul,
      DualLatticeIndexBis.relIndex_ideal_smul htf ⊤ (P • ⊤) le_top P I hP0 hI le_rfl]
    have h3 : (P • (⊤ : Submodule (𝓞 E) M)).toAddSubgroup.relIndex
        (⊤ : Submodule (𝓞 E) M).toAddSubgroup = Ideal.absNorm P ^ Module.finrank (𝓞 E) M := by
      rw [Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right, ← hidx, DualLatticeIndexBis.card_quot_prime P,
        Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h3, map_mul, mul_pow, mul_comm]
end Formalism.HermitianLatticeCounting.P
