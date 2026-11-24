-- Prove2me | solution 1 for Formalism.LIFT.wBTail_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:47:57.937392+00:00
-- url     : https://prove2.me/submissions/8aa05550-b6bd-4111-92c7-b3deed19986d

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_Graded
import Theorems.Thm_Formalism_LIFT_GradedDegree_X_pow_inj
import Theorems.Thm_Formalism_LIFT_GradedDegree_aeval_mem
import Theorems.Thm_Formalism_LIFT_GradedDegree_hom_aeval
import Theorems.Thm_Formalism_LIFT_GradedDegree_graded_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LIFT
open GradedDegree
namespace Formalism.LIFT
theorem _root_.solution (hG : GradedStep) (hL : LagrangeIdealCyc) : WBTail := by
  intro ℓ _ A _ _ B M D₁ D₂ _ _ _ _ _ _ _ _ W₁ W₂ f s a hs hs2 hv hX n hn
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp (hL ℓ B.u s hs hs2 hv a)
  let S : D₂ → Prop := fun y => ∃ m ∈ W₁.N, y = f.f (B.X ^ a • m)
  have hadd : ∀ x y, S x → S y → S (x + y) := by
    rintro x y ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m + m', W₁.N.add_mem hm hm', by rw [smul_add, map_add]⟩
  have hsmul : ∀ (c : ℤ_[ℓ]) x, S x → S (c • x) := by
    rintro c x ⟨m, hm, rfl⟩
    exact ⟨c • m, Submodule.smul_of_tower_mem _ _ hm,
      by rw [smul_comm (B.X ^ a) c m]; exact (LinearMap.map_smul_of_tower f.f c _).symm⟩
  have hγS : ∀ x, S x → S (W₂.γ x) := by
    rintro x ⟨m, hm, rfl⟩
    obtain ⟨m', hm', hg⟩ := hG ℓ A B M D₁ W₁ a m hm
    refine ⟨((B.u : ℤ_[ℓ]) ^ a) • m + B.X • m',
      W₁.N.add_mem (Submodule.smul_of_tower_mem _ _ hm) (W₁.N.smul_mem _ hm'), ?_⟩
    have e : W₁.γ (B.X ^ a • m) = ((B.u : ℤ_[ℓ]) ^ a) • (B.X ^ a • m) + B.X ^ (a + 1) • m' := by
      rw [← hg]; abel
    rw [← f.γ_comm, e, smul_add, smul_comm (B.X ^ a) ((B.u : ℤ_[ℓ]) ^ a) m, ← mul_smul, ← pow_succ]
  obtain ⟨m, hm, hfm⟩ := hX n hn
  have hP₁ : S (Polynomial.aeval W₂.γ
      (∏ i ∈ Finset.range a, (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ i))) (B.X ^ a • n)) := by
    obtain ⟨m₁, hm₁, h1⟩ := graded_prod hG W₁ 0 a (Nat.zero_le a) m hm
    rw [← Finset.range_eq_Ico, pow_zero, one_smul] at h1
    exact ⟨m₁, hm₁, by rw [← hfm, ← hom_aeval, h1]⟩
  have hP₂ : S (Polynomial.aeval W₂.γ
      (∏ i ∈ Finset.Ico a (2 * a), (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ i)))
        (B.X ^ a • n)) := by
    obtain ⟨n₂, hn₂, h2⟩ := graded_prod hG W₂ a (2 * a) (by omega) n hn
    obtain ⟨m₂, hm₂, hfm₂⟩ := hX n₂ hn₂
    exact ⟨m₂, hm₂, by rw [h2, LinearMap.map_smul, hfm₂, ← mul_smul, ← pow_add, two_mul]⟩
  have key : S (Polynomial.aeval W₂.γ (Polynomial.C ((ℓ : ℤ_[ℓ]) ^
      (2 * a * s + padicValNat ℓ (2 * a).factorial))) (B.X ^ a • n)) := by
    rw [← hαβ, map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply]
    exact hadd _ _ (aeval_mem W₂.γ S hadd hsmul hγS α _ hP₁)
      (aeval_mem W₂.γ S hadd hsmul hγS β _ hP₂)
  rw [Polynomial.aeval_C, Module.algebraMap_end_apply] at key
  obtain ⟨m₃, hm₃, h3⟩ := key
  refine ⟨m₃, hm₃, ?_⟩
  have h0 := X_pow_inj W₂ a (f.f m₃ - ((ℓ : ℤ_[ℓ]) ^ (2 * a * s + padicValNat ℓ (2 * a).factorial)) • n)
    (by rw [smul_sub, ← LinearMap.map_smul, smul_comm (B.X ^ a), ← h3, sub_self])
  exact sub_eq_zero.mp h0
end Formalism.LIFT
