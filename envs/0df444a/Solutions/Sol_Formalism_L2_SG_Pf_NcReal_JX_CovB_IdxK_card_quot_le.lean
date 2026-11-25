-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.card_quot_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:32:29.016501+00:00
-- url     : https://prove2.me/submissions/1cf22d44-6d97-4235-b3e9-8d3e7f4622df

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_exists_prim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField
open scoped nonZeroDivisors
namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
variable {K : Type} [Field K] [NumberField K]
section Bound
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
private theorem absNorm_eq_card_quotient (I : Ideal (𝓞 K)) : Ideal.absNorm I = Nat.card (𝓞 K ⧸ I) := by
  first
  | rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  | simp [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  | rfl
private theorem finite_quotient_of_ne_bot (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : Finite (𝓞 K ⧸ I) := by
  first
  | exact Nat.finite_of_card_ne_zero (by
      rw [← absNorm_eq_card_quotient]; exact fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  | exact Ideal.finiteQuotientOfFreeOfNeBot I hI
private theorem ringOfIntegers_coe_injective : Function.Injective (fun x : 𝓞 K => (x : K)) := by
  first
  | exact RingOfIntegers.coe_injective
  | exact Subtype.val_injective
  | exact FaithfulSMul.algebraMap_injective (𝓞 K) K
  | exact IsFractionRing.injective (𝓞 K) K
private theorem card_le_card_pow_of_not_linearIndependent {k V : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (n : ℕ) (h : ∀ v : Fin (n + 1) → V, LinearIndependent k v → False) :
    Nat.card V ≤ Nat.card k ^ n := by
  classical
  have hd : Module.finrank k V ≤ n := by
    by_contra hlt
    push_neg at hlt
    exact h (Module.finBasis k V ∘ Fin.castLE hlt)
      ((Module.finBasis k V).linearIndependent.comp _ (Fin.castLE_injective hlt))
  rw [Nat.card_congr (Module.finBasis k V).equivFun.toEquiv, Nat.card_fun]
  have hc : Nat.card (Fin (Module.finrank k V)) = Module.finrank k V := by simp
  rw [hc]
  exact Nat.pow_le_pow_right Nat.card_pos hd
end Bound
section Principal
open scoped Pointwise
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
end Principal
section General
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
end General
end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
end
end

set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.NcReal.JX.CovB Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
variable {K : Type} [Field K] [NumberField K]
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
theorem _root_.solution (𝔭 : Ideal (𝓞 K)) [h𝔭 : 𝔭.IsMaximal] (n : ℕ)
    (hdep : ∀ y : Fin (n + 1) → M, ∃ c : Fin (n + 1) → 𝓞 K, c ≠ 0 ∧ ∑ i, c i • y i = 0) :
    Nat.card (M ⧸ 𝔭 • (⊤ : Submodule (𝓞 K) M)) ≤ Nat.card (𝓞 K ⧸ 𝔭) ^ n := by
  classical
  letI : Field (𝓞 K ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have hbot : 𝔭 ≠ ⊥ := by
    first
    | exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField K)
    | exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 NumberField.RingOfIntegers.not_isField
  haveI : Finite (𝓞 K ⧸ 𝔭) := finite_quotient_of_ne_bot 𝔭 hbot
  haveI : Module.Finite (𝓞 K ⧸ 𝔭) (M ⧸ 𝔭 • (⊤ : Submodule (𝓞 K) M)) :=
    Module.Finite.of_restrictScalars_finite (𝓞 K) _ _
  refine card_le_card_pow_of_not_linearIndependent n ?_
  intro v hv
  choose y hy using fun i => Submodule.Quotient.mk_surjective (𝔭 • (⊤ : Submodule (𝓞 K) M)) (v i)
  obtain ⟨c, hc0, hcs⟩ := hdep y
  obtain ⟨t, ht, i₀, hi₀⟩ := exists_prim c hc0 𝔭 h𝔭.ne_top
  choose o ho using ht
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc0 (funext h)
  have hoc : ∀ i, o i * c j = o j * c i := by
    intro i
    apply ringOfIntegers_coe_injective
    first
    | (show (o i : K) * (c j : K) = (o j : K) * (c i : K)
       rw [ho, ho]; ring)
    | (simp only [map_mul]
       rw [ho, ho]; ring)
    | (push_cast
       rw [ho, ho]; ring)
  have hsum0 : ∑ i, o i • y i = 0 := by
    have h1 : c j • ∑ i, o i • y i = o j • ∑ i, c i • y i := by
      rw [Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, smul_smul, mul_comm (c j), hoc i]
    rw [hcs, smul_zero] at h1
    exact (smul_eq_zero.mp h1).resolve_left hj
  have h2 : ∑ i, (Ideal.Quotient.mk 𝔭 (o i)) • v i = 0 := by
    have h3 := congrArg (Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) M))) hsum0
    rw [map_sum, map_zero] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hy i, Submodule.mkQ_apply, Submodule.Quotient.mk_smul]
    first
    | rfl
    | (rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul])
    | exact algebraMap_smul _ _ _
  have h4 := (Fintype.linearIndependent_iff.mp hv) _ h2 i₀
  exact hi₀ (o i₀) (ho i₀) (Ideal.Quotient.eq_zero_iff_mem.mp h4)
end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
