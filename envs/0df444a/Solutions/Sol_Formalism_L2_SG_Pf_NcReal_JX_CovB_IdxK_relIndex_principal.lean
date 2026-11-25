-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.relIndex_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:32:33.339996+00:00
-- url     : https://prove2.me/submissions/b7dccf4a-c24b-4094-abd8-50fbee2a997d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_smul_toAddSubgroup
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_smul_inj
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_relIndex_smul_ne_zero
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
end Bound
section Principal
open scoped Pointwise
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
private theorem card_quotient_eq_index {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) : Nat.card (N ⧸ S) = S.toAddSubgroup.index := by
  first
  | rfl
  | exact (Submodule.cardQuot_apply S).symm
private theorem absNorm_eq_index_dual_family_counting (I : Ideal (𝓞 K)) : Ideal.absNorm I = I.toAddSubgroup.index := by
  rw [absNorm_eq_card_quotient, card_quotient_eq_index]
private theorem relIndex_mul_relIndex_of_le_of_le {G : Type*} [AddGroup G] {H J L : AddSubgroup G} (h1 : H ≤ J) (h2 : J ≤ L) :
    H.relIndex J * J.relIndex L = H.relIndex L := by
  first
  | exact AddSubgroup.relIndex_mul_relIndex H J L h1 h2
  | exact AddSubgroup.relIndex_mul_relIndex h1 h2
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
open scoped Pointwise
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
theorem _root_.solution (N : Submodule (𝓞 K) M) (hN : N.FG) (n : ℕ) (ι : (Fin n → 𝓞 K) →ₗ[𝓞 K] M)
    (hι : Function.Injective ι) (hιN : LinearMap.range ι ≤ N) (d : 𝓞 K) (hd : d ≠ 0)
    (hdN : Ideal.span {d} • N ≤ LinearMap.range ι) (π : 𝓞 K) (hπ : π ≠ 0) :
    (Ideal.span {π} • N).toAddSubgroup.relIndex N.toAddSubgroup = (Algebra.norm ℤ π).natAbs ^ n := by
  classical
  have hCB : (LinearMap.range ι).toAddSubgroup ≤ N.toAddSubgroup := fun x hx => hιN hx
  have hDC : (Ideal.span {π} • LinearMap.range ι).toAddSubgroup ≤ (LinearMap.range ι).toAddSubgroup :=
    fun x hx => Submodule.smul_le_right hx
  have hDA : (Ideal.span {π} • LinearMap.range ι).toAddSubgroup ≤ (Ideal.span {π} • N).toAddSubgroup := by
    intro x hx
    first
    | exact Submodule.smul_mono le_rfl hιN hx
    | exact Submodule.smul_mono_right _ hιN hx
    | exact Submodule.smul_mono_right hιN hx
  have hAB : (Ideal.span {π} • N).toAddSubgroup ≤ N.toAddSubgroup := fun x hx => Submodule.smul_le_right hx
  have e1 := relIndex_mul_relIndex_of_le_of_le hDC hCB
  have e2 := relIndex_mul_relIndex_of_le_of_le hDA hAB
  have e3 : (Ideal.span {π} • LinearMap.range ι).toAddSubgroup.relIndex (Ideal.span {π} • N).toAddSubgroup =
      (LinearMap.range ι).toAddSubgroup.relIndex N.toAddSubgroup := by
    rw [smul_toAddSubgroup π (LinearMap.range ι), smul_toAddSubgroup π N,
      ← AddSubgroup.relIndex_comap]
    first
    | rw [AddSubgroup.comap_map_eq_self_of_injective (smul_inj π hπ)]
    | (congr 1
       ext x
       rw [AddSubgroup.mem_comap, AddSubgroup.mem_map]
       constructor
       · rintro ⟨y, hy, hyx⟩
         rwa [← smul_inj π hπ hyx]
       · intro hx
         exact ⟨x, hx, rfl⟩)
  have hCB0 : (LinearMap.range ι).toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 := by
    have hdC : (Ideal.span {d} • N).toAddSubgroup ≤ (LinearMap.range ι).toAddSubgroup := fun x hx => hdN hx
    have e4 := relIndex_mul_relIndex_of_le_of_le hdC hCB
    intro h0
    rw [h0, mul_zero] at e4
    exact relIndex_smul_ne_zero N hN d hd e4.symm
  have hAB_eq : (Ideal.span {π} • N).toAddSubgroup.relIndex N.toAddSubgroup =
      (Ideal.span {π} • LinearMap.range ι).toAddSubgroup.relIndex (LinearMap.range ι).toAddSubgroup := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hCB0)
    rw [e1, ← e2, e3, mul_comm]
  rw [hAB_eq]
  have hmap : AddSubgroup.map ι.toAddMonoidHom ⊤ = (LinearMap.range ι).toAddSubgroup := by
    ext x
    simp [LinearMap.mem_range]
  have hcomap : AddSubgroup.comap ι.toAddMonoidHom (Ideal.span {π} • LinearMap.range ι).toAddSubgroup =
      AddSubgroup.pi Set.univ (fun _ : Fin n => (Ideal.span {π}).toAddSubgroup) := by
    ext x
    show (ι x ∈ Ideal.span {π} • LinearMap.range ι) ↔ ∀ i ∈ (Set.univ : Set (Fin n)), x i ∈ Ideal.span {π}
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, hz1, hz⟩ i -
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hz1
      have hyx : π • y = x := hι (by rw [map_smul]; exact hz)
      rw [← hyx, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
    · intro hx
      choose y hy using fun i => Ideal.mem_span_singleton'.mp (hx i (Set.mem_univ i))
      refine ⟨ι y, LinearMap.mem_range_self ι y, ?_⟩
      rw [← map_smul]
      congr 1
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm]
      exact hy i
  rw [← hmap, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, hcomap, AddSubgroup.index_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← absNorm_eq_index_dual_family_counting, Ideal.absNorm_span_singleton]
end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
