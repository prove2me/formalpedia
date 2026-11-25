-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.relIndex_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:14.23919+00:00
-- url     : https://prove2.me/submissions/9ed53afb-6263-440b-8c3f-4d00dba837d8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_HDep_mono
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_fg_smul
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_relIndex_prime_le
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
end Bound
section Principal
open scoped Pointwise
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
private theorem relIndex_mul_relIndex_of_le_of_le {G : Type*} [AddGroup G] {H J L : AddSubgroup G} (h1 : H ≤ J) (h2 : J ≤ L) :
    H.relIndex J * J.relIndex L = H.relIndex L := by
  first
  | exact AddSubgroup.relIndex_mul_relIndex H J L h1 h2
  | exact AddSubgroup.relIndex_mul_relIndex h1 h2
end Principal
section General
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
private theorem ideal_mul_smul_submodule (I J : Ideal (𝓞 K)) (N : Submodule (𝓞 K) M) : (I * J) • N = I • J • N := by
  first
  | exact Submodule.mul_smul I J N
  | (rw [← Ideal.smul_eq_mul]; exact Submodule.smul_assoc I J N)
  | exact mul_smul I J N
private theorem relIndex_smul_le_absNorm_pow_of_hDep (n k : ℕ) : ∀ (𝔞 : Ideal (𝓞 K)), Ideal.absNorm 𝔞 ≤ k → 𝔞 ≠ ⊥ →
    ∀ (N : Submodule (𝓞 K) M), N.FG → HDep n N →
    (𝔞 • N).toAddSubgroup.relIndex N.toAddSubgroup ≤ Ideal.absNorm 𝔞 ^ n := by
  induction k with
  | zero =>
    intro 𝔞 hk h𝔞
    exact absurd (Ideal.absNorm_eq_zero_iff.mp (Nat.le_zero.mp hk)) h𝔞
  | succ k ih =>
    intro 𝔞 hk h𝔞 N hN hD
    by_cases htop : 𝔞 = ⊤
    · subst htop
      rw [Submodule.top_smul, AddSubgroup.relIndex_self]
      exact Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔞))
    · obtain ⟨𝔭, h𝔭max, h𝔞𝔭⟩ := Ideal.exists_le_maximal 𝔞 htop
      haveI := h𝔭max
      obtain ⟨𝔟, rfl⟩ := Ideal.dvd_iff_le.mpr h𝔞𝔭
      have h𝔭0 : 𝔭 ≠ ⊥ := by
        rintro rfl
        apply h𝔞
        simp
      have h𝔟0 : 𝔟 ≠ ⊥ := by
        rintro rfl
        apply h𝔞
        simp
      rw [map_mul] at hk ⊢
      have hp2 : 2 ≤ Ideal.absNorm 𝔭 := by
        have h0 : Ideal.absNorm 𝔭 ≠ 0 := by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔭0
        have h1 : Ideal.absNorm 𝔭 ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff]; exact h𝔭max.ne_top
        omega
      have hb0 : Ideal.absNorm 𝔟 ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔟0
      have hbk : Ideal.absNorm 𝔟 ≤ k := by
        have hb1 : 1 ≤ Ideal.absNorm 𝔟 := Nat.pos_of_ne_zero hb0
        nlinarith
      rw [ideal_mul_smul_submodule 𝔭 𝔟 N]
      have hle1 : (𝔭 • 𝔟 • N).toAddSubgroup ≤ (𝔟 • N).toAddSubgroup := fun x hx => Submodule.smul_le_right hx
      have hle2 : (𝔟 • N).toAddSubgroup ≤ N.toAddSubgroup := fun x hx => Submodule.smul_le_right hx
      rw [← relIndex_mul_relIndex_of_le_of_le hle1 hle2, mul_pow]
      exact Nat.mul_le_mul
        (relIndex_prime_le 𝔭 n (𝔟 • N) (fg_smul 𝔟 N hN) (hD.mono Submodule.smul_le_right))
        (ih 𝔟 hbk h𝔟0 N hN hD)
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
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
theorem _root_.solution (n : ℕ) : ∀ (𝔞 : Ideal (𝓞 K)), 𝔞 ≠ ⊥ → ∀ (N : Submodule (𝓞 K) M), N.FG → HDep n N →
    (𝔞 • N).toAddSubgroup.relIndex N.toAddSubgroup ≤ Ideal.absNorm 𝔞 ^ n := by
  intro 𝔞 h𝔞 N hN hD
  exact relIndex_smul_le_absNorm_pow_of_hDep n _ 𝔞 le_rfl h𝔞 N hN hD
end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
