-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.relIndex_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:13:29.385948+00:00
-- url     : https://prove2.me/submissions/290b43f1-d1b5-437b-adc2-2462016b0123

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_relIndex_principal
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_HDep_mono
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_fg_smul
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_relIndex_le
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
theorem _root_.solution (n : ℕ) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (N : Submodule (𝓞 K) M) (hN : N.FG) (hD : HDep n N)
    (ι : (Fin n → 𝓞 K) →ₗ[𝓞 K] M) (hι : Function.Injective ι) (hιN : LinearMap.range ι ≤ N) (d : 𝓞 K) (hd : d ≠ 0)
    (hdN : Ideal.span {d} • N ≤ LinearMap.range ι) :
    (𝔞 • N).toAddSubgroup.relIndex N.toAddSubgroup = Ideal.absNorm 𝔞 ^ n := by
  obtain ⟨π, hπ𝔞, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  obtain ⟨𝔟, h𝔟⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ𝔞)
  have h𝔟' : Ideal.span {π} = 𝔟 * 𝔞 := by rw [h𝔟, mul_comm]
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.bot_mul, Ideal.span_singleton_eq_bot] at h𝔟'
    exact hπ0 h𝔟'
  have hN' : (𝔞 • N).FG := fg_smul 𝔞 N hN
  have hD' : HDep n (𝔞 • N) := hD.mono Submodule.smul_le_right
  have h1 := relIndex_le n 𝔞 h𝔞 N hN hD
  have h2 := relIndex_le n 𝔟 h𝔟0 (𝔞 • N) hN' hD'
  have hle1 : (𝔟 • 𝔞 • N).toAddSubgroup ≤ (𝔞 • N).toAddSubgroup := fun x hx => Submodule.smul_le_right hx
  have hle2 : (𝔞 • N).toAddSubgroup ≤ N.toAddSubgroup := fun x hx => Submodule.smul_le_right hx
  have hprod : (𝔟 • 𝔞 • N).toAddSubgroup.relIndex (𝔞 • N).toAddSubgroup *
      (𝔞 • N).toAddSubgroup.relIndex N.toAddSubgroup = Ideal.absNorm 𝔟 ^ n * Ideal.absNorm 𝔞 ^ n := by
    rw [relIndex_mul_relIndex_of_le_of_le hle1 hle2, ← ideal_mul_smul_submodule, ← h𝔟',
      relIndex_principal N hN n ι hι hιN d hd hdN π hπ0, ← Ideal.absNorm_span_singleton, h𝔟',
      map_mul, mul_pow]
  have hB : 0 < Ideal.absNorm 𝔟 ^ n :=
    pow_pos (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔟0)) n
  by_contra hne
  have hlt := lt_of_le_of_ne h1 hne
  have hlt2 : (𝔟 • 𝔞 • N).toAddSubgroup.relIndex (𝔞 • N).toAddSubgroup *
      (𝔞 • N).toAddSubgroup.relIndex N.toAddSubgroup < Ideal.absNorm 𝔟 ^ n * Ideal.absNorm 𝔞 ^ n := by
    first
    | exact lt_of_le_of_lt (Nat.mul_le_mul_right _ h2) (Nat.mul_lt_mul_of_pos_left hlt hB)
    | nlinarith
  exact absurd hprod (ne_of_lt hlt2)
end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
