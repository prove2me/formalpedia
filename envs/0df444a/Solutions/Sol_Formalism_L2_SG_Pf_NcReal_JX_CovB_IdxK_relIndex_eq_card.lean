-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.relIndex_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:32.252737+00:00
-- url     : https://prove2.me/submissions/90d621e9-68ee-4453-8e37-cbc9c96298e3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK
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
private theorem card_quotient_eq_index {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) : Nat.card (N ⧸ S) = S.toAddSubgroup.index := by
  first
  | rfl
  | exact (Submodule.cardQuot_apply S).symm
private theorem mem_smul_univ_iff_coe_mem_smul (I : Ideal (𝓞 K)) (N : Submodule (𝓞 K) M) (x : N) :
    x ∈ I • (⊤ : Submodule (𝓞 K) N) ↔ (x : M) ∈ I • N := by
  first
  | exact Submodule.mem_smul_top_iff N x
  | (have e : Submodule.map N.subtype (I • (⊤ : Submodule (𝓞 K) N)) = I • N := by
       rw [Submodule.map_smul'', Submodule.map_subtype_top]
     rw [← e, Submodule.mem_map]
     constructor
     · intro h
       exact ⟨x, h, rfl⟩
     · rintro ⟨y, hy, hxy⟩
       have hyx : y = x := Subtype.ext hxy
       rwa [hyx] at hy)
private theorem relIndex_smul_eq_card_quotient_smul (I : Ideal (𝓞 K)) (N : Submodule (𝓞 K) M) :
    (I • N).toAddSubgroup.relIndex N.toAddSubgroup = Nat.card (N ⧸ I • (⊤ : Submodule (𝓞 K) N)) := by
  have hmap : AddSubgroup.map N.subtype.toAddMonoidHom ⊤ = N.toAddSubgroup := by
    ext x
    first
    | simp
    | (constructor
       · rintro ⟨y, -, rfl⟩
         exact y.2
       · intro hx
         exact ⟨⟨x, hx⟩, trivial, rfl⟩)
  have hc : AddSubgroup.comap N.subtype.toAddMonoidHom (I • N).toAddSubgroup =
      (I • (⊤ : Submodule (𝓞 K) N)).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, mem_smul_univ_iff_coe_mem_smul]
    first
    | rfl
    | simp
  rw [← hmap, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, hc, card_quotient_eq_index]
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
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
theorem _root_.solution (I : Ideal (𝓞 K)) (N : Submodule (𝓞 K) M) :
    (I • N).toAddSubgroup.relIndex N.toAddSubgroup = Nat.card (N ⧸ I • (⊤ : Submodule (𝓞 K) N)) :=
  relIndex_smul_eq_card_quotient_smul I N
end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
