-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.relIndex_prime_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:44:22.180592+00:00
-- url     : https://prove2.me/submissions/b485d7b2-c648-4e0d-b293-f1f8822b16c9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_card_quot_le
import Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_relIndex_eq_card
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
theorem _root_.solution (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal] (n : ℕ) (N : Submodule (𝓞 K) M) (hN : N.FG)
    (hD : HDep n N) : (𝔭 • N).toAddSubgroup.relIndex N.toAddSubgroup ≤ Ideal.absNorm 𝔭 ^ n := by
  haveI : Module.Finite (𝓞 K) N := Module.Finite.iff_fg.mpr hN
  haveI : NoZeroSMulDivisors (𝓞 K) N := ⟨fun {c x} h => by
    have h' : c • (x : M) = 0 := by simpa using congrArg Subtype.val h
    rcases smul_eq_zero.mp h' with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (Subtype.ext h0)⟩
  have hdep : ∀ y : Fin (n + 1) → N, ∃ c : Fin (n + 1) → 𝓞 K, c ≠ 0 ∧ ∑ i, c i • y i = 0 := by
    intro y
    obtain ⟨c, hc, hs⟩ := hD (fun i => (y i : M)) (fun i => (y i).2)
    refine ⟨c, hc, ?_⟩
    apply Subtype.ext
    simpa using hs
  rw [relIndex_eq_card, absNorm_eq_card_quotient]
  exact card_quot_le 𝔭 n hdep
end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
