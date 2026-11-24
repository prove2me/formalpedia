-- Prove2me | solution 1 for Formalism.REAL.characteristicIdentity_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:29:59.682953+00:00
-- url     : https://prove2.me/submissions/2554da16-cdce-4e22-8d1c-bc929f8880ea

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
import Theorems.Thm_Formalism_REAL_CharId_on_v
import Theorems.Thm_Formalism_REAL_CharId_P_apply
import Theorems.Thm_Formalism_REAL_CharId_P_commutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : CharId := by
  intro V _ _ n E ν v hE hv x hx a b
  let W : Submodule ℂ V := ⨅ (a : Fin n) (b : Fin n), LinearMap.ker (CharId_P E ν a b)
  have hW : W ∈ {W : Submodule ℂ V | v ∈ W ∧ ∀ a b, ∀ x ∈ W, E a b x ∈ W} := by
    refine ⟨?_, ?_⟩
    · simp only [W, Submodule.mem_iInf, LinearMap.mem_ker]
      intro a b
      rw [CharId_P_apply]
      exact CharId_on_v E hE ν v hv a b
    · intro c d y hy
      simp only [W, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
      intro a b
      have h := LinearMap.congr_fun (CharId_P_commutator E hE ν a b c d) y
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hy a b, map_zero, zero_sub] at h
      split_ifs at h <;> simp_all
  have hxW : x ∈ W := Submodule.mem_sInf.1 hx W hW
  simp only [W, Submodule.mem_iInf, LinearMap.mem_ker] at hxW
  rw [← CharId_P_apply]
  exact hxW a b
end Formalism.REAL
