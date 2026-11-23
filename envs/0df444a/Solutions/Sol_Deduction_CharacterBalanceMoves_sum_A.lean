-- Prove2me | solution 1 for Deduction.CharacterBalanceMoves.sum_A
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:51.610171+00:00
-- url     : https://prove2.me/submissions/326977c0-cf98-4342-94ad-668058356a02

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore
import Theorems.Thm_Deduction_CharacterBalanceMoves_mem_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Deduction.CharacterBalanceMoves
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Deduction.CharacterBalanceMoves
theorem _root_.solution (A0 : AddSubgroup H) [Fintype A0] (ψ : AddChar (E0 × H) ℂ) (s t : H) (hs : s ∈ A0) :
    ∑ u : A0, ψ (-(e1 (s + (u : H) - t))) = if ψ ∈ PsiA A0 then (Fintype.card A0 : ℂ) * ψ (e1 t) else 0 := by
  have hg : ∀ u : A0, (-(e1 (s + (u : H) - t)) : E0 × H) = e1 t + (0, -s) + (0, -(u : H)) := by
    intro u
    ext
    · simp [e1]
    · simp [e1]
    · simp [e1]; abel
  simp_rw [hg, AddChar.map_add_eq_mul]
  rw [← Finset.mul_sum]
  split_ifs with h
  · have h' := (mem_psi A0 ψ).1 h
    rw [h' _ (A0.neg_mem hs), Finset.sum_congr rfl (fun (u : A0) _ => h' _ (A0.neg_mem u.2))]
    simp [mul_comm]
  · let φ : AddChar A0 ℂ := ψ.compAddMonoidHom ((AddMonoidHom.inr E0 H).comp A0.subtype)
    have hφ : ∀ u : A0, φ u = ψ (0, (u : H)) := fun u => rfl
    have hne : φ ≠ 0 := by
      intro h0
      apply h
      rw [mem_psi]
      intro v hv
      rw [← hφ ⟨v, hv⟩, h0, AddChar.zero_apply]
    have h1 := AddChar.sum_eq_zero_iff_ne_zero.2 hne
    have h2 : ∑ u : A0, ψ (0, -(u : H)) = ∑ u : A0, φ u := by
      rw [← Equiv.sum_comp (Equiv.neg A0) φ]
      rfl
    rw [h2, h1, mul_zero]
end Deduction.CharacterBalanceMoves
