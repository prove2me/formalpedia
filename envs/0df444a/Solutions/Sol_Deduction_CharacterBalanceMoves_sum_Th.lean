-- Prove2me | solution 1 for Deduction.CharacterBalanceMoves.sum_Th
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:56.679927+00:00
-- url     : https://prove2.me/submissions/add2d2af-de9c-4ee0-812e-7a10af7bd3c5

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore
import Theorems.Thm_Deduction_CharacterBalanceMoves_sum_A
import Theorems.Thm_Formalism_D5_phiSet_card


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
theorem _root_.solution (A0 : AddSubgroup H) [Fintype A0] (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H)
    (hT2 : ∀ s ∈ T2, s ∈ A0) (b y : ℝ) (t : H) :
    ∑ u : A0, Th D ell T2 b y u t
      = (((Fintype.card A0 : ℝ) * (b * (delta2 T2 / 2)) : ℝ) : ℂ) * ∑ ψ ∈ PsiA A0, ψ (e1 t) * GPsi D ell ψ y := by
  unfold Th
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hin : ∀ s ∈ T2, ∑ u : A0, ∑ ψ : AddChar (E0 × H) ℂ, ψ (-(e1 (s + (u : H) - t))) * ((b : ℂ) * GPsi D ell ψ y)
      = ((Fintype.card A0 : ℂ) * b) * ∑ ψ ∈ PsiA A0, ψ (e1 t) * GPsi D ell ψ y := by
    intro s hs
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_A A0 _ s t (hT2 s hs), ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ψ _ => by ring
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul, phiSet_card]
  have hH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold delta2
  push_cast
  field_simp
end Deduction.CharacterBalanceMoves
