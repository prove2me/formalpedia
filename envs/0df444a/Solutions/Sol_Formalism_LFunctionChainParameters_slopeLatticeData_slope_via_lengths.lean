-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.slope_via_lengths
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:51:28.417842+00:00
-- url     : https://prove2.me/submissions/6479b889-d9ae-4cc3-88cc-8e191bf401dd

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_finPl_ne_bot
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealPow_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_slope_formula
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_index_finsupp
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_relIndex_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution : SlopeRelationsLength := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX σ τ M N β hM hM0 hN hrk hβ
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  obtain ⟨h1, h2⟩ := slope_formula K V ι b X hX σ τ M N hM hM0 hN hrk
  have hτ := idealPow_ne_zero τ
  have hidx := relIndex_ne_zero b X hX (idealSmul_fg (idealPow τ) hM) hN
    (hrk.trans (rkK_idealSmul hτ M).symm)
  obtain ⟨k, hk, hc⟩ := index_finsupp _ N hidx
  have hd : (rkK M : ℝ) ≠ 0 := by exact_mod_cast (rkK_pos hM0).ne'
  have hq : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  have hkβ : ∀ w, (k w : ℝ) = (rkK M : ℝ) * β w := fun w => by
    rw [← hβ w, hk, ENat.toNat_natCast]
  have hsupp : Function.support β ⊆ (k.support : Set (FinPl K)) := by
    intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    have := hkβ w
    rw [h0, Nat.cast_zero] at this
    exact hw ((mul_eq_zero.1 this.symm).resolve_left hd)
  refine ⟨fun w => by rw [hk]; exact ENat.natCast_ne_top _, k.support.finite_toSet.subset hsupp, h1, ?_⟩
  rw [h2, hc]
  congr 1
  have hne : ∀ w : FinPl K, ((Ideal.absNorm w.1 : ℕ) : ℝ) ≠ 0 := fun w => by
    exact_mod_cast fun h => finPl_ne_bot w (Ideal.absNorm_eq_zero_iff.1 h)
  rw [finsum_eq_sum_of_support_subset (s := k.support)]
  · unfold Finsupp.prod ell
    rw [Nat.cast_prod, Real.log_prod (fun w _ => by push_cast; exact pow_ne_zero _ (hne w)),
      Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Nat.cast_pow, Real.log_pow, hkβ w]
    field_simp
  · intro w hw
    apply hsupp
    rw [Function.mem_support] at hw ⊢
    intro h0
    rw [h0, mul_zero] at hw
    exact hw rfl
end Formalism.LFunctionChainParameters.slopeLatticeData
