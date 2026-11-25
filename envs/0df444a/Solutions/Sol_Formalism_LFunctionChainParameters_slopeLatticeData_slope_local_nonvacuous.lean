-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.slope_local_nonvacuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:23.838388+00:00
-- url     : https://prove2.me/submissions/7f6071d5-3610-472f-a3af-84cdd9c27260

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_finPl_ne_bot
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealPow_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_local_ideal_pow
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_locScal_one

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
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (σ τ : FinPl K →₀ ℤ)
    (M : Submodule (𝓞 K) V) :
    ∃ (_ : ∀ w : FinPl K, Module (Rloc w) V) (_ : ∀ w : FinPl K, IsScalarTower (𝓞 K) (Rloc w) V)
      (ϖ : FinPl K → 𝓞 K) (N N' : Submodule (𝓞 K) V), (∀ w, ϖ w ∈ w.1 ∧ ϖ w ∉ w.1 ^ 2) ∧
      rkK N = rkK M ∧
      (∀ w, locScal w 1 N ≤ locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M) ∧
      (∀ w, locScal w 1 N' = locScal w (algebraMap (𝓞 K) K (ϖ w) ^ (-σ w)) N) := by
  let i1 : ∀ w : FinPl K, Module (Rloc w) V := fun w => Module.compHom V (rlocToK w)
  have i2 : ∀ w : FinPl K, IsScalarTower (𝓞 K) (Rloc w) V := fun w => ⟨fun r s x => by
    have := w.2.isPrime
    show rlocToK w (r • s) • x = r • (rlocToK w s • x)
    have hr : rlocToK w (algebraMap (𝓞 K) (Rloc w) r) = algebraMap (𝓞 K) K r :=
      IsLocalization.lift_eq _ r
    rw [Algebra.smul_def, map_mul, mul_smul, hr, algebraMap_smul]⟩
  have hex : ∀ w : FinPl K, ∃ x : 𝓞 K, x ∈ w.1 ∧ x ∉ w.1 ^ 2 := fun w => by
    obtain ⟨x, hx, hx'⟩ := Ideal.exists_mem_pow_notMem_pow_succ w.1 (finPl_ne_bot w) w.2.ne_top 1
    exact ⟨x, by simpa using hx, hx'⟩
  choose ϖ hϖ using hex
  refine ⟨i1, i2, ϖ, idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) M, modLat σ (idealSmul ((idealPow τ :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M), hϖ,
      rkK_idealSmul (idealPow_ne_zero τ) M, fun w => ?_, fun w => ?_⟩
  · rw [locScal_one]
    exact (local_ideal_pow K V w (ϖ w) (hϖ w).1 (hϖ w).2 τ M).le
  · rw [locScal_one, ← Finsupp.neg_apply]
    exact local_ideal_pow K V w (ϖ w) (hϖ w).1 (hϖ w).2 (-σ) _
end Formalism.LFunctionChainParameters.slopeLatticeData
