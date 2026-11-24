-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.wUnit_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:32:00.992243+00:00
-- url     : https://prove2.me/submissions/2c20c044-a67b-4994-94e6-fd8a73c6dd54

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_finPl_coe_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_halfUnit_of_le_one

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
variable {K : Type} [Field K] [NumberField K]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (w : FinPl K) {ϖ : 𝓞 K} (h1 : ϖ ∈ w.1) (h2 : ϖ ∉ w.1 ^ 2) :
    WUnit w.1 ((w.1 : FI) *
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ))⁻¹) := by
  have := w.2.isPrime
  have hw0 := finPl_coe_ne_zero w
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl; exact h2 (Ideal.zero_mem _)
  have hϖK : algebraMap (𝓞 K) K ϖ ≠ 0 := by
    intro h0
    exact hϖ0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
  set Pw : FI := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ)
    with hPw
  have hPw0 : Pw ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hϖK
  have hPww : Pw ≤ (w.1 : FI) := by
    rw [hPw, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_le_coeIdeal]
    exact (Ideal.span_singleton_le_iff_mem _).2 h1
  have hC1 : Pw * (w.1 : FI)⁻¹ ≤ 1 := by
    calc Pw * (w.1 : FI)⁻¹ ≤ (w.1 : FI) * (w.1 : FI)⁻¹ := mul_le_mul_left hPww _
      _ = 1 := mul_inv_cancel₀ hw0
  refine ⟨mul_ne_zero hw0 (inv_ne_zero hPw0), ?_, ?_⟩
  ·
    have hex : ∃ t : 𝓞 K, algebraMap (𝓞 K) K t ∈ Pw * (w.1 : FI)⁻¹ ∧ t ∉ w.1 := by
      by_contra hcon
      push Not at hcon
      apply h2
      have hle : Pw * (w.1 : FI)⁻¹ * (w.1 : FI) ≤ ((w.1 ^ 2 : Ideal (𝓞 K)) : FI) := by
        intro x hx
        refine FractionalIdeal.mul_induction_on hx ?_ ?_
        · intro i hi j hj
          obtain ⟨t, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 (hC1 hi)
          obtain ⟨s, hs, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
          refine (FractionalIdeal.mem_coeIdeal _).2 ⟨t * s, ?_, map_mul _ _ _⟩
          rw [sq]; exact Ideal.mul_mem_mul (hcon t hi) hs
        · intro x y hx hy
          exact FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 hx)
            (FractionalIdeal.mem_coe.2 hy))
      rw [mul_assoc, inv_mul_cancel₀ hw0, mul_one] at hle
      obtain ⟨z, hz, hzϖ⟩ := (FractionalIdeal.mem_coeIdeal _).1
        (hle (FractionalIdeal.mem_spanSingleton_self _ _))
      rwa [FaithfulSMul.algebraMap_injective (𝓞 K) K hzϖ] at hz
    obtain ⟨t, htC, htw⟩ := hex
    refine ⟨t, htw, fun x hx => ?_⟩
    have hmem := FractionalIdeal.mul_mem_mul htC hx
    have e : Pw * (w.1 : FI)⁻¹ * ((w.1 : FI) * Pw⁻¹) = 1 := by
      rw [mul_assoc, ← mul_assoc (w.1 : FI)⁻¹, inv_mul_cancel₀ hw0, one_mul, mul_inv_cancel₀ hPw0]
    rw [e] at hmem
    exact (FractionalIdeal.mem_one_iff _).1 hmem
  · rw [mul_inv, inv_inv, mul_comm]
    exact halfUnit_of_le_one w.1 hC1
end Formalism.LFunctionChainParameters.slopeLatticeData
