-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.ht_fractional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:28:09.312683+00:00
-- url     : https://prove2.me/submissions/0e97cf49-fb27-4a79-886c-0326c5aedab5

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_coeIdeal
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_ideal

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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG)
    {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0) :
    ht b X (idealSmul (I : Submodule (𝓞 K) K) L) =
      ht b X L * ((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ rkK L := by
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h0
    exact ha (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
  have hJ : J ≠ ⊥ := by
    rintro rfl
    apply hI
    rw [hIJ]; simp
  have hA : Ideal.span {a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact ha
  have hmul : ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * I =
      (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, hIJ, ← mul_assoc,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ haK,
      FractionalIdeal.spanSingleton_one, one_mul]
  have hlat : Ideal.span {a} • idealSmul (I : Submodule (𝓞 K) K) L = J • L := by
    rw [← idealSmul_coeIdeal, ← idealSmul_mul, ← FractionalIdeal.coe_mul, hmul, idealSmul_coeIdeal]
  have h1 := ht_ideal b X hX (idealSmul_fg I hL) hA
  rw [hlat, ht_ideal b X hX hL hJ, rkK_idealSmul hI] at h1
  have hnorm : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℝ) * ((FractionalIdeal.absNorm I : ℚ) : ℝ) =
      ((Ideal.absNorm J : ℕ) : ℝ) := by
    have := congrArg FractionalIdeal.absNorm hmul
    rw [map_mul, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm] at this
    exact_mod_cast this
  have hA0 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => hA (Ideal.absNorm_eq_zero_iff.1 h)
  rw [← hnorm, mul_pow] at h1
  have h2 : ht b X (idealSmul (I : Submodule (𝓞 K) K) L) *
      ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℝ) ^ rkK L =
      (ht b X L * ((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ rkK L) *
      ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℝ) ^ rkK L := by
    rw [← h1]; ring
  exact mul_right_cancel₀ (pow_ne_zero _ hA0) h2
end Formalism.LFunctionChainParameters.slopeLatticeData
