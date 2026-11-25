-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.slope_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:33.863964+00:00
-- url     : https://prove2.me/submissions/8f4e9a09-d125-4e41-bfad-7579e99bb5dd

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_slope_via_lengths
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_length_at_span
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_local_ideal_pow
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_locScal_one
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_le_of_loc
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_length_congr_sub

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
theorem _root_.solution : SlopeRelationsLocal := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ _ _ b X hX ϖ hϖ σ τ M N N' β hM hM0 hrk hN hN' hβ
  have hloc : ∀ (n : FinPl K →₀ ℤ) (L : Submodule (𝓞 K) V) (w : FinPl K),
      Submodule.span (Rloc w) ((idealSmul ((idealPow n :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) L :
          Submodule (𝓞 K) V) : Set V) = locScal w (algebraMap (𝓞 K) K (ϖ w) ^ n w) L :=
    fun n L w => local_ideal_pow K V w (ϖ w) (hϖ w).1 (hϖ w).2 n L
  have hNle : N ≤ idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) M := by
    refine le_of_loc fun w => ?_
    rw [hloc, ← locScal_one]
    exact hN w
  have hN'eq : N' = modLat σ N := by
    unfold modLat
    apply le_antisymm
    · refine le_of_loc fun w => ?_
      rw [hloc, ← locScal_one, hN' w, Finsupp.neg_apply]
    · refine le_of_loc fun w => ?_
      rw [hloc, ← locScal_one, hN' w, Finsupp.neg_apply]
  have hlen : ∀ w : FinPl K, lenAt w (idealSmul ((idealPow τ :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M) N =
      Module.length (Rloc w) (locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M ⧸
        (locScal w 1 N).comap (locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M).subtype) := by
    intro w
    rw [length_at_span K V w _ N hNle, locScal_one]
    exact length_congr_sub (hloc τ M w) _
  have hmain := slope_via_lengths K V ι b X hX σ τ M N β hM hM0 hNle hrk
    (fun w => by rw [hlen w]; exact hβ w)
  rw [hN'eq]
  exact ⟨fun w => by rw [← hlen w]; exact hmain.1 w, hmain.2⟩
end Formalism.LFunctionChainParameters.slopeLatticeData
