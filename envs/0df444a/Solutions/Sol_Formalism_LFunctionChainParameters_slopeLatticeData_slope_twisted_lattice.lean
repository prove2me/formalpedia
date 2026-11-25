-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.slope_twisted_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:46.056157+00:00
-- url     : https://prove2.me/submissions/fe5a74f5-2839-47b0-9fc4-6c15c107a97a

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealPow_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_slope_formula

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
theorem _root_.solution {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (σ τ : FinPl K →₀ ℤ) (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hM0 : M ≠ ⊥) :
    muDef b X (modLat σ (idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) M)) = muDef b X M + sgSum σ τ := by
  have h := (slope_formula K V ι b X hX σ τ M _ hM hM0 le_rfl
    (rkK_idealSmul (idealPow_ne_zero τ) M)).2
  rw [h, AddSubgroup.relIndex_self]
  simp
end Formalism.LFunctionChainParameters.slopeLatticeData
