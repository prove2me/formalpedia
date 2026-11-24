-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_le_span_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:30:50.725289+00:00
-- url     : https://prove2.me/submissions/a2f06f6a-2569-487e-a2cf-796dcf5a249f

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem

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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (w : Ideal (𝓞 K)) [w.IsPrime] [Module (Localization.AtPrime w) V]
    [IsScalarTower (𝓞 K) (Localization.AtPrime w) V] {J : FI} (hJ : HalfUnit w J)
    (L : Submodule (𝓞 K) V) :
    idealSmul (J : Submodule (𝓞 K) K) L ≤
      (Submodule.span (Localization.AtPrime w) (L : Set V)).restrictScalars (𝓞 K) := by
  obtain ⟨t, ht, h⟩ := hJ
  refine Submodule.span_le.2 ?_
  rintro z ⟨a, ha, x, hx, rfl⟩
  obtain ⟨y, hy⟩ := h a (FractionalIdeal.mem_coe.1 ha)
  have e1 : t • (a • x) = y • x := by
    rw [← algebraMap_smul K t (a • x), smul_smul, ← hy, algebraMap_smul]
  obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime w) (⟨t, ht⟩ : w.primeCompl)
  have e2 : a • x = (↑u⁻¹ : Localization.AtPrime w) • (y • x) := by
    rw [← e1, ← algebraMap_smul (Localization.AtPrime w) t (a • x), smul_smul]
    have : (↑u⁻¹ : Localization.AtPrime w) * algebraMap (𝓞 K) (Localization.AtPrime w) t = 1 := by
      have hu' : (u : Localization.AtPrime w) = algebraMap (𝓞 K) (Localization.AtPrime w) t := hu
      rw [← hu']; exact u.inv_mul
    rw [this, one_smul]
  show a • x ∈ Submodule.span (Localization.AtPrime w) (L : Set V)
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (L.smul_mem y hx))
end Formalism.LFunctionChainParameters.slopeLatticeData
