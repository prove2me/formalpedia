-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.muDef_le_muMaxDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:20:48.615208+00:00
-- url     : https://prove2.me/submissions/4c5243a8-ce38-40fe-ad3d-782b0cb55630

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_fg_of_le
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_slope_characterization


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
    (hX : ∀ v, IsUnit (X v).det) {L Q : Submodule (𝓞 K) V} (hL : L.FG) (hQL : Q ≤ L)
    (hQ0 : Q ≠ ⊥) : muDef b X Q ≤ muMaxDef b X L := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hL0 : L ≠ ⊥ := fun h => hQ0 (eq_bot_iff.2 (h ▸ hQL))
  have hlat := (place_lattice_structure K V ι b X hX L hL).1
  have hch := ((slope_characterization (𝓞 K) V _ (realize b X) L hlat hL0).1
    (muMax (realize b X) L)).1 le_rfl Q hQL
  have hrk := (place_lattice_structure K V ι b X hX Q (fg_of_le hL hQL)).2.1
  have hpos : (0 : ℝ) < (rk (realize b X) Q : ℝ) := by
    rw [hrk]
    exact_mod_cast Nat.mul_pos Module.finrank_pos (rkK_pos hQ0)
  have hs : slope (realize b X) Q ≤ muMax (realize b X) L := by
    show deg (realize b X) Q / (rk (realize b X) Q : ℝ) ≤ _
    rwa [div_le_iff₀ hpos]
  unfold muDef muMaxDef
  linarith
end Formalism.LFunctionChainParameters.slopeLatticeData
