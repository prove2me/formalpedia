-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.lemma_five_three_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:35.242262+00:00
-- url     : https://prove2.me/submissions/0c9e67a7-a81a-42fa-8ee7-b0e5c284534d

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalModuleOf
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Theorems.Thm_Formalism_NG_globalModule


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution : BlockRingDecompositionLemma := by
  unfold BlockRingDecompositionLemma
  intro O _ _ _ X d G _ _ _ t ht bl T D _ _ hTop Z NN _ _ g₀ n hspan hZ hcard
  unfold RingData.Top RingTop at hTop
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9, h10, -⟩ := hTop

  have hsum : ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} = Fintype.card d := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv bl)
  have hcard' : ((g₀ * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
      Cardinal.mk (IsLocalRing.ResidueField O) := by
    rw [hsum]; exact hcard

  have hmain := Formalism.NG.globalModule O X D.X' T D.T' Z D.p D.q D.b h1 (fun x _ => h2 x) d D.R' h3
    NN g₀ n hspan hZ D.π' D.ρπ h7 (Fin (t + 1)) bl h8 D.ρk h9 h10 hcard'
  exact hmain.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
end Formalism.RepresentationBoundsCohomology.ringDataObjects
