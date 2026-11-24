-- Prove2me | solution 1 for BSLambda.LLL.exists_pair_subset_of_two_le_card_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:30:58.113505+00:00
-- url     : https://prove2.me/submissions/92ff0057-c8c3-4a1a-8131-43339775a87f

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
omit [Fintype ι]
namespace BSLambda.LLL
theorem _root_.solution {V W : Finset ι}
    (h : 2 ≤ (V ∩ W).card) : ∃ p ∈ V.powersetCard 2, p ⊆ W := by
  obtain ⟨p, hp⟩ := Finset.powersetCard_nonempty.mpr h
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hp
  exact ⟨p, Finset.mem_powersetCard.mpr ⟨hsub.trans Finset.inter_subset_left, hcard⟩,
    hsub.trans Finset.inter_subset_right⟩
end BSLambda.LLL
