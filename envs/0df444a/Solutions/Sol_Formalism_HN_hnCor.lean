-- Prove2me | solution 1 for Formalism.HN.hnCor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:58:48.447122+00:00
-- url     : https://prove2.me/submissions/a34455b3-bac5-4024-8b0b-402d5e143b0c

import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_StatementCor
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Theorems.Thm_Formalism_F_att_rk_le
import Theorems.Thm_Formalism_HN_hnSlopes
import Theorems.Thm_Formalism_HN_hnStep_spec
import Theorems.Thm_Formalism_HN_hnSum_isLat_mono
import Theorems.Thm_Formalism_HN_hnSum_zl_mono
import Theorems.Thm_Formalism_HN_muChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution : HNCor := by
  intro R V E _ _ _ _ _ _ ρ L hL
  have mono : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → muMax ρ N ≤ muMax ρ L := by
    intro N hN hN0
    have hL0 : L ≠ ⊥ := fun h => hN0 (le_bot_iff.1 (h ▸ hN))
    have hNL := hnSum_isLat_mono ρ hL hN
    refine ((muChar R V E ρ N hNL hN0).1 (muMax ρ L)).2 fun N' hN' => ?_
    exact ((muChar R V E ρ L hL hL0).1 (muMax ρ L)).1 le_rfl N' (hN'.trans hN)
  refine ⟨?_, ?_, ?_, ?_, mono, ?_⟩
  · intro a b hab
    unfold hnStep
    exact sSup_le_sSup fun N ⟨h1, h2, h3⟩ => ⟨h1, h2, hab.trans h3⟩
  · intro hL0 θ
    constructor
    · intro h
      have h2 := (hnStep_spec R V E ρ L hL θ).2.1
      rw [h] at h2
      exact h2 hL0
    · intro hθ
      exact le_antisymm (hnStep_spec R V E ρ L hL θ).1.1
        ((hnStep_spec R V E ρ L hL θ).2.2.1 L le_rfl hL0 hθ)
  · intro θ hθ
    by_contra hne
    have sp := hnStep_spec R V E ρ L hL θ
    have h2 := sp.2.1 hne
    have hNL := hnSum_isLat_mono ρ hL sp.1.1
    have mc := muChar R V E ρ _ hNL hne
    have := mono _ sp.1.1 hne
    linarith [mc.2.2.2.1, mc.2.2.2.2]
  · intro t
    have h := (hnSlopes R V E ρ L hL).2.1 t
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (rk ρ L)))) (p := fun j => slopeList ρ L j < t)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h2
    omega
  · intro N θ hN hN0 hθ
    have sp := hnStep_spec R V E ρ L hL θ
    rw [(hnSlopes R V E ρ L hL).2.1 θ]
    have := hL.2
    have hS := hnSum_isLat_mono ρ hL sp.1.1
    have := hS.2
    exact Formalism.F.att_rk_le (hnSum_zl_mono ρ (sp.2.2.1 N hN hN0 hθ))
end Formalism.HN
