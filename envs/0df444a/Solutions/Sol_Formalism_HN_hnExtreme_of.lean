-- Prove2me | solution 1 for Formalism.HN.hnExtreme_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:25.961677+00:00
-- url     : https://prove2.me/submissions/38a79a2c-c145-43c4-88f3-a13f9eefc199

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Lemmata_GeneralBFactLeftForm_Imports
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNExtreme
import Theorems.Thm_Formalism_HN_hnExtreme_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w
namespace Formalism.HN
theorem _root_.solution (h1 : HNSlopes.{u, v, w}) (h2 : MuChar.{u, v, w}) (h3 : HNStep.{u, v, w})
    (h4 : SatBasic.{u, v, w}) : HNExtreme.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L hL hL0
  obtain ⟨hanti, hcard, -⟩ := h1 R V E ρ L hL
  obtain ⟨B1, B2, B3, B4, B5, -, -, -⟩ := h4 R V E ρ L hL
  obtain ⟨M1, -, M3, -⟩ := h2 R V E ρ L hL hL0
  have key : ∀ (θ : ℝ) (j : Fin (rk ρ L)),
      θ ≤ slopeList ρ L j ↔ (j : ℕ) < rk ρ (hnStep ρ L θ) := by
    intro θ j
    rw [← hcard θ]
    exact hnExtreme_mem_iff _ hanti θ j
  have hSL : ∀ θ : ℝ, hnStep ρ L θ ≤ L := fun θ => (h3 R V E ρ L hL θ).1.1
  have hbot : rk ρ (⊥ : Submodule R V) = 0 := (B4 ⊥ bot_le).2 rfl
  have hrkpos : 0 < rk ρ L := by
    rcases Nat.eq_zero_or_pos (rk ρ L) with h | h
    · exact absurd ((B4 L le_rfl).1 h) hL0
    · exact h

  have hstepMin : hnStep ρ L (muMin ρ L) = L := by
    obtain ⟨-, -, S3, -⟩ := h3 R V E ρ L hL (muMin ρ L)
    exact le_antisymm (hSL _) (S3 L le_rfl hL0 le_rfl)
  have lowB : ∀ j, muMin ρ L ≤ slopeList ρ L j := by
    intro j
    rw [key, hstepMin]
    exact j.2

  have stepMax : ∀ θ : ℝ, hnStep ρ L θ ≠ ⊥ → θ ≤ muMax ρ L := by
    intro θ hne
    obtain ⟨-, S2, -, -⟩ := h3 R V E ρ L hL θ
    have hHL : IsLat ρ (hnStep ρ L θ) := B1 _ (hSL θ)
    obtain ⟨-, N2, -⟩ := h2 R V E ρ _ hHL hne
    have hθ := (N2 θ).1 (S2 hne) ⊥ bot_le
    simp only [hbot, B5, Nat.cast_zero, sub_zero] at hθ
    have hdeg := ((M1 (muMax ρ L)).1 le_rfl) _ (hSL θ)
    have hpos : (0 : ℝ) < rk ρ (hnStep ρ L θ) := by
      have : rk ρ (hnStep ρ L θ) ≠ 0 := fun h => hne ((B4 _ (hSL θ)).1 h)
      exact_mod_cast Nat.pos_of_ne_zero this
    exact le_of_mul_le_mul_right (le_trans hθ hdeg) hpos
  have upB : ∀ j, slopeList ρ L j ≤ muMax ρ L := by
    intro j
    apply stepMax
    intro h
    have := (key _ j).1 le_rfl
    rw [h, hbot] at this
    exact Nat.not_lt_zero _ this

  have hstepMaxNe : hnStep ρ L (muMax ρ L) ≠ ⊥ := by
    obtain ⟨N, hNs, hN0, hNsl⟩ := M3
    have hNL : N ≤ L := hNs.1
    have hNlat : IsLat ρ N := B1 N hNL
    obtain ⟨-, N2, -⟩ := h2 R V E ρ N hNlat hN0
    have hmin : muMax ρ L ≤ muMin ρ N := by
      rw [N2]
      intro Q hQ
      have hQd := ((M1 (muMax ρ L)).1 le_rfl) Q (le_trans hQ hNL)
      have hrkN : (rk ρ N : ℝ) ≠ 0 := by
        have : rk ρ N ≠ 0 := fun h => hN0 ((B4 N hNL).1 h)
        exact_mod_cast this
      have hsl : slope ρ N = deg ρ N / rk ρ N := rfl
      have hdegN : deg ρ N = muMax ρ L * rk ρ N := by
        rw [← hNsl, hsl, div_mul_cancel₀ _ hrkN]
      rw [mul_sub]
      linarith
    obtain ⟨-, -, S3, -⟩ := h3 R V E ρ L hL (muMax ρ L)
    have hle := S3 N hNL hN0 hmin
    intro h
    rw [h] at hle
    exact hN0 (le_bot_iff.1 hle)
  refine ⟨fun j => ⟨lowB j, upB j⟩, ⟨⟨0, hrkpos⟩, le_antisymm (upB _) ?_⟩,
    ⟨⟨rk ρ L - 1, by omega⟩, le_antisymm ?_ (lowB _)⟩⟩
  · rw [key]
    show 0 < rk ρ (hnStep ρ L (muMax ρ L))
    rcases Nat.eq_zero_or_pos (rk ρ (hnStep ρ L (muMax ρ L))) with h | h
    · exact absurd ((B4 _ (hSL _)).1 h) hstepMaxNe
    · exact h
  · by_contra hlt
    rw [not_le] at hlt
    set θ := slopeList ρ L ⟨rk ρ L - 1, by omega⟩ with hθdef
    have hj := (key θ ⟨rk ρ L - 1, by omega⟩).1 le_rfl
    simp only at hj
    obtain ⟨S1, S2, -, -⟩ := h3 R V E ρ L hL θ
    have hle := (B2 _ L (hSL θ) le_rfl).1
    have hrk : rk ρ L = rk ρ (hnStep ρ L θ) := by omega
    have heq : L = hnStep ρ L θ := B3 _ L S1 (hSL θ) le_rfl hrk
    have hne : hnStep ρ L θ ≠ ⊥ := by rw [← heq]; exact hL0
    have := S2 hne
    rw [← heq] at this
    linarith
end Formalism.HN
