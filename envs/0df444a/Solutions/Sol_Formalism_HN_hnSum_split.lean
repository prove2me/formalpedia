-- Prove2me | solution 1 for Formalism.HN.hnSum_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:13.7216+00:00
-- url     : https://prove2.me/submissions/d497690c-4960-4f0f-9468-c8d9e609a2b8

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Theorems.Thm_Formalism_HN_hnSum_isLat_mono
import Theorems.Thm_Formalism_HN_hnSum_orth
import Theorems.Thm_Formalism_HN_hnSum_orth_rk

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
universe u v w x
variable {R : Type u} {V : Type v} {E : Type w} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
namespace Formalism.HN
theorem _root_.solution (h1 : DegSupermod.{u, v, w}) {A B : Submodule R V} (hA : IsLat ρ A)
    (hB : IsLat ρ B) (h : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0) {N : Submodule R V}
    (hN : N ≤ A ⊔ B) :
    deg ρ N ≤ deg ρ (N ⊓ A) + deg ρ (B ⊓ (N ⊔ A)) ∧
      rk ρ N = rk ρ (N ⊓ A) + rk ρ (B ⊓ (N ⊔ A)) := by
  obtain ⟨hL, -, -⟩ := hnSum_orth ρ hA hB h
  have hQ : IsLat ρ (B ⊓ (N ⊔ A)) := hnSum_isLat_mono ρ hB inf_le_left
  have hAQ : ∀ x ∈ A, ∀ y ∈ B ⊓ (N ⊔ A), inner ℝ (ρ x) (ρ y) = 0 :=
    fun x hx y hy => h x hx y hy.1
  have hNA : N ⊔ A = A ⊔ B ⊓ (N ⊔ A) := by
    rw [← sup_inf_assoc_of_le B (le_sup_right : A ≤ N ⊔ A)]
    exact (inf_eq_right.2 (sup_le hN le_sup_left)).symm
  have s := h1 R V E ρ (A ⊔ B) N A hL hN le_sup_left
  obtain ⟨-, -, dQ⟩ := hnSum_orth ρ hA hQ hAQ
  have rQ := hnSum_orth_rk ρ h1 hA hQ hAQ
  rw [hNA, dQ, rQ] at s
  obtain ⟨sr, sd⟩ := s
  refine ⟨by linarith, by omega⟩
end Formalism.HN
