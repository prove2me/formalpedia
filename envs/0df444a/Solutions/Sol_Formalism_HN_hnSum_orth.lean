-- Prove2me | solution 1 for Formalism.HN.hnSum_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:45:18.445802+00:00
-- url     : https://prove2.me/submissions/0a3683fa-f476-49f4-a9a7-2df6a1ab7512

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Theorems.Thm_Formalism_HN_hnSum_mem_zl
import Theorems.Thm_Formalism_HN_hnSum_zl_sup
import Theorems.Thm_Formalism_HN_hnSum_orth_zero
import Theorems.Thm_Formalism_F_orthSum


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
variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)
variable [FiniteDimensional ℝ E]
namespace Formalism.HN
theorem _root_.solution {A B : Submodule R V} (hA : IsLat ρ A) (hB : IsLat ρ B)
    (h : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0) :
    IsLat ρ (A ⊔ B) ∧ A ⊓ B = ⊥ ∧ deg ρ (A ⊔ B) = deg ρ A + deg ρ B := by
  have horth : ∀ x ∈ zl ρ A, ∀ y ∈ zl ρ B, inner ℝ x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (hnSum_mem_zl ρ A x).1 hx
    obtain ⟨b, hb, rfl⟩ := (hnSum_mem_zl ρ B y).1 hy
    exact h a ha b hb
  obtain ⟨hd, hdeg, -⟩ := Formalism.F.orthSum E (zl ρ A) (zl ρ B) hA.2 hB.2 horth
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x hx x' hx' hxx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (show x ∈ A ⊔ B from hx)
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 (show x' ∈ A ⊔ B from hx')
    have e : ρ (a - a') = ρ (b' - b) := by
      rw [map_add, map_add] at hxx
      rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, hxx, add_comm]
    have hu : a - a' = 0 := by
      apply hnSum_orth_zero ρ hA (A.sub_mem ha ha')
      rw [congrArg (inner ℝ (ρ (a - a'))) e]
      exact h _ (A.sub_mem ha ha') _ (B.sub_mem hb' hb)
    have hv : b' - b = 0 := by
      apply hnSum_orth_zero ρ hB (B.sub_mem hb' hb)
      rw [← e]
      nth_rewrite 2 [e]
      exact h _ (A.sub_mem ha ha') _ (B.sub_mem hb' hb)
    rw [sub_eq_zero.1 hu, sub_eq_zero.1 hv]
  · rw [hnSum_zl_sup]
    exact hd
  · rw [eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot R).2 (hnSum_orth_zero ρ hA hx.1 (h x hx.1 x hx.2))
  · unfold deg
    rw [hnSum_zl_sup]
    exact hdeg
end Formalism.HN
