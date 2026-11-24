-- Prove2me | solution 1 for Formalism.L2.NCov.exists_finset_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:31.054555+00:00
-- url     : https://prove2.me/submissions/6baf433c-608b-4cc4-9ed6-d7e2a28040b0

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_pt_injective
import Theorems.Thm_Formalism_L2_NCov_exists_pt
import Theorems.Thm_Formalism_L2_NCov_iSupIndep_alt
import Theorems.Thm_Formalism_L2_NCov_iSup_W_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [IsLocalRing O]
variable {S : Set (End K V)}
namespace Formalism.L2.NCov
theorem _root_.solution [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) :
    ∃ F : Finset (Algebra.adjoin O S →ₐ[O] O),
      (∀ ψ, W _ (pt ψ) ≠ ⊥ → ψ ∈ F) ∧ F.sup (fun ψ => W _ (pt ψ)) = ⊤ := by
  have hind : iSupIndep (fun ψ : Algebra.adjoin O S →ₐ[O] O => W _ (pt ψ)) :=
    (iSupIndep_alt hS).comp (pt_injective hinj)
  have hfin := Submodule.finite_ne_bot_of_iSupIndep hind
  refine ⟨hfin.toFinset, fun ψ h => hfin.mem_toFinset.2 h, ?_⟩
  rw [eq_top_iff, ← iSup_W_eq_top (O := O) hS hsplit]
  refine iSup_le fun χ => ?_
  by_cases h : W _ χ = ⊥
  · rw [h]; exact bot_le
  · obtain ⟨ψ, rfl⟩ := exists_pt hS hint hinj h
    exact Finset.le_sup (f := fun ψ => W _ (pt ψ)) (hfin.mem_toFinset.2 h)
end Formalism.L2.NCov
