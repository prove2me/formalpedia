-- Prove2me | solution 1 for Formalism.L2.NCov.sum_finrank_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:28:10.408341+00:00
-- url     : https://prove2.me/submissions/f897101d-2fb7-4b77-9b19-12a8e89cd9c7

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_finrank_finset_sup
import Theorems.Thm_Formalism_L2_NCov_iSup_eq_sup_filter
import Theorems.Thm_Formalism_L2_NCov_pt_injective
import Theorems.Thm_Formalism_L2_NCov_cls_isMaximal
import Theorems.Thm_Formalism_L2_NCov_iSupIndep_alt
import Theorems.Thm_Formalism_L2_NCov_exists_finset_pts

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
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (Ms : Finset (Ideal (Algebra.adjoin O S)))
    (hMs : ∀ 𝔪 : Ideal (Algebra.adjoin O S), 𝔪.IsMaximal → 𝔪 ∈ Ms) :
    ∑ 𝔪 ∈ Ms, finrank K (part (Algebra.adjoin O S) 𝔪) = finrank K V := by
  classical
  obtain ⟨F, hF, htop⟩ := exists_finset_pts hinj hS hsplit hint
  have hind : iSupIndep (fun ψ : Algebra.adjoin O S →ₐ[O] O => W _ (pt ψ)) :=
    (iSupIndep_alt hS).comp (pt_injective hinj)
  have hpart : ∀ 𝔪, part (Algebra.adjoin O S) 𝔪 =
      (F.filter (fun ψ => cls ψ = 𝔪)).sup (fun ψ => W _ (pt ψ)) := fun 𝔪 =>
    iSup_eq_sup_filter (fun ψ : Algebra.adjoin O S →ₐ[O] O => W _ (pt ψ)) F hF _
  calc ∑ 𝔪 ∈ Ms, finrank K (part (Algebra.adjoin O S) 𝔪)
      = ∑ 𝔪 ∈ Ms, ∑ ψ ∈ F with cls ψ = 𝔪, finrank K (W _ (pt ψ)) := by
        refine Finset.sum_congr rfl fun 𝔪 _ => ?_
        rw [hpart, finrank_finset_sup hind]
    _ = ∑ ψ ∈ F, finrank K (W _ (pt ψ)) :=
        Finset.sum_fiberwise_of_maps_to (fun ψ _ => hMs _ (cls_isMaximal ψ)) _
    _ = finrank K V := by rw [← finrank_finset_sup hind, htop, finrank_top]
end Formalism.L2.NCov
