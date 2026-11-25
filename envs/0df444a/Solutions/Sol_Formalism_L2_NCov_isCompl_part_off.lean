-- Prove2me | solution 1 for Formalism.L2.NCov.isCompl_part_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:08:58.413829+00:00
-- url     : https://prove2.me/submissions/6b326fc8-ab2d-4f81-b3e9-f30d429bdcb6

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_iSup_eq_sup_filter
import Theorems.Thm_Formalism_L2_NCov_pt_injective
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
open Polynomial
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O]
  {S : Set (End K V)}
namespace Formalism.L2.NCov
theorem _root_.solution [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (𝔪 : Ideal (Algebra.adjoin O S)) :
    IsCompl (part (Algebra.adjoin O S) 𝔪) (off (Algebra.adjoin O S) 𝔪) := by
  classical
  obtain ⟨F, hF, htop⟩ := exists_finset_pts hinj hS hsplit hint
  set Wp : (Algebra.adjoin O S →ₐ[O] O) → Submodule K V := fun ψ => W _ (pt ψ) with hWp
  have hind : iSupIndep Wp := (iSupIndep_alt hS).comp (pt_injective hinj)
  have hsi : F.SupIndep Wp := hind.supIndep' F
  have hpart : part (Algebra.adjoin O S) 𝔪 = (F.filter (fun ψ => cls ψ = 𝔪)).sup Wp :=
    iSup_eq_sup_filter Wp F hF _
  have hoff : off (Algebra.adjoin O S) 𝔪 = (F.filter (fun ψ => cls ψ ≠ 𝔪)).sup Wp :=
    iSup_eq_sup_filter Wp F hF _
  rw [hpart, hoff]
  constructor
  · exact hsi.disjoint_sup_sup (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (Finset.disjoint_filter.2 fun ψ _ h h' => h' h)
  · rw [codisjoint_iff, ← Finset.sup_union]
    have e : F.filter (fun ψ => cls ψ = 𝔪) ∪ F.filter (fun ψ => cls ψ ≠ 𝔪) = F := by
      ext ψ; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    rw [e]; exact htop
end Formalism.L2.NCov
