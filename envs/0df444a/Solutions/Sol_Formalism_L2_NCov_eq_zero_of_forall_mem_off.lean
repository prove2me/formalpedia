-- Prove2me | solution 1 for Formalism.L2.NCov.eq_zero_of_forall_mem_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:28:06.26587+00:00
-- url     : https://prove2.me/submissions/3a18a0eb-f416-478f-b8ab-01d42d71caf9

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
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
    (hMs : ∀ 𝔪 : Ideal (Algebra.adjoin O S), 𝔪.IsMaximal → 𝔪 ∈ Ms)
    {y : V} (hy : ∀ 𝔪 ∈ Ms, y ∈ off (Algebra.adjoin O S) 𝔪) : y = 0 := by
  classical
  obtain ⟨F, hF, htop⟩ := exists_finset_pts hinj hS hsplit hint
  set Wp : (Algebra.adjoin O S →ₐ[O] O) → Submodule K V := fun ψ => W _ (pt ψ) with hWp
  have hind : iSupIndep Wp := (iSupIndep_alt hS).comp (pt_injective hinj)
  have hsi : F.SupIndep Wp := hind.supIndep' F
  have hoff : ∀ 𝔪, off (Algebra.adjoin O S) 𝔪 = (F.filter (fun ψ => cls ψ ≠ 𝔪)).sup Wp := fun 𝔪 =>
    iSup_eq_sup_filter Wp F hF _
  have key : ∀ s : Finset (Ideal (Algebra.adjoin O S)), (∀ 𝔪 ∈ s, y ∈ off (Algebra.adjoin O S) 𝔪) →
      y ∈ (F.filter (fun ψ => cls ψ ∉ s)).sup Wp := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      have e : F.filter (fun ψ => cls ψ ∉ (∅ : Finset (Ideal (Algebra.adjoin O S)))) = F := by
        ext ψ; simp
      rw [e, htop]
      exact Submodule.mem_top
    | insert a s ha ih =>
      intro h
      have h1 := ih fun 𝔪 h𝔪 => h 𝔪 (Finset.mem_insert_of_mem h𝔪)
      have h2 := h a (Finset.mem_insert_self a s)
      rw [hoff] at h2
      have e1 : (F.filter (fun ψ => cls ψ ∉ s)).sup Wp =
          (F.filter (fun ψ => cls ψ ∉ insert a s)).sup Wp ⊔
            (F.filter (fun ψ => cls ψ ∉ s ∧ cls ψ = a)).sup Wp := by
        rw [← Finset.sup_union]
        congr 1
        ext ψ
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert]
        tauto
      have e2 : (F.filter (fun ψ => cls ψ ≠ a)).sup Wp =
          (F.filter (fun ψ => cls ψ ∉ insert a s)).sup Wp ⊔
            (F.filter (fun ψ => cls ψ ≠ a ∧ cls ψ ∈ s)).sup Wp := by
        rw [← Finset.sup_union]
        congr 1
        ext ψ
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert]
        tauto
      have hdis : Disjoint ((F.filter (fun ψ => cls ψ ∉ s ∧ cls ψ = a)).sup Wp)
          ((F.filter (fun ψ => cls ψ ≠ a)).sup Wp) :=
        hsi.disjoint_sup_sup (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          (Finset.disjoint_filter.2 fun ψ _ hx hx' => hx' hx.2)
      rw [e1] at h1
      rw [e2] at h2 hdis
      have hm := Submodule.mem_inf.2 ⟨h1, h2⟩
      rw [sup_inf_assoc_of_le _ le_sup_left, hdis.eq_bot, sup_bot_eq] at hm
      exact hm
  have hy' := key Ms hy
  have hempty : F.filter (fun ψ => cls ψ ∉ Ms) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun ψ _ hψ => hψ (hMs _ (cls_isMaximal ψ))
  rw [hempty, Finset.sup_empty] at hy'
  exact (Submodule.mem_bot K).1 hy'
end Formalism.L2.NCov
