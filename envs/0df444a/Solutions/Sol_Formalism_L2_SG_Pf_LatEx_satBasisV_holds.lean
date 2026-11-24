-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatEx.satBasisV_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:05:04.198819+00:00
-- url     : https://prove2.me/submissions/2f83c90b-7d95-46ba-a809-0e68d83c3803

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Lemmata_MiscLemmasD_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_exists_smul_mem_of_mem_span
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_adapted_basis
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_spanE_of_lat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain
namespace Formalism.L2.SG.Pf.LatEx
section Sat
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E
private lemma fg_of_le_lemma {M N : Submodule (𝓞 E) V} (hM : M.FG) (h : N ≤ M) : N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian M hM
  have h1 : (Submodule.comap M.subtype N).FG := IsNoetherian.noetherian _
  have h2 := h1.map M.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 h] at h2
end Sat
private lemma fi_exists_ne_lemma {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Submonoid R}
    {I : FractionalIdeal S K} (hI : I ≠ 0) : ∃ x ∈ I, x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hI
  ext x
  rw [FractionalIdeal.mem_zero_iff]
  exact ⟨h x, fun hx => hx ▸ FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)⟩
end Formalism.L2.SG.Pf.LatEx
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx
namespace Formalism.L2.SG.Pf.LatEx
theorem _root_.solution : SatBasisV := by
  intro E V _ _ _ _ _ _ _ Λ hΛ n w hw a ha
  have hMfg : (Λ ⊓ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E)).FG :=
    fg_of_le_lemma hΛ.fg inf_le_left
  have hd : ∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧
      d • w i ∈ Λ ⊓ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) := by
    intro i
    have hwi : w i ∈ Submodule.span E (Λ : Set V) := by
      rw [hΛ.span_eq_top]; exact Submodule.mem_top
    obtain ⟨d, hd0, hdΛ⟩ := exists_smul_mem_of_mem_span hwi
    exact ⟨d, hd0, hdΛ, Submodule.smul_of_tower_mem _ d (Submodule.subset_span ⟨i, rfl⟩)⟩
  obtain ⟨e, c, hc, hMe⟩ := adapted_basis n w hw _ hMfg inf_le_right hd a ha
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hspw : Submodule.span E ((Λ ⊓ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) :
      Submodule (𝓞 E) V) : Set V) = Submodule.span E (Set.range w) := by
    refine spanE_of_lat _ w _ inf_le_right le_rfl fun i => ?_
    obtain ⟨d, hd0, hdM⟩ := hd i
    exact ⟨algebraMap (𝓞 E) E d, fun h => hd0 (hinj (by rw [h, map_zero])),
      by rw [algebraMap_smul]; exact hdM⟩
  have hspe : Submodule.span E ((Λ ⊓ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) :
      Submodule (𝓞 E) V) : Set V) = Submodule.span E (Set.range e) := by
    refine spanE_of_lat _ e _ ?_ le_rfl fun i => ?_
    · rw [hMe]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, x, hx, rfl⟩
      exact Submodule.smul_mem _ x (Submodule.subset_span ⟨i, rfl⟩)
    · have hne : Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 E)) E) a c i ≠ 0 := by
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hc
        | cast j => rw [Fin.snoc_castSucc]; exact ha j
      obtain ⟨x, hx, hx0⟩ := fi_exists_ne_lemma hne
      exact ⟨x, hx0, by rw [hMe]; exact Submodule.subset_span ⟨i, x, hx, rfl⟩⟩
  have hew : Submodule.span E (Set.range e) = Submodule.span E (Set.range w) := hspe.symm.trans hspw
  refine ⟨e, c, ?_, hew, hc, hMe⟩
  rw [linearIndependent_iff_card_eq_finrank_span]
  unfold Set.finrank
  rw [hew, finrank_span_eq_card hw]
end Formalism.L2.SG.Pf.LatEx
