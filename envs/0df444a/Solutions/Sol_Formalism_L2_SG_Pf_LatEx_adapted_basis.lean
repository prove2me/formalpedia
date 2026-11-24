-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatEx.adapted_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:44:14.777704+00:00
-- url     : https://prove2.me/submissions/a43b46a3-701e-46a5-a96e-8cde9ba433b8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Lemmata_MiscLemmasD_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_latSpanV_succ
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_latSpanV_zero
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_peel
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_rebase
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
end Formalism.L2.SG.Pf.LatEx
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E
namespace Formalism.L2.SG.Pf.LatEx
theorem _root_.solution (n : ℕ) : ∀ (w : Fin (n + 1) → V), LinearIndependent E w →
    ∀ (M : Submodule (𝓞 E) V), M.FG →
    M ≤ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) →
    (∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧ d • w i ∈ M) →
    ∀ a : Fin n → 𝓕, (∀ i, a i ≠ 0) →
    ∃ (e : Fin (n + 1) → V) (c : 𝓕), c ≠ 0 ∧
      M = latSpanV (Fin.snoc (α := fun _ => 𝓕) a c) e := by
  induction n with
  | zero =>
    intro w hw M hM hMX hd a ha
    obtain ⟨d, hd0, hdw⟩ := hd (Fin.last 0)
    obtain ⟨b, u, hb, hMe⟩ := peel w hw M hM hMX hd0 hdw
    refine ⟨fun _ => u, b, hb, ?_⟩
    rw [latSpanV_succ, Fin.init_snoc, Fin.snoc_last, latSpanV_zero, bot_sup_eq]
    have hW : Submodule.span E (Set.range (Fin.init w)) = ⊥ := by
      rw [Set.range_eq_empty, Submodule.span_empty]
    rw [hW, Submodule.restrictScalars_bot, inf_bot_eq, bot_sup_eq] at hMe
    exact hMe
  | succ n ih =>
    intro w hw M hM hMX hd a ha
    obtain ⟨d, hd0, hdw⟩ := hd (Fin.last (n + 1))
    obtain ⟨b, u, hb, hMe⟩ := peel w hw M hM hMX hd0 hdw
    have hM'fg : (M ⊓ (Submodule.span E (Set.range (Fin.init w))).restrictScalars (𝓞 E)).FG :=
      fg_of_le_lemma hM inf_le_left
    have hind : LinearIndependent E (Fin.init w) := hw.comp _ (Fin.castSucc_injective _)
    have hd' : ∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧ d • Fin.init w i ∈
        M ⊓ (Submodule.span E (Set.range (Fin.init w))).restrictScalars (𝓞 E) := by
      intro i
      obtain ⟨d, hd0, hdw⟩ := hd i.castSucc
      exact ⟨d, hd0, hdw, Submodule.smul_of_tower_mem _ d (Submodule.subset_span ⟨i, rfl⟩)⟩
    obtain ⟨e', c', hc', hM'⟩ := ih (Fin.init w) hind _ hM'fg inf_le_right hd' (Fin.init a)
      (fun i => ha _)
    obtain ⟨u1, u2, hre⟩ := rebase c' b (a (Fin.last n)) hc' hb (ha _) (e' (Fin.last n)) u
    refine ⟨Fin.snoc (Fin.snoc (Fin.init e') u1) u2, c' * b * (a (Fin.last n))⁻¹,
      mul_ne_zero (mul_ne_zero hc' hb) (inv_ne_zero (ha _)), ?_⟩
    rw [latSpanV_succ, Fin.init_snoc, Fin.init_snoc, Fin.snoc_last, Fin.snoc_last, latSpanV_succ,
      Fin.init_snoc, Fin.snoc_last]
    rw [hMe, hM', latSpanV_succ, Fin.init_snoc, Fin.snoc_last, sup_assoc, hre, ← sup_assoc]
end Formalism.L2.SG.Pf.LatEx
