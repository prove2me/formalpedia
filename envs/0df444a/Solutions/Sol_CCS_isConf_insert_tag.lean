-- Prove2me | solution 1 for CCS.isConf_insert_tag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:10:37.493406+00:00
-- url     : https://prove2.me/submissions/558b24b6-b460-4e08-8829-fc826a73a942

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Theorems.Thm_CCS_projL_isConf
import Theorems.Thm_CCS_projR_isConf
import Theorems.Thm_CCS_Action_strip_map
import Theorems.Thm_CCS_Label_co_co
import Theorems.Thm_CCS_Label_strip_map
import Theorems.Thm_GES_toFamily_Config
import Theorems.Thm_GES_toFamily_Event
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_PES_toFamily_Config
import Theorems.Thm_PES_toFamily_Event
import Theorems.Thm_SES_toFamily_Config
attribute [local simp] CCS.Action.strip_map
attribute [local simp] CCS.Label.co_co
attribute [local simp] CCS.Label.strip_map
attribute [local simp] GES.toFamily_Config
attribute [local simp] GES.toFamily_Event
attribute [local simp] PES.enables_iff
attribute [local simp] PES.toFamily_Config
attribute [local simp] PES.toFamily_Event
attribute [local simp] SES.toFamily_Config



set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
variable {c : Set (Tag E F)}
namespace CCS
theorem _root_.solution {t : Tag E F} (hc : (parSES E F).toGES.isConf c)
    (hL : ∀ x, t.evL = some x → E.toGES.isConf (projL c ∪ {x}) ∧ x ∉ projL c)
    (hR : ∀ y, t.evR = some y → F.toGES.isConf (projR c ∪ {y}) ∧ y ∉ projR c) :
    (parSES E F).toGES.isConf (c ∪ {t}) := by
  classical
  have hprojL : projL (c ∪ ({t} : Set (Tag E F))) = projL c ∪ {x | t.evL = some x} := by
    ext e
    constructor
    · rintro ⟨u, hu | hu, he⟩
      · exact Or.inl ⟨u, hu, he⟩
      · exact Or.inr ((Set.mem_singleton_iff.mp hu) ▸ he)
    · rintro (⟨u, hu, he⟩ | he)
      · exact ⟨u, Or.inl hu, he⟩
      · exact ⟨t, Or.inr rfl, he⟩
  have hprojR : projR (c ∪ ({t} : Set (Tag E F))) = projR c ∪ {y | t.evR = some y} := by
    ext f
    constructor
    · rintro ⟨u, hu | hu, he⟩
      · exact Or.inl ⟨u, hu, he⟩
      · exact Or.inr ((Set.mem_singleton_iff.mp hu) ▸ he)
    · rintro (⟨u, hu, he⟩ | he)
      · exact ⟨u, Or.inl hu, he⟩
      · exact ⟨t, Or.inr rfl, he⟩
  -- consistency
  have hconL : E.toGES.Consistent (projL (c ∪ ({t} : Set (Tag E F)))) := by
    rw [hprojL]
    cases hev : t.evL with
    | none =>
      have : {x | (none : Option E.Event) = some x} = (∅ : Set E.Event) := by ext e; simp
      rw [this, Set.union_empty]
      exact (projL_isConf hc).1
    | some x =>
      have : {z | (some x : Option E.Event) = some z} = ({x} : Set E.Event) := by
        ext z; simp [eq_comm]
      rw [this]
      exact (hL x hev).1.1
  have hconR : F.toGES.Consistent (projR (c ∪ ({t} : Set (Tag E F)))) := by
    rw [hprojR]
    cases hev : t.evR with
    | none =>
      have : {y | (none : Option F.Event) = some y} = (∅ : Set F.Event) := by ext f; simp
      rw [this, Set.union_empty]
      exact (projR_isConf hc).1
    | some y =>
      have : {z | (some y : Option F.Event) = some z} = ({y} : Set F.Event) := by
        ext z; simp [eq_comm]
      rw [this]
      exact (hR y hev).1.1
  refine ⟨fun W hW => ⟨fun t₁ h₁ t₂ h₂ => ⟨fun e he₁ he₂ => ?_, fun f hf₁ hf₂ => ?_⟩,
    fun V hV => hconL V (hV.trans (projL_mono hW)),
    fun V hV => hconR V (hV.trans (projR_mono hW))⟩, ?_⟩
  · -- injectivity on the left
    rcases hW (by exact_mod_cast h₁) with hm₁ | hm₁ <;>
      rcases hW (by exact_mod_cast h₂) with hm₂ | hm₂
    · exact (hc.1 {t₁, t₂} (by
        intro u hu
        rcases Finset.mem_insert.mp (by exact_mod_cast hu) with rfl | hu'
        · exact hm₁
        · exact (Finset.mem_singleton.mp hu') ▸ hm₂)).1 t₁ (Finset.mem_insert_self _ _) t₂
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) |>.1 e he₁ he₂
    · exact absurd ⟨t₁, hm₁, he₁⟩ ((hL e ((Set.mem_singleton_iff.mp hm₂) ▸ he₂)).2)
    · exact absurd ⟨t₂, hm₂, he₂⟩ ((hL e ((Set.mem_singleton_iff.mp hm₁) ▸ he₁)).2)
    · rw [Set.mem_singleton_iff] at hm₁ hm₂; rw [hm₁, hm₂]
  · -- injectivity on the right
    rcases hW (by exact_mod_cast h₁) with hm₁ | hm₁ <;>
      rcases hW (by exact_mod_cast h₂) with hm₂ | hm₂
    · exact (hc.1 {t₁, t₂} (by
        intro u hu
        rcases Finset.mem_insert.mp (by exact_mod_cast hu) with rfl | hu'
        · exact hm₁
        · exact (Finset.mem_singleton.mp hu') ▸ hm₂)).1 t₁ (Finset.mem_insert_self _ _) t₂
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) |>.2 f hf₁ hf₂
    · exact absurd ⟨t₁, hm₁, hf₁⟩ ((hR f ((Set.mem_singleton_iff.mp hm₂) ▸ hf₂)).2)
    · exact absurd ⟨t₂, hm₂, hf₂⟩ ((hR f ((Set.mem_singleton_iff.mp hm₁) ▸ hf₁)).2)
    · rw [Set.mem_singleton_iff] at hm₁ hm₂; rw [hm₁, hm₂]
  · -- securedness
    have hmono : ∀ {u : Tag E F}, u ∈ c →
        ∃ n, u ∈ (parSES E F).secApprox (c ∪ ({t} : Set (Tag E F))) n := by
      intro u hu
      obtain ⟨n, hn⟩ := hc.2 u hu
      exact ⟨n, GES.secApprox_mono_set Set.subset_union_left n hn⟩
    rintro u (hu | hu)
    · exact hmono hu
    · replace hu : u = t := hu
      subst hu
      -- cover each component's enabling set by tags of `c`
      obtain ⟨WL, hWLc, hWLen⟩ : ∃ W : Finset (Tag E F), ↑W ⊆ c ∧
          ∀ x, u.evL = some x → ∃ Y : Finset E.Event,
            (∀ e' ∈ Y, e' ∈ projL (W : Set (Tag E F))) ∧ E.enable Y x := by
        cases hev : u.evL with
        | none => exact ⟨∅, by simp, fun x hx => absurd hx (by simp)⟩
        | some x =>
          obtain ⟨k, hk⟩ : ∃ k, E.rank (projL c ∪ {x}) x = k + 1 := by
            have : E.rank (projL c ∪ {x}) x ≠ 0 := by
              intro h0
              have hmem := GES.rank_mem ((hL x hev).1.2 x (Or.inr rfl))
              rw [h0] at hmem
              exact hmem
            exact ⟨E.rank (projL c ∪ {x}) x - 1, by omega⟩
          obtain ⟨-, Y, hYsub, hYen⟩ := hk ▸ GES.rank_mem ((hL x hev).1.2 x (Or.inr rfl))
          have hYc : ↑Y ⊆ projL c := by
            intro y hy
            rcases GES.secApprox_subset _ (hYsub hy) with h | h
            · exact h
            · exact absurd (hk ▸ Nat.lt_succ_of_le (GES.rank_le (hYsub hy)) :
                E.rank (projL c ∪ {x}) y < E.rank (projL c ∪ {x}) x)
                (by rw [Set.mem_singleton_iff.mp h]; omega)
          obtain ⟨W, hWc, hWcov⟩ := exists_cover_L Y hYc
          exact ⟨W, hWc, fun x' hx' => ⟨Y, fun e' he' => hWcov (by exact_mod_cast he'),
            (Option.some.inj hx') ▸ hYen⟩⟩
      obtain ⟨WR, hWRc, hWRen⟩ : ∃ W : Finset (Tag E F), ↑W ⊆ c ∧
          ∀ y, u.evR = some y → ∃ Y : Finset F.Event,
            (∀ f' ∈ Y, f' ∈ projR (W : Set (Tag E F))) ∧ F.enable Y y := by
        cases hev : u.evR with
        | none => exact ⟨∅, by simp, fun y hy => absurd hy (by simp)⟩
        | some y =>
          obtain ⟨k, hk⟩ : ∃ k, F.rank (projR c ∪ {y}) y = k + 1 := by
            have : F.rank (projR c ∪ {y}) y ≠ 0 := by
              intro h0
              have hmem := GES.rank_mem ((hR y hev).1.2 y (Or.inr rfl))
              rw [h0] at hmem
              exact hmem
            exact ⟨F.rank (projR c ∪ {y}) y - 1, by omega⟩
          obtain ⟨-, Y, hYsub, hYen⟩ := hk ▸ GES.rank_mem ((hR y hev).1.2 y (Or.inr rfl))
          have hYc : ↑Y ⊆ projR c := by
            intro z hz
            rcases GES.secApprox_subset _ (hYsub hz) with h | h
            · exact h
            · exact absurd (hk ▸ Nat.lt_succ_of_le (GES.rank_le (hYsub hz)) :
                F.rank (projR c ∪ {y}) z < F.rank (projR c ∪ {y}) y)
                (by rw [Set.mem_singleton_iff.mp h]; omega)
          obtain ⟨W, hWc, hWcov⟩ := exists_cover_R Y hYc
          exact ⟨W, hWc, fun y' hy' => ⟨Y, fun f' hf' => hWcov (by exact_mod_cast hf'),
            (Option.some.inj hy') ▸ hYen⟩⟩
      obtain ⟨N, hN⟩ := GES.exists_bound (G := (parSES E F).toGES) (X := WL ∪ WR)
        fun g hg => by
          rcases Finset.mem_union.mp hg with h | h
          · exact hmono (hWLc (by exact_mod_cast h))
          · exact hmono (hWRc (by exact_mod_cast h))
      refine ⟨N + 1, Or.inr rfl, WL ∪ WR, hN, fun x hx => ?_, fun y hy => ?_⟩
      · exact (hWLen x hx).imp fun _ hY =>
          ⟨fun e' he' => projL_mono (by exact_mod_cast Finset.subset_union_left)
            (hY.1 e' he'), hY.2⟩
      · exact (hWRen y hy).imp fun _ hY =>
          ⟨fun f' hf' => projR_mono (by exact_mod_cast Finset.subset_union_right)
            (hY.1 f' hf'), hY.2⟩
end CCS
