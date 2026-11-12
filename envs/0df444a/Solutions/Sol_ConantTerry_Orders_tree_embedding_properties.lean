-- Prove2me | solution 1 for ConantTerry.Orders.tree_embedding_properties
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:21:49.861119+00:00
-- url     : https://prove2.me/submissions/96c504cc-be9f-450b-87a2-22d41b0ac7cd

import Mathlib
import Definitions.Def_ConantTerry_Orders_tree_embeddings

section
set_option autoImplicit false
namespace ConantTerry.Dev.TEP
open ConantTerry.Orders

theorem trichotomy : ∀ (τ σ : List Bool), σ <+: τ ∨ (∃ a, (τ ++ [a]) <+: σ) ∨
    ∃ (ρ : List Bool) (a : Bool), (ρ ++ [a]) <+: σ ∧ (ρ ++ [!a]) <+: τ := by
  intro τ
  induction τ with
  | nil =>
    intro σ
    cases σ with
    | nil => exact Or.inl (List.prefix_refl _)
    | cons b σ' => exact Or.inr (Or.inl ⟨b, ⟨σ', by simp⟩⟩)
  | cons c τ' ih =>
    intro σ
    cases σ with
    | nil => exact Or.inl (List.nil_prefix)
    | cons b σ' =>
      by_cases hbc : b = c
      · subst hbc
        rcases ih σ' with h | ⟨a, h⟩ | ⟨ρ, a, h1, h2⟩
        · exact Or.inl (by simpa using h)
        · exact Or.inr (Or.inl ⟨a, by simpa using h⟩)
        · exact Or.inr (Or.inr ⟨b :: ρ, a, by simpa using h1, by simpa using h2⟩)
      · refine Or.inr (Or.inr ⟨[], b, by simp, ?_⟩)
        have : c = !b := by cases b <;> cases c <;> simp_all
        subst this
        simp

theorem core {D : List Bool → Prop} (hD : ∀ σ τ, σ <+: τ → D τ → D σ)
    (g : List Bool → List Bool)
    (H : ∀ σ τ a, D σ → D τ → σ ++ [a] <+: τ → g σ ++ [a] <+: g τ)
    {σ τ : List Bool} (hσ : D σ) (hτ : D τ) : σ <+: τ ↔ g σ <+: g τ := by
  constructor
  · rintro ⟨rest, rfl⟩
    cases rest with
    | nil => simp
    | cons a r =>
      exact (List.prefix_append (g σ) [a]).trans (H σ (σ ++ a :: r) a hσ hτ ⟨r, by simp⟩)
  · intro hg
    rcases trichotomy τ σ with h | ⟨a, h⟩ | ⟨ρ, a, h1, h2⟩
    · exact h
    · exfalso
      have := (H τ σ a hτ hσ h)
      have h3 := (this.length_le).trans hg.length_le
      simp at h3
    · exfalso
      have hρ : D ρ := hD ρ σ ((List.prefix_append _ _).trans h1) hσ
      have e1 := H ρ σ a hρ hσ h1
      have e2 := H ρ τ (!a) hρ hτ h2
      have p1 : g ρ ++ [a] <+: g τ := e1.trans hg
      have h4 := List.prefix_of_prefix_length_le p1 e2 (by simp)
      rw [List.prefix_append_right_inj] at h4
      cases a <;> simp at h4

/-- Total extension of a map on `WordsBelow s`. -/
noncomputable def ext {s t : ℕ} (φ : WordsBelow s → WordsBelow t) (σ : List Bool) : List Bool :=
  if h : σ.length < s then (φ ⟨σ, h⟩).val else []

theorem ext_of_lt {s t : ℕ} (φ : WordsBelow s → WordsBelow t) (σ : WordsBelow s) :
    ext φ σ.val = (φ σ).val := by
  simp only [ext, dif_pos σ.2]
  rfl

theorem ext_len {s t : ℕ} (φ : WordsBelow s → WordsBelow t) (σ : List Bool) (h : σ.length < s) :
    (ext φ σ).length < t := by
  simp only [ext, dif_pos h]
  exact (φ ⟨σ, h⟩).2

theorem ext_emb {s t : ℕ} (φ : WordsBelow s → WordsBelow t) (hφ : IsTreeEmbedding φ)
    (σ τ : List Bool) (a : Bool) (hσ : σ.length < s) (hτ : τ.length < s)
    (h : σ ++ [a] <+: τ) : ext φ σ ++ [a] <+: ext φ τ := by
  simp only [ext, dif_pos hσ, dif_pos hτ]
  exact hφ ⟨σ, hσ⟩ ⟨τ, hτ⟩ a h

theorem prefix_closed (s : ℕ) : ∀ σ τ : List Bool, σ <+: τ → τ.length < s → σ.length < s :=
  fun σ τ h hτ => lt_of_le_of_lt h.length_le hτ

/-- Extension to leaves. -/
noncomputable def ext2 {s t : ℕ} (φ : WordsBelow s → WordsBelow t) (σ : List Bool) : List Bool :=
  if σ.length < s then ext φ σ
  else ext φ σ.dropLast ++ σ.getLastD false :: List.replicate (t - (ext φ σ.dropLast).length - 1) false

theorem ext2_lt {s t : ℕ} (φ : WordsBelow s → WordsBelow t) (σ : List Bool) (h : σ.length < s) :
    ext2 φ σ = ext φ σ := by simp [ext2, h]

theorem ext2_leaf {s t : ℕ} (φ : WordsBelow s → WordsBelow t) (dl : List Bool) (b : Bool)
    (h : dl.length + 1 = s) :
    ext2 φ (dl ++ [b]) = ext φ dl ++ b :: List.replicate (t - (ext φ dl).length - 1) false := by
  have : ¬ (dl ++ [b]).length < s := by simp; omega
  rw [ext2, if_neg this]
  simp

theorem ext2_len {s t : ℕ} (φ : WordsBelow s → WordsBelow t) (σ : List Bool)
    (hs1 : 1 ≤ s) (h : σ.length ≤ s) : (ext2 φ σ).length ≤ t ∧ (σ.length = s → (ext2 φ σ).length = t) := by
  by_cases hl : σ.length < s
  · rw [ext2_lt φ σ hl]
    exact ⟨(ext_len φ σ hl).le, fun h' => by omega⟩
  · have hs : σ.length = s := by omega
    obtain rfl | ⟨dl, b, rfl⟩ := List.eq_nil_or_concat σ
    · simp at hs
      omega
    · simp only [List.concat_eq_append] at *
      have hdl : dl.length + 1 = s := by simpa using hs
      rw [ext2_leaf φ dl b hdl]
      have := ext_len φ dl (by omega)
      simp
      omega

theorem ext2_emb {s t : ℕ} (φ : WordsBelow s → WordsBelow t) (hφ : IsTreeEmbedding φ)
    (σ τ : List Bool) (a : Bool) (hσ : σ.length ≤ s) (hτ : τ.length ≤ s)
    (h : σ ++ [a] <+: τ) : ext2 φ σ ++ [a] <+: ext2 φ τ := by
  have hlen := h.length_le
  simp at hlen
  have hσ' : σ.length < s := by omega
  rw [ext2_lt φ σ hσ']
  by_cases hτ' : τ.length < s
  · rw [ext2_lt φ τ hτ']
    exact ext_emb φ hφ σ τ a hσ' hτ' h
  · have hs : τ.length = s := by omega
    obtain rfl | ⟨dl, b, rfl⟩ := List.eq_nil_or_concat τ
    · simp at h
    · simp only [List.concat_eq_append] at *
      have hdl : dl.length + 1 = s := by simpa using hs
      rw [ext2_leaf φ dl b hdl]
      rcases List.prefix_concat_iff.1 h with h1 | h1
      · obtain ⟨e1, e2⟩ := List.append_inj' h1 (by simp)
        subst e1
        simp at e2
        subst e2
        exact (List.prefix_append_right_inj _).2 ⟨List.replicate (t - (ext φ σ).length - 1) false, by simp⟩
      · have := ext_emb φ hφ σ dl a hσ' (by omega) h1
        exact this.trans (List.prefix_append _ _)

end ConantTerry.Dev.TEP

namespace ConantTerry.Orders
open ConantTerry.Dev.TEP in
theorem chk_tree_embedding_properties :
    (∀ (s t : ℕ), 1 ≤ s → 1 ≤ t →
      ∀ φ : WordsBelow s → WordsBelow t, IsTreeEmbedding φ →
        (∀ σ τ : WordsBelow s,
          List.IsPrefix σ.val τ.val ↔ List.IsPrefix (φ σ).val (φ τ).val) ∧
        Function.Injective φ) ∧
    ((∀ (s t u : ℕ), 1 ≤ s → 1 ≤ t → 1 ≤ u →
      ∀ (φ : WordsBelow s → WordsBelow t) (ψ : WordsBelow t → WordsBelow u),
        IsTreeEmbedding φ → IsTreeEmbedding ψ →
          IsTreeEmbedding (ψ ∘ φ) ∧
          (IsProperBelow φ → IsProperBelow ψ → IsProperBelow (ψ ∘ φ))) ∧
     (∀ (s t u : ℕ), 1 ≤ s → 1 ≤ t → 1 ≤ u →
      ∀ (φ : WordsAtMost s → WordsAtMost t) (ψ : WordsAtMost t → WordsAtMost u),
        IsTreeEmbedding φ → IsTreeEmbedding ψ →
          IsTreeEmbedding (ψ ∘ φ) ∧
          (IsProperEmbedding φ → IsProperEmbedding ψ → IsProperEmbedding (ψ ∘ φ)))) ∧
    (∀ (s t : ℕ), 1 ≤ s → 1 ≤ t →
      ∀ φ : WordsAtMost s → WordsAtMost t, IsProperEmbedding φ →
        ∀ σ : WordsAtMost s, σ.val.length < s → (φ σ).val.length < t) ∧
    (∀ (s t : ℕ), 1 ≤ s → 1 ≤ t →
      ∀ φ : WordsBelow s → WordsBelow t, IsTreeEmbedding φ →
        ∃ ψ : WordsAtMost s → WordsAtMost t,
          IsProperEmbedding ψ ∧
          ∀ σ : WordsBelow s, (ψ (nodeInclusion σ)).val = (φ σ).val) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro s t _ _ φ hφ
    have key : ∀ σ τ : WordsBelow s, List.IsPrefix σ.val τ.val ↔ List.IsPrefix (φ σ).val (φ τ).val := by
      intro σ τ
      have := core (D := fun σ => σ.length < s) (prefix_closed s) (ext φ)
        (fun σ τ a hσ hτ h => ext_emb φ hφ σ τ a hσ hτ h) σ.2 τ.2
      rwa [ext_of_lt, ext_of_lt] at this
    refine ⟨key, ?_⟩
    intro σ τ h
    have h1 := (key σ τ).2 (by rw [h])
    have h2 := (key τ σ).2 (by rw [h])
    exact Subtype.ext (h1.eq_of_length (h1.length_le.antisymm h2.length_le))
  · intro s t u _ _ _ φ ψ hφ hψ
    refine ⟨fun σ τ a h => hψ (φ σ) (φ τ) a (hφ σ τ a h), ?_⟩
    intro hpφ hpψ
    exact ⟨fun σ τ a h => hψ (φ σ) (φ τ) a (hφ σ τ a h),
      fun σ hσ => hpψ.2 (φ σ) (hpφ.2 σ hσ)⟩
  · intro s t u _ _ _ φ ψ hφ hψ
    refine ⟨fun σ τ a h => hψ (φ σ) (φ τ) a (hφ σ τ a h), ?_⟩
    intro hpφ hpψ
    exact ⟨fun σ τ a h => hψ (φ σ) (φ τ) a (hφ σ τ a h),
      fun σ hσ => hpψ.2 (φ σ) (hpφ.2 σ hσ)⟩
  · intro s t _ _ φ hφ σ hσ
    have hl : (σ.val ++ List.replicate (s - σ.val.length) false).length ≤ s := by simp; omega
    have hs : (σ.val ++ List.replicate (s - σ.val.length) false).length = s := by simp; omega
    have hp : σ.val ++ [false] <+: σ.val ++ List.replicate (s - σ.val.length) false := by
      have : s - σ.val.length = (s - σ.val.length - 1) + 1 := by omega
      rw [this, List.replicate_succ]
      exact ⟨List.replicate (s - σ.val.length - 1) false, by simp⟩
    have := hφ.1 σ ⟨_, hl⟩ false hp
    have h2 := hφ.2 ⟨_, hl⟩ hs
    have h3 := this.length_le
    simp only [List.length_append, List.length_singleton] at h3
    omega
  · intro s t hs _ φ hφ
    refine ⟨fun σ => ⟨ext2 φ σ.val, (ext2_len φ σ.val hs σ.2).1⟩, ⟨?_, ?_⟩, ?_⟩
    · intro σ τ a h
      exact ext2_emb φ hφ σ.val τ.val a σ.2 τ.2 h
    · intro σ hσ
      exact (ext2_len φ σ.val hs σ.2).2 hσ
    · intro σ
      have := ext2_lt φ σ.val σ.2
      simp only [nodeInclusion]
      rw [this, ext_of_lt]

end ConantTerry.Orders
end

theorem solution : type_of% @ConantTerry.Orders.chk_tree_embedding_properties := @ConantTerry.Orders.chk_tree_embedding_properties
