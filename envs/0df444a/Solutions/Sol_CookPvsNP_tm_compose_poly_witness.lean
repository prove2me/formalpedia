-- Prove2me | solution 1 for CookPvsNP.tm_compose_poly_witness
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:30:07.080907+00:00
-- url     : https://prove2.me/submissions/bf78f3c2-f92b-4103-9e03-b431cc9fcb99

import Theorems.Thm_CookPvsNP_comp_run_bound
import Theorems.Thm_CookPvsNP_comp_budget
import Theorems.Thm_CookPvsNP_tm_output_length_le
import Theorems.Thm_CookPvsNP_tm_run_eq_of_halting

set_option autoImplicit false
open CookPvsNP

theorem solution
    {Sym₁ Sym₂ Sym₃ Γ₁ Γ₂ : Type}
    [Fintype Γ₁] [Fintype Γ₂]
    (ι₁ : Sym₁ ↪ Γ₁) (ι₂₁ : Sym₂ ↪ Γ₁) (M₁ : TM Γ₁) (k₁ : ℕ)
    (ι₂₂ : Sym₂ ↪ Γ₂) (ι₃ : Sym₃ ↪ Γ₂) (M₂ : TM Γ₂) (k₂ : ℕ)
    (f : List Sym₁ → List Sym₂) (g : List Sym₂ → List Sym₃)
    (h₁ : ∀ x : List Sym₁,
      M₁.HaltsWithin (x.length ^ k₁ + k₁) (x.map ι₁) ∧
      M₁.output (M₁.run (x.length ^ k₁ + k₁) (M₁.init (x.map ι₁))) =
        (f x).map (some ∘ ι₂₁))
    (h₂ : ∀ y : List Sym₂,
      M₂.HaltsWithin (y.length ^ k₂ + k₂) (y.map ι₂₂) ∧
      M₂.output (M₂.run (y.length ^ k₂ + k₂) (M₂.init (y.map ι₂₂))) =
        (g y).map (some ∘ ι₃)) :
    ∃ (Γ : Type) (_ : Fintype Γ) (j₁ : Sym₁ ↪ Γ) (j₃ : Sym₃ ↪ Γ)
      (M : TM Γ) (k : ℕ),
      ∀ x : List Sym₁,
        M.HaltsWithin (x.length ^ k + k) (x.map j₁) ∧
        M.output (M.run (x.length ^ k + k) (M.init (x.map j₁))) =
          (g (f x)).map (some ∘ j₃) := by
  obtain ⟨k, hk⟩ := CookPvsNP.comp_budget k₁ k₂
  let C := compTM ι₂₁ ι₂₂ M₁ M₂
  refine ⟨CompCell Γ₁ Γ₂, inferInstance, compInputEmbedding ι₁, compOutputEmbedding ι₃, C, k, ?_⟩
  intro x
  obtain ⟨t, ht, hhalt, hout⟩ := comp_run_bound ι₁ ι₂₁ ι₂₂ ι₃ M₁ M₂ x (f x) (g (f x))
    (x.length ^ k₁ + k₁) ((f x).length ^ k₂ + k₂) (h₁ x).1 (h₁ x).2 (h₂ (f x)).1 (h₂ (f x)).2
  have hlen := tm_output_length_le M₁ (x.length ^ k₁ + k₁) (x.map ι₁)
  rw [(h₁ x).2] at hlen
  simp only [List.length_map] at hlen
  have htk : t ≤ x.length ^ k + k := by
    apply le_trans ht
    apply le_trans _ (hk x.length)
    gcongr
    omega
  have hrun : C.run (x.length ^ k + k) (C.init (x.map (compInputEmbedding ι₁))) =
      C.run t (C.init (x.map (compInputEmbedding ι₁))) := by
    conv_lhs => rw [← Nat.sub_add_cancel htk]
    change C.step^[(x.length ^ k + k - t) + t] _ = _
    rw [Function.iterate_add_apply]
    exact tm_run_eq_of_halting C _ hhalt _
  constructor
  · change C.IsHalting (C.run (x.length ^ k + k) (C.init (x.map (compInputEmbedding ι₁))))
    rw [hrun]
    exact hhalt
  · rw [hrun]
    exact hout

#print axioms solution
