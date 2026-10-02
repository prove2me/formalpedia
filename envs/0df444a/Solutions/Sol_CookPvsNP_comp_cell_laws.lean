-- Prove2me | solution 1 for CookPvsNP.comp_cell_laws
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T06:27:19.636439+00:00
-- url     : https://prove2.me/submissions/1075d6c6-7190-49a3-a04d-95ccf950fb83

import Definitions.Def_CookPvsNP_comp_machine

set_option autoImplicit false

open CookPvsNP

private theorem unpack_pack {Γ₁ Γ₂ : Type} (c : CompCell Γ₁ Γ₂) :
    CompCell.unpack (CompCell.pack c) = c := by
  rcases c with ⟨one, two, setup, left, right, second, final⟩
  unfold CompCell.pack
  split
  · next h => simp_all [CompCell.unpack, CompCell.blank]
  · rfl

private theorem pack_injective {Γ₁ Γ₂ : Type} :
    Function.Injective (@CompCell.pack Γ₁ Γ₂) := by
  intro c d h
  have e := congrArg CompCell.unpack h
  simpa only [unpack_pack] using e

private theorem translate_image {Sym Γ₁ Γ₂ : Type}
    (ι₁ : Sym ↪ Γ₁) (ι₂ : Sym ↪ Γ₂) (x : Sym) :
    translateCell ι₁ ι₂ (ι₁ x) = some (ι₂ x) := by
  classical
  have h : ∃ s, ι₁ s = ι₁ x := ⟨x, rfl⟩
  unfold translateCell
  rw [dif_pos h]
  exact congrArg (fun s => some (ι₂ s)) (ι₁.injective (Classical.choose_spec h))

/-- Elementary laws for the already published concrete composition machine.
The packing map is injective, and transfer between the two symbol embeddings is exact. -/
theorem solution {Sym Γ₁ Γ₂ : Type} (ι₁ : Sym ↪ Γ₁) (ι₂ : Sym ↪ Γ₂) :
    (∀ c : CompCell Γ₁ Γ₂, CompCell.unpack (CompCell.pack c) = c) ∧
    Function.Injective (@CompCell.pack Γ₁ Γ₂) ∧
    (∀ x : Sym, translateCell ι₁ ι₂ (ι₁ x) = some (ι₂ x)) := by
  exact ⟨unpack_pack, pack_injective, translate_image ι₁ ι₂⟩

#print axioms solution
