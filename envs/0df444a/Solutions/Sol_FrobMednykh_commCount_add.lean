-- Prove2me | solution 1 for FrobMednykh.commCount_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:46:55.728935+00:00
-- url     : https://prove2.me/submissions/8d1e96a6-c2ef-42c8-824e-88cca7a42fcd

import Mathlib
import Definitions.Def_FrobMednykh_defs

open CategoryTheory
open FrobMednykh
theorem fm_commProd_append {G : Type} [Group G] {m n : ℕ} (x : Fin m → G × G) (y : Fin n → G × G) :
    commProd (Fin.append x y) = commProd x * commProd y := by
  unfold commProd
  rw [List.ofFn_add, List.prod_append]
  congr 2
  · congr 1
    funext i
    have : (i.castLE (Nat.le_add_right m n)) = Fin.castAdd n i := rfl
    rw [this, Fin.append_left]
  · congr 1
    funext i
    rw [Fin.append_right]

theorem fm_add (G : Type) [Group G] [Fintype G] (g₁ g₂ : ℕ) (w : G) :
    commCount G (g₁ + g₂) w = ∑ σ : G, commCount G g₁ (w * σ⁻¹) * commCount G g₂ σ := by
  classical
  unfold commCount
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e := Fin.appendEquiv (α := G × G) g₁ g₂
  rw [← Finset.card_map ⟨Fin.appendEquiv (α := G × G) g₁ g₂ |>.symm, Equiv.injective _⟩]
  have hset : (Finset.univ.filter (fun x : Fin (g₁ + g₂) → G × G => commProd x = w)).map
      ⟨(Fin.appendEquiv (α := G × G) g₁ g₂).symm, Equiv.injective _⟩ =
      Finset.univ.filter (fun p : (Fin g₁ → G × G) × (Fin g₂ → G × G) =>
        commProd p.1 * commProd p.2 = w) := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← fm_commProd_append]
      convert hx
      exact (Fin.appendEquiv g₁ g₂).apply_symm_apply x
    · intro hp
      refine ⟨Fin.appendEquiv g₁ g₂ p, ?_, (Fin.appendEquiv g₁ g₂).symm_apply_apply p⟩
      rw [← hp]
      exact fm_commProd_append p.1 p.2
  rw [hset, Finset.card_eq_sum_card_fiberwise (f := fun p => commProd p.2) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.card_product]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [← h1, h2, mul_inv_cancel_right]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1, h2, inv_mul_cancel_right]

theorem solution (G : Type) [Group G] [Fintype G] (g₁ g₂ : ℕ) (w : G) :
    commCount G (g₁ + g₂) w = ∑ σ : G, commCount G g₁ (w * σ⁻¹) * commCount G g₂ σ := by
  exact fm_add G g₁ g₂ w


