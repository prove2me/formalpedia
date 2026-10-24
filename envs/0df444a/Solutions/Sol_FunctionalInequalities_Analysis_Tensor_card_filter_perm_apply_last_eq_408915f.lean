-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.card_filter_perm_apply_last_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:50:56.563011+00:00
-- url     : https://prove2.me/submissions/761635a9-0748-4b3b-bc97-007e3112f9f2

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Data.Fintype.Perm

noncomputable section
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.Tensor.card_perm_fiber_eq_card_subtype {d : ℕ} (j : Fin (d + 1)) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 1)) =>
      σ (Fin.last d) = j).card =
      Fintype.card {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j} := by
  classical
  let s : Finset (Equiv.Perm (Fin (d + 1))) :=
    Finset.univ.filter fun σ => σ (Fin.last d) = j
  let e : (↥s) ≃ {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j} :=
    { toFun := fun σ =>
        ⟨σ.1, (Finset.mem_filter.mp σ.2).2⟩
      invFun := fun σ =>
        ⟨σ.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.2⟩⟩
      left_inv := by
        intro σ
        rfl
      right_inv := by
        intro σ
        rfl }
  change s.card = _
  calc
    s.card = Fintype.card ↥s := (Fintype.card_coe s).symm
    _ = Fintype.card {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j} :=
      Fintype.card_congr e
private lemma FunctionalInequalities.Analysis.Tensor.card_perm_fiber_eq_card_perm_fiber {d : ℕ}
    (j j' : Fin (d + 1)) :
    Fintype.card {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j} =
      Fintype.card {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j'} := by
  let e :
      {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j} ≃
        {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j'} :=
    { toFun := fun σ =>
        ⟨Equiv.swap j j' * σ.1, by
          simp [Equiv.Perm.mul_apply, σ.2]⟩
      invFun := fun σ =>
        ⟨Equiv.swap j j' * σ.1, by
          simp [Equiv.Perm.mul_apply, σ.2]⟩
      left_inv := by
        intro σ
        simp [Equiv.swap_mul_self_mul]
      right_inv := by
        intro σ
        simp [Equiv.swap_mul_self_mul] }
  exact Fintype.card_congr e
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- Each value of `σ (last d)` is taken by exactly `d!` permutations of `Fin (d + 1)`. -/
theorem solution {d : ℕ} (k : Fin (d + 1)) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 1)) => σ (Fin.last d) = k).card =
      d.factorial := by
    classical
    let β : Fin (d + 1) → Type :=
      fun j => {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j}
    let e :
        Equiv.Perm (Fin (d + 1)) ≃ Σ j : Fin (d + 1), β j :=
      { toFun := fun σ => ⟨σ (Fin.last d), ⟨σ, rfl⟩⟩
        invFun := fun σ => σ.2.1
        left_inv := by
          intro σ
          rfl
        right_inv := by
          rintro ⟨j, ⟨σ, hσ⟩⟩
          cases hσ
          rfl }
    have hsum :
        ∑ j : Fin (d + 1), Fintype.card (β j) =
          (d + 1).factorial := by
      calc
        ∑ j : Fin (d + 1), Fintype.card (β j) =
            Fintype.card (Σ j : Fin (d + 1), β j) := by
              rw [Fintype.card_sigma]
        _ = Fintype.card (Equiv.Perm (Fin (d + 1))) :=
          Fintype.card_congr e.symm
        _ = (d + 1).factorial := by
          simp [Fintype.card_perm, Fintype.card_fin]
    have hconst :
        ∀ j : Fin (d + 1), Fintype.card (β j) =
          Fintype.card (β (Fin.last d)) := by
      intro j
      exact card_perm_fiber_eq_card_perm_fiber j (Fin.last d)
    have hmul :
        (d + 1) * Fintype.card (β (Fin.last d)) =
          (d + 1).factorial := by
      simpa [hconst] using hsum
    rw [Nat.factorial_succ] at hmul
    have hmulK :
        (d + 1) * Fintype.card (β k) =
          (d + 1) * d.factorial := by
      rw [hconst k]
      exact hmul
    rw [show
        (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 1)) =>
          σ (Fin.last d) = k).card =
          Fintype.card (β k) from card_perm_fiber_eq_card_subtype k]
    exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ d) hmulK
