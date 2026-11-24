-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_adjacent_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:34.90089+00:00
-- url     : https://prove2.me/submissions/73ba82c9-90c4-44aa-9fc5-6a17e8145539

import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_AntisymmetrizedProductEqFactorialSmulQdet
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_orderedProduct_adjacent_swap_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 Formalism.REAL TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (i : Fin m)
    (arg : Fin (m + 1) → ℂ) : doublyAntisymmetrizedProduct E (arg ∘ Equiv.swap i.castSucc i.succ) = doublyAntisymmetrizedProduct E arg := by
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  have key := orderedProduct_adjacent_swap_identity E i arg
  generalize hs : Equiv.swap i.castSucc i.succ = s at key ⊢
  have hsg : Equiv.Perm.sign s = -1 := by rw [← hs]; exact Equiv.Perm.sign_swap hne

  have hre : ∀ F : Equiv.Perm (Fin (m + 1)) → A,
      ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * F (σ * s) = -∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * F σ := by
    intro F
    rw [← Equiv.sum_comp (Equiv.mulRight s) (fun σ => ((Equiv.Perm.sign σ : ℤ) : A) * F σ)]
    simp [Equiv.Perm.sign_mul, hsg]
  have q1 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) τ) = -doublyAntisymmetrizedProduct E a := by
    intro a
    simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h := hre (fun σ => orderedTermProduct E a σ τ)
    rw [h, mul_neg]
  have q2 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ (τ * s)) = -doublyAntisymmetrizedProduct E a := by
    intro a
    simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
    have h := hre (fun τ => ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ τ)
    exact h
  have q3 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) (τ * s)) = doublyAntisymmetrizedProduct E a := by
    intro a
    simp only [← Finset.mul_sum]
    have h1 : ∀ τ, ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) (τ * s) =
        -∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ (τ * s) := by
      intro τ
      have h := hre (fun σ => orderedTermProduct E a σ (τ * s))
      exact h
    simp only [h1, mul_neg, Finset.sum_neg_distrib]
    have h := hre (fun τ => ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ τ)
    rw [h, neg_neg]
    simp only [doublyAntisymmetrizedProduct, Finset.mul_sum]
  have T_eq : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * (orderedTermProduct E a σ τ - orderedTermProduct E a (σ * s) τ - orderedTermProduct E a σ (τ * s) +
        orderedTermProduct E a (σ * s) (τ * s))) = 4 • doublyAntisymmetrizedProduct E a := by
    intro a
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [q1 a, q2 a, q3 a]
    simp only [doublyAntisymmetrizedProduct]
    abel
  have h4 : 4 • doublyAntisymmetrizedProduct E arg = 4 • doublyAntisymmetrizedProduct E (arg ∘ s) := by
    rw [← T_eq arg, ← T_eq (arg ∘ s)]
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => by rw [key σ τ]
  have h4' : (4 : ℂ) • doublyAntisymmetrizedProduct E arg = (4 : ℂ) • doublyAntisymmetrizedProduct E (arg ∘ s) := by
    rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h4
  exact (smul_right_injective A (by norm_num : (4 : ℂ) ≠ 0) h4').symm
end Formalism.HermitianLatticeCounting.P
