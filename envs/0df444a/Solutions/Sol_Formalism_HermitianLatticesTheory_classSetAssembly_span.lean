-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:32:04.599996+00:00
-- url     : https://prove2.me/submissions/0baa764a-8791-46e7-8bdb-72bd7b3a4d19

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_sub_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_qsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_sum_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_nondeg
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_coord_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (x : V) :
    ∃ t : Fin n → ℚ, x = ∑ i, (t i : K) • u i := by
  classical
  let L : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) :=
    { toFun := fun r j => ∑ i, r i * Algebra.trace ℚ K (h (u i) (u j))
      map_add' := fun a b => by funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by funext j; simp [Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro r hr0
    exact classSetAssembly_coord_zero h hpos ι hι u hu r (fun j => congrFun hr0 j)
  obtain ⟨t, ht⟩ := (LinearMap.injective_iff_surjective.mp hinj)
    (fun j => Algebra.trace ℚ K (h x (u j)))
  refine ⟨t, ?_⟩
  have hz : x - ∑ i, (t i : K) • u i = 0 := by
    apply classSetAssembly_nondeg h hpos ι hι u hu
    intro j
    have e : ∑ i, t i * Algebra.trace ℚ K (h (u i) (u j)) = Algebra.trace ℚ K (h x (u j)) :=
      congrFun ht j
    rw [classSetAssembly_tr_sub_left, classSetAssembly_tr_sum_left, ← e, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [classSetAssembly_tr_qsmul_left]
  exact sub_eq_zero.mp hz
end Formalism.HermitianLatticesTheory
