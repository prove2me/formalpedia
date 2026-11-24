-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_coord_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:29:29.542145+00:00
-- url     : https://prove2.me/submissions/ce2a4724-d228-4dc8-8297-8b2b7106aa7a

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_qsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_sum_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_nondeg
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_qindep

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
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (r : Fin n → ℚ)
    (hr : ∀ j, ∑ i, r i * Algebra.trace ℚ K (h (u i) (u j)) = 0) : r = 0 := by
  have hty : ∀ j, Algebra.trace ℚ K (h (∑ i, (r i : K) • u i) (u j)) = 0 := by
    intro j
    rw [classSetAssembly_tr_sum_left, ← hr j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [classSetAssembly_tr_qsmul_left]
  have h0 : ∑ i, (r i : K) • u i = 0 := classSetAssembly_nondeg h hpos ι hι u hu _ hty
  exact classSetAssembly_qindep (K := K) ι u hu r h0
end Formalism.HermitianLatticesTheory
