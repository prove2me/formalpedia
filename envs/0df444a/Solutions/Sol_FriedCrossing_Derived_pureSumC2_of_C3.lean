-- Prove2me | solution 1 for FriedCrossing.Derived.pureSumC2_of_C3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:06:56.072863+00:00
-- url     : https://prove2.me/submissions/1331790b-3d12-4f30-9657-7f6f1f7b5b87

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_p__ad8317175eea
import Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_p__e5b14daf2b02
import Theorems.Thm_FriedCrossing_Regularity_differentiable_of_contDiff
import Theorems.Thm_P2M_FriedCrossing_Regularity_contDiff_p__7eb957c067a9
import Theorems.Thm_P2M_FriedCrossing_Regularity_contDiff_p__a098e3e32f33
import Theorems.Thm_FriedCrossing_Regularity_bound_on_square
import Theorems.Thm_FriedCrossing_Derived_two_add_one_le_three
import Theorems.Thm_FriedCrossing_Derived_one_add_one_le_two
import Theorems.Thm_P2M_FriedCrossing_Derived_contDiff_E_f_b048a987d2d2

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (h : ClusterC3 M A) :
    ∃ K₁ : ℝ, PureSumC2 (E₁f M A) (pτ (E₁f M A)) (pθ (pτ (E₁f M A))) K₁ 1 := by
  have h3 := contDiff_E₁f h
  have h2 : ContDiff ℝ 2 fun q : ℝ × ℝ => pτ (E₁f M A) q.1 q.2 :=
    contDiff_pτ (f := E₁f M A) two_add_one_le_three h3
  have h1 : ContDiff ℝ 1 fun q : ℝ × ℝ => pθ (pτ (E₁f M A)) q.1 q.2 :=
    contDiff_pθ (f := pτ (E₁f M A)) one_add_one_le_two h2
  obtain ⟨K, hK, hb⟩ := bound_on_square h1.continuous
  exact ⟨K, hK, one_pos,
    hasDerivAt_pτ (f := E₁f M A) (differentiable_of_contDiff two_add_one_le_three h3),
    hasDerivAt_pθ (f := pτ (E₁f M A)) (differentiable_of_contDiff one_add_one_le_two h2), hb⟩
end FriedCrossing.Derived
