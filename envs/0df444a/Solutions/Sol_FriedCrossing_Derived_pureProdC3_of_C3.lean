-- Prove2me | solution 1 for FriedCrossing.Derived.pureProdC3_of_C3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:08:20.130451+00:00
-- url     : https://prove2.me/submissions/a4f43d26-5c06-4c1c-aade-5028dd56b809

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
import Theorems.Thm_FriedCrossing_Derived_zero_add_one_le_one
import Theorems.Thm_P2M_FriedCrossing_Derived_contDiff_E_f_5dcaf73df3dc

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
    ∃ K₂ : ℝ, PureProdC3 (E₂f M A) (pτ (E₂f M A)) (pτ (pτ (E₂f M A)))
      (pθ (pτ (pτ (E₂f M A)))) K₂ 1 := by
  have h3 := contDiff_E₂f h
  have h2 : ContDiff ℝ 2 fun q : ℝ × ℝ => pτ (E₂f M A) q.1 q.2 :=
    contDiff_pτ (f := E₂f M A) two_add_one_le_three h3
  have h1 : ContDiff ℝ 1 fun q : ℝ × ℝ => pτ (pτ (E₂f M A)) q.1 q.2 :=
    contDiff_pτ (f := pτ (E₂f M A)) one_add_one_le_two h2
  have h0 : ContDiff ℝ 0 fun q : ℝ × ℝ => pθ (pτ (pτ (E₂f M A))) q.1 q.2 :=
    contDiff_pθ (f := pτ (pτ (E₂f M A))) zero_add_one_le_one h1
  obtain ⟨K, hK, hb⟩ := bound_on_square h0.continuous
  exact ⟨K, hK,
    hasDerivAt_pτ (f := E₂f M A) (differentiable_of_contDiff two_add_one_le_three h3),
    hasDerivAt_pτ (f := pτ (E₂f M A)) (differentiable_of_contDiff one_add_one_le_two h2),
    hasDerivAt_pθ (f := pτ (pτ (E₂f M A))) (differentiable_of_contDiff zero_add_one_le_one h1),
    hb⟩
end FriedCrossing.Derived
