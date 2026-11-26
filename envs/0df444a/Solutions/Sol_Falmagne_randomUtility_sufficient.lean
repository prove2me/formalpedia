-- Prove2me | solution 1 for Falmagne.randomUtility_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:45.576114+00:00
-- url     : https://prove2.me/submissions/148fdf58-d174-4bdd-aa88-c0458a8ed9ac

module
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_PathChoice
public import Definitions.Def_EconomicsNextProof_Flow
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Theorems.Thm_EconomicsNextProof_upperSum_upperMobius
public import Theorems.Thm_Falmagne_blockMarschak_isFlow
public import Theorems.Thm_Falmagne_flow_decomposition
public import Theorems.Thm_Falmagne_mem_edgeSupport
public import Theorems.Thm_Falmagne_mem_lowerContour
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_eq_rankingEdge
public import Theorems.Thm_Falmagne_pathFlow_nil
public import Theorems.Thm_Falmagne_rankingEdge_eq_zero_of_not_mem
public import Theorems.Thm_Falmagne_upperSum_lawFlow
attribute [local simp] Falmagne.mem_edgeSupport
attribute [local simp] Falmagne.mem_lowerContour
attribute [local simp] Falmagne.pathFlow_cons
attribute [local simp] Falmagne.pathFlow_nil
attribute [local simp] Falmagne.rankingEdge_eq_zero_of_not_mem



set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
namespace Falmagne
theorem _root_.solution {p : Finset X → X → ℝ}
    (hp : IsChoiceRule p) (hBM : BlockMarschakNonnegative p) :
    RandomUtilityRepresentable p := by
  obtain ⟨w, hnonneg, hrank, hmass, hflow⟩ :=
    flow_decomposition (blockMarschak_isFlow p hp hBM)
  refine ⟨w, ⟨hnonneg, hrank, hmass⟩, ?_⟩
  intro A x
  by_cases hx : x ∈ A
  · have hwflow : ∀ B, x ∈ B → lawFlow w x B = blockMarschak p x B := by
      intro B hxB
      calc
        lawFlow w x B = w.sum (fun l a => a * pathFlow l x B) := by
          unfold lawFlow Finsupp.sum
          apply Finset.sum_congr rfl
          intro l hl
          change w l * rankingEdge l x B = w l * pathFlow l x B
          rw [pathFlow_eq_rankingEdge (hrank l hl)]
        _ = blockMarschak p x B := hflow x B hxB
    calc
      p A x = upperSum (blockMarschak p x) A := by
        exact (congrFun (upperSum_upperMobius (fun B => p B x)) A).symm
      _ = upperSum (lawFlow w x) A := by
        unfold upperSum
        apply Finset.sum_congr rfl
        intro B hB
        exact (hwflow B ((Finset.mem_filter.mp hB).2 hx)).symm
      _ = w.sum (fun l a => a * rankingChoice l A x) :=
        upperSum_lawFlow w hrank x A hx
  · rw [hp.2.1 A x hx]
    simp [rankingChoice, hx]
end Falmagne
