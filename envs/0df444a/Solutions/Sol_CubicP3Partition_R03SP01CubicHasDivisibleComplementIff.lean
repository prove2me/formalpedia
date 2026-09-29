-- Prove2me | solution 1 for CubicP3Partition.R03SP01CubicHasDivisibleComplementIff
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T09:58:33.75616+00:00
-- url     : https://prove2.me/submissions/0996e6f3-9f68-4f05-b89c-ed794f819c0c

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

noncomputable section

set_option maxHeartbeats 1000000

/-- Bridge the canonical noncomputable degree to Mathlib's finite graph degree. -/
lemma R03SP01DegreeEqSimpleGraphDegree {X : Type u} [Fintype X]
    (H : SimpleGraph X) (x : X) [DecidableRel H.Adj] :
    CubicP3Partition.degree H x = H.degree x := by
  rw [CubicP3Partition.degree]
  rw [← H.card_neighborSet_eq_degree x]
  exact Nat.card_eq_fintype_card


end
end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hC : Cubic G) :
    HasDivisibleComplement G ↔ HasDivisibleTwoFactor G := by
  classical
  constructor
  · rintro ⟨M, _hM, hD⟩
    exact ⟨matchingComplement G M, hD⟩
  · rintro ⟨F, hF⟩
    let M : SimpleGraph V := G \ F
    have hMsub : M ≤ G := by
      intro x y hxy
      exact hxy.1
    have hGdeg (v : V) : G.degree v = 3 := by
      calc
        G.degree v = CubicP3Partition.degree G v :=
          (R03SP01DegreeEqSimpleGraphDegree G v).symm
        _ = 3 := hC v
    have hFdeg (v : V) : F.degree v = 2 := by
      calc
        F.degree v = CubicP3Partition.degree F v :=
          (R03SP01DegreeEqSimpleGraphDegree F v).symm
        _ = 2 := hF.1.2 v
    have hMdeg_mathlib (v : V) : M.degree v = 1 := by
      have hsubset : F.neighborFinset v ⊆ G.neighborFinset v := by
        intro w hw
        simp only [SimpleGraph.mem_neighborFinset] at hw ⊢
        exact hF.1.1 hw
      calc
        M.degree v = (M.neighborFinset v).card := rfl
        _ = (G.neighborFinset v \ F.neighborFinset v).card := by
          change ((G \ F).neighborFinset v).card = _
          rw [SimpleGraph.neighborFinset_sdiff]
        _ = (G.neighborFinset v).card - (F.neighborFinset v).card :=
          Finset.card_sdiff_of_subset hsubset
        _ = G.degree v - F.degree v := rfl
        _ = 3 - 2 := by rw [hGdeg v, hFdeg v]
        _ = 1 := by decide
    have hMdeg : ∀ v, CubicP3Partition.degree M v = 1 := by
      intro v
      calc
        CubicP3Partition.degree M v = M.degree v :=
          R03SP01DegreeEqSimpleGraphDegree M v
        _ = 1 := hMdeg_mathlib v
    have hcomp : matchingComplement G M = F := by
      ext x y
      simp only [matchingComplement, SimpleGraph.inf_adj, SimpleGraph.compl_adj]
      constructor
      · rintro ⟨hGxy, _hne, hnotM⟩
        by_contra hnotF
        apply hnotM
        change G.Adj x y ∧ ¬ F.Adj x y
        exact ⟨hGxy, hnotF⟩
      · intro hFxy
        have hGxy : G.Adj x y := hF.1.1 hFxy
        have hne : x ≠ y := by
          intro hxy
          subst y
          exact G.irrefl hGxy
        refine ⟨hGxy, hne, ?_⟩
        intro hM
        change G.Adj x y ∧ ¬ F.Adj x y at hM
        exact hM.2 hFxy
    refine ⟨M, ⟨hMsub, hMdeg⟩, ?_⟩
    rw [hcomp]
    exact hF

