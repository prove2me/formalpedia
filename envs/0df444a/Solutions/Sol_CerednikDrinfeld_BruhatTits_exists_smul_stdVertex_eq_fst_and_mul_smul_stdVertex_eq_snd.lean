-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fa0a1bb9-d9d7-53f8-9168-7dbc6c56a83c

import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Theorems.Thm_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (n : GL (Fin 2) K₀) (hn : (n : Matrix (Fin 2) (Fin 2) K₀) = !![1, 0; 0, algebraMap R K₀ ϖ])
    (s : R → GL (Fin 2) K₀) (hs : ∀ t : R, (s t : Matrix (Fin 2) (Fin 2) K₀) = !![algebraMap R K₀ t, 1; 1, 0])
    (d : (BruhatTits.tree R K₀).Dart) :
    ∃ (g : GL (Fin 2) K₀) (t : R),
      g • LT.LatticeTree.stdVertex R K₀ = d.fst ∧ (g * s t * n) • LT.LatticeTree.stdVertex R K₀ = d.snd := by
  obtain ⟨g₀, hg₀⟩ := LT.LatticeTree.exists_act_stdVertex_eq R K₀ d.fst
  have hg₀' : g₀ • LT.LatticeTree.stdVertex R K₀ = d.fst := hg₀
  obtain ⟨-, hs0, hnb, -, -⟩ := CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer R K₀ ϖ hϖ n hn s hs

  have hadj : (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) (g₀⁻¹ • d.snd) := by
    have := GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) g₀⁻¹ d.adj
    rwa [← hg₀', inv_smul_smul] at this
  rcases hnb _ hadj with h | ⟨t, ht⟩
  · refine ⟨g₀ * (s 0)⁻¹, 0, ?_, ?_⟩
    · have h0 : (s 0)⁻¹ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀ := by
        rw [inv_smul_eq_iff, hs0 0]
      rw [mul_smul, h0, hg₀']
    · rw [show g₀ * (s 0)⁻¹ * s 0 * n = g₀ * n by group, mul_smul, ← h, smul_inv_smul]
  · refine ⟨g₀, t, hg₀', ?_⟩
    rw [mul_assoc, mul_smul, ← ht, smul_inv_smul]

end S_CerednikDrinfeld_BruhatTits_exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd (solution)
