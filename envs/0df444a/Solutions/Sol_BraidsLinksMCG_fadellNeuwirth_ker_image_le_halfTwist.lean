-- Prove2me | solution 1 for BraidsLinksMCG.fadellNeuwirth_ker_image_le_halfTwist
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T23:43:25.920311+00:00
-- url     : https://prove2.me/submissions/1b5dcc17-fe8d-4a5e-9f7e-4a6e03fd31f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_standardGen_image_mem_halfTwist
import Theorems.Thm_BraidsLinksMCG_fadellNeuwirth_ker_le_range
import Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_free_on_standardGen
import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

/-- The standard loops generate, because a generator-matched isomorphism carries
them to the free generators. -/
theorem standardGen_closure_top (n : ℕ) :
    Subgroup.closure (Set.range (fun j : Fin n => standardGen n j)) = ⊤ := by
  obtain ⟨e, he⟩ := BraidsLinksMCG.puncturedPlaneGroup_free_on_standardGen n
  rw [eq_top_iff]
  intro x _
  have himg : (e.toMonoidHom : PuncturedPlaneGroup n → FreeGroup (Fin n))
      '' (Set.range (fun j : Fin n => standardGen n j))
      = Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n)) := by
    ext w
    constructor
    · rintro ⟨z, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (he j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨standardGen n j, ⟨j, rfl⟩, he j⟩
  have h2 : e x ∈ Subgroup.map e.toMonoidHom
      (Subgroup.closure (Set.range (fun j : Fin n => standardGen n j))) := by
    rw [MonoidHom.map_closure, himg, FreeGroup.closure_range_of]
    trivial
  obtain ⟨y, hy, hey⟩ := h2
  have : y = x := e.injective hey
  exact this ▸ hy

theorem _root_.solution (n : ℕ) :
    Subgroup.map (FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1)))
        (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker
      ≤ Subgroup.closure
          (Set.range (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)) := by
  refine le_trans (Subgroup.map_mono (BraidsLinksMCG.fadellNeuwirth_ker_le_range n)) ?_
  rw [MonoidHom.range_eq_map, ← standardGen_closure_top n,
    Subgroup.map_map, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨z, ⟨j, rfl⟩, rfl⟩
  exact BraidsLinksMCG.standardGen_image_mem_halfTwist n j

#print axioms solution
