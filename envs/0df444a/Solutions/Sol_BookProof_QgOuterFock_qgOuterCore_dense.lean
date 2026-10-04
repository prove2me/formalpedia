-- Prove2me | solution 1 for BookProof.QgOuterFock.qgOuterCore_dense
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:40:10.697988+00:00
-- url     : https://prove2.me/submissions/706d17bd-7d98-4744-b725-e3d11c092065

import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa

set_option autoImplicit false

open scoped ENNReal

namespace P85787172

open BookProof.DirectSumEsa

theorem dsCore_dense_of {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℂ (G i)] (D : ∀ i, Submodule ℂ (G i))
    (hD : ∀ i, Dense ((D i : Submodule ℂ (G i)) : Set (G i))) :
    Dense ((dsCore D : Submodule ℂ (lp G 2)) : Set (lp G 2)) := by
  classical
  set S := (dsCore D).topologicalClosure with hS
  have hSc : IsClosed (S : Set (lp G 2)) := Submodule.isClosed_topologicalClosure _
  have hsingle : ∀ i (x : G i), lp.single 2 i x ∈ S := by
    intro i x
    have hx : x ∈ closure ((D i : Submodule ℂ (G i)) : Set (G i)) := by
      rw [(hD i).closure_eq]; trivial
    have hmap : Set.MapsTo (fun y : G i => lp.single 2 i y)
        ((D i : Submodule ℂ (G i)) : Set (G i)) ((dsCore D : Submodule ℂ (lp G 2)) : Set (lp G 2)) := by
      intro y hy
      refine ⟨?_, ?_⟩
      · refine Set.Finite.subset (Set.finite_singleton i) (fun j hj => ?_)
        by_contra hji
        exact hj (lp.single_apply_ne 2 i y hji)
      · intro j
        by_cases hji : j = i
        · subst hji
          rw [lp.single_apply_self]
          exact hy
        · rw [lp.single_apply_ne 2 i y hji]
          exact Submodule.zero_mem _
    have := map_mem_closure (lp.isometry_single (E := G) (p := 2) i).continuous hx hmap
    rw [hS, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact this
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, Set.eq_univ_iff_forall]
  intro f
  have hsum := lp.hasSum_single (E := G) (p := 2) (by simp) f
  refine hSc.mem_of_tendsto hsum (Filter.Eventually.of_forall fun s => ?_)
  exact Submodule.sum_mem _ (fun i _ => hsingle i (f i))

end P85787172

open BookProof.QgOuterFock BookProof.HermiteProductCore BookProof.DirectSumEsa in
theorem solution : Dense ((qgOuterCore : Submodule ℂ qgOuterFock) : Set qgOuterFock) := by
  exact P85787172.dsCore_dense_of _ (fun n => polyGaussCore_dense (d := n * 84))
