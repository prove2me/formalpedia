-- Prove2me | solution 1 for BKAR.Forest.eq_of_mem_orderedCubeSimplex_of_notMem_collisionSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:43.582342+00:00
-- url     : https://prove2.me/submissions/bf5daf19-eb1e-489f-ab47-091d3ce46183

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Theorems.Thm_BKAR_Forest_sectorOrderRel_isAntisymm_of_notMem_collisionSet
import Theorems.Thm_BKAR_Forest_pairwise_sectorOrderRel_of_orderedSimplexParams
import Theorems.Thm_BKAR_Forest_mem_edgeOrders_iff
import Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeOrders


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order₁ order₂ : List (Edge V)}
    (horder₁ : order₁ ∈ F.edgeOrders) (horder₂ : order₂ ∈ F.edgeOrders)
    {u : F.EdgeParam → ℝ}
    (hno : u ∉ F.collisionSet)
    (hu₁ : u ∈ F.orderedCubeSimplex order₁)
    (hu₂ : u ∈ F.orderedCubeSimplex order₂) :
    order₁ = order₂ := by
  classical
  let r := F.sectorOrderRel u
  have : Std.Antisymm r :=
    F.sectorOrderRel_isAntisymm_of_notMem_collisionSet hno
  have hmem₁ : ∀ e ∈ order₁, e ∈ F.edges := by
    intro e he
    have hset := F.toFinset_eq_of_mem_edgeOrders horder₁
    rw [← hset]
    exact List.mem_toFinset.mpr he
  have hmem₂ : ∀ e ∈ order₂, e ∈ F.edges := by
    intro e he
    have hset := F.toFinset_eq_of_mem_edgeOrders horder₂
    rw [← hset]
    exact List.mem_toFinset.mpr he
  have hpair₁ : order₁.Pairwise r :=
    F.pairwise_sectorOrderRel_of_orderedSimplexParams u order₁ hmem₁ hu₁.2
  have hpair₂ : order₂.Pairwise r :=
    F.pairwise_sectorOrderRel_of_orderedSimplexParams u order₂ hmem₂ hu₂.2
  have hperm : order₁.Perm order₂ :=
    ((F.mem_edgeOrders_iff).mp horder₁).trans
      ((F.mem_edgeOrders_iff).mp horder₂).symm
  exact hperm.eq_of_pairwise' hpair₁ hpair₂
end BKAR.Forest
