-- Prove2me | solution 1 for BSLambda.LLL.radiusTwoEvent_subset_biUnion_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:28:52.679795+00:00
-- url     : https://prove2.me/submissions/86e7d659-4188-4aff-abcf-be2dfddcefdb

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_mem_radiusTwoEvent

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
open scoped Classical
namespace BSLambda.LLL
theorem _root_.solution (Arc : ι → ι → Bool) (S : Finset ι) :
    radiusTwoEvent (r := r) Arc S ⊆ S.biUnion fun h =>
      Finset.univ.filter fun ω : GateCfg ι r => IntObstruction Arc 2 S h (toGamma ω) := by
  intro ω hω
  rw [mem_radiusTwoEvent] at hω
  obtain ⟨h, hh, hobs⟩ := hω
  exact Finset.mem_biUnion.mpr ⟨h, hh, (Finset.mem_filter_univ _).mpr hobs⟩
end BSLambda.LLL
