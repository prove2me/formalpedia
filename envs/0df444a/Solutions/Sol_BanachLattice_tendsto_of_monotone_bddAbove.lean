-- Prove2me | solution 1 for BanachLattice.tendsto_of_monotone_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:36.91789+00:00
-- url     : https://prove2.me/submissions/8c0e114b-2482-4598-b6a5-9540592aceb0

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Theorems.Thm_IsSigmaOrderContinuousNorm_tendsto_of_monotone_isLUB


set_option autoImplicit true
@[expose] public section
public section
open BanachLattice
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]
namespace BanachLattice
theorem _root_.solution [IsOrderContinuousNorm X]
    {u : ℕ → X} (hmono : Monotone u) (hbd : BddAbove (Set.range u)) :
    ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x) := by
  -- Order continuity implies order completeness, hence σ-order completeness;
  -- σ-OC gives the LUB and σ-order continuity of the norm gives convergence.
  let : ConditionallyCompleteLattice X :=
    conditionallyCompleteLatticeOfIsOrderContinuousNorm
  have hx : IsLUB (Set.range u) (sSup (Set.range u)) :=
    ⟨fun _ ha => le_csSup hbd ha,
      fun _ ha => csSup_le (Set.range_nonempty u) ha⟩
  exact ⟨_, hx, IsSigmaOrderContinuousNorm.tendsto_of_monotone_isLUB hmono hx⟩
end BanachLattice
