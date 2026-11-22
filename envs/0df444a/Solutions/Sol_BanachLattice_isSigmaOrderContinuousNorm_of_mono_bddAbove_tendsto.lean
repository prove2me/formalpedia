-- Prove2me | solution 1 for BanachLattice.isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:40.364248+00:00
-- url     : https://prove2.me/submissions/80ab36a7-bf2e-4898-85b1-f2511693fc70

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Theorems.Thm_OrderConvergesTo_sub


set_option autoImplicit true
@[expose] public section
public section
open BanachLattice
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable [BanachLattice X]
namespace BanachLattice
theorem _root_.solution
    (h : ∀ {u : ℕ → X}, Monotone u → BddAbove (Set.range u) →
      ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x)) :
    IsSigmaOrderContinuousNorm X := by
  refine ⟨fun {u} hanti hnn hglb => ?_⟩
  -- Set v n = u 0 - u n; this is monotone, ≥ 0, bounded above by u 0.
  have hv_mono : Monotone (fun n => u 0 - u n) :=
    fun n m hnm => sub_le_sub_left (hanti hnm) _
  have hv_bdd : BddAbove (Set.range fun n => u 0 - u n) :=
    ⟨u 0, by
      rintro _ ⟨n, rfl⟩
      simpa using sub_nonneg.mpr (hnn n)⟩
  obtain ⟨x, hx_lub, hx_tend⟩ := h hv_mono hv_bdd
  -- u 0 - x is a lower bound of range u, hence ≤ 0 since IsGLB (range u) 0.
  have hub_le : u 0 - x ∈ lowerBounds (Set.range u) := by
    rintro _ ⟨n, rfl⟩
    have h1 : u 0 - u n ≤ x := hx_lub.1 ⟨n, rfl⟩
    exact sub_le_comm.mp h1
  have h_le_zero : u 0 - x ≤ 0 := hglb.2 hub_le
  -- u 0 - x ≥ 0 since x ≤ u 0.
  have hxle : x ≤ u 0 := hx_lub.2 (by
    rintro _ ⟨n, rfl⟩
    exact sub_le_self _ (hnn n))
  have h_ge_zero : (0 : X) ≤ u 0 - x := sub_nonneg.mpr hxle
  have hux_eq : u 0 - x = 0 := le_antisymm h_le_zero h_ge_zero
  -- Now u n = u 0 - (u 0 - u n) → u 0 - x = 0.
  have htend : Filter.Tendsto (fun n => u 0 - (u 0 - u n)) Filter.atTop (nhds (u 0 - x)) :=
    tendsto_const_nhds.sub hx_tend
  have hux : Filter.Tendsto u Filter.atTop (nhds (u 0 - x)) := by
    convert htend using 1
    ext n; abel
  rw [hux_eq] at hux
  exact hux
end BanachLattice
