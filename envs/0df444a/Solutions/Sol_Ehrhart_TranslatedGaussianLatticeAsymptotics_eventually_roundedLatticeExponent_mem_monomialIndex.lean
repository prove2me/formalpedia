-- Prove2me | solution 1 for Ehrhart.TranslatedGaussianLatticeAsymptotics.eventually_roundedLatticeExponent_mem_monomialIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/323a1f15-689c-4439-9248-698b8b1819b5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TranslatedGaussianLatticeAsymptotics_roundedLatticeExponent_mem_scaledIntegerLattice
import Theorems.Thm_Ehrhart_TranslatedGaussianLatticeAsymptotics_tendsto_roundedLatticeExponent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TranslatedGaussianLatticeAsymptotics
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
namespace Ehrhart.TranslatedGaussianLatticeAsymptotics
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∀ᶠ k : ℕ in atTop,
      roundedLatticeExponent k u ∈
        LatticeAsymptotics.monomialIndex K k := by
  have hnear :
      ∀ᶠ k : ℕ in atTop,
        roundedLatticeExponent k u ∈ interior K.carrier :=
    (tendsto_roundedLatticeExponent u).eventually
      (isOpen_interior.mem_nhds hu)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hnear] with k hk hinterior
  exact ⟨hinterior,
    roundedLatticeExponent_mem_scaledIntegerLattice
      (lt_of_lt_of_le Nat.zero_lt_one hk) u⟩
end Ehrhart.TranslatedGaussianLatticeAsymptotics
