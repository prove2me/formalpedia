-- Prove2me | solution 1 for Ehrhart.TranslatedGaussianLatticeAsymptotics.roundedLatticeExponent_mem_scaledIntegerLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/e06e0467-ca83-48b9-bb4c-66874b1c9c51

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
theorem _root_.solution {n : ℕ}
    {k : ℕ} (hk : 0 < k) (u : Space n) :
    roundedLatticeExponent k u ∈
      LatticeAsymptotics.scaledIntegerLattice n k := by
  rw [LatticeAsymptotics.mem_scaledIntegerLattice_iff hk]
  intro i
  refine ⟨⌊(k : ℝ) * u i⌋, ?_⟩
  dsimp [roundedLatticeExponent]
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  field_simp
end Ehrhart.TranslatedGaussianLatticeAsymptotics
