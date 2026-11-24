-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:49.488441+00:00
-- url     : https://prove2.me/submissions/87cfd436-befd-4f1c-8ab8-1bccc5c5a494

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_map_mul_right_eq_modular
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_modular_eq_one_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.CovariantRepresentation
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
namespace Formalism.L2.SG.CovariantRepresentation
theorem _root_.solution (μ : Measure H) [IsHaarMeasure μ] (Γ : Subgroup H) [Countable Γ]
    [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (g : H) :
    μ.map (· * g) = μ := by

  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : H)
  have hVpos : 0 < μ V := measure_pos_of_mem_nhds μ hV1
  have hB : μ (V * K⁻¹) ≠ ∞ := (hV.mul hK.inv).measure_lt_top.ne

  set b : ℝ≥0 := (μ (V * K⁻¹) / μ V).toNNReal
  have hbd : ∀ r : H, modularCharacterFun r ≤ b := by
    intro r
    obtain ⟨s, hs, hsr⟩ := hcov r
    have hmul : modularCharacterFun r = modularCharacterFun (s * r) := by
      rw [modularCharacterFun_map_mul, modular_eq_one_of_mem μ Γ hK hcov hs, one_mul]
    rw [hmul]
    have h1 : (modularCharacterFun (s * r) : ℝ≥0∞) * μ V ≤ μ (V * K⁻¹) := by
      have e := congrArg (fun m : Measure H => m V) (map_mul_right_eq_modular μ (s * r))
      simp only [Measure.smul_apply, smul_eq_mul] at e
      rw [← e, Measure.map_apply (measurable_mul_const _) hV.measurableSet]
      refine measure_mono fun x hx => ?_
      have hx' : x * (s * r) ∈ V := hx
      have : x = (x * (s * r)) * (s * r)⁻¹ := by group
      rw [this]
      exact Set.mul_mem_mul hx' (Set.inv_mem_inv.2 hsr)
    have h2 : (modularCharacterFun (s * r) : ℝ≥0∞) ≤ μ (V * K⁻¹) / μ V :=
      (ENNReal.le_div_iff_mul_le (Or.inl hVpos.ne') (Or.inr hB)).2 h1
    have hne : μ (V * K⁻¹) / μ V ≠ ∞ := ENNReal.div_ne_top hB hVpos.ne'
    exact ENNReal.coe_le_coe.1 (h2.trans_eq (ENNReal.coe_toNNReal hne).symm)
  have hle : ∀ r : H, modularCharacterFun r ≤ 1 := by
    intro r
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt b h
    have := hbd (r ^ n)
    have e : modularCharacterFun (r ^ n) = modularCharacterFun r ^ n :=
      map_pow (modularCharacter (G := H)) r n
    rw [e] at this
    exact absurd this (not_le.2 hn)
  have hone : modularCharacterFun g = 1 := by
    refine le_antisymm (hle g) ?_
    have e : modularCharacterFun g * modularCharacterFun g⁻¹ = 1 := by
      rw [← modularCharacterFun_map_mul, mul_inv_cancel, modularCharacterFun_map_one]
    calc (1 : ℝ≥0) = modularCharacterFun g * modularCharacterFun g⁻¹ := e.symm
      _ ≤ modularCharacterFun g * 1 := by gcongr; exact hle g⁻¹
      _ = modularCharacterFun g := mul_one _
  rw [map_mul_right_eq_modular μ g, hone, ENNReal.coe_one, one_smul]
end Formalism.L2.SG.CovariantRepresentation
