-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.modular_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:07.126903+00:00
-- url     : https://prove2.me/submissions/ee731b3b-a243-4fd4-8dce-3337b26ec4ab

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Theorems.Thm_CompanionTheory_LimBd_URep_pairing_right
import Theorems.Thm_CompanionTheory_LimBd_URep_pairing_self
import Theorems.Thm_CompanionTheory_LimBd_URep_integral_sq_pos
import Theorems.Thm_CompanionTheory_LimBd_URep_exists_op_right
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace CompanionTheory.LimBd.URep
theorem _root_.solution {π : UnitaryRep G H} [Nontrivial H] (hπ : SqInt μ π) (h : G) :
    Measure.modularCharacterFun h = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨A, hA⟩ := exists_op_right hπ hπ v v
  set s := ∫ g, ‖⟪v, π g v⟫_ℂ‖ ^ 2 ∂μ
  have hs : 0 < s := integral_sq_pos hπ hv
  have hb : ∀ g : G, (Measure.modularCharacterFun g : ℝ) ≤ ‖A‖ * ‖v‖ ^ 2 / s := by
    intro g
    have e := pairing_right (μ := μ) π π v v v v g
    rw [hA, pairing_self] at e
    have e2 := congrArg norm e
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _),
      Real.norm_of_nonneg hs.le] at e2
    rw [le_div_iff₀ hs, ← e2]
    calc ‖⟪π g v, A (π g v)⟫_ℂ‖ ≤ ‖π g v‖ * ‖A (π g v)‖ := norm_inner_le_norm _ _
      _ ≤ ‖π g v‖ * (‖A‖ * ‖π g v‖) := by gcongr; exact A.le_opNorm _
      _ = ‖A‖ * ‖v‖ ^ 2 := by simp; ring
  have hle : ∀ g : G, (Measure.modularCharacterFun g : ℝ) ≤ 1 := by
    intro g
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖A‖ * ‖v‖ ^ 2 / s) hlt
    have := hb (g ^ n)
    have e : Measure.modularCharacterFun (g ^ n) = Measure.modularCharacterFun g ^ n :=
      map_pow (Measure.modularCharacter (G := G)) g n
    rw [e] at this
    push_cast at this
    linarith
  have hm : (Measure.modularCharacterFun h : ℝ) * Measure.modularCharacterFun h⁻¹ = 1 := by
    rw [← NNReal.coe_mul, ← Measure.modularCharacterFun_map_mul, mul_inv_cancel,
      Measure.modularCharacterFun_map_one, NNReal.coe_one]
  have h1 := hle h
  have h2 := hle h⁻¹
  have h3 : (0 : ℝ) ≤ Measure.modularCharacterFun h := NNReal.coe_nonneg _
  have : (Measure.modularCharacterFun h : ℝ) = 1 := by nlinarith
  exact_mod_cast this
end CompanionTheory.LimBd.URep
