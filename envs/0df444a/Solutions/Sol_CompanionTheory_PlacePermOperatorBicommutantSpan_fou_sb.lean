-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.fou_sb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:30.811658+00:00
-- url     : https://prove2.me/submissions/58d6906e-6308-43a6-89b6-b7c36dffb7b2

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_of_mem
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_of_not
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_ind
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_smul
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_sum
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_span
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_level
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_co_perp
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_perp_perp
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_meas_perp
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_chi
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_fou_add
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_fou_smul
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_map_sum_sb
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_fou_ind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
variable (h : NADual V χ μ)
include h
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {φ : V → ℂ} (hφ : SB φ) : SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) := by
  have hh := h
  obtain ⟨_, _, -⟩ := hh
  obtain ⟨-, L, -, hL, -, -, hinv⟩ := sb_level h hφ
  obtain ⟨s, hs⟩ := sb_span hφ hL.2 hinv
  have hP := co_perp h hL
  have e1 : ∀ a, fou χ μ (ind a L) = ((μ L).toReal : ℂ) • fun y => ind 0 (perpG h L) y * χ y a := fun a => by
    funext y
    rw [fou_ind h hL, Pi.smul_apply, smul_eq_mul, chi_sym h y]; ring
  have e2 : ∀ a, SB (fou χ μ (ind a L)) := fun a => e1 a ▸ sb_smul _ (sb_chi h (sb_ind 0 hP) a)
  have e3 : fou χ μ φ = ∑ a ∈ s, φ a • fou χ μ (ind a L) := by
    conv_lhs => rw [hs]
    exact map_sum_sb (fun _ _ => fou_add h) (fun c f _ => fou_smul c f) s φ fun a => sb_ind a hL
  refine ⟨e3 ▸ sb_sum _ fun a _ => sb_smul _ (e2 a), fun x => ?_⟩
  rw [e3, map_sum_sb (fun _ _ => fou_add h) (fun c f _ => fou_smul c f) s φ e2]
  conv_rhs => rw [hs]
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun a _ => congrArg _ ?_
  have e4 : fou χ μ (fun y => ind 0 (perpG h L) y * χ y a) x = fou χ μ (ind 0 (perpG h L)) (a + x) := by
    simp only [fou, chi_add' h, mul_assoc]
  rw [e1, fou_smul, Pi.smul_apply, e4, fou_ind h hP, chi_zero h, mul_one, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
    meas_perp h hL, Complex.ofReal_one, one_mul]
  have e5 : a + x - 0 ∈ perpG h (perpG h L) ↔ -x - a ∈ L := by
    rw [perp_perp h hL, ← L.neg_mem_iff, sub_zero, neg_add_rev, sub_eq_add_neg]
  by_cases hx : -x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (e5.2 hx)]
  · rw [ind_of_not hx, ind_of_not (mt e5.1 hx)]
end CompanionTheory.PlacePermOperatorBicommutantSpan
