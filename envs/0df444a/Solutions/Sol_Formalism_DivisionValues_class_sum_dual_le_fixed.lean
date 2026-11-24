-- Prove2me | solution 1 for Formalism.DivisionValues.class_sum_dual_le_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:16.602281+00:00
-- url     : https://prove2.me/submissions/1af60e51-e1af-4f4b-a4fe-bd30678c693a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_mem_valLatF
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_avg_coe
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_card_ne
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_inv_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open exponent_index_lattice ValuationLatticeField
namespace Formalism.DivisionValues
theorem _root_.solution : ClassSumDualLeF := by
  classical
  intro K _ _ _ n H Cl _ V _ _ _ _ _ pair hs hn Gam _ _ ρ hiso I hI hCS Nab Del hNab s hDel hstab y hy
  rw [mem_valLatF]
  intro c0
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hy
  have hyinv : ∀ c γ, ρ c γ (I y c) = I y c := (hI (I y)).mp ⟨y, rfl⟩
  set N : K := (Fintype.card (Gam c0) : K) with hN
  have hN0 : N ≠ 0 := card_ne (K := K) (Γ := Gam c0)
  let z0 : invSub (ρ c0) := ⟨N⁻¹ • I y c0, (invSub (ρ c0)).smul_mem _ (hyinv c0)⟩
  have hz0 : z0 ∈ Formalism.HermitianLatticesTheory.dual (pair.domRestrict₁₂ (invSub (ρ c0)) (invSub (ρ c0)))
      ((Nab c0).comap ((invSub (ρ c0)).subtype.restrictScalars (𝓞 K))) := by
    rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro x0 hx0
    have hx0' : (x0 : V) ∈ Nab c0 := hx0
    have hinv : ∀ c γ, ρ c γ ((Pi.single c0 (x0 : V) : Cl → V) c) = (Pi.single c0 (x0 : V) : Cl → V) c := by
      intro c γ
      by_cases h : c = c0
      · subst h
        simpa using x0.2 γ
      · simp [Pi.single_eq_of_ne h]
    obtain ⟨x, hx⟩ := (hI _).mpr hinv
    have hxN : x ∈ valLatF I Nab := by
      rw [mem_valLatF, hx]
      intro c
      by_cases h : c = c0
      · subst h
        simpa using hx0'
      · simp [Pi.single_eq_of_ne h]
    have h1 := hy x hxN
    rw [hCS, hx, Finset.sum_eq_single c0 (by
      intro c _ h
      simp [Pi.single_eq_of_ne h]) (by simp)] at h1
    rw [LinearMap.domRestrict₁₂_apply]
    change pair (x0 : V) (N⁻¹ • I y c0) ∈ _
    rw [map_smul, smul_eq_mul]
    simpa using h1
  rw [inv_dual (ρ c0) pair hs hn (hiso c0) (Nab c0) (hNab c0)] at hz0
  obtain ⟨δ, hδ, hδz⟩ := Submodule.mem_map.mp hz0
  have h2 : N⁻¹ • ∑ γ, ρ c0 γ δ = N⁻¹ • I y c0 := by
    have := congrArg (Subtype.val) hδz
    rw [← avg_coe]
    exact this
  have h3 : ∑ γ, ρ c0 γ δ = I y c0 := by
    have := congrArg (fun v => N • v) h2
    simpa [smul_smul, hN0] using this
  rw [LinearMap.map_smul_of_tower, Pi.smul_apply, ← h3, Finset.smul_sum]
  refine Submodule.sum_mem _ fun γ _ => ?_
  rw [← LinearMap.map_smul_of_tower]
  exact hstab c0 γ _ (hDel c0 δ hδ)
end Formalism.DivisionValues
