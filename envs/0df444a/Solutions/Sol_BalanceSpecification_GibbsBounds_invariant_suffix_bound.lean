-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.invariant_suffix_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:13.39918+00:00
-- url     : https://prove2.me/submissions/16f4d094-6d59-4cc5-a0fd-bd9bd6339440

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Theorems.Thm_BalanceSpecification_invariant_inter_cylinder_real_eq_zero
public import Theorems.Thm_BalanceSpecification_real_inter_le_inter_add_symmDiff
public import Theorems.Thm_BalanceSpecification_gibbs_suffix_union_bound
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_exists_centered_cylinder_approximation_real
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
namespace GibbsBounds
theorem _root_.solution {X : ShiftSpace A}
    {hX : X.carrier.Nonempty} {μ : ProbabilityMeasure X.carrier} {K : ℝ}
    (hG : GibbsBounds hX μ K) (hμ : IsInvariant μ)
    {B : Set X.carrier} (hB : MeasurableSet B)
    (hBinv : (shiftMap X) ⁻¹' B = B) (v w : Word A) :
    (μ : Measure X.carrier).real (B ∩ cylinder X (v ++ w) 0) ≤
      K ^ 3 * (μ : Measure X.carrier).real (cylinder X v 0) *
        (μ : Measure X.carrier).real (B ∩ cylinder X w 0) := by
  let ρ : Measure X.carrier := μ
  let q := K ^ 3 * ρ.real (cylinder X v 0)
  have hq : 0 ≤ q := mul_nonneg (pow_nonneg hG.1.le 3) measureReal_nonneg
  have hq1 : 0 < q + 1 := by linarith only [hq]
  change ρ.real (B ∩ cylinder X (v ++ w) 0) ≤ q * ρ.real (B ∩ cylinder X w 0)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (q + 1)
  have hδ : 0 < δ := div_pos hε hq1
  obtain ⟨n, S, hS, herr⟩ := exists_centered_cylinder_approximation_real ρ hB hδ
  let E := ⋃ a ∈ S, cylinder X a (-(n : ℤ))
  let k : ℤ := -(n : ℤ) - (v ++ w).length
  have hloc : k + (v ++ w).length = -(n : ℤ) := sub_add_cancel _ _
  have hfin := gibbs_suffix_union_bound hμ hG S (fun a ha => (hS a ha).2) k v w
  rw [hloc] at hfin
  have hfin' : ρ.real (E ∩ cylinder X (v ++ w) k) ≤
      q * ρ.real (E ∩ cylinder X w (k + v.length)) := by
    simpa only [ρ, E, q, Set.inter_comm] using hfin
  have hleft := real_inter_le_inter_add_symmDiff ρ B E (cylinder X (v ++ w) k)
  have hright := real_inter_le_inter_add_symmDiff ρ E B (cylinder X w (k + v.length))
  rw [symmDiff_comm E B] at hright
  rw [invariant_inter_cylinder_real_eq_zero hμ hB hBinv (v ++ w) k] at hleft
  rw [invariant_inter_cylinder_real_eq_zero hμ hB hBinv w (k + v.length)] at hright
  have hδeq : (q + 1) * δ = ε := by
    dsimp only [δ]
    field_simp
  have herrscaled : (q + 1) * ρ.real (B ∆ E) < ε := by
    calc
      (q + 1) * ρ.real (B ∆ E) < (q + 1) * δ := mul_lt_mul_of_pos_left herr hq1
      _ = ε := hδeq
  calc
    ρ.real (B ∩ cylinder X (v ++ w) 0) ≤
        ρ.real (E ∩ cylinder X (v ++ w) k) + ρ.real (B ∆ E) := hleft
    _ ≤ q * ρ.real (E ∩ cylinder X w (k + v.length)) + ρ.real (B ∆ E) :=
      add_le_add hfin' le_rfl
    _ ≤ q * (ρ.real (B ∩ cylinder X w 0) + ρ.real (B ∆ E)) + ρ.real (B ∆ E) :=
      add_le_add (mul_le_mul_of_nonneg_left hright hq) le_rfl
    _ = q * ρ.real (B ∩ cylinder X w 0) + (q + 1) * ρ.real (B ∆ E) := by ring
    _ ≤ q * ρ.real (B ∩ cylinder X w 0) + ε := add_le_add le_rfl herrscaled.le
end GibbsBounds
end BalanceSpecification
