-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.invariant_inter_prefix_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:24.287+00:00
-- url     : https://prove2.me/submissions/21409675-5c05-4d8a-abac-e99f683af959

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Theorems.Thm_BalanceSpecification_invariant_inter_cylinder_real_eq_zero
public import Theorems.Thm_BalanceSpecification_real_inter_le_inter_add_symmDiff
public import Theorems.Thm_BalanceSpecification_GibbsBounds_left_cylinderUnion_bound
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
    {B : Set X.carrier} (hB : MeasurableSet B) (hBinv : (shiftMap X) ⁻¹' B = B)
    (v w : Word A) :
    (μ : Measure X.carrier).real (B ∩ cylinder X (v ++ w) 0) ≤
      K ^ 3 * (μ : Measure X.carrier).real (B ∩ cylinder X v 0) *
        (μ : Measure X.carrier).real (cylinder X w 0) := by
  let c := K ^ 3 * (μ : Measure X.carrier).real (cylinder X w 0)
  have hc : 0 ≤ c := mul_nonneg (pow_nonneg hG.1.le 3) measureReal_nonneg
  have hcp : 0 < c + 1 := by linarith only [hc]
  have hgoal : (μ : Measure X.carrier).real (B ∩ cylinder X (v ++ w) 0) ≤
      c * (μ : Measure X.carrier).real (B ∩ cylinder X v 0) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := ε / (c + 1)
    have hδ : 0 < δ := div_pos hε hcp
    have hδeq : δ * (c + 1) = ε := div_mul_cancel₀ _ hcp.ne'
    obtain ⟨n, S, hS, herr⟩ := exists_centered_cylinder_approximation_real
      (μ : Measure X.carrier) hB hδ
    let E := ⋃ a ∈ S, cylinder X a (-(n : ℤ))
    let k : ℤ := -(n : ℤ) + (2 * n + 1 : ℕ)
    have hf : (μ : Measure X.carrier).real (E ∩ cylinder X (v ++ w) k) ≤
        c * (μ : Measure X.carrier).real (E ∩ cylinder X v k) := by
      have H := hG.left_cylinderUnion_bound hμ S (2 * n + 1)
        (fun a ha => (hS a ha).2) (-(n : ℤ)) v w
      change (μ : Measure X.carrier).real (E ∩ cylinder X (v ++ w) k) ≤
        K ^ 3 * (μ : Measure X.carrier).real (E ∩ cylinder X v k) *
          (μ : Measure X.carrier).real (cylinder X w 0) at H
      simpa only [c, mul_comm, mul_left_comm, mul_assoc] using H
    have he : (μ : Measure X.carrier).real (E ∩ cylinder X v k) ≤
        (μ : Measure X.carrier).real (B ∩ cylinder X v k) + δ := by
      have H := real_inter_le_inter_add_symmDiff (μ : Measure X.carrier) E B
        (cylinder X v k)
      rw [symmDiff_comm E B] at H
      exact H.trans (add_le_add (le_refl _) herr.le)
    calc
      (μ : Measure X.carrier).real (B ∩ cylinder X (v ++ w) 0) =
          (μ : Measure X.carrier).real (B ∩ cylinder X (v ++ w) k) :=
        (invariant_inter_cylinder_real_eq_zero hμ hB hBinv _ _).symm
      _ ≤ (μ : Measure X.carrier).real (E ∩ cylinder X (v ++ w) k) +
          (μ : Measure X.carrier).real (B ∆ E) :=
        real_inter_le_inter_add_symmDiff _ B E _
      _ ≤ c * (μ : Measure X.carrier).real (E ∩ cylinder X v k) + δ :=
        add_le_add hf herr.le
      _ ≤ c * ((μ : Measure X.carrier).real (B ∩ cylinder X v k) + δ) + δ :=
        add_le_add (mul_le_mul_of_nonneg_left he hc) (le_refl δ)
      _ = c * (μ : Measure X.carrier).real (B ∩ cylinder X v 0) + δ * (c + 1) := by
        rw [invariant_inter_cylinder_real_eq_zero hμ hB hBinv]
        ring
      _ = c * (μ : Measure X.carrier).real (B ∩ cylinder X v 0) + ε := by rw [hδeq]
  simpa only [c, mul_comm, mul_left_comm, mul_assoc] using hgoal
end GibbsBounds
end BalanceSpecification
