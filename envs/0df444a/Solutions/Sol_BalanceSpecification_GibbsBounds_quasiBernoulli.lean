-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.quasiBernoulli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:09:06.80063+00:00
-- url     : https://prove2.me/submissions/8287eebf-6794-4025-b946-d20f493425fb

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_pos
public import Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_exp_bounds
public import Theorems.Thm_BalanceSpecification_IsGibbsMeasure_cylinder_real_pos
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
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


attribute [local simp] BalanceSpecification.cylinder_nil

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
omit [DiscreteTopology A] [BorelSpace A]
namespace BalanceSpecification
namespace GibbsBounds
theorem _root_.solution {X : ShiftSpace A} {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    {v w : Word A} (hvw : v ++ w ∈ language X) :
    ((μ : Measure X.carrier).real (cylinder X v 0) *
      (μ : Measure X.carrier).real (cylinder X w 0)) / K ^ 3 ≤
        (μ : Measure X.carrier).real (cylinder X (v ++ w) 0) ∧
    (μ : Measure X.carrier).real (cylinder X (v ++ w) 0) ≤
      K ^ 3 * (μ : Measure X.carrier).real (cylinder X v 0) *
        (μ : Measure X.carrier).real (cylinder X w 0) := by
  have hv : v ∈ language X :=
    language_factorial X (List.prefix_append v w).isInfix hvw
  have hw : w ∈ language X :=
    language_factorial X (List.suffix_append v w).isInfix hvw
  let p : Word A → ℝ := fun z => (μ : Measure X.carrier).real (cylinder X z 0)
  let a := Real.exp (-((v.length : ℝ) * entropy X hX))
  let b := Real.exp (-((w.length : ℝ) * entropy X hX))
  have hap : 0 < a := Real.exp_pos _
  have hbp : 0 < b := Real.exp_pos _
  have hpv : 0 < p v := hB.cylinder_real_pos hv
  have hpw : 0 < p w := hB.cylinder_real_pos hw
  have hvm : a / K ≤ p v ∧ p v ≤ K * a := hB.cylinder_real_exp_bounds hv
  have hwm : b / K ≤ p w ∧ p w ≤ K * b := hB.cylinder_real_exp_bounds hw
  have hexp : Real.exp (-(((v ++ w).length : ℝ) * entropy X hX)) = a * b := by
    simp only [List.length_append, Nat.cast_add, add_mul, neg_add_rev, Real.exp_add, a, b]
    ring
  have hcm := hB.cylinder_real_exp_bounds hvw
  rw [hexp] at hcm
  change a * b / K ≤ p (v ++ w) ∧ p (v ++ w) ≤ K * (a * b) at hcm
  change p v * p w / K ^ 3 ≤ p (v ++ w) ∧ p (v ++ w) ≤ K ^ 3 * p v * p w
  have hab : a * b ≤ K * p (v ++ w) := by
    simpa only [mul_comm] using (div_le_iff₀ hB.1).mp hcm.1
  constructor
  · apply (div_le_iff₀ (pow_pos hB.1 3)).mpr
    calc
      p v * p w ≤ (K * a) * (K * b) :=
        mul_le_mul hvm.2 hwm.2 hpw.le (mul_pos hB.1 hap).le
      _ = K ^ 2 * (a * b) := by ring
      _ ≤ K ^ 2 * (K * p (v ++ w)) :=
        mul_le_mul_of_nonneg_left hab (sq_nonneg K)
      _ = p (v ++ w) * K ^ 3 := by ring
  · have hva : a ≤ K * p v := by
      simpa only [mul_comm] using (div_le_iff₀ hB.1).mp hvm.1
    have hwb : b ≤ K * p w := by
      simpa only [mul_comm] using (div_le_iff₀ hB.1).mp hwm.1
    calc
      p (v ++ w) ≤ K * (a * b) := hcm.2
      _ ≤ K * ((K * p v) * (K * p w)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hva hwb hbp.le (mul_pos hB.1 hpv).le) hB.1.le
      _ = K ^ 3 * p v * p w := by ring
end GibbsBounds
end BalanceSpecification
