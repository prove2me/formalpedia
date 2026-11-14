-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.independent_uniform_survival
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:37:19.044301+00:00
-- url     : https://prove2.me/submissions/e65b78a2-0d6d-4824-bcc3-edd7c28e162b

import Definitions.Def_CountingLLL_ReciprocalTest
set_option autoImplicit false
open CountingLLL.ReciprocalTest MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

private theorem uniform_probability (n : ℕ) : IsProbabilityMeasure (uniformLaw n) := by
  constructor
  simp [uniformLaw, Measure.smul_apply, Measure.count_apply, ENNReal.inv_mul_cancel]

private theorem uniform_nonzero (n : ℕ) :
    uniformLaw (n+1) {x : Fin (n+2) | x.val ≠ 0} = (n+1 : ℝ≥0∞) / (n+2 : ℝ≥0∞) := by
  rw [uniformLaw]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.count_apply]
  have heq : {x : Fin (n+2) | x.val ≠ 0} = ((Finset.univ.erase 0 : Finset (Fin (n+2))) : Set (Fin (n+2))) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h hx; apply h; rw [hx]; rfl
    · intro h hx; apply h; exact Fin.ext hx
  rw [heq, Measure.count_apply_finset]
  simp [Finset.card_erase_of_mem, div_eq_mul_inv, mul_comm, add_assoc]


private theorem product_telescopes (n : ℕ) :
    (∏ i ∈ Finset.range n, (i+1 : ℝ≥0∞)/(i+2 : ℝ≥0∞)) = 1/(n+1 : ℝ≥0∞) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have hn0 : (n+1 : ℝ≥0∞) ≠ 0 := by positivity
    have hnt : (n+1 : ℝ≥0∞) ≠ ⊤ := by finiteness
    simp only [div_eq_mul_inv, one_mul]
    rw [← mul_assoc, ENNReal.inv_mul_cancel hn0 hnt, one_mul]
    congr 1
    simp [Nat.cast_succ, add_assoc]
    norm_num

/-- Independent uniform draws miss the designated element at every counter
value from 2 through n+1 with probability 1/(n+1). -/
theorem solution (n : ℕ) :
    (Measure.infinitePi fun i : ℕ => uniformLaw (i+1))
      {ω : (i : ℕ) → Fin (i+2) | ∀ i < n, (ω i).val ≠ 0} = 1/(n+1 : ℝ≥0∞) := by
  letI (i : ℕ) : IsProbabilityMeasure (uniformLaw (i+1)) := uniform_probability (i+1)
  have h := Measure.infinitePi_pi (fun i : ℕ => uniformLaw (i+1)) (s := Finset.range n)
    (t := fun i => {x : Fin (i+2) | x.val ≠ 0}) (by intro i hi; exact (Set.to_countable _).measurableSet)
  have heq : ((Finset.range n : Finset ℕ) : Set ℕ).pi
      (fun i => {x : Fin (i+2) | x.val ≠ 0}) =
      {ω : (i : ℕ) → Fin (i+2) | ∀ i < n, (ω i).val ≠ 0} := by
    ext ω
    simp [Set.mem_pi]
  rw [heq] at h
  rw [h]
  simp_rw [uniform_nonzero]
  exact product_telescopes n
