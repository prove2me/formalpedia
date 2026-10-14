-- Prove2me | solution 1 for DistCov.Converse.exists_Ddiff_pos
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T02:24:47.279245+00:00
-- url     : https://prove2.me/submissions/489666f8-8c01-4a84-be90-a5310e9122f2

import Definitions.Def_DistCov_Converse_Setting
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
open DistCov.Indep
namespace DistCovFiniteWitness
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable {n : ℕ}

def atomic (x : Fin n → X) (w : Fin n → ℝ) : Measure X :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i)

instance atomic_finite (x : Fin n → X) (w : Fin n → ℝ) : IsFiniteMeasure (atomic x w) := by
  unfold atomic
  haveI (i : Fin n) : IsFiniteMeasure (ENNReal.ofReal (w i) • Measure.dirac (x i)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  infer_instance

lemma atomic_integrable (x : Fin n → X) (w : Fin n → ℝ) (f : X → ℝ) :
    Integrable f (atomic x w) := by
  unfold atomic
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma atomic_integral (x : Fin n → X) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : X → ℝ) : (∫ t, f t ∂atomic x w) = ∑ i, w i * f (x i) := by
  unfold atomic
  rw [integral_finsetSum_measure (fun i hi =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp [integral_smul_measure, ENNReal.toReal_ofReal, hw]

lemma atomic_prob (x : Fin n → X) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) : IsProbabilityMeasure (atomic x w) := by
  apply isProbabilityMeasure_iff_real.mpr
  have h := atomic_integral x w hw (fun _ => 1)
  simpa [hs] using h

lemma atomic_moment (x : Fin n → X) (w : Fin n → ℝ) (o : X) :
    FiniteFirstMoment (atomic x w) := ⟨o, atomic_integrable x w _⟩

lemma atomic_energy (x : Fin n → X) (w v : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) :
    energy (atomic x w) (atomic x v) =
      ∑ i, ∑ j, w i * v j * dist (x i) (x j) := by
  have hi : Integrable (fun p : X × X => dist p.1 p.2) ((atomic x w).prod (atomic x v)) := by
    apply integrable_prod_iff (by fun_prop) |>.mpr
    exact ⟨Filter.Eventually.of_forall (fun t => atomic_integrable x v _), atomic_integrable x w _⟩
  unfold energy
  rw [integral_prod _ hi, atomic_integral x w hw]
  simp_rw [atomic_integral x v hv, Finset.mul_sum]
  simp only [mul_assoc]

lemma energy_symm (μ ν : Measure X) [SFinite μ] [SFinite ν] : energy ν μ = energy μ ν := by
  unfold energy
  have h := integral_prod_swap (μ := μ) (ν := ν) (fun p : X × X => dist p.1 p.2)
  simpa only [Prod.fst_swap, Prod.snd_swap, dist_comm] using h

lemma atomic_Ddiff (x : Fin n → X) (w v : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) :
    Ddiff (atomic x w) (atomic x v) =
      ∑ i, ∑ j, (w i - v i) * (w j - v j) * dist (x i) (x j) := by
  have he : (∑ i, ∑ j, (w i - v i) * (w j - v j) * dist (x i) (x j)) =
      energy (atomic x w) (atomic x w) - energy (atomic x w) (atomic x v) -
      energy (atomic x v) (atomic x w) + energy (atomic x v) (atomic x v) := by
    rw [atomic_energy x w w hw hw, atomic_energy x w v hw hv,
      atomic_energy x v w hv hw, atomic_energy x v v hv hv]
    have hs (f g : Fin n → ℝ) : (∑ i, (f i - g i)) = (∑ i, f i) - ∑ i, g i :=
      Finset.sum_sub_distrib f g
    simp only [sub_mul, mul_sub]
    simp only [hs]
    ring
  rw [he, energy_symm (atomic x w) (atomic x v)]
  unfold Ddiff
  ring

end DistCovFiniteWitness

open DistCovFiniteWitness

theorem solution
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (hX : ¬ NegType X) :
    ∃ μ₁ μ₂ : Measure X, IsProbabilityMeasure μ₁ ∧ IsProbabilityMeasure μ₂ ∧
      FiniteFirstMoment μ₁ ∧ FiniteFirstMoment μ₂ ∧ μ₁ ≠ μ₂ ∧ 0 < Ddiff μ₁ μ₂ := by
  classical
  unfold NegType at hX
  push Not at hX
  obtain ⟨n, x, α, hsum, hQ⟩ := hX
  let a : Fin n → ℝ := fun i => max (α i) 0
  let b : Fin n → ℝ := fun i => max (-α i) 0
  have ha : ∀ i, 0 ≤ a i := fun i => le_max_right _ _
  have hb : ∀ i, 0 ≤ b i := fun i => le_max_right _ _
  have hsplit : ∀ i, a i - b i = α i := fun i => max_zero_sub_max_neg_zero_eq_self _
  have hab : ∑ i, a i = ∑ i, b i := by
    have he : ∑ i, (a i - b i) = 0 := by simpa only [hsplit] using hsum
    rw [Finset.sum_sub_distrib] at he
    linarith
  let A : ℝ := ∑ i, a i
  have hA : 0 < A := by
    by_contra hn
    have hA0 : ∑ i, a i = 0 := le_antisymm (le_of_not_gt hn) (Finset.sum_nonneg (fun i hi => ha i))
    have hB0 : ∑ i, b i = 0 := hab.symm.trans hA0
    have ha0 : ∀ i, a i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => ha j)).mp hA0 i (Finset.mem_univ i)
    have hb0 : ∀ i, b i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hb j)).mp hB0 i (Finset.mem_univ i)
    have hα0 : ∀ i, α i = 0 := by
      intro i
      rw [← hsplit i, ha0 i, hb0 i]
      simp
    simp only [hα0, zero_mul, Finset.sum_const_zero, lt_self_iff_false] at hQ
  let w : Fin n → ℝ := fun i => a i / A
  let v : Fin n → ℝ := fun i => b i / A
  have hw : ∀ i, 0 ≤ w i := fun i => div_nonneg (ha i) (le_of_lt hA)
  have hv : ∀ i, 0 ≤ v i := fun i => div_nonneg (hb i) (le_of_lt hA)
  have hsw : ∑ i, w i = 1 := by
    simp only [w, ← Finset.sum_div]
    exact div_self (ne_of_gt hA)
  have hsv : ∑ i, v i = 1 := by
    simp only [v, ← Finset.sum_div]
    rw [← hab]
    exact div_self (ne_of_gt hA)
  have hsub : ∀ i, w i - v i = α i / A := by
    intro i
    simp only [w, v, ← sub_div, hsplit]
  have hterm : ∀ i j, (α i / A) * (α j / A) * dist (x i) (x j) =
      (α i * α j * dist (x i) (x j)) / A ^ 2 := by
    intro i j
    field_simp
  have hD : 0 < Ddiff (atomic x w) (atomic x v) := by
    rw [atomic_Ddiff x w v hw hv]
    simp_rw [hsub, hterm, ← Finset.sum_div]
    exact div_pos hQ (sq_pos_of_pos hA)
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simpa using hQ
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  refine ⟨atomic x w, atomic x v, atomic_prob x w hw hsw, atomic_prob x v hv hsv,
    atomic_moment x w (x i), atomic_moment x v (x i), ?_, hD⟩
  intro heq
  rw [heq] at hD
  have hz : Ddiff (atomic x v) (atomic x v) = 0 := by unfold Ddiff; ring
  rw [hz] at hD
  exact (lt_irrefl 0) hD

#print axioms solution
