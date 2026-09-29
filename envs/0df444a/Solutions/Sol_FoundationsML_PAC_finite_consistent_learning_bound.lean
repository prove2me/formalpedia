-- Prove2me | solution 1 for FoundationsML.PAC.finite_consistent_learning_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:40:02.463781+00:00
-- url     : https://prove2.me/submissions/6214a031-b5fd-48a4-903b-17daa0d086b2

import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

open MeasureTheory

namespace FoundationsML.PAC

/-- An eight-point sample space, to be equipped with the trivial σ-algebra. -/
def aux_fclb_X : Type := Fin 8

/-- A two-point label space, to be equipped with the trivial σ-algebra. -/
def aux_fclb_Y : Type := Bool

instance aux_fclb_msX : MeasurableSpace aux_fclb_X := ⊥
instance aux_fclb_msY : MeasurableSpace aux_fclb_Y := ⊥
instance aux_fclb_ftX : Fintype aux_fclb_X := inferInstanceAs (Fintype (Fin 8))
instance aux_fclb_deX : DecidableEq aux_fclb_X := inferInstanceAs (DecidableEq (Fin 8))
instance aux_fclb_ftY : Fintype aux_fclb_Y := inferInstanceAs (Fintype Bool)
instance aux_fclb_deY : DecidableEq aux_fclb_Y := inferInstanceAs (DecidableEq Bool)

theorem aux_fclb_cardX : Fintype.card aux_fclb_X = 8 := Fintype.card_fin 8

theorem aux_fclb_cardY : Fintype.card aux_fclb_Y = 2 := Fintype.card_bool

/-- Every map into a space with the trivial σ-algebra is measurable. -/
theorem aux_fclb_meas (h : aux_fclb_X → aux_fclb_Y) : Measurable h := by
  intro s hs
  rcases MeasurableSpace.measurableSet_bot_iff.1 hs with rfl | rfl
  · exact MeasurableSet.empty
  · exact MeasurableSet.univ

/-- For the trivial σ-algebra, a probability measure gives every nonempty set measure `1`. -/
theorem aux_fclb_nonempty_one (D : Measure aux_fclb_X) [IsProbabilityMeasure D]
    (s : Set aux_fclb_X) (hs : s.Nonempty) : D s = 1 := by
  have h1 : MeasurableSet (toMeasurable D s) := measurableSet_toMeasurable D s
  rcases MeasurableSpace.measurableSet_bot_iff.1 h1 with h | h
  · exfalso
    obtain ⟨x, hx⟩ := hs
    have := subset_toMeasurable D s hx
    rw [h] at this
    exact this
  · rw [← measure_toMeasurable, h, measure_univ]

/-- The target concept: constantly `false`. -/
def aux_fclb_c : aux_fclb_X → aux_fclb_Y := fun _ => (false : Bool)

/-- The learner: predict `true` exactly off the sample. -/
def aux_fclb_A : ∀ m : ℕ, (Fin m → aux_fclb_X) → (aux_fclb_X → aux_fclb_Y) :=
  fun _ S x => (decide (∀ i, S i ≠ x) : Bool)

theorem aux_fclb_consistent (m : ℕ) (S : Fin m → aux_fclb_X) :
    EmpiricalError S aux_fclb_c (aux_fclb_A m S) = 0 := by
  unfold EmpiricalError
  rw [div_eq_zero_iff]
  left
  norm_cast
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  simp only [aux_fclb_A, aux_fclb_c, ne_eq, not_not]
  have : ¬ (∀ j, S j ≠ S i) := fun hj => hj i rfl
  exact decide_eq_false this

/-- Seven sample points never cover the eight-point space. -/
theorem aux_fclb_missing (S : Fin 7 → aux_fclb_X) : ∃ x, ∀ i, S i ≠ x := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective S := fun x => by
    obtain ⟨i, hi⟩ := hcon x
    exact ⟨i, hi⟩
  have := Fintype.card_le_of_surjective S hsurj
  rw [aux_fclb_cardX, Fintype.card_fin] at this
  omega

theorem aux_fclb_set_empty (D : Measure aux_fclb_X) [IsProbabilityMeasure D] :
    {S : Fin 7 → aux_fclb_X |
      GeneralizationError D aux_fclb_c (aux_fclb_A 7 S) ≤ (9 / 10 : ℝ)} = ∅ := by
  ext S
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
  obtain ⟨x, hx⟩ := aux_fclb_missing S
  have hne : ({y | aux_fclb_A 7 S y ≠ aux_fclb_c y} : Set aux_fclb_X).Nonempty := by
    refine ⟨x, ?_⟩
    simp only [Set.mem_ofPred_eq, aux_fclb_A, aux_fclb_c, ne_eq]
    rw [decide_eq_true hx]
    intro h
    cases h
  unfold GeneralizationError
  rw [aux_fclb_nonempty_one D _ hne]
  norm_num

theorem aux_fclb_log :
    Real.log (((Finset.univ : Finset (aux_fclb_X → aux_fclb_Y)).card : ℕ) : ℝ)
      + Real.log (1 / (1 / 2 : ℝ)) ≤ (9 / 10 : ℝ) * ((7 : ℕ) : ℝ) := by
  rw [Finset.card_univ, Fintype.card_fun, aux_fclb_cardX, aux_fclb_cardY]
  have h2 : Real.log (1 / (1 / 2 : ℝ)) = Real.log 2 := by norm_num
  rw [h2]
  have h8 : Real.log (((2 ^ 8 : ℕ) : ℕ) : ℝ) = 8 * Real.log 2 := by
    rw [show (((2 ^ 8 : ℕ) : ℕ) : ℝ) = (2 : ℝ) ^ 8 by norm_num, Real.log_pow]
    norm_num
  rw [h8]
  have := Real.log_two_lt_d9
  push_cast
  nlinarith

end FoundationsML.PAC

open FoundationsML.PAC

theorem solution : ¬ (∀ {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (H : Finset (X → Y)) (D : Measure X)
    [IsProbabilityMeasure D] (c : X → Y) (hc : c ∈ H)
    (hc_meas : Measurable c) (hH_meas : ∀ h ∈ H, Measurable h)
    (A : ∀ m : ℕ, (Fin m → X) → (X → Y))
    (hA_mem : ∀ m (S : Fin m → X), A m S ∈ H)
    (hA_consistent : ∀ m (S : Fin m → X), EmpiricalError S c (A m S) = 0)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (m : ℕ) (hm : Real.log (H.card : ℝ) + Real.log (1 / δ) ≤ ε * m),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c (A m S) ≤ ε}).toReal) := by
  intro hAll
  have key := hAll (X := aux_fclb_X) (Y := aux_fclb_Y) Finset.univ
    (Measure.dirac (α := aux_fclb_X) (show aux_fclb_X from (0 : Fin 8)))
    aux_fclb_c (Finset.mem_univ _) (aux_fclb_meas _) (fun h _ => aux_fclb_meas h)
    aux_fclb_A (fun _ _ => Finset.mem_univ _) aux_fclb_consistent
    (9 / 10) (1 / 2) (by norm_num) (by norm_num) 7 aux_fclb_log
  rw [aux_fclb_set_empty] at key
  simp at key
  norm_num at key
