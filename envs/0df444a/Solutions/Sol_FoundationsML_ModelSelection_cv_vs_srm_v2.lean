-- Prove2me | solution 1 for FoundationsML.ModelSelection.cv_vs_srm_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:19:11.695153+00:00
-- url     : https://prove2.me/submissions/b613a9ba-2079-47ef-a8be-eb072eddb9b5

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_GeneralizationError
import Definitions.Def_FoundationsML_ModelSelection_EmpiricalError
import Definitions.Def_FoundationsML_ModelSelection_RademacherComplexity_v2
import Definitions.Def_FoundationsML_ModelSelection_LeastIndex

/-! Disproof of d88da1af `FoundationsML.ModelSelection.cv_vs_srm_v2`.

`hSRM1` is only pinned by its penalized-training-error minimality, which `c` itself satisfies
when `c` lies in every `H_k`. Take `X = Fin 400` uniform, `c ≡ 1`, `H_k = {±1-valued}` for all
`k`, `m = 200`, `α = 1/2`, `m1 = m2 = 100`, `δ = 1/2`. Let every ERM (and the CV choice) be
`h_S1 = 1` on `range S1` and `-1` elsewhere: zero training error, risk `≥ 3/4`. Let
`hSRM1 = c`, risk `0`. Every `LeastIndex` is `1`, so the bound is
`2 √(log 8 / 200) < 1/2 < 3/4`: the event is empty and has measure `0 < 1/2`. -/

set_option autoImplicit false

open MeasureTheory

namespace CvSrmCex

/-- All `±1`-valued functions on `Fin 400`. -/
def H : Set (Fin 400 → ℝ) := {h | ∀ x, h x = 1 ∨ h x = -1}

/-- The training-set memorizer: `1` on the sample, `-1` elsewhere. -/
noncomputable def bad (S : Fin 100 → Fin 400) : Fin 400 → ℝ :=
  fun x => if x ∈ Set.range S then 1 else -1

/-- The uniform distribution on `Fin 400`. -/
noncomputable def D : Measure (Fin 400) := (PMF.uniformOfFintype (Fin 400)).toMeasure

instance : IsProbabilityMeasure D := by
  unfold D; infer_instance

theorem bad_mem (S : Fin 100 → Fin 400) : bad S ∈ H := by
  intro x; unfold bad; split_ifs <;> simp

theorem one_mem : (fun _ : Fin 400 => (1 : ℝ)) ∈ H := fun _ => Or.inl rfl

theorem emp_nonneg {n : ℕ} (S : Fin n → Fin 400) (h : Fin 400 → ℝ) :
    0 ≤ FoundationsML.ModelSelection.EmpiricalError S (fun _ => (1 : ℝ)) h := by
  unfold FoundationsML.ModelSelection.EmpiricalError; positivity

theorem emp_bad (S : Fin 100 → Fin 400) :
    FoundationsML.ModelSelection.EmpiricalError S (fun _ => (1 : ℝ)) (bad S) = 0 := by
  unfold FoundationsML.ModelSelection.EmpiricalError
  rw [Finset.card_eq_zero.mpr]
  · simp
  · rw [Finset.filter_eq_empty_iff]
    intro i _
    simp [bad]

theorem emp_self {n : ℕ} (S : Fin n → Fin 400) :
    FoundationsML.ModelSelection.EmpiricalError S (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = 0 := by
  unfold FoundationsML.ModelSelection.EmpiricalError
  simp

theorem least_le (h : Fin 400 → ℝ) (hh : h ∈ H) :
    FoundationsML.ModelSelection.LeastIndex (fun _ : ℕ => H) h ≤ 1 := by
  unfold FoundationsML.ModelSelection.LeastIndex
  exact Nat.sInf_le ⟨le_rfl, hh⟩

theorem sqrt_log_zero (n : ℕ) (hn : n ≤ 1) (y : ℝ) (hy : 0 < y) :
    Real.sqrt (Real.log (n : ℝ) / y) = 0 := by
  apply Real.sqrt_eq_zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ hy.le
  apply Real.log_nonpos (Nat.cast_nonneg n)
  exact_mod_cast hn

theorem sqrt_log_zero' (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (y : ℝ) (hy : 0 < y) :
    Real.sqrt (Real.log x / y) = 0 := by
  apply Real.sqrt_eq_zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos h0 h1) hy.le

theorem gen_one :
    FoundationsML.ModelSelection.GeneralizationError D (fun _ : Fin 400 => (1 : ℝ))
      (fun _ : Fin 400 => (1 : ℝ)) = 0 := by
  unfold FoundationsML.ModelSelection.GeneralizationError
  simp

theorem D_single (a : Fin 400) : (D {a}).toReal = 1 / 400 := by
  unfold D
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a), PMF.uniformOfFintype_apply]
  simp

theorem gen_bad (S : Fin 100 → Fin 400) :
    3 / 4 ≤ FoundationsML.ModelSelection.GeneralizationError D (fun _ : Fin 400 => (1 : ℝ))
      (bad S) := by
  unfold FoundationsML.ModelSelection.GeneralizationError
  have hset : {x | bad S x ≠ (fun _ : Fin 400 => (1 : ℝ)) x} = (Set.range S)ᶜ := by
    ext x
    simp only [bad, Set.mem_setOf_eq, Set.mem_compl_iff]
    split_ifs with hx <;> simp [hx]; norm_num
  rw [hset]
  have hu : D.real (Set.range S) ≤ 1 / 4 := by
    rw [← Set.iUnion_singleton_eq_range]
    refine (measureReal_iUnion_fintype_le _).trans ?_
    simp only [Measure.real, D_single, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    norm_num
  have hc := measureReal_compl (μ := D) (s := Set.range S) (Set.toFinite _).measurableSet
  simp only [Measure.real] at hc hu ⊢
  rw [hc]
  simp
  linarith

end CvSrmCex

open FoundationsML.ModelSelection in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c : X → ℝ) (hc : ∀ x, c x = 1 ∨ c x = -1) (hc_meas : Measurable c)
    (Hk : ℕ → Set (X → ℝ))
    (hHk : ∀ k, 1 ≤ k → ∀ h ∈ Hk k, ∀ x, h x = 1 ∨ h x = -1)
    (hHk_meas : ∀ k, 1 ≤ k → ∀ h ∈ Hk k, Measurable h)
    (m m1 m2 : ℕ) (hm : 0 < m) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hm1 : (m1 : ℝ) = (1 - α) * m) (hm2 : (m2 : ℝ) = α * m)
    (hNested : ∀ k, 1 ≤ k → Hk k ⊆ Hk (k + 1))
    (hHk_sup : ∀ k, 1 ≤ k →
      Measurable (fun S : Fin m1 → X => EmpiricalRademacherComplexity (Hk k) S))
    (hCV : (Fin m1 → X) → (Fin m2 → X) → (X → ℝ))
    (hSRM1 : (Fin m1 → X) → (X → ℝ))
    (hERMk : (Fin m1 → X) → ℕ → (X → ℝ))
    (hERMk_mem : ∀ S1 k, 1 ≤ k → hERMk S1 k ∈ Hk k)
    (hERMk_min : ∀ S1 k, 1 ≤ k → ∀ h ∈ Hk k,
      EmpiricalError S1 c (hERMk S1 k) ≤ EmpiricalError S1 c h)
    (hCV_eq : ∀ S1 S2, ∃ k, 1 ≤ k ∧ hCV S1 S2 = hERMk S1 k)
    (hCV_min : ∀ S1 S2, ∀ k, 1 ≤ k →
      EmpiricalError S2 c (hCV S1 S2) ≤ EmpiricalError S2 c (hERMk S1 k))
    (hCV_mem : ∀ S1 S2, ∃ k, 1 ≤ k ∧ hCV S1 S2 ∈ Hk k)
    (hSRM1_mem : ∀ S1, ∃ k, 1 ≤ k ∧ hSRM1 S1 ∈ Hk k)
    (hSRM1_min : ∀ S1, ∀ k, 1 ≤ k → ∀ h ∈ Hk k,
      EmpiricalError S1 c (hSRM1 S1) +
          RademacherComplexity D (Hk (LeastIndex Hk (hSRM1 S1))) m1 +
          Real.sqrt (Real.log (LeastIndex Hk (hSRM1 S1)) / m1) ≤
        EmpiricalError S1 c h + RademacherComplexity D (Hk k) m1 + Real.sqrt (Real.log k / m1))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1),
    (1 - δ) ≤ (Measure.prod (Measure.pi (fun _ : Fin m1 => D)) (Measure.pi (fun _ : Fin m2 => D))
      {p : (Fin m1 → X) × (Fin m2 → X) |
        GeneralizationError D c (hCV p.1 p.2) - GeneralizationError D c (hSRM1 p.1) ≤
          2 * Real.sqrt (Real.log
              (max (LeastIndex Hk (hCV p.1 p.2)) (LeastIndex Hk (hSRM1 p.1))) / (α * m)) +
          2 * Real.sqrt (Real.log (4 / δ) / (2 * α * m))}).toReal) := by
  intro Hyp
  have h0 := Hyp (X := Fin 400) CvSrmCex.D (fun _ => (1 : ℝ)) (fun _ => Or.inl rfl)
    measurable_const (fun _ => CvSrmCex.H) (fun _ _ h hh => hh) (fun _ _ _ _ => Measurable.of_discrete)
    200 100 100 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => subset_rfl) (fun _ _ => measurable_of_countable _)
    (fun S1 _ => CvSrmCex.bad S1) (fun _ => fun _ => (1 : ℝ)) (fun S1 _ => CvSrmCex.bad S1)
    (fun S1 _ _ => CvSrmCex.bad_mem S1)
    (fun S1 _ _ h _ => by rw [CvSrmCex.emp_bad]; exact CvSrmCex.emp_nonneg S1 h)
    (fun _ _ => ⟨1, le_rfl, rfl⟩) (fun _ _ _ _ => le_rfl)
    (fun S1 _ => ⟨1, le_rfl, CvSrmCex.bad_mem S1⟩) (fun _ => ⟨1, le_rfl, CvSrmCex.one_mem⟩)
    (fun S1 k _ h _ => by
      rw [CvSrmCex.emp_self,
        CvSrmCex.sqrt_log_zero _ (CvSrmCex.least_le _ CvSrmCex.one_mem) _ (by norm_num)]
      have := CvSrmCex.emp_nonneg S1 h
      have := Real.sqrt_nonneg (Real.log (k : ℝ) / ((100 : ℕ) : ℝ))
      linarith)
    (1 / 2) (by norm_num) (by norm_num)
  have hzero : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (P : α → Prop),
      (∀ a, ¬ P a) → (μ {a | P a}).toReal = 0 := by
    intro α _ μ P hP
    simp [hP]
  rw [hzero _ _ ?_] at h0
  · norm_num at h0
  · intro p hp
    have hb := CvSrmCex.gen_bad p.1
    rw [CvSrmCex.gen_one,
      CvSrmCex.sqrt_log_zero' _ (le_max_of_le_left (Nat.cast_nonneg _))
        (max_le (by exact_mod_cast CvSrmCex.least_le _ (CvSrmCex.bad_mem p.1))
          (by exact_mod_cast CvSrmCex.least_le _ CvSrmCex.one_mem)) _ (by norm_num)] at hp
    have hl : Real.log (4 / (1 / 2) : ℝ) ≤ 7 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / (1 / 2) by norm_num)
      norm_num at this ⊢; linarith
    have hs : Real.sqrt (Real.log (4 / (1 / 2) : ℝ) / (2 * (1 / 2) * ((200 : ℕ) : ℝ))) ≤ 1 / 4 := by
      rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt
      push_cast
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith
