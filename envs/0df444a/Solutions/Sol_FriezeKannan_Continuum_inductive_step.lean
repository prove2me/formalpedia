-- Prove2me | solution 1 for FriezeKannan.Continuum.inductive_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:31:19.617676+00:00
-- url     : https://prove2.me/submissions/d121b4ef-727f-4d65-af66-05b3cea1a936

import Mathlib
import Definitions.Def_FriezeKannan_Continuum_Setting

open MeasureTheory


namespace FriezeKannan.Continuum

lemma l2Norm_sq' (f : Sq → ℝ) : l2Norm f ^ 2 = ∫ p, f p ^ 2 := by
  unfold l2Norm
  exact Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)

lemma vol_rect' (S T : Set unitInterval) :
    (volume (S ×ˢ T)).toReal = (volume S).toReal * (volume T).toReal := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul]

lemma vol_le_one' (S : Set unitInterval) : (volume S).toReal ≤ 1 := by
  have h : volume S ≤ 1 := by
    calc volume S ≤ volume (Set.univ : Set unitInterval) := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 h
  simpa using this

theorem l2_drop_core (f w : Sq → ℝ) (hw : MemLp w 2) (ε : ℝ) (hε : 0 < ε)
    (S T : Set unitInterval) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h : ε * l2Norm f < |rectInt w S T|) :
    let d := rectInt w S T / ((volume S).toReal * (volume T).toReal)
    l2Norm (fun p => w p - cutFun S T d p) ^ 2 - l2Norm w ^ 2 ≤ -ε ^ 2 * l2Norm f ^ 2 := by
  intro d
  have hR : MeasurableSet (S ×ˢ T) := hS.prod hT
  have hab : (volume S).toReal * (volume T).toReal = (volume (S ×ˢ T)).toReal :=
    (vol_rect' S T).symm
  have hnorm : 0 ≤ l2Norm f := Real.sqrt_nonneg _
  have hIpos : 0 < |rectInt w S T| := lt_of_le_of_lt (by positivity) h
  have hab_nn : 0 ≤ (volume S).toReal * (volume T).toReal :=
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hab0 : 0 < (volume S).toReal * (volume T).toReal := by
    rcases hab_nn.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have h0 : volume (S ×ˢ T) = 0 := by
        rw [← h1] at hab
        have := (ENNReal.toReal_eq_zero_iff _).1 hab.symm
        rcases this with h2 | h2
        · exact h2
        · exact absurd h2 (measure_ne_top _ _)
      have : rectInt w S T = 0 := by
        unfold rectInt
        rw [Measure.restrict_eq_zero.2 h0]
        simp
      rw [this] at hIpos
      simp at hIpos
  have hab1 : (volume S).toReal * (volume T).toReal ≤ 1 := by
    have := vol_le_one' S
    have := vol_le_one' T
    have := ENNReal.toReal_nonneg (a := volume S)
    have := ENNReal.toReal_nonneg (a := volume T)
    nlinarith
  set a := (volume S).toReal * (volume T).toReal with ha
  set I := rectInt w S T with hI
  have hw1 : Integrable w := hw.integrable (by norm_num)
  have hw2 : Integrable (fun p => w p ^ 2) := hw.integrable_sq
  have hg1 : Integrable ((S ×ˢ T).indicator w) := hw1.indicator hR
  have hg2 : Integrable ((S ×ˢ T).indicator (fun _ => (1:ℝ))) := by
    rw [integrable_indicator_iff hR]
    exact integrableOn_const (measure_ne_top _ _)
  have hint1 : ∫ p, (S ×ˢ T).indicator w p = I := by
    rw [hI]; unfold rectInt; exact integral_indicator hR
  have hint2 : ∫ p, (S ×ˢ T).indicator (fun _ => (1:ℝ)) p = a := by
    rw [integral_indicator hR]; simp [hab, Measure.real]
  have hpt : ∀ p, (w p - cutFun S T d p) ^ 2
      = w p ^ 2 - (2 * d) * (S ×ˢ T).indicator w p
        + d ^ 2 * (S ×ˢ T).indicator (fun _ => (1:ℝ)) p := by
    intro p
    by_cases hp : p ∈ S ×ˢ T
    · simp [cutFun, Set.indicator, hp]; ring
    · simp [cutFun, Set.indicator, hp]
  have hmain : ∫ p, (w p - cutFun S T d p) ^ 2 = (∫ p, w p ^ 2) - 2 * d * I + d ^ 2 * a := by
    simp_rw [hpt]
    have i1 : Integrable (fun p => w p ^ 2 - 2 * d * (S ×ˢ T).indicator w p) :=
      hw2.sub (hg1.const_mul (2 * d))
    have i2 : Integrable (fun p => d ^ 2 * (S ×ˢ T).indicator (fun _ => (1:ℝ)) p) :=
      hg2.const_mul (d ^ 2)
    have i3 : Integrable (fun p => 2 * d * (S ×ˢ T).indicator w p) := hg1.const_mul (2 * d)
    rw [integral_add i1 i2, integral_sub hw2 i3, integral_const_mul, integral_const_mul, hint1, hint2]
  have e1 := l2Norm_sq' (fun p => w p - cutFun S T d p)
  have e2 := l2Norm_sq' w
  rw [e1, e2, hmain]
  have hd : d * a = I := by
    show I / a * a = I
    field_simp
  have hI2 : ε ^ 2 * l2Norm f ^ 2 ≤ I ^ 2 := by
    have : ε * l2Norm f ≤ |I| := h.le
    have h0 : 0 ≤ ε * l2Norm f := by positivity
    calc ε ^ 2 * l2Norm f ^ 2 = (ε * l2Norm f) ^ 2 := by ring
      _ ≤ |I| ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = I ^ 2 := sq_abs I
  have hI3 : I ^ 2 ≤ I ^ 2 / a := by
    rw [le_div_iff₀ hab0]
    nlinarith [sq_nonneg I]
  have hcalc : -2 * d * I + d ^ 2 * a = -(I ^ 2 / a) := by
    have : d = I / a := rfl
    rw [this]; field_simp; ring
  linarith

lemma memLp_cutFun' (S T : Set unitInterval) (hS : MeasurableSet S) (hT : MeasurableSet T) (d : ℝ) :
    MemLp (cutFun S T d) 2 := by
  unfold cutFun
  exact (memLp_const d).indicator (hS.prod hT)

lemma memLp_cutFunSum' {t : ℕ} (Ss Ts : Fin t → Set unitInterval) (d : Fin t → ℝ)
    (hm : ∀ j, MeasurableSet (Ss j) ∧ MeasurableSet (Ts j)) :
    MemLp (cutFunSum Ss Ts d) 2 := by
  have := memLp_finsetSum' (μ := (volume : Measure Sq)) (p := 2) (s := Finset.univ)
    (f := fun j => cutFun (Ss j) (Ts j) (d j))
    (fun j _ => memLp_cutFun' _ _ (hm j).1 (hm j).2 _)
  convert this using 1
  funext p
  simp [cutFunSum, Finset.sum_apply]

theorem inductive_core (f : Sq → ℝ) (hf : MemLp f 2)
    (ε : ℝ) (hε : 0 < ε)
    (t : ℕ) (Ss Ts : Fin t → Set unitInterval) (d : Fin t → ℝ)
    (hmS : ∀ j, MeasurableSet (Ss j) ∧ MeasurableSet (Ts j))
    (hinv : l2Norm (fun p => f p - cutFunSum Ss Ts d p) ^ 2
      ≤ (1 - ε ^ 2 * t) * l2Norm f ^ 2) :
    (∀ S T : Set unitInterval, MeasurableSet S → MeasurableSet T →
        |rectInt (fun p => f p - cutFunSum Ss Ts d p) S T| ≤ ε * l2Norm f) ∨
    ∃ (S T : Set unitInterval) (d' : ℝ), MeasurableSet S ∧ MeasurableSet T ∧
      l2Norm (fun p => f p - cutFunSum Ss Ts d p - cutFun S T d' p) ^ 2
        ≤ (1 - ε ^ 2 * (t + 1)) * l2Norm f ^ 2 := by
  by_cases hall : ∀ S T : Set unitInterval, MeasurableSet S → MeasurableSet T →
        |rectInt (fun p => f p - cutFunSum Ss Ts d p) S T| ≤ ε * l2Norm f
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨S, T, hS, hT, hlt⟩ := hall
    have hg : MemLp (fun p => f p - cutFunSum Ss Ts d p) 2 :=
      hf.sub (memLp_cutFunSum' Ss Ts d hmS)
    have key := l2_drop_core f _ hg ε hε S T hS hT hlt
    refine ⟨S, T, rectInt (fun p => f p - cutFunSum Ss Ts d p) S T /
      ((volume S).toReal * (volume T).toReal), hS, hT, ?_⟩
    dsimp only at key
    nlinarith [key, hinv]

end FriezeKannan.Continuum

open FriezeKannan.Continuum


theorem solution (f : Sq → ℝ) (hf : MemLp f 2)
    (ε : ℝ) (hε : 0 < ε)
    (t : ℕ) (Ss Ts : Fin t → Set unitInterval) (d : Fin t → ℝ)
    (hmS : ∀ j, MeasurableSet (Ss j) ∧ MeasurableSet (Ts j))
    (hinv : l2Norm (fun p => f p - cutFunSum Ss Ts d p) ^ 2
      ≤ (1 - ε ^ 2 * t) * l2Norm f ^ 2) :
    (∀ S T : Set unitInterval, MeasurableSet S → MeasurableSet T →
        |rectInt (fun p => f p - cutFunSum Ss Ts d p) S T| ≤ ε * l2Norm f) ∨
    ∃ (S T : Set unitInterval) (d' : ℝ), MeasurableSet S ∧ MeasurableSet T ∧
      l2Norm (fun p => f p - cutFunSum Ss Ts d p - cutFun S T d' p) ^ 2
        ≤ (1 - ε ^ 2 * (t + 1)) * l2Norm f ^ 2 := by
  exact inductive_core f hf ε hε t Ss Ts d hmS hinv
