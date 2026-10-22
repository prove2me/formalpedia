-- Prove2me | solution 1 for DataDrivenRO.Discrete.var_le_cvar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:52:28.127627+00:00
-- url     : https://prove2.me/submissions/2a71369a-e24e-48a9-b8e2-ba90ae80d9dd

import Mathlib
import Definitions.Def_DataDrivenRO_Discrete_Setting

set_option autoImplicit false
open MeasureTheory DataDrivenRO.Discrete

namespace DDDHelp

noncomputable def g {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ) (ε : ℝ) (v : Fin d → ℝ) (t : ℝ) : ℝ :=
  t + (1 / ε) * ∑ j, p j * max (a j ⬝ᵥ v - t) 0

theorem g_lower {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) (t : ℝ) :
    ∑ j, p j * (a j ⬝ᵥ v) ≤ g a p ε v t := by
  unfold g
  have h1 : ∑ j, p j * (a j ⬝ᵥ v - t) ≤ ∑ j, p j * max (a j ⬝ᵥ v - t) 0 :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hp.1 j)
  have h2 : ∑ j, p j * (a j ⬝ᵥ v - t) = ∑ j, p j * (a j ⬝ᵥ v) - t := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]
  have h3 : 0 ≤ ∑ j, p j * max (a j ⬝ᵥ v - t) 0 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hp.1 j) (le_max_right _ _)
  have h4 : ∑ j, p j * max (a j ⬝ᵥ v - t) 0 ≤ (1 / ε) * ∑ j, p j * max (a j ⬝ᵥ v - t) 0 := by
    have : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
    nlinarith
  linarith

theorem g_convex {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (ε : ℝ) (hε0 : 0 < ε) (v w : Fin d → ℝ) (s r : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hsr : s + r = 1) (t1 t2 : ℝ) :
    g a p ε (s • v + r • w) (s * t1 + r * t2) ≤ s * g a p ε v t1 + r * g a p ε w t2 := by
  unfold g
  have hj : ∀ j, p j * max (a j ⬝ᵥ (s • v + r • w) - (s * t1 + r * t2)) 0 ≤
      s * (p j * max (a j ⬝ᵥ v - t1) 0) + r * (p j * max (a j ⬝ᵥ w - t2) 0) := by
    intro j
    have hdot : a j ⬝ᵥ (s • v + r • w) = s * (a j ⬝ᵥ v) + r * (a j ⬝ᵥ w) := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [hdot]
    have hm : max (s * (a j ⬝ᵥ v) + r * (a j ⬝ᵥ w) - (s * t1 + r * t2)) 0 ≤
        s * max (a j ⬝ᵥ v - t1) 0 + r * max (a j ⬝ᵥ w - t2) 0 := by
      apply max_le
      · have h1 := le_max_left (a j ⬝ᵥ v - t1) 0
        have h2 := le_max_left (a j ⬝ᵥ w - t2) 0
        nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 hr]
      · have h1 := le_max_right (a j ⬝ᵥ v - t1) 0
        have h2 := le_max_right (a j ⬝ᵥ w - t2) 0
        nlinarith [mul_nonneg hs h1, mul_nonneg hr h2]
    calc p j * max (s * (a j ⬝ᵥ v) + r * (a j ⬝ᵥ w) - (s * t1 + r * t2)) 0
        ≤ p j * (s * max (a j ⬝ᵥ v - t1) 0 + r * max (a j ⬝ᵥ w - t2) 0) :=
          mul_le_mul_of_nonneg_left hm (hp.1 j)
      _ = s * (p j * max (a j ⬝ᵥ v - t1) 0) + r * (p j * max (a j ⬝ᵥ w - t2) 0) := by ring
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hε' : 0 ≤ 1 / ε := by positivity
  have := mul_le_mul_of_nonneg_left hsum hε'
  nlinarith [this, hsr]


theorem meas_eq {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (v : Fin d → ℝ) (y : ℝ) :
    pointLaw a p {ω | ω ⬝ᵥ v ≤ y} = ENNReal.ofReal (∑ j, p j * (if a j ⬝ᵥ v ≤ y then 1 else 0)) := by
  have hms : MeasurableSet {ω : Fin d → ℝ | ω ⬝ᵥ v ≤ y} := by
    have : Measurable (fun ω : Fin d → ℝ => ω ⬝ᵥ v) := by
      unfold dotProduct
      fun_prop
    exact measurableSet_le this measurable_const
  unfold pointLaw
  rw [Measure.finset_sum_apply, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hms, smul_eq_mul]
    by_cases h : a j ⬝ᵥ v ≤ y
    · simp [h]
    · simp [h]
  · intro j _
    split_ifs
    · simpa using hp j
    · simp

theorem var_le_g {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) (t : ℝ) :
    VaR a p ε v ≤ g a p ε v t := by
  have hp0 := hp.1
  have hp1 := hp.2
  unfold VaR MultistageStochastic.valueAtRisk
  have hmem : ∀ y : ℝ, y ∈ {y : ℝ | ENNReal.ofReal (1 - ε) ≤ pointLaw a p {ω | ω ⬝ᵥ v ≤ y}} ↔
      1 - ε ≤ ∑ j, p j * (if a j ⬝ᵥ v ≤ y then 1 else 0) := by
    intro y
    show ENNReal.ofReal (1 - ε) ≤ pointLaw a p {ω | ω ⬝ᵥ v ≤ y} ↔ _
    rw [meas_eq a p hp0 v y]
    apply ENNReal.ofReal_le_ofReal_iff
    exact Finset.sum_nonneg fun j _ => by
      split_ifs
      · simpa using hp0 j
      · simp
  have hbdd : BddBelow {y : ℝ | ENNReal.ofReal (1 - ε) ≤ pointLaw a p {ω | ω ⬝ᵥ v ≤ y}} := by
    refine ⟨-(∑ j, |a j ⬝ᵥ v|) - 1, fun y hy => ?_⟩
    by_contra hlt
    push Not at hlt
    have hy' := (hmem y).mp hy
    have h0 : ∑ j, p j * (if a j ⬝ᵥ v ≤ y then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj : ¬ a j ⬝ᵥ v ≤ y := by
        intro hle
        have h1 : |a j ⬝ᵥ v| ≤ ∑ k, |a k ⬝ᵥ v| :=
          Finset.single_le_sum (f := fun k => |a k ⬝ᵥ v|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
        have h2 := neg_abs_le (a j ⬝ᵥ v)
        linarith
      simp [hj]
    rw [h0] at hy'
    linarith
  set m : ℝ := ∑ j, p j * max (a j ⬝ᵥ v - t) 0 with hm
  set r : ℝ := g a p ε v t with hr
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun j _ => mul_nonneg (hp0 j) (le_max_right _ _)
  have hrt : r = t + (1 / ε) * m := rfl
  have hrt' : ε * (r - t) = m := by rw [hrt]; field_simp; ring
  have hrt0 : 0 ≤ r - t := by
    have : 0 ≤ ε * (r - t) := by rw [hrt']; exact hm0
    exact nonneg_of_mul_nonneg_right this hε0 |> fun h => by nlinarith
  have hT : ∑ j, p j * (if r < a j ⬝ᵥ v then 1 else 0) ≤ ε := by
    rcases hm0.eq_or_lt with h0 | hpos
    · have hz : ∀ j, p j * max (a j ⬝ᵥ v - t) 0 = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hp0 j) (le_max_right (a j ⬝ᵥ v - t) 0))).mp h0.symm
        intro j; exact this j (Finset.mem_univ j)
      have hr0 : r = t := by
        have : r - t = 0 := by
          have : ε * (r - t) = 0 := by rw [hrt', ← h0]
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h hε0.ne'
          · exact h
        linarith
      have : ∑ j, p j * (if r < a j ⬝ᵥ v then 1 else 0) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases h : r < a j ⬝ᵥ v
        · have h1 := hz j
          have h2 : 0 < max (a j ⬝ᵥ v - t) 0 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
          have : p j = 0 := by
            rcases mul_eq_zero.mp h1 with h3 | h3
            · exact h3
            · exact absurd h3 h2.ne'
          simp [this]
        · simp [h]
      rw [this]; exact hε0.le
    · have hrt1 : 0 < r - t := by
        have : 0 < ε * (r - t) := by rw [hrt']; exact hpos
        exact pos_of_mul_pos_right this hε0.le |> fun h => h
      have hpt : ∀ j, p j * (if r < a j ⬝ᵥ v then 1 else 0) * (r - t) ≤ p j * max (a j ⬝ᵥ v - t) 0 := by
        intro j
        by_cases h : r < a j ⬝ᵥ v
        · simp only [if_pos h, mul_one]
          have : r - t ≤ max (a j ⬝ᵥ v - t) 0 := le_trans (by linarith) (le_max_left _ _)
          exact mul_le_mul_of_nonneg_left this (hp0 j)
        · simp only [if_neg h, mul_zero, zero_mul]
          exact mul_nonneg (hp0 j) (le_max_right _ _)
      have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpt j)
      rw [← Finset.sum_mul] at hs
      have : (∑ j, p j * (if r < a j ⬝ᵥ v then 1 else 0)) * (r - t) ≤ ε * (r - t) := by rw [hrt']; exact hs
      exact le_of_mul_le_mul_right this hrt1
  have hF : ∑ j, p j * (if a j ⬝ᵥ v ≤ r then 1 else 0) = 1 - ∑ j, p j * (if r < a j ⬝ᵥ v then 1 else 0) := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    have : ∑ j, (p j * (if a j ⬝ᵥ v ≤ r then 1 else 0) + p j * (if r < a j ⬝ᵥ v then 1 else 0)) = ∑ j, p j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : a j ⬝ᵥ v ≤ r
      · simp [h, not_lt.mpr h]
      · simp [h, not_le.mp h]
    rw [this, hp1]
  have hrmem : r ∈ {y : ℝ | ENNReal.ofReal (1 - ε) ≤ pointLaw a p {ω | ω ⬝ᵥ v ≤ y}} :=
    (hmem r).mpr (by rw [hF]; linarith)
  exact csInf_le hbdd hrmem

end DDDHelp

theorem solution {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) :
    VaR a p ε v ≤ CVaR a p ε v ∧
      ConvexOn ℝ Set.univ (fun w : Fin d → ℝ => CVaR a p ε w) := by
  have hbdd : ∀ u : Fin d → ℝ, BddBelow (Set.range (DDDHelp.g a p ε u)) := fun u =>
    ⟨_, by rintro _ ⟨t, rfl⟩; exact DDDHelp.g_lower a p hp ε hε0 hε1 u t⟩
  have hne : ∀ u : Fin d → ℝ, (Set.range (DDDHelp.g a p ε u)).Nonempty := fun u => ⟨_, 0, rfl⟩
  constructor
  · exact le_csInf (hne v) (by rintro _ ⟨t, rfl⟩; exact DDDHelp.var_le_g a p hp ε hε0 hε1 v t)
  · refine ⟨convex_univ, ?_⟩
    intro v _ w _ s r hs hr hsr
    simp only [smul_eq_mul]
    show sInf (Set.range (DDDHelp.g a p ε (s • v + r • w))) ≤
      s * sInf (Set.range (DDDHelp.g a p ε v)) + r * sInf (Set.range (DDDHelp.g a p ε w))
    apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨_, ⟨t1, rfl⟩, h1⟩ := exists_lt_of_csInf_lt (hne v)
      (lt_add_of_pos_right (sInf (Set.range (DDDHelp.g a p ε v))) hη)
    obtain ⟨_, ⟨t2, rfl⟩, h2⟩ := exists_lt_of_csInf_lt (hne w)
      (lt_add_of_pos_right (sInf (Set.range (DDDHelp.g a p ε w))) hη)
    have h3 : sInf (Set.range (DDDHelp.g a p ε (s • v + r • w))) ≤
        DDDHelp.g a p ε (s • v + r • w) (s * t1 + r * t2) :=
      csInf_le (hbdd _) ⟨_, rfl⟩
    have h4 := DDDHelp.g_convex a p hp ε hε0 v w s r hs hr hsr t1 t2
    have h5 := mul_le_mul_of_nonneg_left h1.le hs
    have h6 := mul_le_mul_of_nonneg_left h2.le hr
    nlinarith [h3, h4, h5, h6, hsr]
