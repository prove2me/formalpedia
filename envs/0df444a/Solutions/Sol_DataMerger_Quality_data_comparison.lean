-- Prove2me | solution 1 for DataMerger.Quality.data_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:12:26.338207+00:00
-- url     : https://prove2.me/submissions/87c33033-0b82-44a0-b095-ccdbf138ac1d

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

open DataMerger.Quality

/-- A function with positive derivative at `0` cannot be maximized over `[0, ∞)` at `0`. -/
lemma dm_not_max_at_zero (F : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (hF : HasDerivAt F c 0)
    (hmax : ∀ d, 0 ≤ d → F d ≤ F 0) : False := by
  have hloc : IsLocalMaxOn F (Set.Ici 0) 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun d hd => hmax d hd)
  have hy : (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [segment_eq_Icc (by norm_num)]
    intro x hx; exact hx.1
  have := hloc.hasFDerivWithinAt_nonpos hF.hasFDerivAt.hasFDerivWithinAt hy
  simp at this
  linarith

/-- First-order condition at an interior maximizer over `[0, ∞)`. -/
lemma dm_foc (F : ℝ → ℝ) (c d : ℝ) (hd : 0 < d) (hF : HasDerivAt F c d)
    (hmax : ∀ x, 0 ≤ x → F x ≤ F d) : c = 0 := by
  have hloc : IsLocalMax F d := by
    have : Set.Ioi (0 : ℝ) ∈ nhds d := Ioi_mem_nhds hd
    exact Filter.eventually_of_mem this (fun x hx => hmax x (le_of_lt hx))
  exact hloc.hasDerivAt_eq_zero hF

lemma dm_hasDeriv_piB_left (V : ℝ → ℝ) (hV : Differentiable ℝ V) (d : ℝ) :
    HasDerivAt (fun x => piB V x 0) (2 * (3 + V d - V 0) * deriv V d / 18) d := by
  have h1 : HasDerivAt (fun x => 3 + V x - V 0) (deriv V d) d := by
    have := ((hV d).hasDerivAt.const_add 3).sub_const (V 0)
    simpa using this
  have h2 := (h1.pow 2).div_const 18
  have hf : (fun x => piB V x 0) = fun x => (3 + V x - V 0) ^ 2 / 18 := rfl
  rw [hf]
  refine h2.congr_deriv ?_
  norm_num

lemma dm_hasDeriv_piB_right (V : ℝ → ℝ) (hV : Differentiable ℝ V) (d : ℝ) :
    HasDerivAt (fun x => piB V 0 x) (2 * (3 + V 0 - V d) * (-deriv V d) / 18) d := by
  have h1 : HasDerivAt (fun x => 3 + V 0 - V x) (-deriv V d) d := by
    have := ((hV d).hasDerivAt).const_sub (3 + V 0)
    simpa using this
  have h2 := (h1.pow 2).div_const 18
  have hf : (fun x => piB V 0 x) = fun x => (3 + V 0 - V x) ^ 2 / 18 := rfl
  rw [hf]
  refine h2.congr_deriv ?_
  norm_num

lemma dm_hasDeriv_quad (alpha d : ℝ) :
    HasDerivAt (fun x : ℝ => (alpha - x) * x) (alpha - 2 * d) d := by
  have := ((hasDerivAt_id d).const_sub alpha).mul (hasDerivAt_id d)
  refine this.congr_deriv ?_
  simp; ring

lemma dm_strictMonoOn (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V) :
    StrictMonoOn V (Set.Ici 0) := by
  obtain ⟨_, hV, hV', _, _⟩ := hS
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) hV.continuous.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  exact hV' x (le_of_lt hx)

theorem solution (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (dI dM : ℝ) (hdI : 0 ≤ dI) (hdM : 0 ≤ dM)
    (hI : ∀ d, 0 ≤ d →
      (alpha - d) * d + piB V d 0 - piB V 0 d ≤
        (alpha - dI) * dI + piB V dI 0 - piB V 0 dI)
    (hM : ∀ d, 0 ≤ d →
      (alpha - d) * d + piB V d 0 ≤
        (alpha - dM) * dM + piB V dM 0) :
    0 < dM ∧ dM < dI ∧ alpha - dI < alpha - dM := by
  have hmono := dm_strictMonoOn alpha V hS
  obtain ⟨halpha, hV, hV', hV3, _⟩ := hS
  -- objective functions and their derivatives
  set FI : ℝ → ℝ := fun x => (alpha - x) * x + piB V x 0 - piB V 0 x with hFI
  set FM : ℝ → ℝ := fun x => (alpha - x) * x + piB V x 0 with hFM
  have dFI : ∀ d, HasDerivAt FI (alpha - 2 * d + 2 / 3 * deriv V d) d := by
    intro d
    have := ((dm_hasDeriv_quad alpha d).add (dm_hasDeriv_piB_left V hV d)).sub
      (dm_hasDeriv_piB_right V hV d)
    refine this.congr_deriv ?_
    ring
  have dFM : ∀ d, HasDerivAt FM
      (alpha - 2 * d + (3 + V d - V 0) * deriv V d / 9) d := by
    intro d
    have := (dm_hasDeriv_quad alpha d).add (dm_hasDeriv_piB_left V hV d)
    refine this.congr_deriv ?_
    ring
  -- Step 1: dM > 0
  have hdMpos : 0 < dM := by
    rcases eq_or_lt_of_le hdM with h | h
    · exfalso
      subst h
      apply dm_not_max_at_zero FM _ _ (dFM 0)
      · intro d hd; have := hM d hd; simpa [FM] using this
      · have := hV' 0 le_rfl
        have : 0 < (3 + V 0 - V 0) * deriv V 0 / 9 := by
          apply div_pos _ (by norm_num); simp; positivity
        linarith
    · exact h
  -- Step 2: comparative statics, dM ≤ dI
  have hsum : piB V 0 dI ≤ piB V 0 dM := by
    have h1 := hI dM hdM
    have h2 := hM dI hdI
    linarith
  have hle : dM ≤ dI := by
    by_contra hlt
    push Not at hlt
    have hVlt : V dI < V dM := hmono hdI hdM hlt
    have h3M := hV3 dM hdM
    have h0I : V 0 ≤ V dI := hmono.monotoneOn (Set.self_mem_Ici) hdI hdI
    have : piB V 0 dM < piB V 0 dI := by
      unfold piB
      apply div_lt_div_of_pos_right _ (by norm_num)
      nlinarith
    linarith
  -- Step 3: first-order conditions rule out equality
  have hne : dM ≠ dI := by
    intro heq
    have hdIpos : 0 < dI := heq ▸ hdMpos
    have e1 := dm_foc FI _ dI hdIpos (dFI dI) (fun x hx => by simpa [FI] using hI x hx)
    have e2 := dm_foc FM _ dM hdMpos (dFM dM) (fun x hx => by simpa [FM] using hM x hx)
    rw [heq] at e2
    have hpos := hV' dI hdI
    have h3 := hV3 dI hdI
    have : (3 + V dI - V 0) * deriv V dI / 9 = 2 / 3 * deriv V dI := by linarith
    have : (3 + V dI - V 0 - 6) * deriv V dI = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hlt : dM < dI := lt_of_le_of_ne hle hne
  exact ⟨hdMpos, hlt, by linarith⟩
