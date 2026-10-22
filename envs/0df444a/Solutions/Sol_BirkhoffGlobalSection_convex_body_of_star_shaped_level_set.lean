-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_body_of_star_shaped_level_set
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T08:21:50.133989+00:00
-- url     : https://prove2.me/submissions/40204020-03c2-4b54-8a0f-8e174bef3957

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_star_shaped_level_set_convex
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Bounded

namespace BirkhoffGlobalSection

namespace ConvexBodyRepair

/-- Squared Euclidean norm on `Phase`. -/
def N (y : Phase) : ℝ := zNormSq y + wNormSq y

theorem N_smul (a : ℝ) (y : Phase) : N (a • y) = a ^ 2 * N y := by
  simp only [N, zNormSq, wNormSq, Pi.smul_apply, smul_eq_mul]; ring

theorem N_pos {y : Phase} (hy : y ≠ 0) : 0 < N y := by
  have h : ∃ i, y i ≠ 0 := by
    by_contra h; push Not at h; exact hy (funext h)
  obtain ⟨i, hi⟩ := h
  have hi2 : 0 < y i ^ 2 := by positivity
  unfold N zNormSq wNormSq
  fin_cases i <;> simp at hi2 <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1),
    sq_nonneg (y 2), sq_nonneg (y 3)]

/-- Normalise a nonzero vector onto `unitThreeSphere`. -/
theorem normalize_mem {y : Phase} (hy : y ≠ 0) :
    (Real.sqrt (N y))⁻¹ • y ∈ unitThreeSphere := by
  have hN := N_pos hy
  show N _ = 1
  rw [N_smul, inv_pow, Real.sq_sqrt hN.le, inv_mul_cancel₀ hN.ne']

theorem smul_normalize {y : Phase} (hy : y ≠ 0) :
    y = Real.sqrt (N y) • ((Real.sqrt (N y))⁻¹ • y) := by
  have : Real.sqrt (N y) ≠ 0 := (Real.sqrt_pos.2 (N_pos hy)).ne'
  rw [smul_smul, mul_inv_cancel₀ this, one_smul]

end ConvexBodyRepair

open ConvexBodyRepair in
/-- Corrected form of `convex_body_of_regular_starshaped_hessian`: under the ray hypotheses
of `star_shaped_level_set_convex`, the cone hull of `S` is a compact convex body with `0` in
its interior and frontier exactly `S`. -/
theorem convex_body_of_star_shaped_level_set_aux (F : Phase → ℝ) (S : Set Phase)
    (hS : IsCompact S)
    (hF0 : ∀ s ∈ S, F s = 0)
    (hreg : ∀ s ∈ S, fderiv ℝ F s ≠ 0)
    (hTH : HasPositiveTangentialHessianOn F S)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
      (0 : Phase) ∈ interior B ∧ S = frontier B := by
  -- rays written with `•`
  have hfun : ∀ (r : ℝ) (x : Phase), (fun i : Fin 4 => r * x i) = r • x := fun _ _ => rfl
  simp only [hfun] at hray huniq hneg
  have e0S : (fun i : Fin 4 => if i = 0 then (1 : ℝ) else 0) ∈ unitThreeSphere := by
    simp [unitThreeSphere, zNormSq, wNormSq]
  -- `0 ∉ S`
  have h0S : (0 : Phase) ∉ S := by
    intro h0
    obtain ⟨R, hR, hRS⟩ := hray _ e0S
    have := hneg _ e0S R hR hRS 0 le_rfl hR
    rw [zero_smul, hF0 0 h0] at this
    exact lt_irrefl _ this
  -- two points of `S` on the same open ray coincide
  have hratio : ∀ s ∈ S, ∀ k : ℝ, 0 < k → k • s ∈ S → k = 1 := by
    intro s hs k hk hks
    have hs0 : s ≠ 0 := fun h => h0S (h ▸ hs)
    set a := Real.sqrt (N s)
    have ha : 0 < a := Real.sqrt_pos.2 (N_pos hs0)
    set u := a⁻¹ • s
    have hu := normalize_mem hs0
    have hsu : s = a • u := smul_normalize hs0
    have h1 : a • u ∈ S := hsu ▸ hs
    have h2 : (k * a) • u ∈ S := by rw [← smul_smul, ← hsu]; exact hks
    have := huniq u hu a (k * a) ha (mul_pos hk ha) h1 h2
    field_simp at this
    linarith [this]
  set C : Set Phase := {y | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s} with hC
  set C' : Set Phase := {y | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ y = t • s} with hC'
  set E : Set Phase := {y | ∃ s ∈ S, ∃ t : ℝ, 1 ≤ t ∧ y = t • s} with hE
  -- `C'` and `E` partition the space
  have hcover : ∀ y, y ∈ C' ∨ y ∈ E := by
    intro y
    by_cases hy : y = 0
    · obtain ⟨R, hR, hRS⟩ := hray _ e0S
      exact Or.inl ⟨_, hRS, 0, le_rfl, one_pos, by rw [hy, zero_smul]⟩
    · obtain ⟨R, hR, hRS⟩ := hray _ (normalize_mem hy)
      set t := Real.sqrt (N y) / R
      have ht : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) hR.le
      have hyt : y = t • (R • ((Real.sqrt (N y))⁻¹ • y)) := by
        rw [smul_smul, div_mul_cancel₀ _ hR.ne']; exact smul_normalize hy
      rcases lt_or_ge t 1 with h | h
      · exact Or.inl ⟨_, hRS, t, ht, h, hyt⟩
      · exact Or.inr ⟨_, hRS, t, h, hyt⟩
  have hdisj : ∀ y, y ∈ C' → y ∈ E → False := by
    rintro y ⟨s, hs, t, ht0, ht1, rfl⟩ ⟨s', hs', t', ht', hy⟩
    have ht'0 : 0 < t' := by linarith
    have hs' : s' = (t / t') • s := by
      calc s' = t'⁻¹ • (t' • s') := by rw [smul_smul, inv_mul_cancel₀ ht'0.ne', one_smul]
        _ = (t / t') • s := by rw [← hy, smul_smul, div_eq_inv_mul]
    rcases ht0.lt_or_eq with htpos | htz
    · have := hratio s hs (t / t') (div_pos htpos ht'0) (hs' ▸ ‹s' ∈ S›)
      rw [div_eq_one_iff_eq ht'0.ne'] at this
      linarith
    · rw [← htz, zero_div, zero_smul] at hs'
      exact h0S (hs' ▸ ‹s' ∈ S›)
  -- a positive lower bound for norms on `S`
  obtain ⟨m, hm, hmS⟩ : ∃ m : ℝ, 0 < m ∧ ∀ s ∈ S, m ≤ ‖s‖ := by
    obtain ⟨R, hR, hRS⟩ := hray _ e0S
    obtain ⟨s0, hs0, hmin⟩ := hS.exists_isMinOn ⟨_, hRS⟩ continuous_norm.continuousOn
    refine ⟨‖s0‖, norm_pos_iff.2 fun h => h0S (h ▸ hs0), fun s hs => hmin hs⟩
  -- `E` is closed
  have hEclosed : IsClosed E := by
    refine isClosed_of_closure_subset fun y hy => ?_
    set K := ‖y‖ + 1
    set T := K / m
    set P : Set Phase := (fun p : Phase × ℝ => p.2 • p.1) '' (S ×ˢ Set.Icc 1 T)
    have hP : IsClosed P :=
      ((hS.prod isCompact_Icc).image (by fun_prop)).isClosed
    have hball : y ∈ closure (Metric.ball (0 : Phase) K ∩ E) := by
      have := (Metric.isOpen_ball (x := (0 : Phase)) (ε := K)).inter_closure
        ⟨by simp [K], hy⟩
      exact this
    have hsub : Metric.ball (0 : Phase) K ∩ E ⊆ P := by
      rintro z ⟨hz, s, hs, t, ht, rfl⟩
      refine ⟨(s, t), ⟨hs, ht, ?_⟩, rfl⟩
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)] at hz
      rw [le_div_iff₀ hm]
      nlinarith [hmS s hs]
    have hyP : y ∈ P := hP.closure_subset (closure_mono hsub hball)
    obtain ⟨⟨s, t⟩, ⟨hs, ht, -⟩, rfl⟩ := hyP
    exact ⟨s, hs, t, ht, rfl⟩
  have hC'open : IsOpen C' := by
    have : C' = Eᶜ := by
      ext y; constructor
      · intro hy hyE; exact hdisj y hy hyE
      · intro hy; exact (hcover y).resolve_right hy
    rw [this]; exact hEclosed.isOpen_compl
  have hC'C : C' ⊆ C := by
    rintro y ⟨s, hs, t, ht0, ht1, rfl⟩; exact ⟨s, hs, t, ht0, ht1.le, rfl⟩
  have hCcompact : IsCompact C := by
    have : C = (fun p : Phase × ℝ => p.2 • p.1) '' (S ×ˢ Set.Icc 0 1) := by
      ext y; constructor
      · rintro ⟨s, hs, t, ht0, ht1, rfl⟩; exact ⟨(s, t), ⟨hs, ht0, ht1⟩, rfl⟩
      · rintro ⟨⟨s, t⟩, ⟨hs, ht0, ht1⟩, rfl⟩; exact ⟨s, hs, t, ht0, ht1, rfl⟩
    rw [this]; exact (hS.prod isCompact_Icc).image (by fun_prop)
  have hC'int : C' ⊆ interior C := interior_maximal hC'C hC'open
  have hconv : Convex ℝ C :=
    star_shaped_level_set_convex F S hS hF0 hreg hTH
      (by simpa only [hfun] using hray) (by simpa only [hfun] using huniq)
      (by simpa only [hfun] using hneg)
  refine ⟨C, hCcompact, hconv, ?_, ?_⟩
  · obtain ⟨R, hR, hRS⟩ := hray _ e0S
    exact hC'int ⟨_, hRS, 0, le_rfl, one_pos, by rw [zero_smul]⟩
  · rw [hCcompact.isClosed.frontier_eq]
    ext y; constructor
    · intro hy
      refine ⟨⟨y, hy, 1, zero_le_one, le_rfl, (one_smul ℝ y).symm⟩, fun hint => ?_⟩
      -- slightly beyond `y` along its ray is still in `C`
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hint
      have hy0 : y ≠ 0 := fun h => h0S (h ▸ hy)
      set k : ℝ := 1 + ε / (2 * ‖y‖)
      have hny : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have hk1 : 1 < k := by
        have : 0 < ε / (2 * ‖y‖) := by positivity
        simp only [k]; linarith
      have hky : k • y ∈ C := by
        apply interior_subset; apply hball
        have hsub : k • y - y = (ε / (2 * ‖y‖)) • y := by
          simp only [k]; rw [add_smul, one_smul]; abel
        rw [Metric.mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      have hkE : k • y ∈ E := ⟨y, hy, k, hk1.le, rfl⟩
      obtain ⟨s, hs, t, ht0, ht1, hts⟩ := hky
      rcases ht1.lt_or_eq with htl | hte
      · exact hdisj _ ⟨s, hs, t, ht0, htl, hts⟩ hkE
      · -- then `k • y ∈ S`, contradicting uniqueness on the ray
        rw [hte, one_smul] at hts
        have := hratio y hy k (by linarith) (hts ▸ hs)
        linarith
    · rintro ⟨⟨s, hs, t, ht0, ht1, rfl⟩, hnint⟩
      rcases ht1.lt_or_eq with htl | hte
      · exact absurd (hC'int ⟨s, hs, t, ht0, htl, rfl⟩) hnint
      · rw [hte, one_smul]; exact hs

end BirkhoffGlobalSection

open BirkhoffGlobalSection in
theorem solution (F : Phase → ℝ) (S : Set Phase)
    (hS : IsCompact S)
    (hF0 : ∀ s ∈ S, F s = 0)
    (hreg : ∀ s ∈ S, fderiv ℝ F s ≠ 0)
    (hTH : HasPositiveTangentialHessianOn F S)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
      (0 : Phase) ∈ interior B ∧ S = frontier B :=
  convex_body_of_star_shaped_level_set_aux F S hS hF0 hreg hTH hray huniq hneg
