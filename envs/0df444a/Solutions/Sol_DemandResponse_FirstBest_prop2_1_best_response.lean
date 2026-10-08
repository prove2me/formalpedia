-- Prove2me | solution 1 for DemandResponse.FirstBest.prop2_1_best_response
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:43:52.58797+00:00
-- url     : https://prove2.me/submissions/db825135-a250-4c8e-8595-2db51ab6c566

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Hamiltonian



namespace DemandResponse.FirstBest

lemma br_a_coord (μ A z a : ℝ) (hμ : 0 < μ) (hA : 0 < A) (ha0 : 0 ≤ a) (ha1 : a ≤ μ * A) :
    (μ * min (xneg z) A) * z + (μ * min (xneg z) A) ^ 2 / μ / 2 ≤ a * z + a ^ 2 / μ / 2 := by
  have key : μ * ((μ * min (xneg z) A) * z + (μ * min (xneg z) A) ^ 2 / μ / 2)
      ≤ μ * (a * z + a ^ 2 / μ / 2) := by
    have e1 : μ * ((μ * min (xneg z) A) * z + (μ * min (xneg z) A) ^ 2 / μ / 2)
        = μ * μ * min (xneg z) A * z + (μ * min (xneg z) A) ^ 2 / 2 := by
      field_simp
    have e2 : μ * (a * z + a ^ 2 / μ / 2) = μ * a * z + a ^ 2 / 2 := by field_simp
    rw [e1, e2]
    unfold xneg
    rcases le_or_gt 0 z with hz | hz
    · have : max 0 (-z) = 0 := max_eq_left (by linarith)
      rw [this, min_eq_left hA.le]; nlinarith [mul_nonneg hμ.le ha0]
    · have : max 0 (-z) = -z := max_eq_right (by linarith)
      rw [this]
      rcases le_or_gt (-z) A with h2 | h2
      · rw [min_eq_left h2]; nlinarith [sq_nonneg (a + μ * z)]
      · rw [min_eq_right h2.le]
        nlinarith [mul_nonneg (sub_nonneg.2 ha1) hμ.le, mul_nonneg (sub_nonneg.2 ha1) ha0]
  exact le_of_mul_le_mul_left key hμ

lemma br_obj_a {N d : ℕ} (P : Params N d) (z : ℝ) (a : Fin N → ℝ) :
    (∑ i, a i) * z + c1 P a = ∑ i, (a i * z + a i ^ 2 / P.μ i / 2) := by
  unfold c1
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma aHat_mem {N d : ℕ} (P : Params N d) (z : ℝ) : aHat P z ∈ effortA P := by
  intro i
  have h0 : 0 ≤ min (xneg z) P.Amax := le_min (le_max_left _ _) P.hAmax.le
  exact ⟨mul_nonneg (P.hμ i).le h0,
    mul_le_mul_of_nonneg_left (min_le_right _ _) (P.hμ i).le⟩

lemma aHat_opt {N d : ℕ} (P : Params N d) (z : ℝ) : ∀ a ∈ effortA P,
    (∑ i, aHat P z i) * z + c1 P (aHat P z) ≤ (∑ i, a i) * z + c1 P a := by
  intro a ha
  rw [br_obj_a, br_obj_a]
  exact Finset.sum_le_sum fun i _ =>
    br_a_coord (P.μ i) P.Amax z (a i) (P.hμ i) P.hAmax (ha i).1 (ha i).2

/-- rpow facts. -/
lemma rpow_half_facts (x : ℝ) (hx : 1 < x) :
    0 < x ^ (-(1 / 2 : ℝ)) ∧ x ^ (-(1 / 2 : ℝ)) < 1 ∧ x * (x ^ (-(1 / 2 : ℝ))) ^ 2 = 1 := by
  have hx0 : 0 < x := by linarith
  have e : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.sqrt_eq_rpow]
  rw [e]
  have hs : 1 < Real.sqrt x := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  refine ⟨by positivity, inv_lt_one_of_one_lt₀ hs, ?_⟩
  rw [inv_pow, hsq]; field_simp

lemma br_b_coord (lam g ε b : ℝ) (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hb0 : ε ≤ b) (hb1 : b ≤ 1) :
    let b0 := if lam * xneg g ≤ 1 then 1 else max ε ((lam * xneg g) ^ (-(1 / 2 : ℝ)))
    1 / lam * (b0⁻¹ - 1) - g * b0 ≤ 1 / lam * (b⁻¹ - 1) - g * b := by
  intro b0
  have hbp : 0 < b := lt_of_lt_of_le hε hb0
  set x := xneg g with hxdef
  have hx0 : 0 ≤ x := le_max_left _ _
  have hgx : -g ≤ x := le_max_right _ _
  -- general reduction: suffices (b - b0) * (lam * x * b * b0 - 1) ≥ 0 when g = -x, or g ≥ 0
  have hb0pos : 0 < b0 ∧ ε ≤ b0 ∧ b0 ≤ 1 := by
    simp only [b0]
    split_ifs with h
    · exact ⟨one_pos, hε1, le_rfl⟩
    · push_neg at h
      obtain ⟨h1, h2, _⟩ := rpow_half_facts _ h
      exact ⟨lt_of_lt_of_le hε (le_max_left _ _), le_max_left _ _, max_le hε1 h2.le⟩
  obtain ⟨hp, hεb0, hb01⟩ := hb0pos
  rcases le_or_gt 0 g with hg | hg
  · have hx : x = 0 := by simp [hxdef, xneg, hg]
    have hle : lam * xneg g ≤ 1 := by rw [← hxdef, hx]; linarith
    have : b0 = 1 := by
      show (if lam * xneg g ≤ 1 then _ else _) = 1
      rw [if_pos hle]
    rw [this]
    have : 1 / lam * (b⁻¹ - 1) ≥ 0 := by
      apply mul_nonneg (by positivity)
      rw [sub_nonneg]; exact one_le_inv₀ hbp |>.2 hb1
    have : g * b ≤ g * 1 := mul_le_mul_of_nonneg_left hb1 hg
    rw [inv_one, sub_self, mul_zero]; linarith
  · have hx : x = -g := by simp [hxdef, xneg]; linarith
    have hg' : g = -x := by linarith
    rw [hg']
    -- multiply by lam * b * b0
    have key : (b - b0) * (lam * x * b * b0 - 1) ≥ 0 := by
      simp only [b0] at hp hεb0 hb01 ⊢
      split_ifs with h
      · have : lam * x * b * 1 ≤ 1 := by
          have : lam * x * b ≤ lam * x * 1 := mul_le_mul_of_nonneg_left hb1 (by positivity)
          linarith
        nlinarith
      · push_neg at h
        obtain ⟨h1, h2, h3⟩ := rpow_half_facts _ h
        set s := (lam * x) ^ (-(1 / 2 : ℝ))
        rcases le_or_gt s ε with hs | hs
        · rw [max_eq_left hs]
          have : lam * x * ε * ε ≥ 1 := by nlinarith [mul_le_mul hs hs h1.le hε.le]
          have : lam * x * b * ε ≥ lam * x * ε * ε := by
            have := mul_le_mul_of_nonneg_left hb0 (show 0 ≤ lam * x * ε by positivity)
            nlinarith
          nlinarith
        · rw [max_eq_right hs.le]
          have : (b - s) * (lam * x * b * s - 1) = lam * x * s * (b - s) ^ 2 := by
            linear_combination (b - s) * h3
          rw [this]; positivity
    have e : (1 / lam * (b⁻¹ - 1) - -x * b) - (1 / lam * (b0⁻¹ - 1) - -x * b0)
        = (b - b0) * (lam * x * b * b0 - 1) / (lam * b * b0) := by
      field_simp; ring
    have : (b - b0) * (lam * x * b * b0 - 1) / (lam * b * b0) ≥ 0 := by
      apply div_nonneg key; positivity
    linarith

lemma br_obj_b {N d : ℕ} (P : Params N d) (γ : ℝ) (b : Fin d → ℝ) :
    c2 P b - γ * sigSq P b = ∑ j, P.σ j ^ 2 * (1 / P.lam j * ((b j)⁻¹ - 1) - γ * b j) := by
  unfold c2 sigSq
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma bHat_mem {N d : ℕ} (P : Params N d) (γ : ℝ) : bHat P γ ∈ effortB P := by
  intro j
  simp only [bHat]
  split_ifs with h
  · exact ⟨P.hε1, le_rfl⟩
  · push_neg at h
    obtain ⟨_, h2, _⟩ := rpow_half_facts _ h
    exact ⟨le_max_left _ _, max_le P.hε1 h2.le⟩

lemma bHat_opt {N d : ℕ} (P : Params N d) (γ : ℝ) : ∀ b ∈ effortB P,
    c2 P (bHat P γ) - γ * sigSq P (bHat P γ) ≤ c2 P b - γ * sigSq P b := by
  intro b hb
  rw [br_obj_b, br_obj_b]
  refine Finset.sum_le_sum fun j _ => ?_
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact br_b_coord (P.lam j) γ P.ε (b j) (P.hlam j) P.hε P.hε1 (hb j).1 (hb j).2

theorem br_core {N d : ℕ} (P : Params N d) :
    (∀ z : ℝ, aHat P z ∈ effortA P ∧ ∀ a ∈ effortA P,
      (∑ i, aHat P z i) * z + c1 P (aHat P z) ≤ (∑ i, a i) * z + c1 P a) ∧
    (∀ γ : ℝ, bHat P γ ∈ effortB P ∧ ∀ b ∈ effortB P,
      c2 P (bHat P γ) - γ * sigSq P (bHat P γ) ≤ c2 P b - γ * sigSq P b) ∧
    (∀ z : ℝ, Hm P z =
      muBar P * (min (xneg z) P.Amax * xneg z - min (xneg z) P.Amax ^ 2 / 2)) ∧
    (∀ γ : ℝ, Hv P γ = -(1 / 2) * (c2 P (bHat P γ) - γ * sigSq P (bHat P γ))) := by
  refine ⟨fun z => ⟨aHat_mem P z, aHat_opt P z⟩, fun γ => ⟨bHat_mem P γ, bHat_opt P γ⟩, ?_, ?_⟩
  · intro z
    have hl : IsLeast ((fun a => (∑ i, a i) * z + c1 P a) '' effortA P)
        ((∑ i, aHat P z i) * z + c1 P (aHat P z)) := by
      refine ⟨⟨_, aHat_mem P z, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      exact aHat_opt P z a ha
    unfold Hm
    rw [hl.csInf_eq, br_obj_a]
    simp only [aHat, muBar]
    have hm : min (xneg z) P.Amax * z = - (min (xneg z) P.Amax * xneg z) := by
      unfold xneg
      rcases le_or_gt 0 z with hz | hz
      · rw [max_eq_left (by linarith), min_eq_left P.hAmax.le]; ring
      · rw [max_eq_right (by linarith)]; ring
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := P.hμ i
    have e : (P.μ i * min (xneg z) P.Amax) ^ 2 / P.μ i / 2
        = P.μ i * min (xneg z) P.Amax ^ 2 / 2 := by field_simp
    rw [e]
    linear_combination (-P.μ i) * hm
  · intro γ
    have hl : IsLeast ((fun b => c2 P b - γ * sigSq P b) '' effortB P)
        (c2 P (bHat P γ) - γ * sigSq P (bHat P γ)) := by
      refine ⟨⟨_, bHat_mem P γ, rfl⟩, ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      exact bHat_opt P γ b hb
    unfold Hv
    rw [hl.csInf_eq]

end DemandResponse.FirstBest

open DemandResponse.FirstBest


theorem solution {N d : ℕ} (P : Params N d) :
    (∀ z : ℝ, aHat P z ∈ effortA P ∧ ∀ a ∈ effortA P,
      (∑ i, aHat P z i) * z + c1 P (aHat P z) ≤ (∑ i, a i) * z + c1 P a) ∧
    (∀ γ : ℝ, bHat P γ ∈ effortB P ∧ ∀ b ∈ effortB P,
      c2 P (bHat P γ) - γ * sigSq P (bHat P γ) ≤ c2 P b - γ * sigSq P b) ∧
    (∀ z : ℝ, Hm P z =
      muBar P * (min (xneg z) P.Amax * xneg z - min (xneg z) P.Amax ^ 2 / 2)) ∧
    (∀ γ : ℝ, Hv P γ = -(1 / 2) * (c2 P (bHat P γ) - γ * sigSq P (bHat P γ))) := by
  exact br_core P
