-- Prove2me | solution 1 for BirkhoffGlobalSection.symmetric_half_loop_polar_winding
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T23:28:34.498593+00:00
-- url     : https://prove2.me/submissions/b3804ef3-9752-4a02-aa38-a31e76570d1a

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Field.Periodic
import Mathlib.Tactic

open BirkhoffGlobalSection Set Real

theorem solution (γ : ℝ → Plane) (τ : ℝ) (hτ : 0 < τ)
    (hcont : Continuous γ)
    (hper : ∀ t : ℝ, γ (t + 2 * τ) = γ t)
    (hrefl : ∀ t : ℝ, γ (-t) = ![γ t 0, -γ t 1])
    (hlow : ∀ t ∈ Set.Ioo 0 τ, γ t 1 < 0)
    (hstart : γ 0 1 = 0 ∧ γ 0 0 < 0)
    (hend : γ τ 1 = 0 ∧ 0 < γ τ 0) :
    HasPolarWinding γ (2 * τ) 1 := by
  have hP : Function.Periodic γ (2 * τ) := hper
  have h2τ : 0 < 2 * τ := by linarith
  have hr0 : ∀ t, γ (-t) 0 = γ t 0 := fun t => by rw [hrefl]; simp
  have hr1 : ∀ t, γ (-t) 1 = -γ t 1 := fun t => by rw [hrefl]; simp
  -- sign of the second coordinate on the two halves
  have hlow' : ∀ t ∈ Icc 0 τ, γ t 1 ≤ 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hstart.1]
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h', hend.1]
    · exact (hlow t ⟨h, h'⟩).le
  have hup' : ∀ t ∈ Icc (-τ) 0, 0 ≤ γ t 1 := by
    intro t ht
    have := hlow' (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [show t = -(-t) by ring, hr1]; linarith
  -- the curve never vanishes
  have hne0 : ∀ t ∈ Icc (-τ) τ, 0 < γ t 0 ^ 2 + γ t 1 ^ 2 := by
    have key : ∀ t ∈ Icc 0 τ, 0 < γ t 0 ^ 2 + γ t 1 ^ 2 := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]; nlinarith [hstart.2, sq_nonneg (γ 0 1)]
      rcases eq_or_lt_of_le ht.2 with h' | h'
      · rw [h']; nlinarith [hend.2, sq_nonneg (γ τ 1)]
      · nlinarith [hlow t ⟨h, h'⟩, sq_nonneg (γ t 0)]
    intro t ht
    rcases le_total 0 t with h | h
    · exact key t ⟨h, ht.2⟩
    · have := key (-t) ⟨by linarith, by linarith [ht.1]⟩
      rw [show t = -(-t) by ring, hr0, hr1]; nlinarith
  -- reduction to one period
  have hred : ∀ t, toIcoMod h2τ (-τ) t ∈ Ico (-τ) τ ∧
      γ t = γ (toIcoMod h2τ (-τ) t) ∧
      t = toIcoMod h2τ (-τ) t + (toIcoDiv h2τ (-τ) t : ℝ) * (2 * τ) := by
    intro t
    have hm := toIcoMod_mem_Ico h2τ (-τ) t
    have he := self_sub_toIcoDiv_zsmul h2τ (-τ) t
    refine ⟨by rw [show -τ + 2 * τ = τ by ring] at hm; exact hm, ?_, ?_⟩
    · rw [← he, hP.sub_zsmul_eq]
    · rw [← he, zsmul_eq_mul]; ring
  have hne : ∀ t, 0 < γ t 0 ^ 2 + γ t 1 ^ 2 := by
    intro t
    obtain ⟨hm, hγ, _⟩ := hred t
    rw [hγ]; exact hne0 _ ⟨hm.1, hm.2.le⟩
  -- radius
  set r : ℝ → ℝ := fun t => Real.sqrt (γ t 0 ^ 2 + γ t 1 ^ 2) with hr
  have hrpos : ∀ t, 0 < r t := fun t => Real.sqrt_pos.2 (hne t)
  have hγ0c : Continuous (fun t => γ t 0) := (continuous_apply 0).comp hcont
  have hγ1c : Continuous (fun t => γ t 1) := (continuous_apply 1).comp hcont
  have hrc : Continuous r := by
    simp only [hr]; exact (hγ0c.pow 2 |>.add (hγ1c.pow 2)).sqrt
  -- cosine of the angle
  set u : ℝ → ℝ := fun t => γ t 0 / r t with hu
  have huc : Continuous u := hγ0c.div hrc (fun t => (hrpos t).ne')
  have hsq : ∀ t, r t ^ 2 = γ t 0 ^ 2 + γ t 1 ^ 2 := fun t => Real.sq_sqrt (hne t).le
  have hu_bd : ∀ t, -1 ≤ u t ∧ u t ≤ 1 := by
    intro t
    have hrt := hrpos t
    have : (γ t 0) ^ 2 ≤ r t ^ 2 := by rw [hsq]; nlinarith [sq_nonneg (γ t 1)]
    have habs : |γ t 0| ≤ r t := abs_le_of_sq_le_sq' this hrt.le |> fun h => abs_le.2 h
    constructor
    · rw [hu, le_div_iff₀ hrt]; linarith [neg_abs_le (γ t 0)]
    · rw [hu, div_le_one hrt]; linarith [le_abs_self (γ t 0)]
  have hsin_abs : ∀ t, Real.sqrt (1 - u t ^ 2) = |γ t 1| / r t := by
    intro t
    have hrt := hrpos t
    have : 1 - u t ^ 2 = (|γ t 1| / r t) ^ 2 := by
      simp only [hu]
      rw [div_pow, div_pow, sq_abs]
      field_simp
      linarith [hsq t]
    rw [this, Real.sqrt_sq (by positivity)]
  -- the angle on one period `[-τ, τ]`
  set θ0 : ℝ → ℝ := fun t => if t ≤ 0 then Real.arccos (u t) else 2 * π - Real.arccos (u t)
    with hθ0
  have hu0 : u 0 = -1 := by
    have hr0' : r 0 = -γ 0 0 := by
      simp only [hr, hstart.1]
      rw [show (0:ℝ) ^ 2 = 0 by ring, add_zero, Real.sqrt_sq_eq_abs, abs_of_neg hstart.2]
    simp only [hu]; rw [hr0']; field_simp [hstart.2.ne]
  have huτ : u τ = 1 := by
    have hrτ : r τ = γ τ 0 := by
      simp only [hr, hend.1]
      rw [show (0:ℝ) ^ 2 = 0 by ring, add_zero, Real.sqrt_sq hend.2.le]
    simp only [hu]; rw [hrτ]; field_simp [hend.2.ne']
  have hθ0c : Continuous θ0 := by
    refine Continuous.if_le (Real.continuous_arccos.comp huc)
      (continuous_const.sub (Real.continuous_arccos.comp huc)) continuous_id continuous_const ?_
    intro t ht
    have ht' : t = 0 := ht
    rw [ht', hu0, Real.arccos_neg_one]; ring
  -- the periodic correction
  set h0 : ℝ → ℝ := fun t => θ0 t - π * t / τ with hh0
  have hh0c : Continuous h0 := hθ0c.sub (by fun_prop)
  have hendpts : h0 (-τ) = h0 (-τ + 2 * τ) := by
    have e : -τ + 2 * τ = τ := by ring
    rw [e]
    have hum : u (-τ) = 1 := by
      simp only [hu, hr]; rw [hr0, hr1, neg_sq]; exact huτ
    simp only [hh0, hθ0]
    rw [if_pos (by linarith), if_neg (by linarith), hum, huτ, Real.arccos_one]
    field_simp; ring
  haveI : Fact (0 < 2 * τ) := ⟨h2τ⟩
  set H : AddCircle (2 * τ) → ℝ := AddCircle.liftIco (2 * τ) (-τ) h0 with hH
  have hHc : Continuous H := AddCircle.liftIco_continuous hendpts hh0c.continuousOn
  set θ : ℝ → ℝ := fun t => π * t / τ + H (t : AddCircle (2 * τ)) with hθ
  have hθc : Continuous θ := by
    simp only [hθ]
    exact (by fun_prop : Continuous fun t : ℝ => π * t / τ).add
      (hHc.comp (AddCircle.continuous_mk' (2 * τ)))
  -- the angle agrees with `θ0` up to multiples of `2π`
  have hθval : ∀ t, θ t = θ0 (toIcoMod h2τ (-τ) t) + (toIcoDiv h2τ (-τ) t : ℝ) * (2 * π) := by
    intro t
    obtain ⟨hm, _, ht⟩ := hred t
    have hcoe : (t : AddCircle (2 * τ)) = ((toIcoMod h2τ (-τ) t : ℝ) : AddCircle (2 * τ)) := by
      have he := self_sub_toIcoDiv_zsmul h2τ (-τ) t
      rw [← he]
      apply QuotientAddGroup.eq.2
      refine ⟨-toIcoDiv h2τ (-τ) t, ?_⟩
      simp only [neg_smul]
      abel
    simp only [hθ]
    rw [hcoe, hH, AddCircle.liftIco_coe_apply (by rw [show -τ + 2 * τ = τ by ring]; exact hm)]
    simp only [hh0]
    generalize (toIcoDiv h2τ (-τ) t : ℝ) = k at ht ⊢
    generalize toIcoMod h2τ (-τ) t = t' at ht ⊢
    have e : π * t / τ - π * t' / τ = k * (2 * π) := by
      rw [ht]; field_simp; ring
    linarith
  refine ⟨r, θ, hrc, hθc, hrpos, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨hm, hγt, _⟩ := hred t
    set t' := toIcoMod h2τ (-τ) t
    have hrt : r t = r t' := by simp only [hr]; rw [hγt]
    have hut : u t = u t' := by simp only [hu]; rw [hrt, hγt]
    rw [hθval t, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi, hrt]
    have hrt' := hrpos t'
    have hcos : r t' * Real.cos (θ0 t') = γ t' 0 := by
      simp only [hθ0]
      split_ifs
      · rw [Real.cos_arccos (hu_bd t').1 (hu_bd t').2]; simp only [hu]; field_simp
      · rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi,
          Real.cos_arccos (hu_bd t').1 (hu_bd t').2]
        simp only [hu]; field_simp; ring
    have hsin : r t' * Real.sin (θ0 t') = γ t' 1 := by
      simp only [hθ0]
      split_ifs with hle
      · rw [Real.sin_arccos, hsin_abs, abs_of_nonneg (hup' t' ⟨hm.1, hle⟩)]; field_simp
      · rw [Real.sin_sub, Real.cos_two_pi, Real.sin_two_pi, Real.sin_arccos, hsin_abs,
          abs_of_nonpos (hlow' t' ⟨by linarith, hm.2.le⟩)]
        field_simp; ring
    rw [hγt]
    funext i; fin_cases i
    · simpa using hcos.symm
    · simpa using hsin.symm
  · intro t; simp only [hr]; rw [hper]
  · intro t
    simp only [hθ]
    have hc : ((t + 2 * τ : ℝ) : AddCircle (2 * τ)) = (t : AddCircle (2 * τ)) := by
      simp [AddCircle.coe_add_period]
    rw [hc]
    field_simp; ring
