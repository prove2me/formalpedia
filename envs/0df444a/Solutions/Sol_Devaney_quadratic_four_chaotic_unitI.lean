-- Prove2me | solution 1 for Devaney.quadratic_four_chaotic_unitI
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T04:10:16.987534+00:00
-- url     : https://prove2.me/submissions/d1321bbf-9197-4d2a-8269-7e7e570f2536

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Real
open Devaney

/-!
# Chaos of the logistic map at `mu = 4`

Mathlib has no interval dynamics; the semiconjugacy `F4 . h = h . (2*)` with
`h t = (1 - cos 2*pi*t)/2` and everything derived from it is built here in a private namespace.
-/

namespace Log4


/-- The semiconjugating map `h θ = sin²(πθ) = (1 - cos 2πθ)/2`. -/
noncomputable def h (θ : ℝ) : ℝ := (1 - Real.cos (2 * π * θ)) / 2

theorem h_mem (θ : ℝ) : h θ ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 := Real.neg_one_le_cos (2 * π * θ)
  have h2 := Real.cos_le_one (2 * π * θ)
  constructor <;> simp only [h] <;> linarith

theorem h_continuous : Continuous h := by
  unfold h
  fun_prop

/-- `h` is Lipschitz with constant `π`. -/
theorem h_lip (a b : ℝ) : |h a - h b| ≤ π * |a - b| := by
  have hcos : |Real.cos (2 * π * a) - Real.cos (2 * π * b)| ≤ |2 * π * a - 2 * π * b| := by
    have := Real.lipschitzWith_cos.dist_le_mul (2 * π * a) (2 * π * b)
    simpa [Real.dist_eq] using this
  have e : |2 * π * a - 2 * π * b| = 2 * π * |a - b| := by
    rw [show 2 * π * a - 2 * π * b = 2 * π * (a - b) by ring, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  rw [e] at hcos
  have : |h a - h b| = |Real.cos (2 * π * a) - Real.cos (2 * π * b)| / 2 := by
    rw [show h a - h b = -((Real.cos (2 * π * a) - Real.cos (2 * π * b)) / 2) by
      simp only [h]; ring, abs_neg, abs_div]
    norm_num
  rw [this]
  linarith

/-- The semiconjugacy `F₄(h θ) = h (2θ)`. -/
theorem quad_h (θ : ℝ) : quadratic 4 (h θ) = h (2 * θ) := by
  have hc : Real.cos (2 * π * θ) ^ 2 = 1 / 2 + Real.cos (2 * (2 * π * θ)) / 2 :=
    Real.cos_sq _
  simp only [quadratic, h]
  rw [show 2 * π * (2 * θ) = 2 * (2 * π * θ) by ring]
  nlinarith [hc]

theorem iterate_h (n : ℕ) (θ : ℝ) : (quadratic 4)^[n] (h θ) = h (2 ^ n * θ) := by
  induction n generalizing θ with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, quad_h, ih]
      congr 1
      ring

theorem h_periodic (θ : ℝ) (k : ℕ) : h (θ + k) = h θ := by
  simp only [h]
  congr 2
  rw [show 2 * π * (θ + k) = 2 * π * θ + k * (2 * π) by ring]
  rw [Real.cos_add_nat_mul_two_pi]

theorem h_int (m : ℤ) : h m = 0 := by
  simp only [h]
  rw [show 2 * π * (m : ℝ) = (m : ℝ) * (2 * π) by ring, Real.cos_int_mul_two_pi]
  norm_num

theorem h_half_int (m : ℤ) : h ((m : ℝ) + 1 / 2) = 1 := by
  simp only [h]
  rw [show 2 * π * ((m : ℝ) + 1 / 2) = (m : ℝ) * (2 * π) + π by ring,
    Real.cos_add_pi, Real.cos_int_mul_two_pi]
  norm_num

/-- Any interval of length at least one has, under `h`, the whole of `[0,1]` as image. -/
theorem covering {a L : ℝ} (hL : 1 ≤ L) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ s ∈ Set.Icc a (a + L), h s = x := by
  set m : ℤ := ⌈a⌉ with hm
  set m' : ℤ := ⌈a - 1 / 2⌉ with hm'
  have hs0 : (m : ℝ) ∈ Set.Icc a (a + L) := by
    constructor
    · exact Int.le_ceil a
    · have := Int.ceil_lt_add_one a
      linarith
  have hs1 : ((m' : ℝ) + 1 / 2) ∈ Set.Icc a (a + L) := by
    constructor
    · have := Int.le_ceil (a - 1 / 2); linarith
    · have := Int.ceil_lt_add_one (a - 1 / 2); linarith
  have hsub : Set.uIcc ((m : ℝ)) ((m' : ℝ) + 1 / 2) ⊆ Set.Icc a (a + L) :=
    Set.uIcc_subset_Icc hs0 hs1
  have hiv := intermediate_value_uIcc (a := (m : ℝ)) (b := ((m' : ℝ) + 1 / 2))
    (f := h) (h_continuous.continuousOn)
  rw [h_int, h_half_int] at hiv
  have hxmem : x ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hx
  obtain ⟨s, hs, hsx⟩ := hiv hxmem
  exact ⟨s, hsub hs, hsx⟩

theorem h_surj {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : ∃ θ ∈ Set.Icc (0 : ℝ) 1, h θ = x := by
  obtain ⟨s, hs, hsx⟩ := covering (a := 0) (L := 1) le_rfl hx
  exact ⟨s, by simpa using hs, hsx⟩

theorem mapsTo_unitI : Set.MapsTo (quadratic 4) unitI unitI := by
  intro x hx
  obtain ⟨h0, h1⟩ := hx
  constructor
  · simp only [quadratic]; nlinarith
  · simp only [quadratic]; nlinarith [sq_nonneg (2 * x - 1)]

theorem iterate_mem (n : ℕ) {x : ℝ} (hx : x ∈ unitI) : (quadratic 4)^[n] x ∈ unitI := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (mapsTo_unitI hx)

/-! ## The three chaos properties -/

theorem exists_big {c : ℝ} (hc : 0 < c) : ∃ n : ℕ, 0 < n ∧ c < 2 ^ n - 1 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c + 1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

theorem exists_pow {c : ℝ} (hc : 0 < c) : ∃ n : ℕ, 0 < n ∧ 1 ≤ 2 ^ n * c := by
  obtain ⟨n, hn, h⟩ := exists_big (c := 1 / c) (by positivity)
  refine ⟨n, hn, ?_⟩
  have : 1 / c < 2 ^ n := by linarith
  rw [div_lt_iff₀ hc] at this
  nlinarith

theorem pow_sub_one_pos {n : ℕ} (hn : 0 < n) : (0 : ℝ) < 2 ^ n - 1 := by
  have : (2 : ℝ) ^ 1 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  simp only [pow_one] at this
  linarith

theorem periodic_pt {n : ℕ} (hn : 0 < n) (j : ℕ) :
    (quadratic 4)^[n] (h ((j : ℝ) / (2 ^ n - 1))) = h ((j : ℝ) / (2 ^ n - 1)) := by
  have hd := pow_sub_one_pos hn
  rw [iterate_h]
  have he : (2 : ℝ) ^ n * ((j : ℝ) / (2 ^ n - 1)) = (j : ℝ) / (2 ^ n - 1) + (j : ℕ) := by
    field_simp
    ring
  rw [he, h_periodic]

theorem per_dense : unitI ⊆ closure (Per unitI (quadratic 4)) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨θ, hθ, hθx⟩ := h_surj hx
  obtain ⟨n, hn, hnε⟩ := exists_big (c := π / ε) (by positivity)
  have hd := pow_sub_one_pos hn
  set D : ℝ := 2 ^ n - 1 with hD
  set j : ℕ := ⌊θ * D⌋₊ with hj
  set θ' : ℝ := (j : ℝ) / D with hθ'
  have hjle : (j : ℝ) ≤ θ * D := Nat.floor_le (mul_nonneg hθ.1 hd.le)
  have hjlt : θ * D < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdiff : |θ - θ'| ≤ 1 / D := by
    have e : θ - θ' = (θ * D - (j : ℝ)) / D := by rw [hθ']; field_simp
    have hb : |θ * D - (j : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    rw [e, abs_div, abs_of_pos hd, div_le_div_iff_of_pos_right hd]
    exact hb
  refine ⟨h θ', ⟨h_mem θ', n, hn, periodic_pt hn j⟩, ?_⟩
  have hlip := h_lip θ θ'
  rw [Real.dist_eq, ← hθx]
  have hπ := Real.pi_pos
  have : π * |θ - θ'| ≤ π * (1 / D) := by nlinarith
  have hfin : π * (1 / D) < ε := by
    rw [mul_one_div, div_lt_iff₀ hd]
    rw [div_lt_iff₀ hε] at hnε
    nlinarith
  linarith

theorem transitive : TopologicallyTransitive unitI (quadratic 4) := by
  intro U V hU hV hUI hVI
  obtain ⟨u, huU, huI⟩ := hUI
  obtain ⟨x, hxV, hxI⟩ := hVI
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU u huU
  obtain ⟨θu, -, hθu⟩ := h_surj huI
  have hπ := Real.pi_pos
  set ρ : ℝ := r / (2 * π) with hρ
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨k, hk, hkρ⟩ := exists_pow (c := 2 * ρ) (by positivity)
  obtain ⟨s, hs, hsx⟩ := covering (a := 2 ^ k * (θu - ρ)) (L := 2 ^ k * (2 * ρ)) hkρ hxI
  set θ : ℝ := s / 2 ^ k with hθ
  have hpk : (0 : ℝ) < 2 ^ k := by positivity
  have hθrange : |θ - θu| ≤ ρ := by
    obtain ⟨hs1, hs2⟩ := hs
    have e : θ - θu = (s - 2 ^ k * θu) / 2 ^ k := by rw [hθ]; field_simp
    have hb : |s - 2 ^ k * θu| ≤ ρ * 2 ^ k := by
      rw [abs_le]; constructor <;> nlinarith
    rw [e, abs_div, abs_of_pos hpk, div_le_iff₀ hpk]
    exact hb
  have hθU : h θ ∈ U := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, ← hθu]
    have := h_lip θ θu
    have h2 : π * |θ - θu| ≤ π * ρ := by nlinarith
    have h3 : π * ρ = r / 2 := by rw [hρ]; field_simp
    linarith
  refine ⟨k, hk, ⟨(quadratic 4)^[k] (h θ), ⟨h θ, ⟨hθU, h_mem θ⟩, rfl⟩, ?_⟩⟩
  rw [iterate_h]
  have : (2 : ℝ) ^ k * θ = s := by rw [hθ]; field_simp
  rw [this, hsx]
  exact hxV

theorem sensitive : SensitiveDependence unitI (quadratic 4) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro x hx ε hε
  obtain ⟨θx, -, hθx⟩ := h_surj hx
  have hπ := Real.pi_pos
  set ρ : ℝ := ε / (2 * π) with hρ
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨n, hn, hnρ⟩ := exists_pow (c := 2 * ρ) (by positivity)
  have hpk : (0 : ℝ) < 2 ^ n := by positivity
  have hclose : ∀ s ∈ Set.Icc (2 ^ n * (θx - ρ)) (2 ^ n * (θx - ρ) + 2 ^ n * (2 * ρ)),
      dist x (h (s / 2 ^ n)) < ε ∧ (quadratic 4)^[n] (h (s / 2 ^ n)) = h s := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hrange : |s / 2 ^ n - θx| ≤ ρ := by
      have e : s / 2 ^ n - θx = (s - 2 ^ n * θx) / 2 ^ n := by field_simp
      have hb : |s - 2 ^ n * θx| ≤ ρ * 2 ^ n := by
        rw [abs_le]; constructor <;> nlinarith
      rw [e, abs_div, abs_of_pos hpk, div_le_iff₀ hpk]
      exact hb
    constructor
    · rw [Real.dist_eq, ← hθx]
      have hl := h_lip θx (s / 2 ^ n)
      have h2 : π * |θx - (s / 2 ^ n)| ≤ π * ρ := by
        rw [abs_sub_comm] at hl ⊢
        nlinarith [abs_sub_comm θx (s / 2 ^ n)]
      have h3 : π * ρ = ε / 2 := by rw [hρ]; field_simp
      linarith
    · rw [iterate_h]
      congr 1
      field_simp
  obtain ⟨s0, hs0, hs0v⟩ := covering (a := 2 ^ n * (θx - ρ)) (L := 2 ^ n * (2 * ρ)) hnρ
    (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  obtain ⟨s1, hs1, hs1v⟩ := covering (a := 2 ^ n * (θx - ρ)) (L := 2 ^ n * (2 * ρ)) hnρ
    (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  obtain ⟨hFx0, hFx1⟩ := iterate_mem n hx
  rcases le_or_gt ((quadratic 4)^[n] x) (1 / 2) with hc | hc
  · obtain ⟨hd, hit⟩ := hclose s1 hs1
    refine ⟨h (s1 / 2 ^ n), h_mem _, hd, n, ?_⟩
    rw [hit, hs1v, Real.dist_eq]
    rw [abs_of_nonpos (by linarith)]
    linarith
  · obtain ⟨hd, hit⟩ := hclose s0 hs0
    refine ⟨h (s0 / 2 ^ n), h_mem _, hd, n, ?_⟩
    rw [hit, hs0v, Real.dist_eq]
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem chaotic_four : Chaotic unitI (quadratic 4) :=
  ⟨sensitive, transitive, per_dense⟩


end Log4

theorem solution : Devaney.Chaotic Devaney.unitI (Devaney.quadratic 4) :=
  Log4.chaotic_four
