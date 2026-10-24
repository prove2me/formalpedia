-- Prove2me | solution 1 for BellRegret.Representation.theorem1_regret_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T15:08:13.843902+00:00
-- url     : https://prove2.me/submissions/63f5e201-a8e5-44b4-a844-e83c877717b4

import Mathlib
import Definitions.Def_BellRegret_Representation_Model

set_option autoImplicit false

namespace BellRegretRepProof

/-- An additive function bounded on `[0,1]` is linear. -/
theorem add_bdd_linear (B : ℝ → ℝ) (hadd : ∀ x y, B (x + y) = B x + B y) (M : ℝ)
    (hM : ∀ x, 0 ≤ x → x ≤ 1 → |B x| ≤ M) : ∀ x, B x = B 1 * x := by
  set h : ℝ → ℝ := fun x => B x - B 1 * x with hh
  have hadd' : ∀ x y, h (x + y) = h x + h y := by
    intro x y; simp only [hh, hadd]; ring
  let H : ℝ →+ ℝ := AddMonoidHom.mk' h hadd'
  have hH : ∀ x, H x = h x := fun x => rfl
  have h1 : h 1 = 0 := by simp [hh]
  have hint : ∀ z : ℤ, h (z : ℝ) = 0 := by
    intro z
    have := map_zsmul H z (1 : ℝ)
    rw [hH, hH, zsmul_eq_mul, mul_one, h1, smul_zero] at this
    exact this
  have hbd : ∀ x, |h x| ≤ M + |B 1| := by
    intro x
    have hx : x = Int.fract x + (⌊x⌋ : ℝ) := by rw [Int.fract]; ring
    have e : h x = h (Int.fract x) := by
      have := hadd' (Int.fract x) (⌊x⌋ : ℝ)
      rw [hint, add_zero, Int.fract_add_floor] at this
      exact this
    rw [e]
    have f0 := Int.fract_nonneg x
    have f1 := (Int.fract_lt_one x).le
    have hb := hM (Int.fract x) f0 f1
    simp only [hh]
    calc |B (Int.fract x) - B 1 * Int.fract x|
        ≤ |B (Int.fract x)| + |B 1 * Int.fract x| := abs_sub _ _
      _ ≤ M + |B 1| := by
        rw [abs_mul, abs_of_nonneg f0]
        nlinarith [abs_nonneg (B 1)]
  have hn : ∀ (n : ℕ) x, h ((n : ℝ) * x) = (n : ℝ) * h x := by
    intro n x
    have := map_nsmul H n x
    rw [hH, hH, nsmul_eq_mul, nsmul_eq_mul] at this
    exact this
  intro x
  have hx0 : h x = 0 := by
    by_contra hne
    have hpos : 0 < |h x| := abs_pos.mpr hne
    obtain ⟨n, hn'⟩ := exists_nat_gt ((M + |B 1|) / |h x|)
    have := hbd ((n : ℝ) * x)
    rw [hn, abs_mul, Nat.abs_cast] at this
    rw [div_lt_iff₀ hpos] at hn'
    linarith
  have : B x - B 1 * x = 0 := hx0
  linarith

end BellRegretRepProof

open BellRegret.Representation in
theorem solution (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ)
    (hux : ∀ y, StrictMono (fun x => u x y)) (huy : ∀ x, StrictAnti (fun y => u x y))
    (hv : StrictMono v) (hvs : Function.Surjective v)
    (hA2 : Assumption2 u v) (hA3 : Assumption3 u v) :
    ∃ α : ℝ, ∃ f : ℝ → ℝ, ∀ x y : ℝ, u x y = α * v x + f (v x - v y) := by
  set w : ℝ → ℝ := Function.surjInv hvs with hwdef
  have hw : ∀ a, v (w a) = a := fun a => Function.surjInv_eq hvs a
  have hwv : ∀ x, w (v x) = x := fun x => hv.injective (hw (v x))
  have hwm : StrictMono w := by
    intro a b hab
    rw [← hv.lt_iff_lt, hw, hw]; exact hab
  set U : ℝ → ℝ → ℝ := fun a b => u (w a) (w b) with hUdef
  have hU1 : ∀ b, StrictMono (fun a => U a b) := fun b => (hux (w b)).comp hwm
  have hU2 : ∀ a, StrictAnti (fun b => U a b) := fun a => (huy (w a)).comp_strictMono hwm
  have huU : ∀ x y, u x y = U (v x) (v y) := by
    intro x y; simp only [hUdef, hwv]
  -- Assumption 2 in value coordinates
  have hA2U : ∀ m t, U m (m - t) + U m (m + t) = U (m - t) m + U (m + t) m := by
    intro m t
    have h := hA2 (w (m - t)) (w m) (w (m + t)) (by rw [hw, hw, hw]; ring)
    obtain ⟨h1, h2⟩ := h
    simp only [Prefers, selectEU, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      not_lt] at h1 h2
    simp only [hUdef]
    linarith
  -- Assumption 3 in value coordinates, two states
  have hA3U : ∀ l : ℝ, 0 ≤ l → l ≤ 1 → ∀ a1 b1 a2 b2 c1 d1 c2 d2 δ : ℝ,
      l * U c1 d1 + (1 - l) * U c2 d2 < l * U a1 b1 + (1 - l) * U a2 b2 →
      l * U (c1 + δ) (d1 + δ) + (1 - l) * U (c2 + δ) (d2 + δ)
        < l * U (a1 + δ) (b1 + δ) + (1 - l) * U (a2 + δ) (b2 + δ) := by
    intro l hl0 hl1 a1 b1 a2 b2 c1 d1 c2 d2 δ hlt
    have hp : IsProbVec ![l, 1 - l] := by
      refine ⟨?_, ?_⟩
      · intro i; fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_two]
    have key := hA3 2 ![l, 1 - l] ![w a1, w a2] ![w b1, w b2] ![w c1, w c2] ![w d1, w d2]
      ![w (a1 + δ), w (a2 + δ)] ![w (b1 + δ), w (b2 + δ)] ![w (c1 + δ), w (c2 + δ)]
      ![w (d1 + δ), w (d2 + δ)] δ hp
      (by intro i; fin_cases i <;> simp [hw])
      (by intro i; fin_cases i <;> simp [hw])
      (by intro i; fin_cases i <;> simp [hw])
      (by intro i; fin_cases i <;> simp [hw])
      (by simpa [selectEU, Fin.sum_univ_two, hUdef] using hlt)
    simpa [selectEU, Fin.sum_univ_two, hUdef] using key
  -- equality of a sure pair with a two-point mixture is preserved by shifts
  have hEq : ∀ l : ℝ, 0 ≤ l → l ≤ 1 → ∀ c d a1 b1 a2 b2 δ : ℝ,
      U c d = l * U a1 b1 + (1 - l) * U a2 b2 →
      U (c + δ) (d + δ) = l * U (a1 + δ) (b1 + δ) + (1 - l) * U (a2 + δ) (b2 + δ) := by
    intro l hl0 hl1 c d a1 b1 a2 b2 δ he
    rcases lt_trichotomy (U (c + δ) (d + δ))
        (l * U (a1 + δ) (b1 + δ) + (1 - l) * U (a2 + δ) (b2 + δ)) with h | h | h
    · have := hA3U l hl0 hl1 (a1 + δ) (b1 + δ) (a2 + δ) (b2 + δ) (c + δ) (d + δ) (c + δ) (d + δ)
        (-δ) (by linarith)
      simp only [add_neg_cancel_right] at this
      linarith
    · exact h
    · have := hA3U l hl0 hl1 (c + δ) (d + δ) (c + δ) (d + δ) (a1 + δ) (b1 + δ) (a2 + δ) (b2 + δ)
        (-δ) (by linarith)
      simp only [add_neg_cancel_right] at this
      linarith
  -- affine relation
  have hx01 : U 0 1 < U 1 0 := by
    have h1 : U 0 1 < U 0 0 := hU2 0 (by norm_num : (0:ℝ) < 1)
    have h2 : U 0 0 < U 1 0 := hU1 0 (by norm_num : (0:ℝ) < 1)
    linarith
  have hAff : ∀ δ a b, U (a + δ) (b + δ) = U (0 + δ) (1 + δ) +
      (U a b - U 0 1) / (U 1 0 - U 0 1) * (U (1 + δ) (0 + δ) - U (0 + δ) (1 + δ)) := by
    intro δ a b
    set x0 := U 0 1
    set x1 := U 1 0
    set z := U a b
    have hd : 0 < x1 - x0 := by linarith
    rcases le_or_gt z x1 with hz1 | hz1
    · rcases le_or_gt x0 z with hz0 | hz0
      · -- middle case
        set l := (z - x0) / (x1 - x0)
        have hl0 : 0 ≤ l := div_nonneg (by linarith) hd.le
        have hl1 : l ≤ 1 := by rw [div_le_one hd]; linarith
        have he : U a b = l * U 1 0 + (1 - l) * U 0 1 := by
          show z = l * x1 + (1 - l) * x0
          simp only [l]; field_simp; ring
        have := hEq l hl0 hl1 a b 1 0 0 1 δ he
        rw [this]; ring
      · -- z < x0
        set μ := (x1 - x0) / (x1 - z)
        have hd' : 0 < x1 - z := by linarith
        have hm0 : 0 ≤ μ := div_nonneg hd.le hd'.le
        have hm1 : μ ≤ 1 := by rw [div_le_one hd']; linarith
        have he : U 0 1 = μ * U a b + (1 - μ) * U 1 0 := by
          show x0 = μ * z + (1 - μ) * x1
          simp only [μ]; field_simp; ring
        have h := hEq μ hm0 hm1 0 1 a b 1 0 δ he
        have hμ : μ * (x1 - z) = x1 - x0 := by simp only [μ]; field_simp
        rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add', eq_div_iff hd.ne']
        linear_combination (-(x1 - z)) * h - (U (a + δ) (b + δ) - U (1 + δ) (0 + δ)) * hμ
    · -- z > x1
      set μ := (x1 - x0) / (z - x0)
      have hd' : 0 < z - x0 := by linarith
      have hm0 : 0 ≤ μ := div_nonneg hd.le hd'.le
      have hm1 : μ ≤ 1 := by rw [div_le_one hd']; linarith
      have he : U 1 0 = μ * U a b + (1 - μ) * U 0 1 := by
        show x1 = μ * z + (1 - μ) * x0
        simp only [μ]; field_simp; ring
      have h := hEq μ hm0 hm1 1 0 a b 0 1 δ he
      have hμ : μ * (z - x0) = x1 - x0 := by simp only [μ]; field_simp
      rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add', eq_div_iff hd.ne']
      linear_combination (-(z - x0)) * h - (U (a + δ) (b + δ) - U (0 + δ) (1 + δ)) * hμ
  -- the scale factor of every shift is one
  have hr1 : ∀ t : ℝ, t ≠ 0 →
      (U (1 + t) (0 + t) - U (0 + t) (1 + t)) / (U 1 0 - U 0 1) = 1 := by
    intro t ht
    set r := (U (1 + t) (0 + t) - U (0 + t) (1 + t)) / (U 1 0 - U 0 1) with hrdef
    set c := U (0 + t) (1 + t) - r * U 0 1 with hcdef
    have hlin : ∀ a b, U (a + t) (b + t) = r * U a b + c := by
      intro a b; rw [hAff t a b, hrdef, hcdef]; ring
    by_contra hr
    have e1 : U t 0 = r * U 0 (-t) + c := by simpa using hlin 0 (-t)
    have e2 : U 0 t = r * U (-t) 0 + c := by simpa using hlin (-t) 0
    have a2 : U 0 (-t) + U 0 t = U (-t) 0 + U t 0 := by simpa using hA2U 0 t
    have hXY : (1 - r) * (U 0 (-t) - U (-t) 0) = 0 := by linear_combination a2 - e2 + e1
    have h1r : (1 - r) ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
    have hXY' : U 0 (-t) = U (-t) 0 := by
      have := (mul_eq_zero.mp hXY).resolve_left h1r
      linarith
    rcases lt_or_gt_of_ne ht with htn | htp
    · have m1 : U t 0 < U (-t) 0 := hU1 0 (by linarith)
      have m2 : U 0 (-t) < U 0 t := hU2 0 (by linarith)
      linarith
    · have m1 : U (-t) 0 < U t 0 := hU1 0 (by linarith)
      have m2 : U 0 t < U 0 (-t) := hU2 0 (by linarith)
      linarith
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ → ℝ, ∀ t, B t = U t t - U 0 0 := ⟨_, fun t => rfl⟩
  have hB : ∀ a b t, U (a + t) (b + t) = U a b + B t := by
    intro a b t
    rcases eq_or_ne t 0 with rfl | ht
    · simp [hBdef]
    have k : ∀ a b, U (a + t) (b + t) = U (0 + t) (1 + t) + (U a b - U 0 1) := by
      intro a b
      rw [hAff t a b, div_mul_eq_mul_div, mul_div_assoc, hr1 t ht, mul_one]
    have k0 := k 0 0
    simp only [zero_add] at k0
    rw [k a b, hBdef]
    simp only [zero_add] at k0 ⊢
    linarith
  have hadd : ∀ x y, B (x + y) = B x + B y := by
    intro x y
    have := hB x x y
    have h1 := hBdef (x + y)
    have h2 := hBdef x
    linarith
  have hdec : ∀ a b, U a b = U (a - b) 0 + B b := by
    intro a b
    have := hB (a - b) 0 b
    simpa using this
  have hbd : ∀ x, 0 ≤ x → x ≤ 1 →
      |B x| ≤ (U 0 0 - U (-1) 0) + (U 0 0 - U 0 1) := by
    intro x hx0 hx1
    have e := hdec 0 x
    simp only [zero_sub] at e
    have m1 : U 0 x ≤ U 0 0 := (hU2 0).antitone hx0
    have m2 : U 0 1 ≤ U 0 x := (hU2 0).antitone hx1
    have m3 : U (-1) 0 ≤ U (-x) 0 := (hU1 0).monotone (by linarith)
    have m4 : U (-x) 0 ≤ U 0 0 := (hU1 0).monotone (by linarith)
    rw [abs_le]; constructor <;> linarith
  have lin := BellRegretRepProof.add_bdd_linear B hadd _ hbd
  refine ⟨B 1, fun s => U s 0 - B 1 * s, ?_⟩
  intro x y
  rw [huU, hdec (v x) (v y), lin (v y)]
  ring

