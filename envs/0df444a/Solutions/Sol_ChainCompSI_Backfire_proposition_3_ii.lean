-- Prove2me | solution 1 for ChainCompSI.Backfire.proposition_3_ii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:25:44.105194+00:00
-- url     : https://prove2.me/submissions/30d07365-2d7e-40b4-9672-b4ee83468498
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ChainCompSI_Backfire_table_1_si

open ChainCompSI.Backfire

/-- The SI retailer profit computed from the Table 1 values (valid for `h (4+θ) ≤ 1`). -/
theorem chainCompSI_ret_value (θ h w1 p1 D1 I w2 p2 D2 : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h)
    (hx : h * (4 + θ) ≤ 1)
    (hw1 : w1 = (36 - 2 * h * (4 - θ)) / (68 + 19 * θ))
    (hp1 : p1 = (104 + 55 * θ - 2 * h * (1 + θ) * (4 - θ)) / ((2 + θ) * (68 + 19 * θ)))
    (hD1 : D1 = (1 + θ) * (32 + 19 * θ + 2 * h * (4 - θ)) / ((2 + θ) * (68 + 19 * θ)))
    (hI : I = (1 + θ) * (20 + 7 * θ) * (1 - h * (4 + θ)) / ((2 + θ) * (68 + 19 * θ)))
    (hw2 : w2 = (24 + 40 * h + 14 * h * θ) / (68 + 19 * θ))
    (hp2 : p2 = (92 + 43 * θ + 2 * h * (1 + θ) * (20 + 7 * θ)) / ((2 + θ) * (68 + 19 * θ)))
    (hD2 : D2 = (1 + θ) * (44 + 19 * θ - 2 * h * (20 + 7 * θ)) / ((2 + θ) * (68 + 19 * θ))) :
    p1 * max D1 0 - w1 * (max D1 0 + I) - h * I +
        (p2 * max D2 0 - w2 * max (max D2 0 - I) 0) =
      (2480 + 4960 * θ + 3118 * θ ^ 2 + 638 * θ ^ 3 +
        h * (-1888 - 3312 * θ - 1666 * θ ^ 2 - 207 * θ ^ 3 + 35 * θ ^ 4) +
        h ^ 2 * (4864 + 10592 * θ + 8400 * θ ^ 2 + 3246 * θ ^ 3 + 623 * θ ^ 4 + 49 * θ ^ 5)) /
        ((2 + θ) * (68 + 19 * θ)) ^ 2 := by
  have hK : 0 < (2 + θ) * (68 + 19 * θ) := by positivity
  have hhθ : h * θ ≤ 1 := by nlinarith
  have hD1pos : 0 < D1 := by
    rw [hD1]; apply div_pos _ hK
    apply mul_pos (by linarith); nlinarith
  have hI0 : 0 ≤ I := by
    rw [hI]; apply div_nonneg _ hK.le
    have : 0 ≤ 1 - h * (4 + θ) := by linarith
    positivity
  have hDI : D2 - I = (1 + θ) * (24 + 12 * θ + 40 * h + 34 * h * θ + 7 * h * θ ^ 2) /
      ((2 + θ) * (68 + 19 * θ)) := by
    rw [hD2, hI]; field_simp; ring
  have hDIpos : 0 < D2 - I := by rw [hDI]; positivity
  have hD2pos : 0 < D2 := by linarith
  rw [max_eq_left hD1pos.le, max_eq_left hD2pos.le, max_eq_left hDIpos.le]
  rw [hw1, hp1, hD1, hI, hw2, hp2, hD2]; field_simp; ring

theorem solution (θ h h' : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h) (hlo : (1888 + 1424 * θ + 242 * θ ^ 2 - 35 * θ ^ 3) / (9728 + 11456 * θ + 5344 * θ ^ 2 + 1148 * θ ^ 3 + 98 * θ ^ 4) ≤ h) (hlt : h < h') (hhi : h' ≤ 1 / (4 + θ)) : (∃ E, IsEq θ h SI E) ∧ (∃ E', IsEq θ h' SI E') ∧ ∀ E E', IsEq θ h SI E → IsEq θ h' SI E' → ∀ i : Fin 2, retProfit θ h E i < retProfit θ h' E' i := by
  have h4 : (0 : ℝ) < 4 + θ := by linarith
  have hx' : h' * (4 + θ) ≤ 1 := (le_div_iff₀ h4).1 hhi
  have hx : h * (4 + θ) ≤ 1 := by nlinarith
  have hh' : 0 ≤ h' := by linarith
  obtain ⟨ex, hall⟩ := table_1_si θ h hθ hh hx
  obtain ⟨ex', hall'⟩ := table_1_si θ h' hθ hh' hx'
  refine ⟨ex, ex', fun E E' hE hE' i => ?_⟩
  have hval : ∀ (k : ℝ) (F : Profile), 0 ≤ k → k * (4 + θ) ≤ 1 → IsEq θ k SI F →
      (∀ F, IsEq θ k SI F → ∀ i : Fin 2, F.w1 i = (36 - 2 * k * (4 - θ)) / (68 + 19 * θ) ∧ F.p1 i = (104 + 55 * θ - 2 * k * (1 + θ) * (4 - θ)) / ((2 + θ) * (68 + 19 * θ)) ∧ F.D1 θ i = (1 + θ) * (32 + 19 * θ + 2 * k * (4 - θ)) / ((2 + θ) * (68 + 19 * θ)) ∧ F.inv i = (1 + θ) * (20 + 7 * θ) * (1 - k * (4 + θ)) / ((2 + θ) * (68 + 19 * θ)) ∧ F.w2' i = (24 + 40 * k + 14 * k * θ) / (68 + 19 * θ) ∧ F.p2' i = (92 + 43 * θ + 2 * k * (1 + θ) * (20 + 7 * θ)) / ((2 + θ) * (68 + 19 * θ)) ∧ F.D2 θ i = (1 + θ) * (44 + 19 * θ - 2 * k * (20 + 7 * θ)) / ((2 + θ) * (68 + 19 * θ)) ∧ mfrProfit θ F i = 4 * (1 + θ) * (306 - 34 * k * (4 - θ) + k ^ 2 * (272 + θ * (136 + 21 * θ))) / (68 + 19 * θ) ^ 2) →
      retProfit θ k F i =
        (2480 + 4960 * θ + 3118 * θ ^ 2 + 638 * θ ^ 3 +
          k * (-1888 - 3312 * θ - 1666 * θ ^ 2 - 207 * θ ^ 3 + 35 * θ ^ 4) +
          k ^ 2 * (4864 + 10592 * θ + 8400 * θ ^ 2 + 3246 * θ ^ 3 + 623 * θ ^ 4 + 49 * θ ^ 5)) /
          ((2 + θ) * (68 + 19 * θ)) ^ 2 := by
    intro k F hk hkx hF hallk
    obtain ⟨hw1, hp1, hD1, hinv, hw2, hp2, hD2, -⟩ := hallk F hF i
    have hD1' : demand θ (F.p1 i) (F.p1 (rival i)) = _ := hD1
    have hD2' : demand θ (F.p2' i) (F.p2' (rival i)) = _ := hD2
    unfold retProfit retP1 retP2 sales
    exact chainCompSI_ret_value θ k _ _ _ _ _ _ _ hθ hk hkx hw1 hp1 hD1' hinv hw2 hp2 hD2'
  rw [hval h E hh hx hE hall, hval h' E' hh' hx' hE' hall']
  have hK : 0 < ((2 + θ) * (68 + 19 * θ)) ^ 2 := by positivity
  rw [div_lt_div_iff_of_pos_right hK]
  have hc : 0 < 9728 + 11456 * θ + 5344 * θ ^ 2 + 1148 * θ ^ 3 + 98 * θ ^ 4 := by positivity
  have hL := (div_le_iff₀ hc).1 hlo
  have key : (2480 + 4960 * θ + 3118 * θ ^ 2 + 638 * θ ^ 3 +
        h' * (-1888 - 3312 * θ - 1666 * θ ^ 2 - 207 * θ ^ 3 + 35 * θ ^ 4) +
        h' ^ 2 * (4864 + 10592 * θ + 8400 * θ ^ 2 + 3246 * θ ^ 3 + 623 * θ ^ 4 + 49 * θ ^ 5)) -
      (2480 + 4960 * θ + 3118 * θ ^ 2 + 638 * θ ^ 3 +
        h * (-1888 - 3312 * θ - 1666 * θ ^ 2 - 207 * θ ^ 3 + 35 * θ ^ 4) +
        h ^ 2 * (4864 + 10592 * θ + 8400 * θ ^ 2 + 3246 * θ ^ 3 + 623 * θ ^ 4 + 49 * θ ^ 5)) =
      (1 + θ) * (h' - h) * ((h + h') / 2 *
        (9728 + 11456 * θ + 5344 * θ ^ 2 + 1148 * θ ^ 3 + 98 * θ ^ 4) -
        (1888 + 1424 * θ + 242 * θ ^ 2 - 35 * θ ^ 3)) := by
    ring
  have hpos : 0 < (1 + θ) * (h' - h) * ((h + h') / 2 *
        (9728 + 11456 * θ + 5344 * θ ^ 2 + 1148 * θ ^ 3 + 98 * θ ^ 4) -
        (1888 + 1424 * θ + 242 * θ ^ 2 - 35 * θ ^ 3)) := by
    have : 0 < (h + h') / 2 * (9728 + 11456 * θ + 5344 * θ ^ 2 + 1148 * θ ^ 3 + 98 * θ ^ 4) -
        (1888 + 1424 * θ + 242 * θ ^ 2 - 35 * θ ^ 3) := by
      nlinarith [mul_lt_mul_of_pos_right hlt hc]
    have : 0 < h' - h := by linarith
    positivity
  linarith
