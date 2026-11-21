-- Prove2me | solution 1 for FiniteEnergyPlane.tubeCoords_div_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T18:09:21.351848+00:00
-- url     : https://prove2.me/submissions/d9d85700-4db9-4f13-9b57-8d2408d898ad

import Definitions.Def_FiniteEnergyPlane_TubeFamily



/-!
# A3 child K: the `C⁰` rate of `ψ(z)/z - κ`

Compare `f(z) = Φ(ψ z, v z)` with `u(ζ') = Φ(ζ', 0)` at the shifted point
`ζ' = cylInf (s + (df - d)/T) (t + cf/T) = κ z`: their `aCoord` and `proj` agree up to
`O(e^{-βs})`, and the weighted lower bound `hlow` turns this into `|ψ z - κ z| = O(|z| e^{-βs})`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

namespace DGA3K

lemma norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma cylInf_ne_zero' (s t : ℝ) : cylInf s t ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_cylInf]; exact (Real.exp_pos _).ne'

lemma cylInf_add' (a b c e : ℝ) : cylInf (a + c) (b + e) = cylInf a b * cylInf c e := by
  unfold cylInf ccwLoop
  rw [show 2 * π * (a + c) = 2 * π * a + 2 * π * c by ring, Real.exp_add,
    show 2 * π * (b + e) = 2 * π * b + 2 * π * e by ring]
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

lemma norm_le_of_fderiv {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ)
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) (z : ℂ) :
    ‖ψ z‖ ≤ ‖ψ 0‖ + 3 / 2 * ‖z‖ := by
  have hb : ∀ x ∈ (univ : Set ℂ), ‖fderiv ℝ ψ x‖ ≤ 3 / 2 := fun x _ => by
    have h1 := norm_add_le (fderiv ℝ ψ x - ContinuousLinearMap.id ℝ ℂ)
      (ContinuousLinearMap.id ℝ ℂ)
    rw [sub_add_cancel] at h1
    have h2 := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℂ)
    linarith [hDψ x]
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hψ x) hb convex_univ
    (mem_univ (0 : ℂ)) (mem_univ z)
  rw [sub_zero] at h
  have := norm_sub_norm_le (ψ z) (ψ 0)
  linarith

end DGA3K

open DGA3K in
theorem tubeCoords_div_sub_le_aux (H : V 1 → ℝ) (P : ReebOrbit H) (u : ℂ → V 1) (d b : ℝ)
    (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (hlow : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖)
    (f : ℂ → V 1) (df cf bf : ℝ) (hbf : 0 < bf)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (ψ v : ℂ → ℂ) (hψ : Differentiable ℝ ψ) (hvρ : ∀ z, ‖v z‖ ≤ ρ / 2)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∃ β > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖ψ (cylInf s t) / cylInf s t - κ‖ ≤ C * Real.exp (-(β * s)) := by
  have hT := P.T_pos
  set a₀ : ℝ := (df - d) / P.T with ha₀
  set b₀ : ℝ := cf / P.T with hb₀
  have hTa : P.T * a₀ = df - d := by rw [ha₀]; field_simp
  have hTb : P.T * b₀ = cf := by rw [hb₀]; field_simp
  set κ : ℂ := cylInf a₀ b₀ with hκdef
  have hκ : κ ≠ 0 := cylInf_ne_zero' _ _
  obtain ⟨Ca, sa, hCa⟩ := ha.2 0
  obtain ⟨Cw, sw, hCw⟩ := hw.2 0
  obtain ⟨Cfa, sfa, hCfa⟩ := hfa.2 0
  obtain ⟨Cfw, sfw, hCfw⟩ := hfw.2 0
  simp only [norm_iteratedFDeriv_zero] at hCa hCw hCfa hCfw
  set β : ℝ := min b bf with hβ
  have hβ0 : 0 < β := lt_min hb hbf
  set B : ℝ := |Cfa| + |Cfw| + (|Ca| + |Cw|) * Real.exp (-(b * a₀)) with hB
  set A : ℝ := 1 + ‖ψ 0‖ + 3 / 2 + ‖κ‖ with hA
  refine ⟨κ, hκ, β, hβ0, B * A / c, max (max (max (sa - a₀) (sw - a₀)) (max sfa sfw)) 0,
    fun s hs t => ?_⟩
  have hs0 : 0 ≤ s := le_of_max_le_right hs
  have hs1 := le_of_max_le_left hs
  have m1 := le_max_left (sa - a₀) (sw - a₀)
  have m2 := le_max_right (sa - a₀) (sw - a₀)
  have m3 := le_max_left (max (sa - a₀) (sw - a₀)) (max sfa sfw)
  have hsa : sa ≤ s + a₀ := by linarith
  have hsw : sw ≤ s + a₀ := by linarith
  have hsfa : sfa ≤ s := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hs1)
  have hsfw : sfw ≤ s := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hs1)
  set z : ℂ := cylInf s t with hz
  set ζ : ℂ := cylInf (s + a₀) (t + b₀) with hζ
  have hζz : ζ = z * κ := cylInf_add' s t a₀ b₀
  have hz1 : 1 ≤ ‖z‖ := by
    rw [hz, norm_cylInf]; exact Real.one_le_exp (by positivity)
  have hz0 : z ≠ 0 := cylInf_ne_zero' _ _
  -- the lower bound at `p = (ψ z, v z)`, `q = (ζ, 0)`
  have hl := hlow (ψ z, v z) ⟨mem_univ _, mem_ball_zero_iff.2 (lt_of_le_of_lt (hvρ z)
    (by linarith))⟩ (ζ, 0) ⟨mem_univ _, mem_ball_self hρ⟩
  simp only [map_zero, add_zero, sub_zero] at hl
  rw [← hf z] at hl
  -- the two coordinate differences
  have eA : aCoord H (f z) - aCoord H (u ζ) =
      (endA H f cylInf (s, t) - P.T * s - df) -
        (endA H u cylInf (s + a₀, t + b₀) - P.T * (s + a₀) - d) := by
    simp only [endA, hz, hζ]; rw [mul_add, hTa]; ring
  have eW : proj H (f z) - proj H (u ζ) =
      (endW H f cylInf (s, t) - P.x (P.T * t + cf)) -
        (endW H u cylInf (s + a₀, t + b₀) - P.x (P.T * (t + b₀))) := by
    simp only [endW, hz, hζ]; rw [mul_add P.T t b₀, hTb]; abel
  have h1 := hCfa s hsfa t
  have h2 := hCa (s + a₀) hsa (t + b₀)
  have h3 := hCfw s hsfw t
  have h4 := hCw (s + a₀) hsw (t + b₀)
  simp only [Real.norm_eq_abs] at h1 h2
  have hexp1 : Real.exp (-(bf * s)) ≤ Real.exp (-(β * s)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right b bf])
  have hexp2 : Real.exp (-(b * (s + a₀))) ≤ Real.exp (-(b * a₀)) * Real.exp (-(β * s)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith [min_le_left b bf])
  have hR : |aCoord H (f z) - aCoord H (u ζ)| + ‖proj H (f z) - proj H (u ζ)‖ ≤
      B * Real.exp (-(β * s)) := by
    rw [eA, eW]
    have t1 := abs_sub (endA H f cylInf (s, t) - P.T * s - df)
      (endA H u cylInf (s + a₀, t + b₀) - P.T * (s + a₀) - d)
    have t2 := norm_sub_le (endW H f cylInf (s, t) - P.x (P.T * t + cf))
      (endW H u cylInf (s + a₀, t + b₀) - P.x (P.T * (t + b₀)))
    have e0 : 0 ≤ Real.exp (-(β * s)) := (Real.exp_pos _).le
    have e1 : 0 ≤ Real.exp (-(b * a₀)) := (Real.exp_pos _).le
    have k1 : Cfa * Real.exp (-(bf * s)) ≤ |Cfa| * Real.exp (-(β * s)) :=
      mul_le_mul (le_abs_self _) hexp1 (Real.exp_pos _).le (abs_nonneg _)
    have k3 : Cfw * Real.exp (-(bf * s)) ≤ |Cfw| * Real.exp (-(β * s)) :=
      mul_le_mul (le_abs_self _) hexp1 (Real.exp_pos _).le (abs_nonneg _)
    have k2 : Ca * Real.exp (-(b * (s + a₀))) ≤
        |Ca| * (Real.exp (-(b * a₀)) * Real.exp (-(β * s))) :=
      mul_le_mul (le_abs_self _) hexp2 (Real.exp_pos _).le (abs_nonneg _)
    have k4 : Cw * Real.exp (-(b * (s + a₀))) ≤
        |Cw| * (Real.exp (-(b * a₀)) * Real.exp (-(β * s))) :=
      mul_le_mul (le_abs_self _) hexp2 (Real.exp_pos _).le (abs_nonneg _)
    have : B * Real.exp (-(β * s)) = |Cfa| * Real.exp (-(β * s)) + |Cfw| * Real.exp (-(β * s)) +
        |Ca| * (Real.exp (-(b * a₀)) * Real.exp (-(β * s))) +
        |Cw| * (Real.exp (-(b * a₀)) * Real.exp (-(β * s))) := by rw [hB]; ring
    linarith
  -- the weighted bound
  have hψz := norm_le_of_fderiv hψ hDψ z
  have hζn : ‖ζ‖ = ‖z‖ * ‖κ‖ := by rw [hζz, norm_mul]
  have hden : 1 + ‖ψ z‖ + ‖ζ‖ ≤ A * ‖z‖ := by
    have p1 : ‖ψ 0‖ ≤ ‖ψ 0‖ * ‖z‖ := by
      simpa using mul_le_mul_of_nonneg_left hz1 (norm_nonneg (ψ 0))
    have e : A * ‖z‖ = ‖z‖ + ‖ψ 0‖ * ‖z‖ + 3 / 2 * ‖z‖ + ‖z‖ * ‖κ‖ := by rw [hA]; ring
    rw [hζn, e]; linarith
  have hden0 : 0 < 1 + ‖ψ z‖ + ‖ζ‖ := by positivity
  have hq : c * (‖ψ z - ζ‖ / (1 + ‖ψ z‖ + ‖ζ‖)) ≤ B * Real.exp (-(β * s)) := by
    have h7 := mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (norm_nonneg (v z)) :
        ‖ψ z - ζ‖ / (1 + ‖ψ z‖ + ‖ζ‖) ≤ ‖ψ z - ζ‖ / (1 + ‖ψ z‖ + ‖ζ‖) + ‖v z‖) hc.le
    exact h7.trans (hl.trans hR)
  have hmain : ‖ψ z - ζ‖ ≤ B * Real.exp (-(β * s)) / c * (A * ‖z‖) := by
    have h5 : ‖ψ z - ζ‖ / (1 + ‖ψ z‖ + ‖ζ‖) ≤ B * Real.exp (-(β * s)) / c := by
      rw [le_div_iff₀ hc]; linarith
    rw [div_le_iff₀ hden0] at h5
    have h6 : 0 ≤ B * Real.exp (-(β * s)) / c := by
      have hB0 : 0 ≤ B := by rw [hB]; positivity
      positivity
    exact h5.trans (mul_le_mul_of_nonneg_left hden h6)
  have e : ψ z / z - κ = (ψ z - ζ) / z := by
    rw [hζz]; field_simp
  rw [e, norm_div, div_le_iff₀ (norm_pos_iff.2 hz0)]
  calc ‖ψ z - ζ‖ ≤ B * Real.exp (-(β * s)) / c * (A * ‖z‖) := hmain
    _ = B * A / c * Real.exp (-(β * s)) * ‖z‖ := by ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (P : ReebOrbit H) (u : ℂ → V 1) (d b : ℝ)
    (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (hlow : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖)
    (f : ℂ → V 1) (df cf bf : ℝ) (hbf : 0 < bf)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (ψ v : ℂ → ℂ) (hψ : Differentiable ℝ ψ) (hvρ : ∀ z, ‖v z‖ ≤ ρ / 2)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∃ β > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖ψ (cylInf s t) / cylInf s t - κ‖ ≤ C * Real.exp (-(β * s)) :=
  FiniteEnergyPlane.tubeCoords_div_sub_le_aux H P u d b hb ha hw N ρ c hρ hc hlow f df cf bf hbf hfa hfw ψ v hψ hvρ hf hDψ
