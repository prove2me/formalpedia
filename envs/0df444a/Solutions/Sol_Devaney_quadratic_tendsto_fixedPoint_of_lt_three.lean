-- Prove2me | solution 1 for Devaney.quadratic_tendsto_fixedPoint_of_lt_three
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T18:50:46.426815+00:00
-- url     : https://prove2.me/submissions/55f3492a-1965-4d3f-9350-b9431d57c3fc

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Filter Topology Set Devaney

/-!
# Global convergence to the attracting fixed point of `Fμ` for `1 < μ < 3`

Mathlib has no interval dynamics at all.  The two ingredients built here are a general
monotone-orbit convergence lemma for a monotone self-map of a compact interval, and the
absence of genuine 2-cycles for the quadratic family below the first period doubling.
-/

namespace QuadConvAux

/-! ### Elementary facts about the quadratic family -/

theorem quad_eq (μ x : ℝ) : quadratic μ x = μ * x * (1 - x) := rfl

theorem hasDerivAt_quad (μ x : ℝ) : HasDerivAt (quadratic μ) (μ * (1 - 2 * x)) x := by
  have h1 : HasDerivAt (fun t : ℝ => μ * t) μ x := by
    simpa using (hasDerivAt_id x).const_mul μ
  have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
  have := h1.mul h2
  have he : μ * (1 - x) + μ * x * -1 = μ * (1 - 2 * x) := by ring
  rw [he] at this
  exact this

theorem deriv_quad (μ x : ℝ) : deriv (quadratic μ) x = μ * (1 - 2 * x) :=
  (hasDerivAt_quad μ x).deriv

theorem cont_quad (μ : ℝ) : Continuous (quadratic μ) := by
  unfold quadratic; fun_prop

theorem quad_le {μ : ℝ} (hμ : 0 < μ) (x : ℝ) : quadratic μ x ≤ μ / 4 := by
  rw [quad_eq]; nlinarith [sq_nonneg (x - 1 / 2)]

theorem quad_pos {μ : ℝ} (hμ : 0 < μ) {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    0 < quadratic μ x := by
  rw [quad_eq]; positivity

theorem quad_sub {μ : ℝ} (hμ : 0 < μ) (x : ℝ) :
    quadratic μ x - x = μ * x * ((μ - 1) / μ - x) := by
  rw [quad_eq]; field_simp; ring

theorem quad_zero (μ : ℝ) : quadratic μ 0 = 0 := by rw [quad_eq]; ring

theorem quad_fix {μ : ℝ} (hμ : 0 < μ) : quadratic μ ((μ - 1) / μ) = (μ - 1) / μ := by
  have h := quad_sub hμ ((μ - 1) / μ)
  simp only [sub_self, mul_zero] at h
  linarith

theorem fixed_iff {μ : ℝ} (hμ : 0 < μ) {x : ℝ} :
    quadratic μ x = x ↔ x = 0 ∨ x = (μ - 1) / μ := by
  constructor
  · intro h
    have h2 : μ * x * ((μ - 1) / μ - x) = 0 := by rw [← quad_sub hμ, h, sub_self]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 (ne_of_gt hμ)
      · exact Or.inl h4
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · exact quad_zero μ
    · exact quad_fix hμ

/-- Below the first period doubling the quadratic map has no genuine 2-cycle. -/
theorem no_two_cycle {μ : ℝ} (hμ : 1 < μ) (hμ3 : μ < 3) {a : ℝ}
    (h : quadratic μ (quadratic μ a) = a) : quadratic μ a = a := by
  set b := quadratic μ a with hb
  have ha : μ * a * (1 - a) = b := rfl
  have hba : μ * b * (1 - b) = a := h
  have key : (a - b) * (μ - μ * (a + b) + 1) = 0 := by linear_combination ha - hba
  rcases mul_eq_zero.1 key with h1 | h1
  · linarith [sub_eq_zero.1 h1]
  · exfalso
    have hμ0 : (0 : ℝ) < μ := by linarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_pos hμ0 hμ0]

/-! ### Monotone orbits on a compact interval -/

theorem mono_orbit {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    (hmono : MonotoneOn g (Icc a b)) (hmaps : MapsTo g (Icc a b) (Icc a b))
    {y : ℝ} (hy : y ∈ Icc a b) :
    ∃ q ∈ Icc a b, g q = q ∧ Tendsto (fun n => g^[n] y) atTop (𝓝 q) := by
  have hmem : ∀ n, g^[n] y ∈ Icc a b := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih => rw [Function.iterate_succ_apply']; exact hmaps ih
  have hstep : ∀ (s : ℕ → ℝ), s = (fun n => g^[n] y) → True := fun _ _ => trivial
  rcases le_total y (g y) with h | h
  · have hmo : Monotone (fun n => g^[n] y) := by
      apply monotone_nat_of_le_succ
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        calc g^[n + 1] y = g (g^[n] y) := Function.iterate_succ_apply' g n y
          _ ≤ g (g^[n + 1] y) := hmono (hmem n) (hmem (n + 1)) ih
          _ = g^[n + 1 + 1] y := (Function.iterate_succ_apply' g (n + 1) y).symm
    have hbdd : BddAbove (Set.range fun n => g^[n] y) := by
      refine ⟨b, ?_⟩; rintro _ ⟨n, rfl⟩; exact (hmem n).2
    have htend : Tendsto (fun n => g^[n] y) atTop (𝓝 (⨆ n, g^[n] y)) :=
      tendsto_atTop_ciSup hmo hbdd
    refine ⟨⨆ n, g^[n] y, ⟨?_, ?_⟩, ?_, htend⟩
    · exact le_trans hy.1 (by simpa using le_ciSup hbdd 0)
    · exact ciSup_le fun n => (hmem n).2
    · have h2 : Tendsto (fun n => g (g^[n] y)) atTop (𝓝 (g (⨆ n, g^[n] y))) :=
        (hg.tendsto _).comp htend
      have h3 : (fun n => g (g^[n] y)) = fun n => g^[n + 1] y := by
        funext n; rw [Function.iterate_succ_apply']
      rw [h3] at h2
      exact tendsto_nhds_unique h2 (htend.comp (tendsto_add_atTop_nat 1))
  · have hmo : Antitone (fun n => g^[n] y) := by
      apply antitone_nat_of_succ_le
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        calc g^[n + 1 + 1] y = g (g^[n + 1] y) := Function.iterate_succ_apply' g (n + 1) y
          _ ≤ g (g^[n] y) := hmono (hmem (n + 1)) (hmem n) ih
          _ = g^[n + 1] y := (Function.iterate_succ_apply' g n y).symm
    have hbdd : BddBelow (Set.range fun n => g^[n] y) := by
      refine ⟨a, ?_⟩; rintro _ ⟨n, rfl⟩; exact (hmem n).1
    have htend : Tendsto (fun n => g^[n] y) atTop (𝓝 (⨅ n, g^[n] y)) :=
      tendsto_atTop_ciInf hmo hbdd
    refine ⟨⨅ n, g^[n] y, ⟨?_, ?_⟩, ?_, htend⟩
    · exact le_ciInf fun n => (hmem n).1
    · exact le_trans (by simpa using ciInf_le hbdd 0) hy.2
    · have h2 : Tendsto (fun n => g (g^[n] y)) atTop (𝓝 (g (⨅ n, g^[n] y))) :=
        (hg.tendsto _).comp htend
      have h3 : (fun n => g (g^[n] y)) = fun n => g^[n + 1] y := by
        funext n; rw [Function.iterate_succ_apply']
      rw [h3] at h2
      exact tendsto_nhds_unique h2 (htend.comp (tendsto_add_atTop_nat 1))

theorem tendsto_even_odd {s : ℕ → ℝ} {L : ℝ}
    (he : Tendsto (fun k => s (2 * k)) atTop (𝓝 L))
    (ho : Tendsto (fun k => s (2 * k + 1)) atTop (𝓝 L)) :
    Tendsto s atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at he ho ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := he ε hε
  obtain ⟨N₂, hN₂⟩ := ho ε hε
  refine ⟨2 * (max N₁ N₂) + 1, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : n = 2 * k := by omega
    have : N₁ ≤ k := by omega
    have := hN₁ k this
    rwa [← hk2] at this
  · have : N₂ ≤ k := by omega
    have := hN₂ k this
    rwa [← hk] at this

/-! ### Monotonicity of the quadratic map on the two halves -/

theorem quad_mono {μ : ℝ} (hμ0 : 0 < μ) {x y : ℝ} (hxy : x ≤ y) (h : x + y ≤ 1) :
    quadratic μ x ≤ quadratic μ y := by
  rw [quad_eq, quad_eq]
  nlinarith [mul_nonneg (mul_nonneg hμ0.le (sub_nonneg.2 hxy)) (by linarith : (0:ℝ) ≤ 1 - (x + y))]

theorem quad_anti {μ : ℝ} (hμ0 : 0 < μ) {x y : ℝ} (hxy : x ≤ y) (h : 1 ≤ x + y) :
    quadratic μ y ≤ quadratic μ x := by
  rw [quad_eq, quad_eq]
  nlinarith [mul_nonneg (mul_nonneg hμ0.le (sub_nonneg.2 hxy)) (by linarith : (0:ℝ) ≤ (x + y) - 1)]

theorem p_pos {μ : ℝ} (hμ : 1 < μ) : 0 < (μ - 1) / μ := by
  apply div_pos <;> linarith

theorem p_lt_one {μ : ℝ} (hμ : 1 < μ) : (μ - 1) / μ < 1 := by
  rw [div_lt_one (by linarith)]; linarith

theorem p_le_M {μ : ℝ} (hμ : 1 < μ) : (μ - 1) / μ ≤ μ / 4 := by
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith [sq_nonneg (μ - 2)]

theorem M_lt_one {μ : ℝ} (hμ3 : μ < 3) : μ / 4 < 1 := by linarith

theorem FM_pos {μ : ℝ} (hμ : 1 < μ) (hμ3 : μ < 3) : 0 < quadratic μ (μ / 4) :=
  quad_pos (by linarith) (by linarith) (M_lt_one hμ3)

theorem iter_le {μ : ℝ} (hμ0 : 0 < μ) {y : ℝ} (hy : y ≤ μ / 4) (n : ℕ) :
    (quadratic μ)^[n] y ≤ μ / 4 := by
  cases n with
  | zero => simpa using hy
  | succ n => rw [Function.iterate_succ_apply']; exact quad_le hμ0 _

/-! ### The trapping interval -/

theorem key_interval {μ : ℝ} (hμ : 1 < μ) (hμ3 : μ < 3) :
    ∃ m : ℝ, 0 < m ∧ m ≤ (μ - 1) / μ ∧
      MapsTo (quadratic μ) (Icc m (μ / 4)) (Icc m (μ / 4)) ∧
      MonotoneOn (quadratic μ ∘ quadratic μ) (Icc m (μ / 4)) := by
  have hμ0 : (0 : ℝ) < μ := by linarith
  rcases le_or_gt μ 2 with h2 | h2
  · -- `μ ≤ 2`: the map is increasing on `[p, μ/4] ⊆ [0, 1/2]`
    have hM2 : μ / 4 ≤ 1 / 2 := by linarith
    have hmaps : MapsTo (quadratic μ) (Icc ((μ - 1) / μ) (μ / 4)) (Icc ((μ - 1) / μ) (μ / 4)) := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, quad_le hμ0 x⟩
      have := quad_mono hμ0 hx1 (by linarith [p_le_M hμ])
      rwa [quad_fix hμ0] at this
    refine ⟨(μ - 1) / μ, p_pos hμ, le_rfl, hmaps, ?_⟩
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ hxy
    have h1 : quadratic μ x ≤ quadratic μ y := quad_mono hμ0 hxy (by linarith)
    have hfx := hmaps ⟨hx1, hx2⟩
    have hfy := hmaps ⟨hy1, hy2⟩
    exact quad_mono hμ0 h1 (by linarith [hfx.2, hfy.2])
  · -- `2 < μ < 3`: the map is decreasing on `[F(μ/4), μ/4] ⊆ [1/2, 1]`
    have hhalf : (1 : ℝ) / 2 ≤ quadratic μ (μ / 4) := by
      rw [quad_eq]
      nlinarith [mul_pos (sub_pos.2 h2) (by nlinarith [sq_nonneg (μ - 1)] : (0:ℝ) < 4 + 2 * μ - μ ^ 2)]
    have hle : quadratic μ (μ / 4) ≤ (μ - 1) / μ := by
      rw [quad_eq, le_div_iff₀ hμ0]
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ μ - 2)
        (by linarith : (0:ℝ) ≤ μ - 2)) (by linarith : (0:ℝ) ≤ μ - 2))
        (by linarith : (0:ℝ) ≤ μ + 2)]
    have hM1 : μ / 4 ≤ 1 := by linarith
    have hmaps : MapsTo (quadratic μ) (Icc (quadratic μ (μ / 4)) (μ / 4))
        (Icc (quadratic μ (μ / 4)) (μ / 4)) := by
      rintro x ⟨hx1, hx2⟩
      exact ⟨quad_anti hμ0 hx2 (by linarith [p_le_M hμ]), quad_le hμ0 x⟩
    refine ⟨quadratic μ (μ / 4), FM_pos hμ hμ3, hle, hmaps, ?_⟩
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ hxy
    have h1 : quadratic μ y ≤ quadratic μ x := quad_anti hμ0 hxy (by linarith)
    have hfx := hmaps ⟨hx1, hx2⟩
    have hfy := hmaps ⟨hy1, hy2⟩
    exact quad_anti hμ0 h1 (by linarith [hfx.1, hfy.1])

/-! ### Convergence -/

theorem iterate_two (μ : ℝ) : (quadratic μ)^[2] = quadratic μ ∘ quadratic μ := by
  funext z; simp [Function.iterate_succ_apply]

theorem conv_in_K {μ : ℝ} (hμ : 1 < μ) (hμ3 : μ < 3) {m y : ℝ} (hm : 0 < m)
    (hmaps : MapsTo (quadratic μ) (Icc m (μ / 4)) (Icc m (μ / 4)))
    (hmono2 : MonotoneOn (quadratic μ ∘ quadratic μ) (Icc m (μ / 4)))
    (hy : y ∈ Icc m (μ / 4)) :
    Tendsto (fun n => (quadratic μ)^[n] y) atTop (𝓝 ((μ - 1) / μ)) := by
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hmaps2 : MapsTo (quadratic μ ∘ quadratic μ) (Icc m (μ / 4)) (Icc m (μ / 4)) :=
    hmaps.comp hmaps
  obtain ⟨q, hq, hfq, htend⟩ :=
    mono_orbit ((cont_quad μ).comp (cont_quad μ)) hmono2 hmaps2 hy
  have hq2 : quadratic μ q = q := no_two_cycle hμ hμ3 hfq
  have hqp : q = (μ - 1) / μ := by
    rcases (fixed_iff hμ0).1 hq2 with h | h
    · exact absurd (h ▸ hq.1) (by simp [h]; linarith)
    · exact h
  rw [hqp] at htend
  have heven : Tendsto (fun n => (quadratic μ)^[2 * n] y) atTop (𝓝 ((μ - 1) / μ)) := by
    have : ∀ n, (quadratic μ)^[2 * n] y = (quadratic μ ∘ quadratic μ)^[n] y := by
      intro n; rw [Function.iterate_mul, iterate_two]
    simpa only [this] using htend
  refine tendsto_even_odd heven ?_
  have hc : Tendsto (fun n => quadratic μ ((quadratic μ)^[2 * n] y)) atTop
      (𝓝 (quadratic μ ((μ - 1) / μ))) := ((cont_quad μ).tendsto _).comp heven
  rw [quad_fix hμ0] at hc
  have he : ∀ n : ℕ, quadratic μ ((quadratic μ)^[2 * n] y) = (quadratic μ)^[2 * n + 1] y := by
    intro n; rw [Function.iterate_succ_apply']
  simpa only [he] using hc

theorem conv_below {μ : ℝ} (hμ : 1 < μ) (hμ3 : μ < 3) {y : ℝ} (hy0 : 0 < y)
    (hall : ∀ n, (quadratic μ)^[n] y < (μ - 1) / μ) :
    Tendsto (fun n => (quadratic μ)^[n] y) atTop (𝓝 ((μ - 1) / μ)) := by
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hpos : ∀ n, 0 < (quadratic μ)^[n] y := by
    intro n
    induction n with
    | zero => simpa using hy0
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact quad_pos hμ0 ih (lt_trans (hall n) (p_lt_one hμ))
  have hmo : Monotone (fun n => (quadratic μ)^[n] y) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [Function.iterate_succ_apply']
    have h := quad_sub hμ0 ((quadratic μ)^[n] y)
    nlinarith [hpos n, hall n, mul_pos hμ0 (hpos n)]
  have hbdd : BddAbove (Set.range fun n => (quadratic μ)^[n] y) := by
    refine ⟨(μ - 1) / μ, ?_⟩; rintro _ ⟨n, rfl⟩; exact (hall n).le
  have htend : Tendsto (fun n => (quadratic μ)^[n] y) atTop (𝓝 (⨆ n, (quadratic μ)^[n] y)) :=
    tendsto_atTop_ciSup hmo hbdd
  have hfix : quadratic μ (⨆ n, (quadratic μ)^[n] y) = ⨆ n, (quadratic μ)^[n] y := by
    have h2 : Tendsto (fun n => quadratic μ ((quadratic μ)^[n] y)) atTop
        (𝓝 (quadratic μ (⨆ n, (quadratic μ)^[n] y))) := ((cont_quad μ).tendsto _).comp htend
    have h3 : (fun n => quadratic μ ((quadratic μ)^[n] y)) = fun n => (quadratic μ)^[n + 1] y := by
      funext n; rw [Function.iterate_succ_apply']
    rw [h3] at h2
    exact tendsto_nhds_unique h2 (htend.comp (tendsto_add_atTop_nat 1))
  have hge : 0 < ⨆ n, (quadratic μ)^[n] y := by
    refine lt_of_lt_of_le hy0 ?_
    simpa using le_ciSup hbdd 0
  rcases (fixed_iff hμ0).1 hfix with h | h
  · exact absurd h (ne_of_gt hge)
  · rwa [h] at htend

theorem main_conv {μ : ℝ} (hμ : 1 < μ) (hμ3 : μ < 3) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun n => (quadratic μ)^[n] x) atTop (𝓝 ((μ - 1) / μ)) := by
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hy0 : 0 < quadratic μ x := quad_pos hμ0 hx0 hx1
  have hyM : quadratic μ x ≤ μ / 4 := quad_le hμ0 x
  have key : Tendsto (fun n => (quadratic μ)^[n] (quadratic μ x)) atTop (𝓝 ((μ - 1) / μ)) := by
    by_cases hc : ∃ N, (μ - 1) / μ ≤ (quadratic μ)^[N] (quadratic μ x)
    · obtain ⟨N, hN⟩ := hc
      obtain ⟨m, hm0, hmp, hmaps, hmono2⟩ := key_interval hμ hμ3
      have hz : (quadratic μ)^[N] (quadratic μ x) ∈ Icc m (μ / 4) :=
        ⟨le_trans hmp hN, iter_le hμ0 hyM N⟩
      have hzz := conv_in_K hμ hμ3 hm0 hmaps hmono2 hz
      rw [← tendsto_add_atTop_iff_nat N]
      simpa only [Function.iterate_add_apply] using hzz
    · push_neg at hc
      exact conv_below hμ hμ3 hy0 fun n => hc n
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa only [Function.iterate_succ_apply] using key

/-! ### The milestone -/

theorem devaney {μ : ℝ} (hμ : 1 < μ) (hμ3 : μ < 3) :
    quadratic μ 0 = 0 ∧ quadratic μ ((μ - 1) / μ) = (μ - 1) / μ ∧
      |deriv (quadratic μ) ((μ - 1) / μ)| < 1 ∧ 1 < |deriv (quadratic μ) 0| ∧
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        Tendsto (fun n : ℕ => (quadratic μ)^[n] x) atTop (𝓝 ((μ - 1) / μ)) := by
  have hμ0 : (0 : ℝ) < μ := by linarith
  refine ⟨quad_zero μ, quad_fix hμ0, ?_, ?_, fun x hx => main_conv hμ hμ3 hx.1 hx.2⟩
  · rw [deriv_quad]
    have h : μ * (1 - 2 * ((μ - 1) / μ)) = 2 - μ := by field_simp; ring
    rw [h, abs_lt]
    constructor <;> linarith
  · rw [deriv_quad]
    have h : μ * (1 - 2 * (0 : ℝ)) = μ := by ring
    rw [h, abs_of_pos hμ0]
    exact hμ

end QuadConvAux

theorem solution (μ : ℝ) (hμ : 1 < μ) (hμ' : μ < 3) :
    Devaney.quadratic μ 0 = 0 ∧ Devaney.quadratic μ ((μ - 1) / μ) = (μ - 1) / μ ∧
      |deriv (Devaney.quadratic μ) ((μ - 1) / μ)| < 1 ∧ 1 < |deriv (Devaney.quadratic μ) 0| ∧
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        Filter.Tendsto (fun n : ℕ => (Devaney.quadratic μ)^[n] x) Filter.atTop
          (nhds ((μ - 1) / μ)) :=
  QuadConvAux.devaney hμ hμ'
