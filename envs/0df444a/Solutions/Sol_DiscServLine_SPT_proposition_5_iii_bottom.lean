-- Prove2me | solution 1 for DiscServLine.SPT.proposition_5_iii_bottom
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:54:54.288444+00:00
-- url     : https://prove2.me/submissions/9339c1bd-e474-49a7-97cc-56078d1a505b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model
import Theorems.Thm_DiscServLine_SPT_lemma_A7
import Theorems.Thm_DiscServLine_SPT_W_quadratic_at_optimum

open DiscServLine.SPT

/-- At an optimal line, the one-sided slope of the price at the bottom end, expressed through the
root `ω = w²` of (A–35) (Lemma A7) and the quadratic waiting time. -/
private theorem slope_bottom (P : Params) (hP : P.Standing) (d : Design) (hd : IsOptimal P d) :
    ∃ s r w : ℝ, s ^ 2 = 1 + κ P ∧ r ^ 2 = 1 + w ^ 2 * κ P ∧ 0 < w ∧ w < 1 ∧ 1 ≤ r ∧ r < s ∧
      HasDerivWithinAt (price P d)
        ((1 - w ^ 2) * ((P.θbar - P.c) / (r * (r + s * w)) - P.c * s * κ P / (s + r)))
        (Set.Icc d.lo d.hi) d.lo := by
  obtain ⟨-, hall⟩ := lemma_A7 P hP
  obtain ⟨ω, ⟨hω0, hω1⟩, -, -, -, -, hlo, hhi⟩ := hall d hd
  obtain ⟨α0, α2, hα2, hW, hhi2⟩ := W_quadratic_at_optimum P hP d hd
  have hlohi : d.lo ≤ d.hi := hd.1.1.2.2.1
  obtain ⟨hc, hcθ, hb, hΛ⟩ := hP
  have hκ : 0 < κ P := by unfold κ; positivity
  set s := Real.sqrt (1 + κ P) with hs
  set w := Real.sqrt ω with hw
  have hr1 : 0 < 1 + ω * κ P := by positivity
  set r := Real.sqrt (1 + ω * κ P) with hr
  have hs2 : s ^ 2 = 1 + κ P := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 = 1 + ω * κ P := Real.sq_sqrt hr1.le
  have hw2 : w ^ 2 = ω := Real.sq_sqrt hω0.le
  have hwpos : 0 < w := Real.sqrt_pos.mpr hω0
  have hw1 : w < 1 := by nlinarith
  have hrpos : 0 < r := Real.sqrt_pos.mpr hr1
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hr1' : 1 ≤ r := by nlinarith [mul_pos hω0 hκ]
  have hsr : r < s := by nlinarith [mul_pos hω0 hκ]
  have hq : Real.sqrt (ω / (1 + ω * κ P)) = w / r := by
    rw [Real.sqrt_div' _ hr1.le]
  -- the price is the quadratic q on the line
  set q : ℝ → ℝ := fun t => (P.θbar * t - P.b * t ^ 2) - P.c * (t + (-α0 + t ^ 2 * α2)) with hqdef
  have heq : Set.EqOn q (price P d) (Set.Icc d.lo d.hi) := by
    intro t ht; simp only [hqdef, price, hW t ht]
  have hderiv : ∀ t, HasDerivAt q (P.θbar - 2 * P.b * t - P.c * (1 + 2 * α2 * t)) t := by
    intro t
    have := (((hasDerivAt_id t).const_mul P.θbar).sub ((hasDerivAt_pow 2 t).const_mul P.b)).sub
      (((hasDerivAt_id t).add (((hasDerivAt_pow 2 t).mul_const α2).const_add (-α0))).const_mul P.c)
    exact (this.congr_deriv (by simp; ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp [hqdef])
  refine ⟨s, r, w, hs2, by rw [hr2, hw2], hwpos, hw1, hr1', hsr, ?_⟩
  have hval : P.θbar - 2 * P.b * d.lo - P.c * (1 + 2 * α2 * d.lo) =
      (1 - w ^ 2) * ((P.θbar - P.c) / (r * (r + s * w)) - P.c * s * κ P / (s + r)) := by
    rw [hhi] at hhi2
    unfold tHiA7 at hhi2
    rw [← hs, ← hr, hq] at hhi2
    rw [hlo]
    unfold tLoA7
    rw [← hs, ← hr]
    have hD : 0 < s - r := by linarith
    have hk : 0 < P.c / (2 * P.b) := by positivity
    set lo := P.c / (2 * P.b) * s * (s - r) with hlodef
    set hi := P.c / (2 * P.b) * (s - r) / (w / r) with hhidef
    have hlohi' : lo = hi * (s * w / r) := by
      rw [hlodef, hhidef]; field_simp
    have h2 : 2 * α2 * lo = (P.θbar / P.c - 1) * (s * w / r) := by
      rw [hlohi', ← hhi2]; ring
    have h3 : 2 * P.b * lo = P.c * s * (s - r) := by
      rw [hlodef]; field_simp
    have h4 : P.θbar - 2 * P.b * lo - P.c * (1 + 2 * α2 * lo) =
        (P.θbar - P.c) * (1 - s * w / r) - P.c * s * (s - r) := by
      rw [show P.c * (1 + 2 * α2 * lo) = P.c + P.c * (2 * α2 * lo) by ring, h2, h3]
      field_simp; ring
    rw [h4]
    have hκv : κ P = s ^ 2 - 1 := by linarith
    have hr2' : r ^ 2 = 1 + w ^ 2 * (s ^ 2 - 1) := by rw [hr2, hκv, hw2]
    rw [hκv]
    have hsw : 0 < r + s * w := by positivity
    have hsr' : 0 < s + r := by positivity
    have ha : 1 - s * w / r = (1 - w ^ 2) / (r * (r + s * w)) := by
      field_simp; linear_combination hr2'
    have hb' : s - r = (s ^ 2 - 1) * (1 - w ^ 2) / (s + r) := by
      field_simp; linear_combination -hr2'
    rw [ha, hb']; ring
  rw [← hval]
  exact (hderiv d.lo).hasDerivWithinAt.congr_of_mem (fun t ht => (heq ht).symm)
    ⟨le_refl _, hlohi⟩

theorem solution (θbar b c : ℝ) (hc : 0 < c) (hcθ : c < θbar) (hb : 0 < b) :
    (∀ Λ : ℝ, 0 < Λ → ∃ d, IsOptimal ⟨θbar, b, c, Λ⟩ d) ∧
      ∃ Λlow Λhigh : ℝ, 0 < Λlow ∧ 0 < Λhigh ∧
        (∀ Λ ∈ Set.Ioo 0 Λlow, ∀ d, IsOptimal ⟨θbar, b, c, Λ⟩ d →
          ∃ p < 0, HasDerivWithinAt (price ⟨θbar, b, c, Λ⟩ d) p (Set.Icc d.lo d.hi) d.lo) ∧
        (∀ Λ ∈ Set.Ioi Λhigh, ∀ d, IsOptimal ⟨θbar, b, c, Λ⟩ d →
          ∃ p > 0, HasDerivWithinAt (price ⟨θbar, b, c, Λ⟩ d) p (Set.Icc d.lo d.hi) d.lo) := by
  have hM : 0 < θbar - c := by linarith
  refine ⟨fun Λ hΛ => (lemma_A7 _ ⟨hc, hcθ, hb, hΛ⟩).1, b / (θbar - c),
    2 * b / c + 12 * b / (θbar - c), by positivity, by positivity, ?_, ?_⟩
  · rintro Λ ⟨hΛ, hΛlow⟩ d hd
    obtain ⟨s, r, w, hs2, hr2, hw0, hw1, hr1, hrs, hder⟩ := slope_bottom _ ⟨hc, hcθ, hb, hΛ⟩ d hd
    refine ⟨_, ?_, hder⟩
    simp only at hs2 hr2 ⊢
    set κ' := κ (⟨θbar, b, c, Λ⟩ : Params) with hκ'
    -- c κ > 2 (θ̄ − c)
    have hcκ : 2 * (θbar - c) < c * κ' := by
      rw [hκ']; unfold κ; simp only
      rw [lt_div_iff₀ hM] at hΛlow
      rw [show c * (2 * b / (Λ * c)) = 2 * b / Λ by field_simp]
      rw [lt_div_iff₀ hΛ]; linarith
    have hs1 : 1 < s := by nlinarith
    have hsw : 0 < r + s * w := by positivity
    have hsr : 0 < s + r := by positivity
    have hww : 0 < 1 - w ^ 2 := by nlinarith
    apply mul_neg_of_pos_of_neg hww
    rw [sub_neg, div_lt_div_iff₀ (by positivity) hsr]
    have h1 : 1 ≤ r * (r + s * w) := by nlinarith [mul_pos (by linarith : (0:ℝ) < s) hw0]
    have h2 : (θbar - c) * (s + r) ≤ (θbar - c) * (2 * s) := by nlinarith
    have h3 : c * s * κ' * 1 ≤ c * s * κ' * (r * (r + s * w)) := by
      apply mul_le_mul_of_nonneg_left h1; nlinarith
    nlinarith
  · intro Λ hΛhigh d hd
    have hΛpos : 0 < Λ := lt_trans (by positivity) hΛhigh
    obtain ⟨s, r, w, hs2, hr2, hw0, hw1, hr1, hrs, hder⟩ := slope_bottom _ ⟨hc, hcθ, hb, hΛpos⟩ d hd
    refine ⟨_, ?_, hder⟩
    simp only at hs2 hr2 ⊢
    set κ' := κ (⟨θbar, b, c, Λ⟩ : Params) with hκ'
    have hκpos : 0 < κ' := by rw [hκ']; unfold κ; simp only; positivity
    simp only [Set.mem_Ioi] at hΛhigh
    have hcκ : c * κ' * 6 < θbar - c := by
      rw [hκ']; unfold κ; simp only
      rw [show c * (2 * b / (Λ * c)) = 2 * b / Λ by field_simp]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hΛpos]
      have : 12 * b / (θbar - c) < Λ := by
        have : 0 < 2 * b / c := by positivity
        linarith
      rw [div_lt_iff₀ hM] at this; linarith
    have hκ1 : κ' < 1 := by
      rw [hκ']; unfold κ; simp only
      rw [div_lt_one (by positivity)]
      have : 2 * b / c < Λ := by
        have : 0 < 12 * b / (θbar - c) := by positivity
        linarith
      rw [div_lt_iff₀ hc] at this; linarith
    have hs32 : s < 3 / 2 := by nlinarith
    have hspos : 0 < s := by linarith
    have hsw : 0 < r + s * w := by positivity
    have hsr : 0 < s + r := by positivity
    have hww : 0 < 1 - w ^ 2 := by nlinarith
    apply mul_pos hww
    rw [sub_pos, div_lt_div_iff₀ hsr (by positivity)]
    -- c s κ r (r + s w) ≤ c κ · s · s · 2 s < 2 (θ̄ − c) ≤ (θ̄ − c)(s + r)
    have h1 : r * (r + s * w) ≤ s * (2 * s) := by
      have : s * w ≤ s := by nlinarith
      nlinarith
    have hs3 : s * (s * (2 * s)) < 6 := by nlinarith
    have h2 : c * s * κ' * (r * (r + s * w)) ≤ c * κ' * (s * (s * (2 * s))) := by
      have : 0 ≤ c * s * κ' := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 this]
    have h3 : c * κ' * (s * (s * (2 * s))) ≤ c * κ' * 6 := by
      have : 0 < c * κ' := by positivity
      nlinarith
    nlinarith
