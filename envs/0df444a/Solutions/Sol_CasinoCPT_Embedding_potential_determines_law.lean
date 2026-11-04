-- Prove2me | solution 1 for CasinoCPT.Embedding.potential_determines_law
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T06:57:51.005646+00:00
-- url     : https://prove2.me/submissions/dfe52dda-e119-4bec-9d13-ef1cb3d1e67a

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding

namespace Casino31Aux

lemma integrable_abs_sub (μ : Measure ℤ) (hμ : InP0Z μ) (x : ℝ) :
    Integrable (fun y : ℤ => |x - (y : ℝ)|) μ := by
  have := hμ.1
  have h1 : Integrable (fun y : ℤ => x - (y : ℝ)) μ := (integrable_const x).sub hμ.2.1
  exact h1.abs

lemma abs_le_potential (μ : Measure ℤ) (hμ : InP0Z μ) (x : ℝ) : |x| ≤ potential μ x := by
  have := hμ.1
  have h1 : ∫ y, (x - (y : ℝ)) ∂μ = x := by
    rw [integral_sub (integrable_const x) hμ.2.1, hμ.2.2]; simp
  unfold potential
  calc |x| = |∫ y, (x - (y : ℝ)) ∂μ| := by rw [h1]
    _ ≤ ∫ y, |x - (y : ℝ)| ∂μ := abs_integral_le_integral_abs

lemma potential_midconvex (μ : Measure ℤ) (hμ : InP0Z μ) (x : ℝ) :
    2 * potential μ x ≤ potential μ (x - 1) + potential μ (x + 1) := by
  unfold potential
  rw [← integral_const_mul, ← integral_add (integrable_abs_sub μ hμ _) (integrable_abs_sub μ hμ _)]
  apply integral_mono ((integrable_abs_sub μ hμ x).const_mul 2)
    ((integrable_abs_sub μ hμ _).add (integrable_abs_sub μ hμ _))
  intro y
  simp only
  have := abs_add_le (x - 1 - (y:ℝ)) (x + 1 - y)
  have e : (x - 1 - (y:ℝ)) + (x + 1 - y) = 2 * (x - y) := by ring
  rw [e, abs_mul] at this
  simpa using this

lemma potential_outside (μ : Measure ℤ) (hμ : InP0Z μ) (T : ℕ)
    (hsupp : μ (Set.Icc (-(T : ℤ)) T) = 1) (x : ℤ) (hx : (T : ℤ) ≤ |x|) :
    potential μ (x : ℝ) = |(x : ℝ)| := by
  have := hμ.1
  have hae : ∀ᵐ y ∂μ, y ∈ Set.Icc (-(T : ℤ)) (T : ℤ) := by
    rw [ae_iff]
    have : {a | ¬ a ∈ Set.Icc (-(T : ℤ)) (T : ℤ)} = (Set.Icc (-(T : ℤ)) (T : ℤ))ᶜ := rfl
    rw [this, prob_compl_eq_zero_iff (measurableSet_Icc)]; exact hsupp
  unfold potential
  rcases le_or_gt 0 x with h0 | h0
  · have hxT : (T : ℤ) ≤ x := by rwa [abs_of_nonneg h0] at hx
    have : ∀ᵐ (y : ℤ) ∂μ, |(x : ℝ) - (y : ℝ)| = (x : ℝ) - y := by
      filter_upwards [hae] with y hy
      apply abs_of_nonneg
      have : y ≤ x := hy.2.trans hxT
      have : (y : ℝ) ≤ x := by exact_mod_cast this
      linarith
    rw [integral_congr_ae this, integral_sub (integrable_const _) hμ.2.1, hμ.2.2]
    simp [abs_of_nonneg (show (0:ℝ) ≤ x by exact_mod_cast h0)]
  · have hxT : x ≤ -(T : ℤ) := by rw [abs_of_neg h0] at hx; omega
    have : ∀ᵐ (y : ℤ) ∂μ, |(x : ℝ) - (y : ℝ)| = -((x : ℝ) - y) := by
      filter_upwards [hae] with y hy
      apply abs_of_nonpos
      have : x ≤ y := hxT.trans hy.1
      have : (x : ℝ) ≤ y := by exact_mod_cast this
      linarith
    rw [integral_congr_ae this, integral_neg, integral_sub (integrable_const _) hμ.2.1, hμ.2.2]
    simp [abs_of_neg (show (x:ℝ) < 0 by exact_mod_cast h0)]

lemma evol_succ (μ : Measure ℤ) (t : ℕ) (x : ℤ) :
    evol μ (t + 1) x = min ((evol μ t (x - 1) + evol μ t (x + 1)) / 2) (potential μ (x : ℝ)) :=
  rfl

lemma abs_le_avg (x : ℤ) : |(x : ℝ)| ≤ (|((x - 1 : ℤ) : ℝ)| + |((x + 1 : ℤ) : ℝ)|) / 2 := by
  push_cast
  have := abs_add_le ((x:ℝ) - 1) ((x:ℝ) + 1)
  have e : ((x:ℝ) - 1) + ((x:ℝ) + 1) = 2 * x := by ring
  rw [e, abs_mul] at this
  norm_num at this
  linarith

lemma evol_ge_abs (μ : Measure ℤ) (hμ : InP0Z μ) : ∀ (t : ℕ) (x : ℤ), |(x : ℝ)| ≤ evol μ t x := by
  intro t
  induction t with
  | zero => intro x; simp [evol]
  | succ t ih =>
    intro x
    rw [evol_succ]
    apply le_min
    · have := abs_le_avg x
      have h1 := ih (x - 1); have h2 := ih (x + 1)
      linarith
    · exact abs_le_potential μ hμ _

lemma evol_le_potential (μ : Measure ℤ) (hμ : InP0Z μ) :
    ∀ (t : ℕ) (x : ℤ), evol μ t x ≤ potential μ (x : ℝ) := by
  intro t x
  cases t with
  | zero => simpa [evol] using abs_le_potential μ hμ (x : ℝ)
  | succ t => rw [evol_succ]; exact min_le_right _ _

/-- Prop A.2 (ii) core: parity. -/
lemma evol_parity (μ : Measure ℤ) (hμ : InP0Z μ) :
    ∀ (t : ℕ) (x : ℤ), Odd ((t : ℤ) + x) → evol μ (t + 1) x = evol μ t x := by
  intro t
  induction t with
  | zero =>
    intro x hx
    simp only [Nat.cast_zero, zero_add] at hx
    rw [evol_succ]
    simp only [evol]
    have hav : (|((x - 1 : ℤ) : ℝ)| + |((x + 1 : ℤ) : ℝ)|) / 2 = |(x : ℝ)| := by
      have hz : |x - 1| + |x + 1| = 2 * |x| := by
        obtain ⟨k, rfl⟩ := hx
        simp only [abs_eq_max_neg]; omega
      have hz' : ((|x - 1| + |x + 1| : ℤ) : ℝ) = ((2 * |x| : ℤ) : ℝ) := by rw [hz]
      push_cast at hz' ⊢
      linarith
    rw [hav]
    exact min_eq_left (abs_le_potential μ hμ _)
  | succ t ih =>
    intro x hx
    rw [evol_succ μ (t + 1) x, evol_succ μ t x]
    have h1 : Odd ((t : ℤ) + (x - 1)) := by
      have : ((t : ℤ) + (x - 1)) = ((t + 1 : ℕ) : ℤ) + x - 2 := by push_cast; ring
      rw [this]; exact hx.sub_even (by decide)
    have h2 : Odd ((t : ℤ) + (x + 1)) := by
      have : ((t : ℤ) + (x + 1)) = ((t + 1 : ℕ) : ℤ) + x := by push_cast; ring
      rw [this]; exact hx
    rw [ih _ h1, ih _ h2]

lemma evol_midconvex_and_le (μ : Measure ℤ) (hμ : InP0Z μ) :
    ∀ (t : ℕ) (x : ℤ), 2 * evol μ t x ≤ evol μ t (x - 1) + evol μ t (x + 1) := by
  intro t
  induction t with
  | zero =>
    intro x; simp only [evol]
    have := abs_le_avg x; push_cast at this ⊢; linarith
  | succ t ih =>
    intro x
    -- U_{t+1}(y) ≥ U_t(y)
    have hmono : ∀ y : ℤ, evol μ t y ≤ evol μ (t + 1) y := by
      intro y
      rw [evol_succ]
      apply le_min
      · have := ih y; linarith
      · exact evol_le_potential μ hμ t y
    have a := hmono (x - 1)
    have b := hmono (x + 1)
    have c : evol μ (t + 1) x ≤ (evol μ t (x - 1) + evol μ t (x + 1)) / 2 := by
      rw [evol_succ]; exact min_le_left _ _
    linarith

lemma evol_mono_succ (μ : Measure ℤ) (hμ : InP0Z μ) (t : ℕ) (y : ℤ) :
    evol μ t y ≤ evol μ (t + 1) y := by
  rw [evol_succ]
  apply le_min
  · have := evol_midconvex_and_le μ hμ t y; linarith
  · exact evol_le_potential μ hμ t y

end Casino31Aux

namespace Casino31Aux

lemma mass_eq_potential (μ : Measure ℤ) (hμ : InP0Z μ) (x : ℤ) :
    (μ {x}).toReal =
        (potential μ ((x : ℝ) + 1) + potential μ ((x : ℝ) - 1)) / 2 - potential μ (x : ℝ) := by
  have hP := hμ.1
  have hpt : ∀ y : ℤ, (|((x : ℝ) + 1) - (y : ℝ)| + |((x : ℝ) - 1) - (y : ℝ)|) / 2
      - |(x : ℝ) - (y : ℝ)| = ({x} : Set ℤ).indicator 1 y := by
    intro y
    have hz : |x + 1 - y| + |x - 1 - y| - 2 * |x - y| = if y = x then 2 else 0 := by
      split_ifs with h
      · subst h; simp
      · simp only [abs_eq_max_neg]; omega
    have hz' : ((|x + 1 - y| + |x - 1 - y| - 2 * |x - y| : ℤ) : ℝ)
        = ((if y = x then 2 else 0 : ℤ) : ℝ) := by rw [hz]
    push_cast at hz'
    simp only [Set.indicator, Set.mem_singleton_iff, Pi.one_apply]
    split_ifs at hz' ⊢ <;> linarith
  unfold potential
  have hA : Integrable (fun y : ℤ => (|((x : ℝ) + 1) - (y : ℝ)| + |((x : ℝ) - 1) - (y : ℝ)|) / 2) μ :=
    ((integrable_abs_sub μ hμ _).add (integrable_abs_sub μ hμ _)).div_const 2
  have h1 := integral_sub hA (integrable_abs_sub μ hμ (x : ℝ))
  rw [← integral_add (integrable_abs_sub μ hμ _) (integrable_abs_sub μ hμ _), ← integral_div]
  rw [← h1]
  simp_rw [hpt]
  rw [integral_indicator_one (measurableSet_singleton x), measureReal_def]

lemma eq_of_potential_int (μ ν : Measure ℤ) (hμ : InP0Z μ) (hν : InP0Z ν)
    (h : ∀ x : ℤ, potential μ (x : ℝ) = potential ν (x : ℝ)) : μ = ν := by
  have hP := hμ.1
  have hQ := hν.1
  rw [ext_iff_measureReal_singleton]
  intro x
  rw [measureReal_def, measureReal_def, mass_eq_potential μ hμ, mass_eq_potential ν hν]
  have e1 : ((x : ℝ) + 1) = ((x + 1 : ℤ) : ℝ) := by push_cast; ring
  have e2 : ((x : ℝ) - 1) = ((x - 1 : ℤ) : ℝ) := by push_cast; ring
  rw [e1, e2, h, h, h]

end Casino31Aux

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding Casino31Aux

theorem solution (μ ν : Measure ℤ) (hμ : InP0Z μ) (hν : InP0Z ν) :
    ((∀ x : ℝ, potential μ x = potential ν x) ↔ μ = ν) ∧
      ((∀ x : ℤ, potential μ (x : ℝ) = potential ν (x : ℝ)) ↔ μ = ν) := by
  refine ⟨⟨fun h => eq_of_potential_int μ ν hμ hν (fun x => h x), fun h x => by rw [h]⟩,
    ⟨eq_of_potential_int μ ν hμ hν, fun h x => by rw [h]⟩⟩
