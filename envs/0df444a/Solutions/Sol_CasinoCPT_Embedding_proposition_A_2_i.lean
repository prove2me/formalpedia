-- Prove2me | solution 1 for CasinoCPT.Embedding.proposition_A_2_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:06:03.682856+00:00
-- url     : https://prove2.me/submissions/1f7a8d8f-3e7c-4189-a6e7-d18344a4c09c

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

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding

namespace Casino31Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sv_of_le (S : ℕ → Ω → ℤ) (τ : Ω → ℕ∞) (n : ℕ) (ω : Ω) (h : (n : ℕ∞) ≤ τ ω) :
    stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)) ω = S n ω := by
  unfold stoppedValue
  congr 1
  have : (min (τ ω) (n:ℕ∞)) = (n:ℕ∞) := min_eq_right h
  exact (congrArg (fun z : ℕ∞ => WithTop.untopA (α := ℕ) z) this).trans rfl

lemma sv_of_ge (S : ℕ → Ω → ℤ) (τ : Ω → ℕ∞) (n : ℕ) (ω : Ω) (h : τ ω ≤ (n : ℕ∞)) :
    stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)) ω = stoppedValue S τ ω := by
  unfold stoppedValue
  congr 1
  have : (min (τ ω) (n:ℕ∞)) = τ ω := min_eq_left h
  exact (congrArg (fun z : ℕ∞ => WithTop.untopA (α := ℕ) z) this)

lemma enat_le_of_lt_succ (a : ℕ∞) (s : ℕ) (h : a < ((s + 1 : ℕ) : ℕ∞)) : a ≤ (s : ℕ∞) := by
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe k => norm_cast at h ⊢; omega

lemma enat_succ_le_iff (a : ℕ∞) (s : ℕ) : ((s + 1 : ℕ) : ℕ∞) ≤ a ↔ ¬ a ≤ (s : ℕ∞) := by
  induction a using ENat.recTopCoe with
  | top => simp
  | coe k => norm_cast; omega

/-- pointwise recursion of the stopped walk -/
lemma stopped_succ (S : ℕ → Ω → ℤ) (τ : Ω → ℕ∞) (s : ℕ) (ω : Ω) :
    stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)) ω =
      stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)) ω +
        (if ((s + 1 : ℕ) : ℕ∞) ≤ τ ω then S (s + 1) ω - S s ω else 0) := by
  split_ifs with h
  · have h' : (s : ℕ∞) ≤ τ ω := le_trans (by exact_mod_cast Nat.le_succ s) h
    rw [sv_of_le _ _ _ _ h, sv_of_le _ _ _ _ h']; ring
  · have h2 : τ ω ≤ (s : ℕ∞) := (enat_succ_le_iff _ _).not_left.mp h |> fun x => by
      by_contra hc; exact h ((enat_succ_le_iff _ _).mpr hc)
    have h1 : τ ω ≤ ((s + 1 : ℕ) : ℕ∞) := h2.trans (by exact_mod_cast Nat.le_succ s)
    rw [sv_of_ge _ _ _ _ h1, sv_of_ge _ _ _ _ h2]; ring

lemma stopped_zero (S : ℕ → Ω → ℤ) (τ : Ω → ℕ∞) (ω : Ω) :
    stoppedValue S (fun ω => min (τ ω) ((0 : ℕ) : ℕ∞)) ω = S 0 ω :=
  sv_of_le _ _ _ _ (by simp)

lemma abs_S_le {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) : ∀ (t : ℕ) (ω : Ω), |S t ω| ≤ t := by
  intro t
  induction t with
  | zero => intro ω; simp [hS.zero ω]
  | succ t ih =>
    intro ω
    have h1 := ih ω
    rcases hS.step t ω with h | h <;>
    · rw [abs_le] at h1 ⊢; push_cast; constructor <;> linarith [h1.1, h1.2]

lemma parity_S {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) : ∀ (t : ℕ) (ω : Ω), Even (S t ω - t) := by
  intro t
  induction t with
  | zero => intro ω; simp [hS.zero ω]
  | succ t ih =>
    intro ω
    obtain ⟨k, hk⟩ := ih ω
    rcases hS.step t ω with h | h
    · exact ⟨k, by push_cast; linarith⟩
    · exact ⟨k - 1, by push_cast; linarith⟩

lemma stopped_bound (S : ℕ → Ω → ℤ) (hb : ∀ (t : ℕ) (ω : Ω), |S t ω| ≤ t)
    (τ : Ω → ℕ∞) (s : ℕ) (ω : Ω) :
    |stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)) ω| ≤ s := by
  induction s with
  | zero => rw [stopped_zero]; have := hb 0 ω; simpa using this
  | succ s ih =>
    rw [stopped_succ]
    split_ifs with h
    · rw [sv_of_le _ _ _ _ (le_trans (by exact_mod_cast Nat.le_succ s) h)]
      have := hb (s + 1) ω
      simp only [add_sub_cancel]; exact this
    · simp only [add_zero]; push_cast; linarith

lemma meas_stopped {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ) :
    ∀ s : ℕ, Measurable[F s] (stoppedValue S (fun ω => min (τ ω) (s : ℕ∞))) := by
  intro s
  induction s with
  | zero =>
    have : stoppedValue S (fun ω => min (τ ω) ((0 : ℕ) : ℕ∞)) = S 0 := funext (stopped_zero S τ)
    rw [this]; exact hS.adapted 0
  | succ s ih =>
    have : stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)) = fun ω =>
        stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)) ω +
        (if ((s + 1 : ℕ) : ℕ∞) ≤ τ ω then S (s + 1) ω - S s ω else 0) :=
      funext (stopped_succ S τ s)
    rw [this]
    have hA : MeasurableSet[F s] {ω | ((s + 1 : ℕ) : ℕ∞) ≤ τ ω} := by
      have := (hτ (s)).compl
      convert this using 1
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact enat_succ_le_iff _ _
    have hmono := F.mono (Nat.le_succ s)
    apply Measurable.add (ih.mono hmono le_rfl)
    apply Measurable.ite (hmono _ hA)
    · exact (hS.adapted (s + 1)).sub ((hS.adapted s).mono hmono le_rfl)
    · exact measurable_const

end Casino31Prob

namespace Casino31Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma indep_fun_of {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (s : ℕ) (h : ℤ → ℝ) (f : Ω → ℝ) (hf : Measurable[F s] f) :
    IndepFun (fun ω => h (S (s + 1) ω - S s ω)) f P := by
  rw [IndepFun_iff_Indep]
  have h1 : MeasurableSpace.comap (fun ω => h (S (s + 1) ω - S s ω)) (borel ℝ) ≤
      MeasurableSpace.comap (fun ω => S (s + 1) ω - S s ω) inferInstance := by
    have : (fun ω => h (S (s + 1) ω - S s ω)) = h ∘ (fun ω => S (s + 1) ω - S s ω) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_from_top (f := h)).comap_le
  have h2 : MeasurableSpace.comap f (borel ℝ) ≤ F s := hf.comap_le
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (hS.indep s) h1) h2

lemma prob_up {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (s : ℕ) :
    P.real {ω | S (s + 1) ω - S s ω = 1} = 1 / 2 := by
  rw [measureReal_def, hS.fair s]; simp

lemma prob_down {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (s : ℕ) :
    P.real {ω | S (s + 1) ω - S s ω = -1} = 1 / 2 := by
  have hP := hS.isProb
  have hm : ∀ t, Measurable (S t) := fun t => (hS.adapted t).mono (F.le t) le_rfl
  have hDm : Measurable (fun ω => S (s + 1) ω - S s ω) := (hm (s + 1)).sub (hm s)
  have hcompl : {ω | S (s + 1) ω - S s ω = -1} = {ω | S (s + 1) ω - S s ω = 1}ᶜ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    rcases hS.step s ω with h | h <;> rw [h] <;> norm_num
  have hm1 : MeasurableSet {ω | S (s + 1) ω - S s ω = 1} := hDm (measurableSet_singleton 1)
  rw [hcompl, probReal_compl_eq_one_sub hm1, prob_up hS s]
  norm_num

/-- One step of the (possibly stopped) walk: the key expectation identity. -/
lemma key_step {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (s : ℕ) (X : Ω → ℤ) (hX : Measurable[F s] X)
    (p : Ω → Prop) [DecidablePred p] (hA : MeasurableSet[F s] {ω | p ω}) (g : ℤ → ℝ)
    (h0 : Integrable (fun ω => g (X ω)) P) (hp : Integrable (fun ω => g (X ω + 1)) P)
    (hn : Integrable (fun ω => g (X ω - 1)) P) :
    ∫ ω, g (X ω + (if p ω then S (s + 1) ω - S s ω else 0)) ∂P =
      ∫ ω, {ω | p ω}ᶜ.indicator (fun ω => g (X ω)) ω ∂P +
        ∫ ω, {ω | p ω}.indicator (fun ω => (g (X ω + 1) + g (X ω - 1)) / 2) ω ∂P := by
  have hP := hS.isProb
  set A : Set Ω := {ω | p ω} with hAdef
  set D : Ω → ℤ := fun ω => S (s + 1) ω - S s ω with hD
  let e1 : Ω → ℝ := fun ω => (fun z : ℤ => if z = 1 then (1:ℝ) else 0) (D ω)
  let e2 : Ω → ℝ := fun ω => (fun z : ℤ => if z = -1 then (1:ℝ) else 0) (D ω)
  have hF : F s ≤ mΩ := F.le s
  have hXm : Measurable X := hX.mono hF le_rfl
  have hAm : MeasurableSet A := hF _ hA
  have f1m : Measurable[F s] (A.indicator (fun ω => g (X ω + 1))) :=
    Measurable.indicator ((measurable_from_top (f := fun z : ℤ => g (z + 1))).comp hX) hA
  have f2m : Measurable[F s] (A.indicator (fun ω => g (X ω - 1))) :=
    Measurable.indicator ((measurable_from_top (f := fun z : ℤ => g (z - 1))).comp hX) hA
  have hDm : Measurable D :=
    ((hS.adapted (s + 1)).mono (F.le _) le_rfl).sub ((hS.adapted s).mono hF le_rfl)
  have e1m : Measurable e1 :=
    (measurable_from_top (f := fun z : ℤ => if z = 1 then (1:ℝ) else 0)).comp hDm
  have e2m : Measurable e2 :=
    (measurable_from_top (f := fun z : ℤ => if z = -1 then (1:ℝ) else 0)).comp hDm
  have hm1 : MeasurableSet {ω | D ω = 1} := hDm (measurableSet_singleton 1)
  have hm2 : MeasurableSet {ω | D ω = -1} := hDm (measurableSet_singleton (-1))
  have i1 := indep_fun_of hS s (fun z : ℤ => if z = 1 then (1:ℝ) else 0) _ f1m
  have i2 := indep_fun_of hS s (fun z : ℤ => if z = -1 then (1:ℝ) else 0) _ f2m
  have I1 : Integrable (A.indicator (fun ω => g (X ω + 1))) P := hp.indicator hAm
  have I2 : Integrable (A.indicator (fun ω => g (X ω - 1))) P := hn.indicator hAm
  have E1 : ∫ ω, e1 ω ∂P = 1 / 2 := by
    have : e1 = {ω | D ω = 1}.indicator 1 := by
      ext ω; simp only [e1, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [this, integral_indicator_one hm1]
    exact prob_up hS s
  have E2 : ∫ ω, e2 ω ∂P = 1 / 2 := by
    have : e2 = {ω | D ω = -1}.indicator 1 := by
      ext ω; simp only [e2, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [this, integral_indicator_one hm2]
    exact prob_down hS s
  have J1 := i1.integral_fun_mul_eq_mul_integral e1m.aestronglyMeasurable I1.1
  have J2 := i2.integral_fun_mul_eq_mul_integral e2m.aestronglyMeasurable I2.1
  have hb1 : ∀ ω, ‖e1 ω‖ ≤ 1 := by intro ω; simp only [e1]; split_ifs <;> simp
  have hb2 : ∀ ω, ‖e2 ω‖ ≤ 1 := by intro ω; simp only [e2]; split_ifs <;> simp
  have K1 : Integrable (fun ω => e1 ω * A.indicator (fun ω => g (X ω + 1)) ω) P :=
    I1.bdd_mul e1m.aestronglyMeasurable (Filter.Eventually.of_forall hb1)
  have K2 : Integrable (fun ω => e2 ω * A.indicator (fun ω => g (X ω - 1)) ω) P :=
    I2.bdd_mul e2m.aestronglyMeasurable (Filter.Eventually.of_forall hb2)
  have K0 : Integrable (Aᶜ.indicator (fun ω => g (X ω))) P := h0.indicator hAm.compl
  have hpt : ∀ ω, g (X ω + (if p ω then D ω else 0)) =
      Aᶜ.indicator (fun ω => g (X ω)) ω + (e1 ω * A.indicator (fun ω => g (X ω + 1)) ω +
        e2 ω * A.indicator (fun ω => g (X ω - 1)) ω) := by
    intro ω
    by_cases hω : ω ∈ A
    · have hω' : p ω := hω
      simp only [hω', if_true, Set.indicator_of_mem hω, Set.indicator_of_notMem
        (Set.notMem_compl_iff.mpr hω), e1, e2]
      rcases hS.step s ω with h | h
      · have : D ω = 1 := h
        rw [this]; norm_num
      · have : D ω = -1 := h
        rw [this]; norm_num; ring_nf
    · have hω' : ¬ p ω := hω
      simp only [hω', if_false, Set.indicator_of_notMem hω, Set.indicator_of_mem
        (Set.mem_compl hω)]
      simp
  refine (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans ?_
  have Ksum : Integrable (fun ω => e1 ω * A.indicator (fun ω => g (X ω + 1)) ω +
      e2 ω * A.indicator (fun ω => g (X ω - 1)) ω) P := K1.add K2
  rw [integral_add K0 Ksum, integral_add K1 K2, J1, J2, E1, E2]
  congr 1
  rw [← mul_add, ← integral_add I1 I2, ← integral_const_mul]
  congr 1; ext ω
  simp only [Set.indicator]
  split_ifs <;> ring

end Casino31Prob

namespace Casino31Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma pot_map (P : Measure Ω) (X : Ω → ℤ) (hX : Measurable X) (x : ℝ) :
    potential (P.map X) x = ∫ ω, |x - (X ω : ℝ)| ∂P := by
  unfold potential
  exact integral_map hX.aemeasurable
    (measurable_from_top (f := fun y : ℤ => |x - (y : ℝ)|)).aestronglyMeasurable

lemma integrable_bdd (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℤ) (hX : Measurable X)
    (C : ℤ) (hC : ∀ ω, |X ω| ≤ C) (g : ℤ → ℝ) (k : ℤ) (x : ℝ)
    (hg : ∀ y : ℤ, |g y| ≤ |x| + |(y : ℝ)|) :
    Integrable (fun ω => g (X ω + k)) P := by
  refine Integrable.of_bound ((measurable_from_top (f := fun y : ℤ => g (y + k))).comp hX
    ).aestronglyMeasurable (|x| + C + |(k : ℝ)|) (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs]
  refine (hg _).trans ?_
  have h1 : |((X ω + k : ℤ) : ℝ)| ≤ |(X ω : ℝ)| + |(k : ℝ)| := by push_cast; exact abs_add_le _ _
  have h2 : |(X ω : ℝ)| ≤ (C : ℝ) := by
    have := hC ω; rw [← Int.cast_abs]; exact_mod_cast this
  linarith

lemma kernel_bound (x : ℝ) (y : ℤ) : |(|x - (y : ℝ)|)| ≤ |x| + |(y : ℝ)| := by
  rw [abs_abs]; exact abs_sub _ _

lemma second_diff (x y : ℤ) :
    (|(x : ℝ) - ((y + 1 : ℤ) : ℝ)| + |(x : ℝ) - ((y - 1 : ℤ) : ℝ)|) / 2 - |(x : ℝ) - (y : ℝ)| =
      if y = x then 1 else 0 := by
  have hz : |x - (y + 1)| + |x - (y - 1)| - 2 * |x - y| = if y = x then 2 else 0 := by
    split_ifs with h
    · subst h; simp
    · simp only [abs_eq_max_neg]; omega
  have hz' : ((|x - (y + 1)| + |x - (y - 1)| - 2 * |x - y| : ℤ) : ℝ)
      = ((if y = x then 2 else 0 : ℤ) : ℝ) := by rw [hz]
  push_cast at hz' ⊢
  split_ifs at hz' ⊢ <;> linarith

/-- Proposition A.1 (iii), eq. (17), in the form `t = s + 1`. -/
lemma pot_step {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ) (s : ℕ) (x : ℤ) :
    potential (P.map (stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)))) (x : ℝ) =
      potential (P.map (stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)))) (x : ℝ) +
        (P {ω | S s ω = x ∧ ((s + 1 : ℕ) : ℕ∞) ≤ τ ω}).toReal := by
  have hP := hS.isProb
  set X := stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)) with hXdef
  have hXF : Measurable[F s] X := meas_stopped hS τ hτ s
  have hXm : Measurable X := hXF.mono (F.le s) le_rfl
  have hXF1 := meas_stopped hS τ hτ (s + 1)
  have hX1m := hXF1.mono (F.le (s + 1)) le_rfl
  have hb : ∀ ω, |X ω| ≤ (s : ℤ) := stopped_bound S (abs_S_le hS) τ s
  let g : ℤ → ℝ := fun y => |(x : ℝ) - (y : ℝ)|
  have hg : ∀ y : ℤ, |g y| ≤ |(x : ℝ)| + |(y : ℝ)| := kernel_bound _
  have I : ∀ k : ℤ, Integrable (fun ω => g (X ω + k)) P :=
    fun k => integrable_bdd P X hXm s hb g k x hg
  have I0 : Integrable (fun ω => g (X ω)) P := by simpa using I 0
  have Ip : Integrable (fun ω => g (X ω + 1)) P := I 1
  have In : Integrable (fun ω => g (X ω - 1)) P := by simpa [sub_eq_add_neg] using I (-1)
  let p : Ω → Prop := fun ω => ((s + 1 : ℕ) : ℕ∞) ≤ τ ω
  have hA : MeasurableSet[F s] {ω | p ω} := by
    have := (hτ s).compl
    convert this using 1
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, p]
    exact enat_succ_le_iff _ _
  have key := key_step hS s X hXF p hA g I0 Ip In
  rw [pot_map P _ hX1m, pot_map P _ hXm]
  have e1 : (fun ω => |(x : ℝ) - ((stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)) ω : ℤ) : ℝ)|)
      = fun ω => g (X ω + (if p ω then S (s + 1) ω - S s ω else 0)) := by
    ext ω; simp only [g, p]; rw [stopped_succ]
  rw [e1, key]
  have hAm : MeasurableSet {ω | p ω} := F.le s _ hA
  have split0 : ∫ ω, g (X ω) ∂P = ∫ ω, {ω | p ω}ᶜ.indicator (fun ω => g (X ω)) ω ∂P +
      ∫ ω, {ω | p ω}.indicator (fun ω => g (X ω)) ω ∂P := by
    rw [← integral_add (I0.indicator hAm.compl) (I0.indicator hAm)]
    congr 1; ext ω
    by_cases h : ω ∈ {ω | p ω}
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h)]; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (Set.mem_compl h)]; ring
  have hgX : (fun ω => |(x : ℝ) - (X ω : ℝ)|) = fun ω => g (X ω) := rfl
  rw [hgX, split0, add_assoc]
  congr 1
  have hE : {ω | S s ω = x ∧ ((s + 1 : ℕ) : ℕ∞) ≤ τ ω} = {ω | p ω} ∩ {ω | X ω = x} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, p]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [hXdef, sv_of_le _ _ _ _ (le_trans (by exact_mod_cast Nat.le_succ s) h2)]; exact h1
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      rw [hXdef, sv_of_le _ _ _ _ (le_trans (by exact_mod_cast Nat.le_succ s) h2)] at h1; exact h1
  have hXx : MeasurableSet {ω | X ω = x} := hXm (measurableSet_singleton x)
  have hsum := integral_add (μ := P) (f := {ω | p ω}.indicator (fun ω => g (X ω)))
    (g := ({ω | p ω} ∩ {ω | X ω = x}).indicator (1 : Ω → ℝ)) (I0.indicator hAm)
    (by exact (integrable_const (1:ℝ)).indicator (hAm.inter hXx))
  rw [hE, ← measureReal_def, ← integral_indicator_one (hAm.inter hXx), ← hsum]
  · congr 1; ext ω
    by_cases h : ω ∈ {ω | p ω}
    · have h' : ω ∈ ({ω | p ω} ∩ {ω | X ω = x}) ↔ X ω = x := by
        simp only [Set.mem_inter_iff]; exact ⟨fun h => h.2, fun h2 => ⟨h, h2⟩⟩
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      have := second_diff x (X ω)
      simp only [g]
      by_cases hx : X ω = x
      · rw [Set.indicator_of_mem (h'.mpr hx)]; rw [if_pos hx] at this
        push_cast at this ⊢; simp only [Pi.one_apply]; linarith
      · rw [Set.indicator_of_notMem (fun hh => hx (h'.mp hh))]; rw [if_neg hx] at this
        push_cast at this ⊢; linarith
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
        Set.indicator_of_notMem (fun hh => h hh.1)]; ring

end Casino31Prob

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding Casino31Aux Casino31Prob

lemma walk_pot_step {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ)
    (hS : IsCasinoSpace P F S ξ) (s : ℕ) (x : ℤ) :
    potential (P.map (S (s + 1))) (x : ℝ) =
      (potential (P.map (S s)) ((x - 1 : ℤ) : ℝ) + potential (P.map (S s)) ((x + 1 : ℤ) : ℝ)) / 2 := by
  have hP := hS.isProb
  have hXF := hS.adapted s
  have hXm : Measurable (S s) := hXF.mono (F.le s) le_rfl
  have hX1m : Measurable (S (s + 1)) := (hS.adapted (s + 1)).mono (F.le (s + 1)) le_rfl
  have hb : ∀ ω, |S s ω| ≤ (s : ℤ) := abs_S_le hS s
  let g : ℤ → ℝ := fun y => |(x : ℝ) - (y : ℝ)|
  have hg : ∀ y : ℤ, |g y| ≤ |(x : ℝ)| + |(y : ℝ)| := kernel_bound _
  have I : ∀ k : ℤ, Integrable (fun ω => g (S s ω + k)) P :=
    fun k => integrable_bdd P (S s) hXm s hb g k x hg
  have I0 : Integrable (fun ω => g (S s ω)) P := by simpa using I 0
  have Ip : Integrable (fun ω => g (S s ω + 1)) P := I 1
  have In : Integrable (fun ω => g (S s ω - 1)) P := by simpa [sub_eq_add_neg] using I (-1)
  have key := key_step hS s (S s) hXF (fun _ => True) (by simp) g I0 Ip In
  rw [pot_map P _ hX1m, pot_map P _ hXm, pot_map P _ hXm]
  have e1 : (fun ω => |(x : ℝ) - ((S (s + 1) ω : ℤ) : ℝ)|)
      = fun ω => g (S s ω + (if True then S (s + 1) ω - S s ω else 0)) := by
    ext ω; simp only [g, if_true]; congr 3; ring
  rw [e1, key]
  simp only [Set.setOf_true, Set.compl_univ, Set.indicator_empty, integral_zero, zero_add,
    Set.indicator_univ]
  rw [integral_div, integral_add Ip In]
  congr 2
  · congr 1; ext ω; simp only [g]; congr 1; push_cast; ring
  · congr 1; ext ω; simp only [g]; congr 1; push_cast; ring

theorem solution (μ : Measure ℤ) (hμ : InP0Z μ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ)
    (hS : IsCasinoSpace P F S ξ) :
    ∀ (t : ℕ) (x : ℤ), evol μ 0 x ≤ evol μ t x ∧
      evol μ t x ≤ min (potential μ (x : ℝ)) (potential (P.map (S t)) (x : ℝ)) := by
  have hP := hS.isProb
  have hwalk : ∀ (t : ℕ) (x : ℤ), evol μ t x ≤ potential (P.map (S t)) (x : ℝ) := by
    intro t
    induction t with
    | zero =>
      intro x
      have h0 : S 0 = fun _ => 0 := funext hS.zero
      rw [h0, Measure.map_const]
      simp [evol, potential]
    | succ t ih =>
      intro x
      rw [walk_pot_step P F S ξ hS t x, evol_succ]
      refine (min_le_left _ _).trans ?_
      have := ih (x - 1); have := ih (x + 1)
      linarith
  intro t x
  refine ⟨?_, le_min (evol_le_potential μ hμ t x) (hwalk t x)⟩
  have : Monotone (fun t : ℕ => evol μ t x) :=
    monotone_nat_of_le_succ (fun t => evol_mono_succ μ hμ t x)
  exact this (Nat.zero_le t)
