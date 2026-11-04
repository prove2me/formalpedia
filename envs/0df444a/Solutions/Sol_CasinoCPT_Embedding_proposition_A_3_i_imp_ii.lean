-- Prove2me | solution 1 for CasinoCPT.Embedding.proposition_A_3_i_imp_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:23:35.445199+00:00
-- url     : https://prove2.me/submissions/cf36b181-ff7a-46ed-ac6e-9188ae305e2f

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model
import Theorems.Thm_CasinoCPT_Embedding_root_coins_exist
import Theorems.Thm_CasinoCPT_Embedding_rootTime_continue_factor

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

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding Casino31Prob Filter Topology

namespace Casino31A1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma meas_stoppedValue_top {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ) :
    Measurable (stoppedValue S τ) := by
  apply measurable_to_countable'
  intro z
  have hτtop : MeasurableSet {ω | τ ω = ⊤} := by
    have : {ω | τ ω = ⊤} = ⋂ n : ℕ, {ω | τ ω ≤ (n : ℕ∞)}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff, not_le]
      constructor
      · intro h n; rw [h]; exact WithTop.coe_lt_top n
      · intro h
        by_contra hne
        obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
        have := h k
        rw [← hk] at this
        exact lt_irrefl _ this
    rw [this]
    exact MeasurableSet.iInter fun n => (F.le n _ (hτ n)).compl
  have hτn : ∀ n : ℕ, MeasurableSet {ω | τ ω = (n : ℕ∞)} := fun n =>
    F.le n _ (hτ.measurableSet_eq_of_countable n)
  have : stoppedValue S τ ⁻¹' {z} =
      (⋃ n : ℕ, ({ω | τ ω = (n : ℕ∞)} ∩ {ω | S n ω = z})) ∪ ({ω | τ ω = ⊤} ∩ {ω | S (WithTop.untopA (⊤ : WithTop ℕ)) ω = z}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_union, stoppedValue]
    constructor
    · intro h
      cases hτω : τ ω with
      | top => right; rw [hτω] at h; exact ⟨rfl, h⟩
      | coe k => left; rw [hτω] at h; exact ⟨k, rfl, h⟩
    · rintro (⟨n, h1, h2⟩ | ⟨h1, h2⟩)
      · rw [h1]; exact h2
      · rw [h1]; exact h2
  have hSm : ∀ n, Measurable (S n) := fun n => (hS.adapted n).mono (F.le n) le_rfl
  rw [this]
  exact (MeasurableSet.iUnion fun n => (hτn n).inter ((hSm n) (measurableSet_singleton z))).union
    (hτtop.inter ((hSm _) (measurableSet_singleton z)))

/-- real version of monotonicity of the stopped potentials -/
lemma pot_step_real {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ) (s : ℕ) (x : ℝ) :
    potential (P.map (stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)))) x ≤
      potential (P.map (stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)))) x := by
  have hP := hS.isProb
  set X := stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)) with hXdef
  have hXF : Measurable[F s] X := meas_stopped hS τ hτ s
  have hXm : Measurable X := hXF.mono (F.le s) le_rfl
  have hX1m := (meas_stopped hS τ hτ (s + 1)).mono (F.le (s + 1)) le_rfl
  have hb : ∀ ω, |X ω| ≤ (s : ℤ) := stopped_bound S (abs_S_le hS) τ s
  let g : ℤ → ℝ := fun y => |x - (y : ℝ)|
  have hg : ∀ y : ℤ, |g y| ≤ |x| + |(y : ℝ)| := kernel_bound _
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
  have e1 : (fun ω => |x - ((stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)) ω : ℤ) : ℝ)|)
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
  have hgX : (fun ω => |x - (X ω : ℝ)|) = fun ω => g (X ω) := rfl
  rw [hgX, split0]
  have hmono : ∫ ω, {ω | p ω}.indicator (fun ω => g (X ω)) ω ∂P ≤
      ∫ ω, {ω | p ω}.indicator (fun ω => (g (X ω + 1) + g (X ω - 1)) / 2) ω ∂P := by
    apply integral_mono (I0.indicator hAm) (((Ip.add In).div_const 2).indicator hAm)
    intro ω
    simp only [Set.indicator]
    split_ifs
    · simp only [g]
      have := abs_add_le (x - ((X ω + 1 : ℤ) : ℝ)) (x - ((X ω - 1 : ℤ) : ℝ))
      have e : (x - ((X ω + 1 : ℤ) : ℝ)) + (x - ((X ω - 1 : ℤ) : ℝ)) = 2 * (x - X ω) := by
        push_cast; ring
      rw [e, abs_mul] at this
      norm_num at this
      simp only [Pi.add_apply]; push_cast
      linarith
    · exact le_rfl
  linarith

lemma integral_step_zero {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (s : ℕ) (B : Set Ω) (hB : MeasurableSet[F s] B) :
    ∫ ω, B.indicator (fun ω => ((S (s + 1) ω - S s ω : ℤ) : ℝ)) ω ∂P = 0 := by
  have hP := hS.isProb
  have hBm : MeasurableSet B := F.le s _ hB
  have hind := indep_fun_of hS s (fun z : ℤ => (z : ℝ)) (B.indicator (1 : Ω → ℝ))
    (Measurable.indicator measurable_const hB)
  have hDm : Measurable (fun ω => S (s + 1) ω - S s ω) :=
    ((hS.adapted (s + 1)).mono (F.le _) le_rfl).sub ((hS.adapted s).mono (F.le s) le_rfl)
  have hDcm : Measurable (fun ω => ((S (s + 1) ω - S s ω : ℤ) : ℝ)) :=
    (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp hDm
  have J := hind.integral_fun_mul_eq_mul_integral hDcm.aestronglyMeasurable
    ((measurable_const.indicator hBm).aestronglyMeasurable)
  have e : (fun ω => B.indicator (fun ω => ((S (s + 1) ω - S s ω : ℤ) : ℝ)) ω) =
      fun ω => ((S (s + 1) ω - S s ω : ℤ) : ℝ) * B.indicator (1 : Ω → ℝ) ω := by
    ext ω; simp only [Set.indicator, Pi.one_apply]; split_ifs <;> simp
  rw [e, J]
  have hm1 : MeasurableSet {ω | S (s + 1) ω - S s ω = 1} := hDm (measurableSet_singleton 1)
  have hm2 : MeasurableSet {ω | S (s + 1) ω - S s ω = -1} := hDm (measurableSet_singleton (-1))
  have eD : (fun ω => ((S (s + 1) ω - S s ω : ℤ) : ℝ)) =
      fun ω => {ω | S (s + 1) ω - S s ω = 1}.indicator (1 : Ω → ℝ) ω -
        {ω | S (s + 1) ω - S s ω = -1}.indicator (1 : Ω → ℝ) ω := by
    ext ω
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rcases hS.step s ω with h | h <;> rw [h] <;> norm_num
  have : ∫ ω, ((S (s + 1) ω - S s ω : ℤ) : ℝ) ∂P = 0 := by
    rw [eD, integral_sub (f := {ω | S (s + 1) ω - S s ω = 1}.indicator (1 : Ω → ℝ))
      (g := {ω | S (s + 1) ω - S s ω = -1}.indicator (1 : Ω → ℝ))
      (by exact (integrable_const (1:ℝ)).indicator hm1)
      (by exact (integrable_const (1:ℝ)).indicator hm2)]
    rw [show ∫ ω, {ω | S (s + 1) ω - S s ω = 1}.indicator (1 : Ω → ℝ) ω ∂P = _ from
      integral_indicator_one hm1, show ∫ ω, {ω | S (s + 1) ω - S s ω = -1}.indicator
      (1 : Ω → ℝ) ω ∂P = _ from integral_indicator_one hm2, prob_up hS s, prob_down hS s]
    ring
  rw [this, zero_mul]

lemma stopped_martingale {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ) :
    Martingale (fun (t : ℕ) (ω : Ω) =>
      ((stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)) ω : ℤ) : ℝ)) F P := by
  have hP := hS.isProb
  have hint : ∀ t : ℕ, Integrable (fun ω =>
      ((stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)) ω : ℤ) : ℝ)) P := by
    intro t
    have hXm := (meas_stopped hS τ hτ t).mono (F.le t) le_rfl
    have := integrable_bdd P _ hXm t (stopped_bound S (abs_S_le hS) τ t) (fun y : ℤ => (y : ℝ)) 0 0
      (by intro y; simp)
    simpa using this
  refine martingale_of_setIntegral_eq_succ ?_ hint ?_
  · intro t
    exact ((measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp
      (meas_stopped hS τ hτ t)).stronglyMeasurable
  · intro t B hB
    have hBm : MeasurableSet B := F.le t _ hB
    have hA : MeasurableSet[F t] {ω | ((t + 1 : ℕ) : ℕ∞) ≤ τ ω} := by
      have := (hτ t).compl
      convert this using 1
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact enat_succ_le_iff _ _
    have hz := integral_step_zero hS t (B ∩ {ω | ((t + 1 : ℕ) : ℕ∞) ≤ τ ω}) (hB.inter hA)
    have e : ∀ ω, ((stoppedValue S (fun ω => min (τ ω) ((t + 1 : ℕ) : ℕ∞)) ω : ℤ) : ℝ) =
        ((stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)) ω : ℤ) : ℝ) +
        {ω | ((t + 1 : ℕ) : ℕ∞) ≤ τ ω}.indicator
          (fun ω => ((S (t + 1) ω - S t ω : ℤ) : ℝ)) ω := by
      intro ω
      rw [stopped_succ]
      simp only [Set.indicator, Set.mem_setOf_eq]
      split_ifs <;> push_cast <;> ring
    simp_rw [e]
    have hDcm : Measurable (fun ω => ((S (t + 1) ω - S t ω : ℤ) : ℝ)) :=
      (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp
        (((hS.adapted (t + 1)).mono (F.le _) le_rfl).sub ((hS.adapted t).mono (F.le t) le_rfl))
    have hInd : Integrable ({ω | ((t + 1 : ℕ) : ℕ∞) ≤ τ ω}.indicator
        (fun ω => ((S (t + 1) ω - S t ω : ℤ) : ℝ))) P := by
      refine Integrable.indicator ?_ (F.le t _ hA)
      refine Integrable.of_bound hDcm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
      rcases hS.step t ω with h | h <;> simp [h]
    rw [integral_add (hint t).integrableOn hInd.integrableOn, integral_indicator hBm
      (f := {ω | ((t + 1 : ℕ) : ℕ∞) ≤ τ ω}.indicator (fun ω => ((S (t + 1) ω - S t ω : ℤ) : ℝ))) |>.symm,
      Set.indicator_indicator, hz, add_zero]

end Casino31A1

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding Casino31Aux Casino31Prob

namespace Casino31A3

lemma pot_step_parity {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ) (s : ℕ) (x : ℤ)
    (hx : ¬ Even (x - s)) :
    potential (P.map (stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)))) (x : ℝ) =
      potential (P.map (stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)))) (x : ℝ) := by
  rw [pot_step hS τ hτ s x]
  have hempty : {ω | S s ω = x ∧ ((s + 1 : ℕ) : ℕ∞) ≤ τ ω} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hxx _
    apply hx
    have := parity_S hS s ω
    rwa [hxx] at this
  rw [hempty]; simp

lemma pot_stopped_mono {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ) (x : ℤ) :
    Monotone (fun s : ℕ =>
      potential (P.map (stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)))) (x : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro s
  show _ ≤ potential (P.map (stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)))) (x : ℝ)
  rw [pot_step hS τ hτ s x]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

lemma pot_stopped_midconvex {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ) (s : ℕ) (x : ℤ) :
    2 * potential (P.map (stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)))) (x : ℝ) ≤
      potential (P.map (stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)))) ((x - 1 : ℤ) : ℝ) +
      potential (P.map (stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)))) ((x + 1 : ℤ) : ℝ) := by
  have hP := hS.isProb
  set X := stoppedValue S (fun ω => min (τ ω) (s : ℕ∞))
  have hXm : Measurable X := (meas_stopped hS τ hτ s).mono (F.le s) le_rfl
  have hb : ∀ ω, |X ω| ≤ (s : ℤ) := stopped_bound S (abs_S_le hS) τ s
  have I : ∀ z : ℤ, Integrable (fun ω => |(z : ℝ) - (X ω : ℝ)|) P := by
    intro z
    have := integrable_bdd P X hXm s hb (fun y : ℤ => |(z : ℝ) - (y : ℝ)|) 0 z (kernel_bound _)
    simpa using this
  rw [pot_map P X hXm, pot_map P X hXm, pot_map P X hXm, ← integral_const_mul,
    ← integral_add (I _) (I _)]
  apply integral_mono ((I x).const_mul 2) ((I _).add (I _))
  intro ω
  simp only
  have := abs_add_le (((x - 1 : ℤ) : ℝ) - (X ω : ℝ)) (((x + 1 : ℤ) : ℝ) - X ω)
  have e : (((x - 1 : ℤ) : ℝ) - (X ω : ℝ)) + (((x + 1 : ℤ) : ℝ) - X ω) = 2 * ((x : ℝ) - X ω) := by
    push_cast; ring
  rw [e, abs_mul] at this
  simpa using this

lemma pot_stopped_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (x : ℤ) :
    potential (P.map (stoppedValue S (fun ω => min (τ ω) ((0 : ℕ) : ℕ∞)))) (x : ℝ) = |(x : ℝ)| := by
  have hP := hS.isProb
  have : stoppedValue S (fun ω => min (τ ω) ((0 : ℕ) : ℕ∞)) = fun _ => 0 := by
    funext ω; rw [stopped_zero, hS.zero ω]
  rw [this, Measure.map_const]
  simp [potential]

/-- Last assertion of Proposition A.3. -/
lemma domination {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (T : ℕ) (μ : Measure ℤ) (hμ : InP0Z μ)
    (τ : Ω → ℕ∞) (hτ : IsAdmissible F T τ) (hlaw : P.map (stoppedValue S τ) = μ) :
    ∀ t : ℕ, t ≤ T → ∀ x : ℤ,
      potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) (x : ℝ) ≤
        evol μ t x := by
  have hT : stoppedValue S (fun ω => min (τ ω) (T : ℕ∞)) = stoppedValue S τ := by
    funext ω; exact sv_of_ge S τ T ω (hτ.2 ω)
  have hcap : ∀ t : ℕ, t ≤ T → ∀ x : ℤ,
      potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) (x : ℝ) ≤
        potential μ (x : ℝ) := by
    intro t ht x
    have := pot_stopped_mono hS τ hτ.1 x ht
    simp only at this
    rwa [hT, hlaw] at this
  intro t
  induction t with
  | zero => intro _ x; rw [pot_stopped_zero hS τ x]; simp [evol]
  | succ s ih =>
    intro hs x
    have ih' := ih (by omega)
    rw [evol_succ]
    apply le_min _ (hcap _ hs x)
    by_cases hx : Even (x - s)
    · have h1 : ¬ Even ((x - 1) - s) := by
        intro h; have := h.add hx
        have e : (x - 1 - s) + (x - s) = 2 * (x - s) - 1 := by ring
        rw [e] at this
        exact (Int.not_even_iff_odd.mpr (by exact ⟨x - s - 1, by ring⟩)) this
      have h2 : ¬ Even ((x + 1) - s) := by
        intro h; have := h.add hx
        have e : (x + 1 - s) + (x - s) = 2 * (x - s) + 1 := by ring
        rw [e] at this
        exact (Int.not_even_iff_odd.mpr (by exact ⟨x - s, by ring⟩)) this
      have c := pot_stopped_midconvex hS τ hτ.1 (s + 1) x
      rw [pot_step_parity hS τ hτ.1 s _ h1, pot_step_parity hS τ hτ.1 s _ h2] at c
      have a1 := ih' (x - 1)
      have a2 := ih' (x + 1)
      push_cast at c a1 a2 ⊢
      linarith
    · rw [pot_step_parity hS τ hτ.1 s x hx]
      have := evol_midconvex_and_le μ hμ s x
      have := ih' x
      linarith

end Casino31A3

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding Casino31Aux Casino31Prob Casino31A1

namespace Casino31Root

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma rootTime_le_iff (S : ℕ → Ω → ℤ) (b : ℤ → ℕ) (coin : ℕ → ℤ → Ω → Bool) (ω : Ω) (n : ℕ) :
    rootTime S b coin ω ≤ (n : ℕ∞) ↔
      ∃ t, t ≤ n ∧ b (S t ω) ≤ t ∧ coin t (S t ω) ω = false := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have : ((n + 1 : ℕ) : ℕ∞) ≤ rootTime S b coin ω := by
      unfold rootTime
      refine le_iInf₂ fun t ht => ?_
      have : ¬ t ≤ n := fun h' => (hne t h' ht.1) ht.2
      exact_mod_cast (show n + 1 ≤ t by omega)
    have := this.trans h
    norm_cast at this; omega
  · rintro ⟨t, ht, h1, h2⟩
    unfold rootTime
    exact (iInf₂_le t ⟨h1, h2⟩).trans (by exact_mod_cast ht)

lemma rootTime_stopping {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (b : ℤ → ℕ) (r : ℤ → ℝ) (coin : ℕ → ℤ → Ω → Bool)
    (hc : IsRootCoins P F b r coin) : IsStoppingTime F (rootTime S b coin) := by
  intro n
  have : {ω | rootTime S b coin ω ≤ (n : ℕ∞)} =
      ⋃ t ∈ Finset.range (n + 1), ⋃ y : ℤ,
        ({ω | S t ω = y} ∩ {_ω | b y ≤ t} ∩ {ω | coin t y ω = false}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_range,
      exists_prop]
    rw [rootTime_le_iff]
    constructor
    · rintro ⟨t, ht, h1, h2⟩; exact ⟨t, by omega, S t ω, ⟨⟨rfl, h1⟩, h2⟩⟩
    · rintro ⟨t, ht, y, ⟨hy, h1⟩, h2⟩; subst hy; exact ⟨t, by omega, h1, h2⟩
  change MeasurableSet[F n] {ω | rootTime S b coin ω ≤ (n : ℕ∞)}
  rw [this]
  refine Finset.measurableSet_biUnion _ fun t ht => MeasurableSet.iUnion fun y => ?_
  have htn : t ≤ n := by simp at ht; omega
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · exact F.mono htn _ ((hS.adapted t) (measurableSet_singleton y))
  · exact MeasurableSet.const _
  · exact F.mono (Nat.zero_le n) _ ((hc.meas t y) (measurableSet_singleton false))

lemma inP0Z_stopped {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ) (n : ℕ) :
    InP0Z (P.map (stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)))) := by
  have hP := hS.isProb
  have hXm : Measurable (stoppedValue S (fun ω => min (τ ω) (n : ℕ∞))) :=
    (meas_stopped hS τ hτ n).mono (F.le n) le_rfl
  have hI : Integrable (fun ω => ((stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)) ω : ℤ) : ℝ)) P := by
    have h := integrable_bdd P _ hXm n (stopped_bound S (abs_S_le hS) τ n)
      (fun y : ℤ => (y : ℝ)) 0 0 (by intro y; simp)
    simpa using h
  refine ⟨Measure.isProbabilityMeasure_map hXm.aemeasurable, ?_, ?_⟩
  · rw [integrable_map_measure (measurable_from_top (f := fun y : ℤ => (y : ℝ))).aestronglyMeasurable
      hXm.aemeasurable]
    exact hI
  · rw [integral_map hXm.aemeasurable
      (measurable_from_top (f := fun y : ℤ => (y : ℝ))).aestronglyMeasurable]
    have M := stopped_martingale hS τ hτ
    have h := M.setIntegral_eq (Nat.zero_le n) (MeasurableSet.univ)
    simp only [Measure.restrict_univ] at h
    rw [← h]
    have : (fun ω => ((stoppedValue S (fun ω => min (τ ω) ((0 : ℕ) : ℕ∞)) ω : ℤ) : ℝ)) =
        fun _ => 0 := by
      funext ω; rw [stopped_zero, hS.zero ω]; simp
    rw [this]; simp

end Casino31Root

open Casino31Root Casino31A3

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (T : ℕ) (hT : 1 ≤ T) (μ : Measure ℤ) (hμ : InP0Z μ)
    (hsupp : μ (Set.Icc (-(T : ℤ)) T) = 1)
    (hi : ∀ x : ℤ, evol μ T x = potential μ (x : ℝ)) :
    ∃ (b : ℤ → ℕ) (r : ℤ → ℝ) (coin : ℕ → ℤ → Ω → Bool),
      IsRootBarrier b r ∧ IsRootCoins P F b r coin ∧
        IsStoppingTime F (rootTime S b coin) ∧ (∀ ω, rootTime S b coin ω ≤ T) ∧
        (∀ t : ℕ, t ≤ T → ∀ x : ℤ,
          potential (P.map (stoppedValue S (fun ω => min (rootTime S b coin ω) (t : ℕ∞))))
            (x : ℝ) = evol μ t x) ∧
        P.map (stoppedValue S (rootTime S b coin)) = μ := by
  classical
  have hP := hS.isProb
  set U := evol μ with hU
  set V : ℤ → ℝ := fun x => potential μ (x : ℝ) with hV
  have Ule : ∀ t x, U t x ≤ V x := fun t x => evol_le_potential μ hμ t x
  have Uge : ∀ t (x : ℤ), |(x : ℝ)| ≤ U t x := fun t x => evol_ge_abs μ hμ t x
  have Umono : ∀ x, Monotone (fun t => U t x) := fun x =>
    monotone_nat_of_le_succ (fun t => evol_mono_succ μ hμ t x)
  have Ucvx : ∀ t x, 2 * U t x ≤ U t (x - 1) + U t (x + 1) := evol_midconvex_and_le μ hμ
  -- eventually U = V
  have Ueq : ∀ t x, T ≤ t → U t x = V x := by
    intro t x ht
    exact le_antisymm (Ule t x) ((hi x).symm.le.trans (Umono x ht))
  have Vout : ∀ x : ℤ, (T : ℤ) ≤ |x| → V x = |(x : ℝ)| := fun x hx =>
    potential_outside μ hμ T hsupp x hx
  have hex : ∀ x : ℤ, ∃ t : ℕ, (|x| : ℤ) ≤ t ∧ U (t + 1) x = V x := by
    intro x
    refine ⟨x.natAbs + T, ?_, Ueq _ _ (by omega)⟩
    push_cast; rw [Int.abs_eq_natAbs]; omega
  let b : ℤ → ℕ := fun x => Nat.find (hex x)
  have b_spec : ∀ x, (|x| : ℤ) ≤ b x ∧ U (b x + 1) x = V x := fun x => Nat.find_spec (hex x)
  have b_min : ∀ x (t : ℕ), (|x| : ℤ) ≤ t → t < b x → U (t + 1) x ≠ V x := by
    intro x t h1 h2 h3
    exact Nat.find_min (hex x) h2 ⟨h1, h3⟩
  have b_le : ∀ x (t : ℕ), (|x| : ℤ) ≤ t → U (t + 1) x = V x → b x ≤ t := by
    intro x t h1 h2
    exact Nat.find_min' (hex x) ⟨h1, h2⟩
  have b_lt_T : ∀ x : ℤ, |x| < (T : ℤ) → b x ≤ T - 1 := by
    intro x hx
    apply b_le x (T - 1) (by push_cast [show 1 ≤ T from hT]; omega)
    rw [show T - 1 + 1 = T by omega]; exact hi x
  have b_out : ∀ x : ℤ, (T : ℤ) ≤ |x| → b x = x.natAbs := by
    intro x hx
    apply le_antisymm
    · apply b_le x x.natAbs (by rw [Int.abs_eq_natAbs])
      apply le_antisymm (Ule _ _)
      rw [Vout x hx]; exact Uge _ _
    · have := (b_spec x).1
      rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  -- the probabilities r
  let dd : ℤ → ℝ := fun x => U (b x) (x - 1) + U (b x) (x + 1) - 2 * U (b x) x
  let nn : ℤ → ℝ := fun x => U (b x) (x - 1) + U (b x) (x + 1) - 2 * V x
  let r : ℤ → ℝ := fun x => if dd x = 0 then 1 else nn x / dd x
  have dd_nn : ∀ x, 0 ≤ nn x ∧ nn x ≤ dd x := by
    intro x
    have h1 := (b_spec x).2
    rw [hU, evol_succ] at h1
    have h2 : V x ≤ (U (b x) (x - 1) + U (b x) (x + 1)) / 2 := by
      have := min_le_left ((evol μ (b x) (x - 1) + evol μ (b x) (x + 1)) / 2)
        (potential μ (x : ℝ))
      rw [h1] at this; exact this
    have h3 := Ule (b x) x
    constructor <;> simp only [nn, dd] <;> linarith
  have r_mem : ∀ x, 0 ≤ r x ∧ r x ≤ 1 := by
    intro x
    simp only [r]
    split_ifs with h
    · norm_num
    · have hd : 0 < dd x := lt_of_le_of_ne ((dd_nn x).1.trans (dd_nn x).2) (Ne.symm h)
      exact ⟨div_nonneg (dd_nn x).1 hd.le, (div_le_one hd).mpr (dd_nn x).2⟩
  have r_out : ∀ x : ℤ, (T : ℤ) ≤ |x| → r x = 1 := by
    intro x hx
    have hb := b_out x hx
    have hbx : U (b x) x = V x := by
      apply le_antisymm (Ule _ _)
      rw [Vout x hx]; exact Uge _ _
    have : nn x = dd x := by simp only [nn, dd]; rw [hbx]
    simp only [r]
    split_ifs with h
    · rfl
    · rw [this]; exact div_self h
  -- parity of the barrier
  have b_par : ∀ x, Even ((b x : ℤ) - x) := by
    intro x
    by_contra hodd
    have hodd' : Odd ((b x : ℤ) + x) := by
      rw [Int.not_even_iff_odd] at hodd
      have : (b x : ℤ) + x = ((b x : ℤ) - x) + 2 * x := by ring
      rw [this]; exact hodd.add_even (even_two_mul x)
    have hgt : (|x| : ℤ) < b x := by
      rcases lt_or_eq_of_le (b_spec x).1 with h | h
      · exact h
      · exfalso; apply hodd; rw [← h]
        rcases abs_choice x with h' | h' <;> rw [h']
        · simp
        · exact ⟨-x, by ring⟩
    have hpar := evol_parity μ hμ (b x) x hodd'
    obtain ⟨k, hk⟩ : ∃ k, b x = k + 1 := ⟨b x - 1, by have := abs_nonneg x; omega⟩
    have hk' : ((b x : ℕ) : ℤ) = (k : ℤ) + 1 := by exact_mod_cast hk
    apply b_min x k (by omega) (by omega)
    rw [← hk, ← (b_spec x).2]
    exact hpar.symm
  have hbarrier : IsRootBarrier b r := fun x => ⟨(b_spec x).1, b_par x, (r_mem x).1, (r_mem x).2⟩
  obtain ⟨coin, hc, c_lt, c_gt, c_one⟩ := root_coins_exist P F S ξ hS b r r_mem
  set τ := rootTime S b coin with hτdef
  have hτ : IsStoppingTime F τ := rootTime_stopping hS b r coin hc
  have hbound : ∀ ω, τ ω ≤ T := by
    intro ω
    rw [hτdef, rootTime_le_iff]
    refine ⟨T, le_rfl, ?_⟩
    set y := S T ω
    have hy : |y| ≤ (T : ℤ) := abs_S_le hS T ω
    rcases lt_or_eq_of_le hy with h | h
    · have := b_lt_T y h
      exact ⟨by omega, c_gt T y ω (by omega)⟩
    · have hb := b_out y (le_of_eq h.symm)
      have hbT : b y = T := by rw [hb]; rw [Int.abs_eq_natAbs] at h; omega
      refine ⟨hbT.le, ?_⟩
      rw [← hbT]; exact c_one y ω (r_out y (le_of_eq h.symm))
  -- the coin law in real form
  have hlaw_true : ∀ t x, (P {ω | coin t x ω = true}).toReal =
      1 - (if t < b x then 0 else if t = b x then r x else 1) := by
    intro t x
    rw [← hc.law t x]
    have hm : MeasurableSet {ω | coin t x ω = false} :=
      F.le 0 _ ((hc.meas t x) (measurableSet_singleton false))
    have : {ω | coin t x ω = true} = {ω | coin t x ω = false}ᶜ := by
      ext ω; simp
    rw [this, ← measureReal_def, ← measureReal_def, probReal_compl_eq_one_sub hm]
  -- main induction
  have main : ∀ n : ℕ, n ≤ T → ∀ x : ℤ,
      potential (P.map (stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)))) (x : ℝ) = U n x := by
    intro n
    induction n with
    | zero => intro _ x; rw [pot_stopped_zero hS τ x]; simp [hU, evol]
    | succ n ih =>
      intro hn x
      have ih' := ih (by omega)
      -- mass of the stopped law
      have hmass : ∀ y : ℤ, (P {ω | stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)) ω = y}).toReal =
          (U n (y - 1) + U n (y + 1)) / 2 - U n y := by
        intro y
        have hXm : Measurable (stoppedValue S (fun ω => min (τ ω) (n : ℕ∞))) :=
          (meas_stopped hS τ hτ n).mono (F.le n) le_rfl
        have h := mass_eq_potential _ (inP0Z_stopped hS τ hτ n) y
        rw [Measure.map_apply hXm (measurableSet_singleton y)] at h
        have e1 : ((y : ℝ) + 1) = ((y + 1 : ℤ) : ℝ) := by push_cast; ring
        have e2 : ((y : ℝ) - 1) = ((y - 1 : ℤ) : ℝ) := by push_cast; ring
        rw [e1, e2, ih', ih', ih'] at h
        rw [show {ω | stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)) ω = y} =
          stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)) ⁻¹' {y} from rfl, h]
        ring
      -- if not yet past the barrier, unstopped mass = stopped mass
      have hsame : n ≤ b x → {ω | S n ω = x ∧ (n : ℕ∞) ≤ τ ω} =
          {ω | stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)) ω = x} := by
        intro hbx
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨h1, h2⟩; rw [sv_of_le _ _ _ _ h2]; exact h1
        · intro h
          by_cases h2 : (n : ℕ∞) ≤ τ ω
          · rw [sv_of_le _ _ _ _ h2] at h; exact ⟨h, h2⟩
          · exfalso
            push_neg at h2
            obtain ⟨k, hk⟩ : ∃ k : ℕ, τ ω = (k : ℕ∞) :=
              ⟨(τ ω).toNat, (ENat.coe_toNat (ne_top_of_lt h2)).symm⟩
            have hkn : k < n := by rw [hk] at h2; exact_mod_cast h2
            have hkle : τ ω ≤ (n : ℕ∞) := h2.le
            rw [sv_of_ge _ _ _ _ hkle] at h
            have hτk : τ ω ≤ (k : ℕ∞) := hk.le
            rw [hτdef, rootTime_le_iff] at hτk
            obtain ⟨t, htk, hb1, hb2⟩ := hτk
            -- τ ω ≤ t, so τ ω = t = k; S τ = S t
            have htau : τ ω ≤ (t : ℕ∞) := by
              rw [hτdef, rootTime_le_iff]; exact ⟨t, le_rfl, hb1, hb2⟩
            have ht_eq : t = k := by
              have : (k : ℕ∞) ≤ t := hk ▸ htau
              have : k ≤ t := by exact_mod_cast this
              omega
            subst ht_eq
            have hSt : stoppedValue S τ ω = S t ω := by
              unfold stoppedValue; rw [hk]; rfl
            rw [hSt] at h
            rw [h] at hb1
            omega
      rw [show ((n + 1 : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) from rfl, pot_step hS τ hτ n x, ih',
        rootTime_continue_factor P F S ξ hS b r coin hc n x, ENNReal.toReal_mul, hlaw_true]
      rw [hU, evol_succ]
      rcases lt_trichotomy n (b x) with hlt | heq | hgt
      · -- before the barrier: continue
        rw [if_pos hlt, sub_zero, mul_one, hsame hlt.le, hmass x]
        rw [← hU]
        have hmin : min ((U n (x - 1) + U n (x + 1)) / 2) (V x) = (U n (x - 1) + U n (x + 1)) / 2 := by
          by_cases hxn : (|x| : ℤ) ≤ n
          · have hne := b_min x n hxn hlt
            have hle := Ule (n + 1) x
            rw [hU, evol_succ] at hne hle
            rcases min_choice ((evol μ n (x - 1) + evol μ n (x + 1)) / 2) (potential μ (x : ℝ))
              with h | h
            · exact h
            · exact absurd h hne
          · -- the walk cannot be at x at time n
            have hzero : (P {ω | stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)) ω = x}).toReal = 0 := by
              have : {ω | stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)) ω = x} = ∅ := by
                ext ω
                simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
                intro h
                have := stopped_bound S (abs_S_le hS) τ n ω
                rw [h] at this; omega
              rw [this]; simp
            rw [hmass x] at hzero
            apply min_eq_left
            have := Ule n x
            linarith
        rw [hmin]; ring
      · -- at the barrier: randomise
        subst heq
        rw [if_neg (lt_irrefl _), if_pos rfl, hsame le_rfl, hmass x, ← hU]
        have hbV := (b_spec x).2
        rw [hU, evol_succ] at hbV
        rw [hbV]
        simp only [r]
        split_ifs with hd
        · simp only [dd] at hd
          have h3 := Ule (b x) x
          have h4 : V x ≤ (U (b x) (x - 1) + U (b x) (x + 1)) / 2 := by
            have := min_le_left ((evol μ (b x) (x - 1) + evol μ (b x) (x + 1)) / 2)
              (potential μ (x : ℝ))
            rw [hbV] at this; exact this
          simp only [hV] at h3 h4 ⊢
          linarith
        · simp only [dd, nn] at hd ⊢
          generalize U (b x) (x - 1) = A at hd ⊢
          generalize U (b x) (x + 1) = B at hd ⊢
          generalize U (b x) x = C at hd ⊢
          have key : ((A + B) / 2 - C) * (1 - (A + B - 2 * V x) / (A + B - 2 * C)) = V x - C := by
            field_simp
            ring
          linarith
      · -- past the barrier: stop surely
        rw [if_neg (by omega), if_neg (by omega), sub_self, mul_zero, add_zero, ← hU]
        have h1 : U n x = V x := by
          apply le_antisymm (Ule n x)
          rw [← (b_spec x).2]; exact Umono x (by omega)
        have h2 : U (n + 1) x = V x := by
          apply le_antisymm (Ule (n + 1) x)
          rw [← (b_spec x).2]; exact Umono x (by omega)
        rw [hU, evol_succ] at h2
        rw [h1]; exact h2.symm
  refine ⟨b, r, coin, hbarrier, hc, hτ, hbound, main, ?_⟩
  -- the law
  have hT' : stoppedValue S (fun ω => min (τ ω) (T : ℕ∞)) = stoppedValue S τ := by
    funext ω; exact sv_of_ge S τ T ω (hbound ω)
  have hlaw := inP0Z_stopped hS τ hτ T
  rw [hT'] at hlaw
  apply eq_of_potential_int _ _ hlaw hμ
  intro x
  have := main T le_rfl x
  rw [hT'] at this
  rw [this, hi x]
