-- Prove2me | solution 1 for BesbesZeevi.Parametric.a25
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T08:09:07.598476+00:00
-- url     : https://prove2.me/submissions/b5cc012e-2d7d-42fa-9ebe-c20d2ea8ca55

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Algorithm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BZA25

lemma poi_hasSum_mgf (r : ℝ≥0) (t : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) * Real.exp (t * n))
      (Real.exp ((r : ℝ) * (Real.exp t - 1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp t)).mul_left (Real.exp (-(r : ℝ)))
  rw [← Real.exp_eq_exp_ℝ] at h
  have e : (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) * Real.exp (t * n))
      = (fun i : ℕ => Real.exp (-(r : ℝ)) * (((r : ℝ) * Real.exp t) ^ i / (i.factorial : ℝ))) := by
    funext n
    rw [mul_pow, ← Real.exp_nat_mul]
    ring_nf
  have e2 : Real.exp ((r : ℝ) * (Real.exp t - 1)) = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ) * Real.exp t) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, e2]
  exact h

lemma poi_integrable (r : ℝ≥0) (t : ℝ) :
    Integrable (fun k : ℕ => Real.exp (t * (k : ℝ))) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have := (poi_hasSum_mgf r t).summable
  refine this.congr (fun n => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma poi_mgf (r : ℝ≥0) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure r) t = Real.exp ((r : ℝ) * (Real.exp t - 1)) := by
  unfold mgf
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  exact (poi_hasSum_mgf r t).tsum_eq

lemma exp_quad (t : ℝ) (ht : |t| ≤ 1) : Real.exp t ≤ 1 + t + t ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le ht
  have h2 := (abs_le.mp this).2
  nlinarith

/-- Upper Poisson tail: `P(X ≥ r + 2√(ur) + 4u) ≤ e^{-u}`. -/
lemma poi_upper (r : ℝ≥0) (u : ℝ) (hu : 0 ≤ u) :
    (poissonMeasure r).real {k : ℕ | (r : ℝ) + 2 * Real.sqrt (u * r) + 4 * u ≤ (k : ℝ)}
      ≤ Real.exp (-u) := by
  set a := Real.sqrt u with ha
  set b := Real.sqrt (r : ℝ) with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hua : u = a ^ 2 := (Real.sq_sqrt hu).symm
  have hrb : (r : ℝ) = b ^ 2 := (Real.sq_sqrt r.2).symm
  have hsq : Real.sqrt (u * r) = a * b := by rw [Real.sqrt_mul hu]
  rcases eq_or_lt_of_le (add_nonneg ha0 hb0) with h0 | hpos
  · have hu0 : u = 0 := by
      have : a = 0 := by linarith
      rw [hua, this]; ring
    rw [hu0, neg_zero, Real.exp_zero]
    exact measureReal_le_one
  set t := a / (a + b) with htdef
  have ht0 : 0 ≤ t := div_nonneg ha0 hpos.le
  have ht1 : t ≤ 1 := by rw [div_le_one hpos]; linarith
  have hch := measure_ge_le_exp_mul_mgf (X := fun k : ℕ => (k : ℝ)) (μ := poissonMeasure r)
    ((r : ℝ) + 2 * Real.sqrt (u * r) + 4 * u) ht0 (poi_integrable r t)
  rw [poi_mgf, ← Real.exp_add] at hch
  refine hch.trans (Real.exp_le_exp.mpr ?_)
  have hq := exp_quad t (by rw [abs_of_nonneg ht0]; exact ht1)
  have hr0 : (0 : ℝ) ≤ r := r.2
  have h1 : (r : ℝ) * (Real.exp t - 1) ≤ (r : ℝ) * (t + t ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hr0; linarith
  have key : t * (2 * (a * b) + 4 * a ^ 2) - b ^ 2 * t ^ 2 ≥ a ^ 2 := by
    rw [htdef]
    rw [ge_iff_le, div_pow, ← sub_nonneg]
    have hne : (a + b) ≠ 0 := hpos.ne'
    have : a / (a + b) * (2 * (a * b) + 4 * a ^ 2) - b ^ 2 * (a ^ 2 / (a + b) ^ 2) - a ^ 2
        = a ^ 2 * (3 * a ^ 2 + 4 * a * b) / (a + b) ^ 2 := by
      field_simp
      ring
    rw [this]
    positivity
  rw [hsq]
  nlinarith

/-- Lower Poisson tail: `P(X < r - 2√(ur)) ≤ e^{-u}`. -/
lemma poi_lower (r : ℝ≥0) (u : ℝ) (hu : 0 ≤ u) :
    (poissonMeasure r).real {k : ℕ | (k : ℝ) < (r : ℝ) - 2 * Real.sqrt (u * r)}
      ≤ Real.exp (-u) := by
  set a := Real.sqrt u with ha
  set b := Real.sqrt (r : ℝ) with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hrb : (r : ℝ) = b ^ 2 := (Real.sq_sqrt r.2).symm
  have hua : u = a ^ 2 := (Real.sq_sqrt hu).symm
  have hsq : Real.sqrt (u * r) = a * b := by rw [Real.sqrt_mul hu]
  rcases le_or_gt b a with hab | hab
  · have hempty : {k : ℕ | (k : ℝ) < (r : ℝ) - 2 * Real.sqrt (u * r)} = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hsq, hrb]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    rw [hempty, measureReal_empty]
    exact (Real.exp_pos _).le
  have hbpos : 0 < b := lt_of_le_of_lt ha0 hab
  set t := a / b with htdef
  have ht0 : 0 ≤ t := div_nonneg ha0 hbpos.le
  have ht1 : t ≤ 1 := by rw [div_le_one hbpos]; exact hab.le
  have hch := measure_le_le_exp_mul_mgf (X := fun k : ℕ => (k : ℝ)) (μ := poissonMeasure r)
    ((r : ℝ) - 2 * Real.sqrt (u * r)) (neg_nonpos.mpr ht0) (poi_integrable r (-t))
  rw [poi_mgf, ← Real.exp_add] at hch
  have hsub : {k : ℕ | (k : ℝ) < (r : ℝ) - 2 * Real.sqrt (u * r)}
      ⊆ {k : ℕ | (k : ℝ) ≤ (r : ℝ) - 2 * Real.sqrt (u * r)} := by
    intro k hk
    exact le_of_lt (show (k : ℝ) < (r : ℝ) - 2 * Real.sqrt (u * r) from hk)
  refine (measureReal_mono hsub).trans (hch.trans (Real.exp_le_exp.mpr ?_))
  have hq := exp_quad (-t) (by rw [abs_neg, abs_of_nonneg ht0]; exact ht1)
  have hr0 : (0 : ℝ) ≤ r := r.2
  have h1 : (r : ℝ) * (Real.exp (-t) - 1) ≤ (r : ℝ) * (-t + t ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hr0; nlinarith
  have hbt : b * t = a := by rw [htdef]; field_simp
  rw [hsq]
  have : -(-t) * ((r : ℝ) - 2 * (a * b)) + (r : ℝ) * (-t + t ^ 2) = -(a ^ 2) := by
    rw [hrb]
    have : b ^ 2 * t ^ 2 = a ^ 2 := by rw [← hbt]; ring
    nlinarith
  rw [hua]
  linarith

end BZA25

open MeasureTheory ProbabilityTheory BesbesZeevi.Parametric
open scoped NNReal

namespace BZA25

/-- Deviation bound at all integer pairs `j ≤ k ≤ K`. -/
def GoodPath (Nω : ℝ → ℕ) (K : ℕ) (u : ℝ) : Prop :=
  ∀ j k : ℕ, j ≤ k → k ≤ K →
    ((Nω (k : ℝ) : ℝ) - Nω (j : ℝ) ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
    (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (Nω (k : ℝ) : ℝ) - Nω (j : ℝ))

lemma path_dev (Nω : ℝ → ℕ) (hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → Nω s ≤ Nω t) (K : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hG : GoodPath Nω K u) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbK : b ≤ K) :
    |((Nω b : ℝ) - Nω a) - (b - a)| ≤ 2 + 2 * Real.sqrt (u * (b - a + 2)) + 4 * u := by
  have hsq0 : 0 ≤ Real.sqrt (u * (b - a + 2)) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := le_trans ha hab
  apply abs_le.mpr
  constructor
  · rcases lt_or_ge (b - a) 2 with hsmall | hbig
    · have : (Nω a : ℝ) ≤ Nω b := by exact_mod_cast hmono _ _ ha hab
      linarith
    set j := ⌈a⌉₊ with hj
    set k := ⌊b⌋₊ with hk
    have hj1 : a ≤ (j : ℝ) := Nat.le_ceil a
    have hj2 : (j : ℝ) < a + 1 := Nat.ceil_lt_add_one ha
    have hk1 : (k : ℝ) ≤ b := Nat.floor_le hb0
    have hk2 : b < (k : ℝ) + 1 := Nat.lt_floor_add_one b
    have hjk : j ≤ k := by
      have : (j : ℝ) ≤ k := by linarith
      exact_mod_cast this
    have hkK : k ≤ K := by
      have : (k : ℝ) ≤ K := le_trans hk1 hbK
      exact_mod_cast this
    have h1 := (hG j k hjk hkK).2
    have m1 : (Nω a : ℝ) ≤ Nω (j : ℝ) := by exact_mod_cast hmono _ _ ha hj1
    have m2 : (Nω (k : ℝ) : ℝ) ≤ Nω b := by exact_mod_cast hmono _ _ (Nat.cast_nonneg k) hk1
    have hs : Real.sqrt (u * ((k : ℝ) - j)) ≤ Real.sqrt (u * (b - a + 2)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ hu
      linarith
    linarith
  · set j := ⌊a⌋₊ with hj
    set k := ⌈b⌉₊ with hk
    have hj1 : (j : ℝ) ≤ a := Nat.floor_le ha
    have hj2 : a < (j : ℝ) + 1 := Nat.lt_floor_add_one a
    have hk1 : b ≤ (k : ℝ) := Nat.le_ceil b
    have hk2 : (k : ℝ) < b + 1 := Nat.ceil_lt_add_one hb0
    have hjk : j ≤ k := by
      have : (j : ℝ) ≤ k := by linarith
      exact_mod_cast this
    have hkK : k ≤ K := Nat.ceil_le.mpr hbK
    have h1 := (hG j k hjk hkK).1
    have m1 : (Nω (j : ℝ) : ℝ) ≤ Nω a := by exact_mod_cast hmono _ _ (Nat.cast_nonneg j) hj1
    have m2 : (Nω b : ℝ) ≤ Nω (k : ℝ) := by exact_mod_cast hmono _ _ hb0 hk1
    have hs : Real.sqrt (u * ((k : ℝ) - j)) ≤ Real.sqrt (u * (b - a + 2)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ hu
      linarith
    linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma incr_law (N : PoissonProcess Ω P) (j k : ℕ) (hjk : j ≤ k) (S : Set ℕ) :
    P ((fun ω => N.count (k : ℝ) ω - N.count (j : ℝ) ω) ⁻¹' S)
      = poissonMeasure ⟨(k : ℝ) - j, sub_nonneg.mpr (by exact_mod_cast hjk)⟩ S := by
  have hmeas : Measurable (fun ω => N.count (k : ℝ) ω - N.count (j : ℝ) ω) :=
    (N.measurable _).sub (N.measurable _)
  rw [← Measure.map_apply hmeas (MeasurableSet.of_discrete),
    N.incrementLaw (j : ℝ) (k : ℝ) (Nat.cast_nonneg j) (by exact_mod_cast hjk)]

lemma bad_pair (N : PoissonProcess Ω P) (u : ℝ) (hu : 0 ≤ u) (j k : ℕ) :
    P {ω | j ≤ k ∧ ¬ (((N.count (k : ℝ) ω : ℝ) - N.count (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N.count (k : ℝ) ω : ℝ) - N.count (j : ℝ) ω))}
      ≤ ENNReal.ofReal (2 * Real.exp (-u)) := by
  by_cases hjk : j ≤ k
  · set r : ℝ≥0 := ⟨(k : ℝ) - j, sub_nonneg.mpr (by exact_mod_cast hjk)⟩ with hr
    have hrr : ((r : ℝ)) = (k : ℝ) - j := rfl
    set X := fun ω => N.count (k : ℝ) ω - N.count (j : ℝ) ω with hX
    have hcast : ∀ ω, ((X ω : ℕ) : ℝ) = (N.count (k : ℝ) ω : ℝ) - N.count (j : ℝ) ω := by
      intro ω
      have : N.count (j : ℝ) ω ≤ N.count (k : ℝ) ω := N.mono ω (Nat.cast_nonneg j) (by exact_mod_cast hjk)
      simp only [hX]
      rw [Nat.cast_sub this]
    set SU : Set ℕ := {m | (r : ℝ) + 2 * Real.sqrt (u * r) + 4 * u ≤ (m : ℝ)} with hSU
    set SL : Set ℕ := {m | (m : ℝ) < (r : ℝ) - 2 * Real.sqrt (u * r)} with hSL
    have hsub : {ω | j ≤ k ∧ ¬ (((N.count (k : ℝ) ω : ℝ) - N.count (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N.count (k : ℝ) ω : ℝ) - N.count (j : ℝ) ω))}
        ⊆ X ⁻¹' SU ∪ X ⁻¹' SL := by
      intro ω hω
      obtain ⟨-, hω⟩ := hω
      rw [not_and_or] at hω
      rcases hω with h1 | h1
      · left
        show (r : ℝ) + 2 * Real.sqrt (u * r) + 4 * u ≤ ((X ω : ℕ) : ℝ)
        rw [hcast, hrr]; push_neg at h1; exact h1.le
      · right
        show ((X ω : ℕ) : ℝ) < (r : ℝ) - 2 * Real.sqrt (u * r)
        rw [hcast, hrr]; push_neg at h1; exact h1
    refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
    have e1 : P (X ⁻¹' SU) = poissonMeasure r SU := incr_law N j k hjk SU
    have e2 : P (X ⁻¹' SL) = poissonMeasure r SL := incr_law N j k hjk SL
    rw [e1, e2]
    have b1 : poissonMeasure r SU ≤ ENNReal.ofReal (Real.exp (-u)) :=
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr
        (poi_upper r u hu)
    have b2 : poissonMeasure r SL ≤ ENNReal.ofReal (Real.exp (-u)) :=
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr
        (poi_lower r u hu)
    calc poissonMeasure r SU + poissonMeasure r SL
        ≤ ENNReal.ofReal (Real.exp (-u)) + ENNReal.ofReal (Real.exp (-u)) := add_le_add b1 b2
      _ = ENNReal.ofReal (2 * Real.exp (-u)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; ring_nf
  · have : {ω | j ≤ k ∧ ¬ (((N.count (k : ℝ) ω : ℝ) - N.count (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N.count (k : ℝ) ω : ℝ) - N.count (j : ℝ) ω))}
        = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hjk h.1
    rw [this, measure_empty]; exact bot_le

lemma good_event (N : PoissonProcess Ω P) (K : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    P {ω | ¬ GoodPath (fun t => N.count t ω) K u}
      ≤ ((K : ENNReal) + 1) ^ 2 * ENNReal.ofReal (2 * Real.exp (-u)) := by
  set B : ℕ → ℕ → Set Ω := fun j k => {ω | j ≤ k ∧ ¬ (((N.count (k : ℝ) ω : ℝ) - N.count (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N.count (k : ℝ) ω : ℝ) - N.count (j : ℝ) ω))}
    with hB
  have hsub : {ω | ¬ GoodPath (fun t => N.count t ω) K u}
      ⊆ ⋃ j ∈ Finset.range (K + 1), ⋃ k ∈ Finset.range (K + 1), B j k := by
    intro ω hω
    simp only [Set.mem_setOf_eq, GoodPath, not_forall] at hω
    obtain ⟨j, k, hjk, hkK, hbad⟩ := hω
    simp only [Set.mem_iUnion, Finset.mem_range]
    exact ⟨j, by omega, k, by omega, hjk, hbad⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have : ∀ j ∈ Finset.range (K + 1),
      P (⋃ k ∈ Finset.range (K + 1), B j k) ≤ ((K : ENNReal) + 1) * ENNReal.ofReal (2 * Real.exp (-u)) := by
    intro j _
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun k _ => bad_pair N u hu j k)) ?_
    simp
  refine le_trans (Finset.sum_le_sum this) ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl

end BZA25

open MeasureTheory BesbesZeevi.Parametric

namespace BZA25

variable {k : ℕ} {D : Market} {F : Family k D}

lemma lam_off {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) : F.demand D.pOff θ = 0 := (F.regular θ hθ).1

lemma lam_nonneg {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) {p : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi) :
    0 ≤ F.demand p θ := ((F.regular θ hθ).2.1 p hp).1

lemma lam_anti {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) : AntitoneOn (fun p => F.demand p θ) (Set.Icc D.pLo D.pHi) :=
  fun _ ha _ hb hab => (F.regular θ hθ).2.2.1 _ ha _ hb hab

lemma gam_lam {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) {p : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi) :
    F.inverse (F.demand p θ) θ = p := (F.regular θ hθ).2.2.2.1 p hp

lemma lam_inj {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) : Set.InjOn (fun p => F.demand p θ) (Set.Icc D.pLo D.pHi) := by
  intro a ha b hb h
  have h' : F.demand a θ = F.demand b θ := h
  rw [← gam_lam hθ ha, ← gam_lam hθ hb, h']

lemma lam_le_M {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) {p : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi) :
    F.demand p θ ≤ D.M := ((F.regular θ hθ).2.1 p hp).2

lemma lam_cont {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) : ContinuousOn (fun p => F.demand p θ) (Set.Icc D.pLo D.pHi) := by
  have hL := (F.regular θ hθ).2.2.2.2.2.2.1
  have hK : 0 ≤ D.KHi := le_trans D.KLo_pos.le D.K_order
  have : LipschitzOnWith (Real.toNNReal D.KHi) (fun p => F.demand p θ) (Set.Icc D.pLo D.pHi) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
    exact hL a ha b hb
  exact this.continuousOn

lemma pLo_mem : D.pLo ∈ Set.Icc D.pLo D.pHi := ⟨le_rfl, D.price_order.le⟩
lemma pHi_mem : D.pHi ∈ Set.Icc D.pLo D.pHi := ⟨D.price_order.le, le_rfl⟩

lemma lam_mem_J {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) {p : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi) :
    F.demand p θ ∈ Set.Icc (F.demand D.pHi θ) (F.demand D.pLo θ) :=
  ⟨lam_anti hθ hp pHi_mem hp.2, lam_anti hθ pLo_mem hp hp.1⟩

lemma lam_surj {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) {l : ℝ}
    (hl : l ∈ Set.Icc (F.demand D.pHi θ) (F.demand D.pLo θ)) :
    ∃ p ∈ Set.Icc D.pLo D.pHi, F.demand p θ = l :=
  intermediate_value_Icc' D.price_order.le (lam_cont hθ) hl

lemma price_lip {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) {p q : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi)
    (hq : q ∈ Set.Icc D.pLo D.pHi) : |p - q| ≤ D.KLo⁻¹ * |F.demand p θ - F.demand q θ| := by
  have h := (F.regular θ hθ).2.2.2.2.2.2.2.1 _ (lam_mem_J hθ hp) _ (lam_mem_J hθ hq)
  beta_reduce at h
  rwa [gam_lam hθ hp, gam_lam hθ hq] at h

variable (S : OptimizerSelection D F)

lemma pD_mem {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) : pD S θ ∈ Set.Icc D.pLo D.pHi := by
  unfold pD
  exact ⟨le_trans (S.pu_range θ hθ).1 (le_max_left _ _), max_le (S.pu_range θ hθ).2 (S.pc_range θ hθ).2⟩

lemma pc_le_max {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) :
    F.demand (S.pc θ) θ ≤ max (D.x / D.T) (F.demand D.pHi θ) := by
  by_contra h
  push_neg at h
  have h1 := lt_of_le_of_lt (le_max_left _ _) h
  have h2 := lt_of_le_of_lt (le_max_right _ _) h
  have hmin := S.pc_min θ hθ
  have hpc := S.pc_range θ hθ
  rcases le_or_gt (D.x / D.T) (F.demand D.pHi θ) with hc | hc
  · have := hmin _ (pHi_mem (D := D))
    rw [abs_of_pos (by linarith), abs_of_nonneg (by linarith)] at this
    linarith
  · have hle : F.demand (S.pc θ) θ ≤ F.demand D.pLo θ := lam_anti hθ pLo_mem hpc hpc.1
    obtain ⟨p, hp, hpe⟩ := lam_surj hθ (l := D.x / D.T) ⟨hc.le, by linarith⟩
    have := hmin _ hp
    rw [hpe, sub_self, abs_zero, abs_of_pos (by linarith)] at this
    linarith

lemma pD_rate_le {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) :
    F.demand (pD S θ) θ ≤ max (D.x / D.T) (F.demand D.pHi θ) := by
  refine le_trans ?_ (pc_le_max S hθ)
  exact lam_anti hθ (S.pc_range θ hθ) (pD_mem S hθ) (le_max_right _ _)

lemma case2_pD_eq {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) (h : D.x / D.T < F.demand D.pHi θ) : pD S θ = D.pHi := by
  have hpc := S.pc_range θ hθ
  have h1 := pc_le_max S hθ
  rw [max_eq_right h.le] at h1
  have h2 : F.demand D.pHi θ ≤ F.demand (S.pc θ) θ := lam_anti hθ hpc pHi_mem hpc.2
  have heq : S.pc θ = D.pHi := lam_inj hθ hpc pHi_mem (le_antisymm h1 h2)
  unfold pD
  rw [heq]
  exact max_eq_right (S.pu_range θ hθ).2

/-- Supergradient (Lagrange multiplier) for the constrained revenue maximisation. -/
lemma sg {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) (h : F.demand D.pHi θ ≤ D.x / D.T) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ pD S θ ∧ (s = 0 ∨ F.demand (pD S θ) θ = D.x / D.T) ∧
      ∀ p ∈ Set.Icc D.pLo D.pHi,
        p * F.demand p θ ≤ pD S θ * F.demand (pD S θ) θ + s * (F.demand p θ - F.demand (pD S θ) θ) := by
  have hpu := S.pu_range θ hθ
  have hpc := S.pc_range θ hθ
  have hmax := S.pu_max θ hθ
  rcases le_or_gt (S.pc θ) (S.pu θ) with hcu | hcu
  · have hpD : pD S θ = S.pu θ := max_eq_left hcu
    refine ⟨0, le_rfl, ?_, Or.inl rfl, fun p hp => ?_⟩
    · rw [hpD]; linarith [hpu.1, D.pLo_pos]
    · rw [hpD, zero_mul, add_zero]; exact hmax _ hp
  have hpD : pD S θ = S.pc θ := max_eq_right hcu.le
  set c := D.x / D.T with hcdef
  set f : ℝ → ℝ := fun p => F.demand p θ with hfdef
  -- f(pc) = c
  have hfpc : f (S.pc θ) = c := by
    have hcl : c ≤ f D.pLo := by
      by_contra hlt
      push_neg at hlt
      have := S.pc_min θ hθ _ (pLo_mem (D := D))
      have hle : f (S.pc θ) ≤ f D.pLo := lam_anti hθ pLo_mem hpc hpc.1
      rw [abs_of_neg (by simp only [hfdef] at hle hlt ⊢; linarith),
        abs_of_neg (by simp only [hfdef] at hlt ⊢; linarith)] at this
      have heq : f (S.pc θ) = f D.pLo := le_antisymm hle (by linarith)
      have : S.pc θ = D.pLo := lam_inj hθ hpc pLo_mem heq
      linarith [hpu.1]
    obtain ⟨p0, hp0, hp0e⟩ := lam_surj hθ (l := c) ⟨h, hcl⟩
    have := S.pc_min θ hθ _ hp0
    rw [hp0e, sub_self, abs_zero] at this
    have := abs_nonpos_iff.mp this
    simp only [hfdef]; linarith
  set γ : ℝ → ℝ := fun l => F.inverse l θ with hγ
  set R : ℝ → ℝ := fun l => l * γ l with hR
  have hconc : ConcaveOn ℝ (Set.Icc (f D.pHi) (f D.pLo)) R := (F.regular θ hθ).2.2.2.2.2.1
  have hRf : ∀ p ∈ Set.Icc D.pLo D.pHi, R (f p) = p * f p := by
    intro p hp
    simp only [hR, hγ]
    rw [gam_lam hθ hp]; ring
  -- γ l ≤ pc for l ≥ c in J
  have hγle : ∀ l ∈ Set.Ioc c (f D.pLo), γ l ≤ S.pc θ ∧ f (γ l) = l ∧ γ l ∈ Set.Icc D.pLo D.pHi := by
    intro l hl
    have hlJ : l ∈ Set.Icc (f D.pHi) (f D.pLo) := ⟨by linarith [hl.1], hl.2⟩
    obtain ⟨q, hq, hqe⟩ := lam_surj hθ hlJ
    have hq' : γ l = q := by
      simp only [hγ]; rw [← hqe]; exact gam_lam hθ hq
    refine ⟨?_, by rw [hq']; exact hqe, by rw [hq']; exact hq⟩
    rw [hq']
    by_contra hgt
    push_neg at hgt
    have : f q ≤ f (S.pc θ) := lam_anti hθ hpc hq hgt.le
    simp only [hfdef] at hqe this hfpc
    linarith [hl.1]
  set SS : Set ℝ := (fun l => (R l - R c) / (l - c)) '' Set.Ioc c (f D.pLo) with hS
  have hRc : R c = S.pc θ * c := by rw [← hfpc, hRf _ hpc, hfpc]
  have hSbdd : ∀ y ∈ SS, y ≤ S.pc θ := by
    rintro y ⟨l, hl, rfl⟩
    obtain ⟨h1, -, -⟩ := hγle l hl
    have hlc : 0 < l - c := by linarith [hl.1]
    rw [div_le_iff₀ hlc, hRc]
    simp only [hR]
    have : 0 ≤ l := by linarith [hl.1, lam_nonneg hθ (pHi_mem (D := D)), h]
    nlinarith
  have hfu : c < f (S.pu θ) := by
    have h1 : f (S.pc θ) ≤ f (S.pu θ) := lam_anti hθ hpu hpc hcu.le
    have h2 : f (S.pc θ) ≠ f (S.pu θ) := fun he => hcu.ne' (lam_inj hθ hpc hpu he)
    rw [← hfpc]; exact lt_of_le_of_ne h1 h2
  have hfuJ : f (S.pu θ) ∈ Set.Ioc c (f D.pLo) := ⟨hfu, lam_anti hθ pLo_mem hpu hpu.1⟩
  have hSne : SS.Nonempty := ⟨_, Set.mem_image_of_mem _ hfuJ⟩
  have hSB : BddAbove SS := ⟨S.pc θ, hSbdd⟩
  refine ⟨sSup SS, ?_, ?_, Or.inr (by rw [hpD]; exact hfpc), ?_⟩
  · have hmem : (R (f (S.pu θ)) - R c) / (f (S.pu θ) - c) ∈ SS := Set.mem_image_of_mem _ hfuJ
    refine le_trans ?_ (le_csSup hSB hmem)
    apply div_nonneg _ (by linarith)
    rw [hRf _ hpu, ← hfpc, hRf _ hpc]
    have := hmax _ hpc
    linarith
  · rw [hpD]; exact csSup_le hSne hSbdd
  · intro p hp
    rw [hpD]
    show p * f p ≤ S.pc θ * f (S.pc θ) + sSup SS * (f p - f (S.pc θ))
    rw [← hRf _ hp, hfpc, ← hRc]
    have hlJ := lam_mem_J hθ hp
    rcases lt_trichotomy (f p) c with hlt | heq | hgt
    · -- left of c: concavity
      have hcJ : c ∈ Set.Icc (f D.pHi) (f D.pLo) := by rw [← hfpc]; exact lam_mem_J hθ hpc
      have key : sSup SS ≤ (R c - R (f p)) / (c - f p) := by
        apply csSup_le hSne
        rintro y ⟨l, hl, rfl⟩
        have hlJ' : l ∈ Set.Icc (f D.pHi) (f D.pLo) := ⟨by linarith [hl.1, hcJ.1], hl.2⟩
        exact hconc.slope_anti_adjacent hlJ hlJ' hlt hl.1
      have hpos : 0 < c - f p := by linarith
      rw [le_div_iff₀ hpos] at key
      nlinarith
    · rw [heq]; simp
    · have hmem : (R (f p) - R c) / (f p - c) ∈ SS := Set.mem_image_of_mem _ ⟨hgt, hlJ.2⟩
      have := le_csSup hSB hmem
      have hpos : 0 < f p - c := by linarith
      rw [div_le_iff₀ hpos] at this
      linarith

end BZA25

open MeasureTheory BesbesZeevi.Parametric

namespace BZA25

variable {k : ℕ} {D : Market} {F : Family k D}

lemma pHi_pos : 0 < D.pHi := lt_trans D.pLo_pos D.price_order

/-- The benchmark rate of return `p * min (T λ(p;θ)) x`. -/
noncomputable def fval (D : Market) (F : Family k D) (θ : Fin k → ℝ) (p : ℝ) : ℝ :=
  p * min (D.T * F.demand p θ) D.x

lemma fval_nonneg {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) {p : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi) :
    0 ≤ fval D F θ p := by
  unfold fval
  have hp0 : 0 < p := lt_of_lt_of_le D.pLo_pos hp.1
  exact mul_nonneg hp0.le (le_min (mul_nonneg D.T_pos.le (lam_nonneg hθ hp)) D.x_pos.le)

lemma fval_le_pHi_x {θ : Fin k → ℝ} {p : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi) :
    fval D F θ p ≤ D.pHi * D.x := by
  unfold fval
  have hp0 : 0 < p := lt_of_lt_of_le D.pLo_pos hp.1
  calc p * min (D.T * F.demand p θ) D.x ≤ p * D.x :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hp0.le
    _ ≤ D.pHi * D.x := mul_le_mul_of_nonneg_right hp.2 D.x_pos.le

variable (S : OptimizerSelection D F)

lemma fval_max {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) {p : ℝ}
    (hp : p ∈ Set.Icc D.pLo D.pHi) : fval D F θ p ≤ fval D F θ (pD S θ) := by
  have hp0 : 0 < p := lt_of_lt_of_le D.pLo_pos hp.1
  have hT := D.T_pos
  unfold fval
  rcases le_or_gt (F.demand D.pHi θ) (D.x / D.T) with h | h
  · obtain ⟨s0, hs0, hsq, hsor, hsg⟩ := sg S hθ h
    have hq := pD_mem S hθ
    have hrate : F.demand (pD S θ) θ ≤ D.x / D.T := by
      have := pD_rate_le S hθ; rwa [max_eq_left h] at this
    have hrate' : D.T * F.demand (pD S θ) θ ≤ D.x := (le_div_iff₀' hT).mp hrate
    rw [min_eq_left hrate']
    have hline := hsg p hp
    have hf0 := lam_nonneg hθ hp
    have hq0 : 0 < pD S θ := lt_of_lt_of_le D.pLo_pos hq.1
    rcases le_total (D.T * F.demand p θ) D.x with hle | hge
    · rw [min_eq_left hle]
      have key : p * F.demand p θ ≤ pD S θ * F.demand (pD S θ) θ := by
        rcases hsor with hs | hs
        · rw [hs] at hline; nlinarith
        · have h1 : F.demand p θ ≤ F.demand (pD S θ) θ := by
            rw [hs]; exact (le_div_iff₀' hT).mpr hle
          nlinarith [mul_nonneg hs0 (sub_nonneg.mpr h1)]
      calc p * (D.T * F.demand p θ) = D.T * (p * F.demand p θ) := by ring
        _ ≤ D.T * (pD S θ * F.demand (pD S θ) θ) := mul_le_mul_of_nonneg_left key hT.le
        _ = pD S θ * (D.T * F.demand (pD S θ) θ) := by ring
    · rw [min_eq_right hge]
      rcases hsor with hs | hs
      · rw [hs] at hline
        have key : p * F.demand p θ ≤ pD S θ * F.demand (pD S θ) θ := by nlinarith
        calc p * D.x ≤ p * (D.T * F.demand p θ) := mul_le_mul_of_nonneg_left hge hp0.le
          _ = D.T * (p * F.demand p θ) := by ring
          _ ≤ D.T * (pD S θ * F.demand (pD S θ) θ) := mul_le_mul_of_nonneg_left key hT.le
          _ = pD S θ * (D.T * F.demand (pD S θ) θ) := by ring
      · have hTl : D.T * F.demand (pD S θ) θ = D.x := by
          rw [hs]; field_simp
        rw [hTl]
        rcases le_total p (pD S θ) with hpp | hpp
        · exact mul_le_mul_of_nonneg_right hpp D.x_pos.le
        · have h1 : F.demand p θ ≤ F.demand (pD S θ) θ := lam_anti hθ hq hp hpp
          have h2 : D.T * F.demand p θ ≤ D.x := by rw [← hTl]; exact mul_le_mul_of_nonneg_left h1 hT.le
          have h3 : D.T * F.demand p θ = D.x := le_antisymm h2 hge
          have h4 : F.demand p θ = F.demand (pD S θ) θ := by
            apply mul_left_cancel₀ hT.ne'; rw [h3, hTl]
          have := lam_inj hθ hp hq h4
          rw [this]
  · have hpD := case2_pD_eq S hθ h
    rw [hpD]
    have hx : D.x < D.T * F.demand D.pHi θ := by
      have := (div_lt_iff₀ hT).mp h
      linarith
    rw [min_eq_right hx.le]
    calc p * min (D.T * F.demand p θ) D.x ≤ p * D.x :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hp0.le
      _ ≤ D.pHi * D.x := mul_le_mul_of_nonneg_right hp.2 D.x_pos.le

lemma fval_lip {θ θ' : Fin k → ℝ} (hθ : θ ∈ F.Θ) (hθ' : θ' ∈ F.Θ) {p : ℝ}
    (hp : p ∈ Set.Icc D.pLo D.pHi) {e : ℝ} (he : ‖θ' - θ‖ ≤ e) :
    |fval D F θ' p - fval D F θ p| ≤ D.pHi * D.T * F.K2 * e := by
  have hp0 : 0 < p := lt_of_lt_of_le D.pLo_pos hp.1
  have hl := F.parameter_lipschitz p hp θ' hθ' θ hθ
  have hl2 : |F.demand p θ' - F.demand p θ| ≤ F.K2 * e :=
    le_trans hl (mul_le_mul_of_nonneg_left he F.K2_pos.le)
  have h1 : |min (D.T * F.demand p θ') D.x - min (D.T * F.demand p θ) D.x|
      ≤ D.T * (F.K2 * e) := by
    have := abs_min_sub_min_le_max (D.T * F.demand p θ') D.x (D.T * F.demand p θ) D.x
    have h2 : |D.T * F.demand p θ' - D.T * F.demand p θ| ≤ D.T * (F.K2 * e) := by
      rw [← mul_sub, abs_mul, abs_of_pos D.T_pos]
      exact mul_le_mul_of_nonneg_left hl2 D.T_pos.le
    have h3 : 0 ≤ D.T * (F.K2 * e) := le_trans (abs_nonneg _) h2
    refine le_trans this ?_
    simp only [sub_self, abs_zero]
    exact max_le h2 h3
  have h4 : 0 ≤ F.K2 * e := le_trans (abs_nonneg _) hl2
  unfold fval
  rw [← mul_sub, abs_mul, abs_of_pos hp0]
  calc p * |min (D.T * F.demand p θ') D.x - min (D.T * F.demand p θ) D.x|
      ≤ D.pHi * (D.T * (F.K2 * e)) :=
        mul_le_mul hp.2 h1 (abs_nonneg _) pHi_pos.le
    _ = D.pHi * D.T * F.K2 * e := by ring

lemma stab {θ θ' : Fin k → ℝ} (hθ : θ ∈ F.Θ) (hθ' : θ' ∈ F.Θ) {e : ℝ} (he : ‖θ' - θ‖ ≤ e) :
    fval D F θ (pD S θ) ≤ fval D F θ (pD S θ') + 2 * (D.pHi * D.T * F.K2 * e) := by
  have h1 := fval_lip hθ hθ' (pD_mem S hθ) he
  have h2 := fval_max S hθ' (pD_mem S hθ)
  have h3 := fval_lip hθ hθ' (pD_mem S hθ') he
  have := (abs_le.mp h1).1
  have := (abs_le.mp h3).2
  linarith

/-- Every feasible path earns at most `p̄ · y`. -/
lemma path_le_pHi {f : ℝ → ℝ} {y : ℝ} (hf0 : ∀ p ∈ Set.Icc D.pLo D.pHi, 0 ≤ f p)
    (hoff : f D.pOff = 0) {q : ℝ → ℝ} (hq : DetFeasible D f y q) :
    ∫ s in Set.Icc (0 : ℝ) D.T, q s * f (q s) ≤ D.pHi * y := by
  obtain ⟨-, hrange, hint1, hint2, hle⟩ := hq
  calc ∫ s in Set.Icc (0 : ℝ) D.T, q s * f (q s)
      ≤ ∫ s in Set.Icc (0 : ℝ) D.T, D.pHi * f (q s) := by
        apply setIntegral_mono_on hint2 (hint1.const_mul D.pHi) measurableSet_Icc
        intro s hs
        rcases hrange s hs with h | h
        · exact mul_le_mul_of_nonneg_right h.2 (hf0 _ h)
        · rw [h, hoff]; simp
    _ = D.pHi * ∫ s in Set.Icc (0 : ℝ) D.T, f (q s) := integral_const_mul _ _
    _ ≤ D.pHi * y := mul_le_mul_of_nonneg_left hle pHi_pos.le

/-- Upper bound through a Lagrange line `r(p) ≤ A + s λ(p)` with `A ≥ 0`, `s ≥ 0`. -/
lemma path_le_line {f : ℝ → ℝ} {y A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hline : ∀ p ∈ Set.Icc D.pLo D.pHi, p * f p ≤ A + s * f p)
    (hoff : f D.pOff = 0) {q : ℝ → ℝ} (hq : DetFeasible D f y q) :
    ∫ s in Set.Icc (0 : ℝ) D.T, q s * f (q s) ≤ D.T * A + s * y := by
  obtain ⟨-, hrange, hint1, hint2, hle⟩ := hq
  have hfin : IntegrableOn (fun _ : ℝ => A) (Set.Icc (0 : ℝ) D.T) :=
    integrableOn_const measure_Icc_lt_top.ne
  calc ∫ t in Set.Icc (0 : ℝ) D.T, q t * f (q t)
      ≤ ∫ t in Set.Icc (0 : ℝ) D.T, (A + s * f (q t)) := by
        apply setIntegral_mono_on hint2 (hfin.add (hint1.const_mul s)) measurableSet_Icc
        intro t ht
        show q t * f (q t) ≤ A + s * f (q t)
        rcases hrange t ht with h | h
        · exact hline _ h
        · rw [h, hoff, mul_zero, mul_zero, add_zero]; exact hA
    _ = D.T * A + s * ∫ t in Set.Icc (0 : ℝ) D.T, f (q t) := by
        rw [integral_add hfin (hint1.const_mul s), integral_const_mul, setIntegral_const]
        rw [measureReal_def, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal D.T_pos.le,
          smul_eq_mul]
    _ ≤ D.T * A + s * y := by linarith [mul_le_mul_of_nonneg_left hle hs]

lemma jDet_le_fval {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) :
    jDet D (fun p => F.demand p θ) D.x ≤ fval D F θ (pD S θ) := by
  have hq := pD_mem S hθ
  have hT := D.T_pos
  have hfv0 := fval_nonneg (F := F) hθ hq
  unfold jDet
  rcases le_or_gt (F.demand D.pHi θ) (D.x / D.T) with h | h
  · obtain ⟨s0, hs0, hsq, hsor, hsg⟩ := sg S hθ h
    have hf0 : 0 ≤ F.demand (pD S θ) θ := lam_nonneg hθ hq
    have hrate : F.demand (pD S θ) θ ≤ D.x / D.T := by
      have := pD_rate_le S hθ; rwa [max_eq_left h] at this
    have hrate' : D.T * F.demand (pD S θ) θ ≤ D.x := (le_div_iff₀' hT).mp hrate
    have hfv : fval D F θ (pD S θ) = pD S θ * (D.T * F.demand (pD S θ) θ) := by
      unfold fval; rw [min_eq_left hrate']
    set A := pD S θ * F.demand (pD S θ) θ - s0 * F.demand (pD S θ) θ with hA
    have hA0 : 0 ≤ A := by
      rw [hA]
      have := mul_le_mul_of_nonneg_right hsq hf0
      linarith
    have hfin : D.T * A + s0 * D.x = fval D F θ (pD S θ) := by
      rw [hfv, hA]
      rcases hsor with hs | hs
      · rw [hs]; ring
      · have : D.T * F.demand (pD S θ) θ = D.x := by rw [hs]; field_simp
        linear_combination (-s0) * this
    apply Real.sSup_le _ hfv0
    rintro v ⟨q, hq', rfl⟩
    rw [← hfin]
    apply path_le_line (D := D) (f := fun p => F.demand p θ) hA0 hs0 _ (lam_off hθ) hq'
    intro p hp
    have := hsg p hp
    simp only [hA]
    linarith
  · have hpD := case2_pD_eq S hθ h
    have hx : D.x < D.T * F.demand D.pHi θ := by
      have := (div_lt_iff₀ hT).mp h
      linarith
    have hfv : fval D F θ (pD S θ) = D.pHi * D.x := by
      unfold fval; rw [hpD, min_eq_right hx.le]
    apply Real.sSup_le _ hfv0
    rintro v ⟨q, hq', rfl⟩
    rw [hfv]
    exact path_le_pHi (D := D) (f := fun p => F.demand p θ)
      (fun p hp => lam_nonneg hθ hp) (lam_off hθ) hq'

end BZA25

open MeasureTheory Pointwise ProbabilityTheory BesbesZeevi.Parametric

namespace BZA25


lemma detFeasible_scale_iff_b58 (D : Market) (lam : ℝ → ℝ) (x c : ℝ) (hc : 0 < c)
    (p : ℝ → ℝ) :
    DetFeasible D (fun q => c * lam q) (c * x) p ↔ DetFeasible D lam x p := by
  unfold DetFeasible
  have hu : IsUnit c := isUnit_iff_ne_zero.mpr hc.ne'
  have h1 : IntegrableOn (fun t => c * lam (p t)) (Set.Icc (0 : ℝ) D.T) ↔
      IntegrableOn (fun t => lam (p t)) (Set.Icc (0 : ℝ) D.T) :=
    integrable_const_mul_iff hu _
  have h2e : (fun t => p t * (c * lam (p t))) = (fun t => c * (p t * lam (p t))) := by
    funext t; ring
  have h2 : IntegrableOn (fun t => p t * (c * lam (p t))) (Set.Icc (0 : ℝ) D.T) ↔
      IntegrableOn (fun t => p t * lam (p t)) (Set.Icc (0 : ℝ) D.T) := by
    rw [h2e]; exact integrable_const_mul_iff hu _
  have h3 : (∫ t in Set.Icc (0 : ℝ) D.T, c * lam (p t)) =
      c * ∫ t in Set.Icc (0 : ℝ) D.T, lam (p t) := integral_const_mul c _
  simp only []
  rw [h1, h2, h3, mul_le_mul_iff_of_pos_left hc]

lemma jDet_scale_b58 (D : Market) (lam : ℝ → ℝ) (x c : ℝ) (hc : 0 < c) :
    jDet D (fun q => c * lam q) (c * x) = c * jDet D lam x := by
  unfold jDet
  have hset : {v : ℝ | ∃ p : ℝ → ℝ, DetFeasible D (fun q => c * lam q) (c * x) p ∧
      v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * (fun q => c * lam q) (p t)} =
      c • {v : ℝ | ∃ p : ℝ → ℝ, DetFeasible D lam x p ∧
        v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * lam (p t)} := by
    have hint : ∀ p : ℝ → ℝ, (∫ t in Set.Icc (0 : ℝ) D.T, p t * (fun q => c * lam q) (p t))
        = c * ∫ t in Set.Icc (0 : ℝ) D.T, p t * lam (p t) := by
      intro p
      rw [← integral_const_mul]
      congr 1
      funext t
      simp only []
      ring
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul,
      detFeasible_scale_iff_b58 D lam x c hc, hint]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [hset, Real.sSup_smul_of_nonneg hc.le, smul_eq_mul]

lemma jDet_lower_b58 (D : Market) (lam γ : ℝ → ℝ) (h : IsRegularDemand D lam γ) :
    D.m * min D.T (D.x / D.M) ≤ jDet D lam D.x := by
  obtain ⟨hoff, hbd, -, -, -, -, -, -, ⟨ps, hps, hm⟩⟩ := h
  set τ := min D.T (D.x / D.M) with hτ
  have hτ0 : 0 ≤ τ := le_min D.T_pos.le (div_pos D.x_pos D.M_pos).le
  have hτT : τ ≤ D.T := min_le_left _ _
  have hτx : τ ≤ D.x / D.M := min_le_right _ _
  have hps0 : 0 < ps := lt_of_lt_of_le D.pLo_pos hps.1
  obtain ⟨hl0, hlM⟩ := hbd ps hps
  -- the path
  let p : ℝ → ℝ := fun t => if t ≤ τ then ps else D.pOff
  have hpm : Measurable p :=
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hlam : (fun t => lam (p t)) = (Set.Iic τ).indicator (fun _ => lam ps) := by
    funext t
    simp only [p, Set.indicator, Set.mem_Iic]
    split_ifs <;> simp [hoff]
  have hrev : (fun t => p t * lam (p t)) = (Set.Iic τ).indicator (fun _ => ps * lam ps) := by
    funext t
    simp only [p, Set.indicator, Set.mem_Iic]
    split_ifs <;> simp [hoff]
  have hmeas : (volume.restrict (Set.Icc (0 : ℝ) D.T)) (Set.Iic τ) = ENNReal.ofReal τ := by
    rw [Measure.restrict_apply measurableSet_Iic]
    have : Set.Iic τ ∩ Set.Icc (0 : ℝ) D.T = Set.Icc 0 τ := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2 hτT⟩
    rw [this, Real.volume_Icc, sub_zero]
  have hint_c : ∀ a : ℝ, (∫ t in Set.Icc (0 : ℝ) D.T, (Set.Iic τ).indicator (fun _ => a) t)
      = τ * a := by
    intro a
    rw [integral_indicator_const a measurableSet_Iic, measureReal_def, hmeas,
      ENNReal.toReal_ofReal hτ0, smul_eq_mul]
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) D.T)) := by
    rw [isFiniteMeasure_restrict]; exact measure_Icc_lt_top.ne
  have hintegr : ∀ a : ℝ, IntegrableOn ((Set.Iic τ).indicator (fun _ => a))
      (Set.Icc (0 : ℝ) D.T) := by
    intro a
    exact (integrable_const a).indicator measurableSet_Iic
  have hfeas : DetFeasible D lam D.x p := by
    refine ⟨hpm, ?_, ?_, ?_, ?_⟩
    · intro t _
      simp only [p]
      split_ifs
      · exact Or.inl hps
      · exact Or.inr rfl
    · rw [hlam]; exact hintegr _
    · rw [hrev]; exact hintegr _
    · rw [hlam, hint_c]
      calc τ * lam ps ≤ (D.x / D.M) * D.M :=
            mul_le_mul hτx hlM hl0 (div_pos D.x_pos D.M_pos).le
        _ = D.x := div_mul_cancel₀ _ D.M_pos.ne'
  -- boundedness
  have hbdd : BddAbove {v : ℝ | ∃ p : ℝ → ℝ, DetFeasible D lam D.x p ∧
      v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * lam (p t)} := by
    refine ⟨∫ t in Set.Icc (0 : ℝ) D.T, D.pHi * D.M, ?_⟩
    rintro v ⟨q, hq, rfl⟩
    obtain ⟨-, hrange, -, hqi, -⟩ := hq
    refine setIntegral_mono_on hqi (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc ?_
    intro t ht
    have hHi : 0 < D.pHi := lt_trans D.pLo_pos D.price_order
    rcases hrange t ht with hq' | hq'
    · obtain ⟨a, b⟩ := hbd (q t) hq'
      have hq0 : 0 < q t := lt_of_lt_of_le D.pLo_pos hq'.1
      exact mul_le_mul hq'.2 b a hHi.le
    · rw [hq', hoff, mul_zero]
      exact (mul_pos hHi D.M_pos).le
  have hval : τ * (ps * lam ps) ∈ {v : ℝ | ∃ p : ℝ → ℝ, DetFeasible D lam D.x p ∧
      v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * lam (p t)} :=
    ⟨p, hfeas, by rw [hrev, hint_c]⟩
  unfold jDet
  calc D.m * τ ≤ τ * (ps * lam ps) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hm hτ0
    _ ≤ _ := le_csSup hbdd hval


end BZA25

open MeasureTheory ProbabilityTheory BesbesZeevi.Parametric

namespace BZA25

variable {k : ℕ} {D : Market} {F : Family k D}

noncomputable def Edev (u r : ℝ) : ℝ := 2 + 2 * Real.sqrt (u * (r + 2)) + 4 * u

lemma Edev_mono (u : ℝ) (hu : 0 ≤ u) {r r' : ℝ} (h : r ≤ r') : Edev u r ≤ Edev u r' := by
  unfold Edev
  have : Real.sqrt (u * (r + 2)) ≤ Real.sqrt (u * (r' + 2)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) hu)
  linarith

lemma Edev_nonneg (u r : ℝ) (hu : 0 ≤ u) : 0 ≤ Edev u r := by
  unfold Edev
  have := Real.sqrt_nonneg (u * (r + 2))
  linarith

lemma delta_pos (hk : 0 < k) {τ : ℝ} (hτ : 0 < τ) : 0 < delta k τ :=
  div_pos hτ (Nat.cast_pos.mpr hk)

lemma lc_term_nonneg {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) {τ : ℝ} (hτ : 0 < τ) (j : Fin k) :
    0 ≤ (n : ℝ) * F.demand (F.testPrice j) θ * delta k τ :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (lam_nonneg hθ (F.test_range j)))
    (delta_pos F.k_pos hτ).le

lemma lc_last (n : ℕ) (θ : Fin k → ℝ) (τ : ℝ) :
    learningClock F n θ τ ⟨k, Nat.lt_succ_self k⟩
      = ∑ j : Fin k, (n : ℝ) * F.demand (F.testPrice j) θ * delta k τ := by
  unfold learningClock
  apply Finset.sum_congr rfl
  intro j _
  have : j.val < k := j.isLt
  simp [this]

lemma lc_nonneg {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) {τ : ℝ} (hτ : 0 < τ) (i : Fin (k + 1)) :
    0 ≤ learningClock F n θ τ i := by
  unfold learningClock
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact lc_term_nonneg hθ n hτ j
  · exact le_rfl

lemma lc_le_last {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) {τ : ℝ} (hτ : 0 < τ) (i : Fin (k + 1)) :
    learningClock F n θ τ i ≤ learningClock F n θ τ ⟨k, Nat.lt_succ_self k⟩ := by
  unfold learningClock
  apply Finset.sum_le_sum
  intro j _
  have hk : j.val < k := j.isLt
  simp only [Fin.val_mk, hk, if_true]
  split_ifs
  · exact le_rfl
  · exact lc_term_nonneg hθ n hτ j

lemma lc_last_le {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    learningClock F n θ τ ⟨k, Nat.lt_succ_self k⟩ ≤ (n : ℝ) * D.M * τ := by
  rw [lc_last]
  have hδ := delta_pos F.k_pos hτ
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr F.k_pos.ne'
  calc ∑ j : Fin k, (n : ℝ) * F.demand (F.testPrice j) θ * delta k τ
      ≤ ∑ j : Fin k, (n : ℝ) * D.M * delta k τ := by
        apply Finset.sum_le_sum
        intro j _
        have := lam_le_M hθ (F.test_range j)
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hn) hδ.le
    _ = (n : ℝ) * D.M * τ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, delta]
        field_simp

lemma lc_diff (n : ℕ) (θ : Fin k → ℝ) (τ : ℝ) (i : Fin k) :
    learningClock F n θ τ i.succ - learningClock F n θ τ (Fin.castSucc i)
      = (n : ℝ) * F.demand (F.testPrice i) θ * delta k τ := by
  unfold learningClock
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hne : j.val ≠ i.val := fun h => hj (Fin.ext h)
    by_cases h1 : j.val < i.val
    · simp [h1, show j.val < i.val + 1 by omega]
    · simp [h1, show ¬ j.val < i.val + 1 by omega]
  · simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma est_close (N : PoissonProcess Ω P) {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 0 < n)
    {τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ D.T) (ω : Ω) (K : ℕ)
    (hK : (n : ℝ) * D.M * D.T ≤ K) (u : ℝ) (hu : 0 ≤ u)
    (hG : GoodPath (fun t => N.count t ω) K u) :
    ‖estimate F N n θ τ ω - fun i => F.demand (F.testPrice i) θ‖
      ≤ Edev u ((n : ℝ) * D.M * delta k τ) / ((n : ℝ) * delta k τ) := by
  have hδ := delta_pos F.k_pos hτ
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnδ : 0 < (n : ℝ) * delta k τ := mul_pos hn' hδ
  have hr : 0 ≤ Edev u ((n : ℝ) * D.M * delta k τ) / ((n : ℝ) * delta k τ) :=
    div_nonneg (Edev_nonneg _ _ hu) hnδ.le
  rw [pi_norm_le_iff_of_nonneg hr]
  intro i
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have hdiff := lc_diff (F := F) n θ τ i
  have ha0 := lc_nonneg hθ n hτ (Fin.castSucc i)
  have hterm := lc_term_nonneg hθ n hτ i
  have hab : learningClock F n θ τ (Fin.castSucc i) ≤ learningClock F n θ τ i.succ := by linarith
  have hMT : (n : ℝ) * D.M * τ ≤ (n : ℝ) * D.M * D.T :=
    mul_le_mul_of_nonneg_left hτT (mul_nonneg hn'.le D.M_pos.le)
  have hbK : learningClock F n θ τ i.succ ≤ K :=
    le_trans (lc_le_last hθ n hτ _) (le_trans (lc_last_le hθ n hτ) (le_trans hMT hK))
  have hdev := path_dev (fun t => N.count t ω) (fun s t hs hst => N.mono ω hs hst) K u hu hG _ _
    ha0 hab hbK
  have hbd : 2 + 2 * Real.sqrt (u * (learningClock F n θ τ i.succ - learningClock F n θ τ (Fin.castSucc i) + 2)) + 4 * u
      ≤ Edev u ((n : ℝ) * D.M * delta k τ) := by
    unfold Edev
    have : learningClock F n θ τ i.succ - learningClock F n θ τ (Fin.castSucc i) ≤ (n : ℝ) * D.M * delta k τ := by
      rw [hdiff]
      have := lam_le_M hθ (F.test_range i)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hn'.le) hδ.le
    have h2 : Real.sqrt (u * (learningClock F n θ τ i.succ - learningClock F n θ τ (Fin.castSucc i) + 2))
        ≤ Real.sqrt (u * ((n : ℝ) * D.M * delta k τ + 2)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) hu)
    linarith
  unfold estimate
  have hcast : (((N.count (learningClock F n θ τ i.succ) ω - N.count (learningClock F n θ τ (Fin.castSucc i)) ω : ℕ)) : ℝ)
      = (N.count (learningClock F n θ τ i.succ) ω : ℝ) - N.count (learningClock F n θ τ (Fin.castSucc i)) ω :=
    Nat.cast_sub (N.mono ω ha0 hab)
  rw [hcast]
  have hkey : ((N.count (learningClock F n θ τ i.succ) ω : ℝ) - N.count (learningClock F n θ τ (Fin.castSucc i)) ω)
        / ((n : ℝ) * delta k τ) - F.demand (F.testPrice i) θ
      = (((N.count (learningClock F n θ τ i.succ) ω : ℝ) - N.count (learningClock F n θ τ (Fin.castSucc i)) ω)
          - (learningClock F n θ τ i.succ - learningClock F n θ τ (Fin.castSucc i))) / ((n : ℝ) * delta k τ) := by
    rw [hdiff]
    field_simp
  rw [hkey, abs_div, abs_of_pos hnδ]
  exact div_le_div_of_nonneg_right (le_trans hdev hbd) hnδ.le

lemma theta_close (N : PoissonProcess Ω P) {θ : Fin k → ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 0 < n)
    {τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ D.T) (ω : Ω) (K : ℕ)
    (hK : (n : ℝ) * D.M * D.T ≤ K) (u : ℝ) (hu : 0 ≤ u)
    (hG : GoodPath (fun t => N.count t ω) K u) :
    ‖thetaHat F N n θ τ ω - θ‖
      ≤ F.alpha * (Edev u ((n : ℝ) * D.M * delta k τ) / ((n : ℝ) * delta k τ)) := by
  unfold thetaHat
  have h1 := F.g_left_inverse θ hθ
  have h2 := F.g_lipschitz (estimate F N n θ τ ω) (fun i => F.demand (F.testPrice i) θ)
  rw [h1] at h2
  exact le_trans h2 (mul_le_mul_of_nonneg_left (est_close N hθ n hn hτ hτT ω K hK u hu hG)
    F.alpha_pos.le)

lemma sales_lb (a b c : ℝ) (hab : a ≤ b) : min (b - a) (c - a) ≤ min b c - min a c := by
  rcases le_or_gt a c with h | h
  · rw [min_eq_left h, min_sub_sub_right]
  · rw [min_eq_right h.le, min_eq_right (le_trans h.le hab)]
    have := min_le_right (b - a) (c - a)
    linarith

end BZA25

open MeasureTheory ProbabilityTheory BesbesZeevi.Parametric

namespace BZA25

variable {k : ℕ} {D : Market} {F : Family k D}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma rev_lower (S : OptimizerSelection D F) (N : PoissonProcess Ω P) {θ : Fin k → ℝ}
    (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ D.T) (ω : Ω) (K : ℕ)
    (hK : (n : ℝ) * D.M * D.T ≤ K) (u : ℝ) (hu : 0 ≤ u)
    (hG : GoodPath (fun t => N.count t ω) K u) :
    (n : ℝ) * fval D F θ (priceHat F S N n θ τ ω)
      - D.pHi * (1 + (n : ℝ) * D.M * τ + Edev u ((n : ℝ) * D.M * D.T))
      ≤ pathRevenue F S N n θ τ ω := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hθh : thetaHat F N n θ τ ω ∈ F.Θ := F.g_range _
  have hph : priceHat F S N n θ τ ω ∈ Set.Icc D.pLo D.pHi := pD_mem S hθh
  have hph0 : 0 < priceHat F S N n θ τ ω := lt_of_lt_of_le D.pLo_pos hph.1
  set ph := priceHat F S N n θ τ ω with hphdef
  set A := learningClock F n θ τ ⟨k, Nat.lt_succ_self k⟩ with hA
  have hA0 : 0 ≤ A := lc_nonneg hθ n hτ _
  have hAτ : A ≤ n * D.M * τ := lc_last_le hθ n hτ
  have hlam0 : 0 ≤ F.demand ph θ := lam_nonneg hθ hph
  have hlamM : F.demand ph θ ≤ D.M := lam_le_M hθ hph
  have hTτ : 0 ≤ D.T - τ := by linarith
  set L := (n : ℝ) * F.demand ph θ * (D.T - τ) with hL
  have hL0 : 0 ≤ L := mul_nonneg (mul_nonneg hn'.le hlam0) hTτ
  have hLM : L ≤ n * D.M * (D.T - τ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlamM hn'.le) hTτ
  have hEfin : finalClock F S N n θ τ ω = A + L := rfl
  have hsplit : (n : ℝ) * D.M * τ + (n : ℝ) * D.M * (D.T - τ) = (n : ℝ) * D.M * D.T := by ring
  have hEK : A + L ≤ K := by linarith
  have hnMT : A + L ≤ (n : ℝ) * D.M * D.T := by linarith
  have hAK : A ≤ K := by linarith
  set Ed := Edev u ((n : ℝ) * D.M * D.T) with hEd
  have hEd0 : 0 ≤ Ed := Edev_nonneg _ _ hu
  have hX := path_dev (fun t => N.count t ω) (fun s t hs hst => N.mono ω hs hst) K u hu hG A (A + L)
    hA0 (by linarith) hEK
  have hX' : |((N.count (A + L) ω : ℝ) - N.count A ω) - ((A + L) - A)| ≤ Ed :=
    le_trans hX (Edev_mono u hu (by linarith))
  have hY := path_dev (fun t => N.count t ω) (fun s t hs hst => N.mono ω hs hst) K u hu hG 0 A
    le_rfl hA0 hAK
  have hY' : |((N.count A ω : ℝ) - N.count 0 ω) - (A - 0)| ≤ Ed :=
    le_trans hY (Edev_mono u hu (by linarith))
  rw [N.zero ω] at hY'
  have hb_a : L - Ed ≤ (N.count (A + L) ω : ℝ) - N.count A ω := by
    have := (abs_le.mp hX').1
    linarith
  have ha_le : (N.count A ω : ℝ) ≤ A + Ed := by
    have := (abs_le.mp hY').2
    simp only [Nat.cast_zero, sub_zero] at this
    linarith
  have hcapge : (n : ℝ) * D.x - 1 ≤ (cap D n : ℝ) := by
    unfold cap
    have := Nat.lt_floor_add_one ((n : ℝ) * D.x)
    linarith
  set mm := min (D.T * F.demand ph θ) D.x with hmm
  set Zb := 1 + (n : ℝ) * D.M * τ + Ed with hZb
  have hZb0 : 0 ≤ Zb := by
    have : 0 ≤ (n : ℝ) * D.M * τ := mul_nonneg (mul_nonneg hn'.le D.M_pos.le) hτ.le
    linarith
  have hnmm1 : (n : ℝ) * mm ≤ n * (D.T * F.demand ph θ) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hn'.le
  have hnmm2 : (n : ℝ) * mm ≤ n * D.x := mul_le_mul_of_nonneg_left (min_le_right _ _) hn'.le
  have hlamτ : (n : ℝ) * F.demand ph θ * τ ≤ n * D.M * τ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlamM hn'.le) hτ.le
  have hLeq : L = (n : ℝ) * (D.T * F.demand ph θ) - (n : ℝ) * F.demand ph θ * τ := by
    rw [hL]; ring
  have hmin : (n : ℝ) * mm - Zb ≤
      min ((N.count (A + L) ω : ℝ) - N.count A ω) ((cap D n : ℝ) - N.count A ω) := by
    apply le_min
    · linarith
    · linarith
  have hlow := le_trans hmin
    (sales_lb (N.count A ω : ℝ) (N.count (A + L) ω : ℝ) (cap D n : ℝ)
      (by exact_mod_cast N.mono ω hA0 (by linarith : A ≤ A + L)))
  have hcast : ((min (N.count (A + L) ω) (cap D n) - min (N.count A ω) (cap D n) : ℕ) : ℝ)
      = min (N.count (A + L) ω : ℝ) (cap D n : ℝ) - min (N.count A ω : ℝ) (cap D n : ℝ) := by
    rw [Nat.cast_sub (min_le_min_right _ (N.mono ω hA0 (by linarith : A ≤ A + L))),
      Nat.cast_min, Nat.cast_min]
  unfold pathRevenue
  rw [hEfin, hcast]
  have hsum0 : 0 ≤ ∑ i : Fin k, F.testPrice i *
      (((min (N.count (learningClock F n θ τ i.succ) ω) (cap D n) -
        min (N.count (learningClock F n θ τ (Fin.castSucc i)) ω) (cap D n) : ℕ) : ℝ)) := by
    apply Finset.sum_nonneg
    intro i _
    have := (F.test_range i).1
    exact mul_nonneg (le_trans D.pLo_pos.le this) (Nat.cast_nonneg _)
  have h1 : ph * ((n : ℝ) * mm - Zb) ≤
      ph * (min (N.count (A + L) ω : ℝ) (cap D n : ℝ) - min (N.count A ω : ℝ) (cap D n : ℝ)) :=
    mul_le_mul_of_nonneg_left hlow hph0.le
  have h2 : ph * Zb ≤ D.pHi * Zb := mul_le_mul_of_nonneg_right hph.2 hZb0
  have h3 : (n : ℝ) * fval D F θ ph = ph * ((n : ℝ) * mm) := by
    unfold fval; rw [hmm]; ring
  have h4 : D.pHi * (1 + (n : ℝ) * D.M * τ + Edev u ((n : ℝ) * D.M * D.T)) = D.pHi * Zb := rfl
  rw [h4, h3]
  nlinarith

end BZA25

open MeasureTheory ProbabilityTheory BesbesZeevi.Parametric

namespace BZA25

variable {k : ℕ} {D : Market} {F : Family k D}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma nat_term_le (a b c : ℕ) : ((min a c - min b c : ℕ) : ℝ) ≤ (c : ℝ) := by
  have : min a c - min b c ≤ c := le_trans (Nat.sub_le _ _) (min_le_right _ _)
  exact_mod_cast this

lemma rev_bounds (S : OptimizerSelection D F) (N : PoissonProcess Ω P) (θ : Fin k → ℝ)
    (n : ℕ) (τ : ℝ) (ω : Ω) :
    0 ≤ pathRevenue F S N n θ τ ω ∧
    pathRevenue F S N n θ τ ω ≤ ((k : ℝ) + 1) * (D.pHi * (cap D n : ℝ)) := by
  have hθh : thetaHat F N n θ τ ω ∈ F.Θ := F.g_range _
  have hph : priceHat F S N n θ τ ω ∈ Set.Icc D.pLo D.pHi := pD_mem S hθh
  have hph0 : 0 < priceHat F S N n θ τ ω := lt_of_lt_of_le D.pLo_pos hph.1
  unfold pathRevenue
  have hnn : ∀ i : Fin k, 0 ≤ F.testPrice i *
      (((min (N.count (learningClock F n θ τ i.succ) ω) (cap D n) -
        min (N.count (learningClock F n θ τ (Fin.castSucc i)) ω) (cap D n) : ℕ) : ℝ)) :=
    fun i => mul_nonneg (le_trans D.pLo_pos.le (F.test_range i).1) (Nat.cast_nonneg _)
  have hle : ∀ i : Fin k, F.testPrice i *
      (((min (N.count (learningClock F n θ τ i.succ) ω) (cap D n) -
        min (N.count (learningClock F n θ τ (Fin.castSucc i)) ω) (cap D n) : ℕ) : ℝ))
      ≤ D.pHi * (cap D n : ℝ) :=
    fun i => mul_le_mul (F.test_range i).2 (nat_term_le _ _ _) (Nat.cast_nonneg _) pHi_pos.le
  have hfin0 : 0 ≤ priceHat F S N n θ τ ω *
      (((min (N.count (finalClock F S N n θ τ ω) ω) (cap D n) -
       min (N.count (learningClock F n θ τ ⟨k, Nat.lt_succ_self k⟩) ω)
         (cap D n) : ℕ) : ℝ)) := mul_nonneg hph0.le (Nat.cast_nonneg _)
  have hfinle : priceHat F S N n θ τ ω *
      (((min (N.count (finalClock F S N n θ τ ω) ω) (cap D n) -
       min (N.count (learningClock F n θ τ ⟨k, Nat.lt_succ_self k⟩) ω)
         (cap D n) : ℕ) : ℝ)) ≤ D.pHi * (cap D n : ℝ) :=
    mul_le_mul hph.2 (nat_term_le _ _ _) (Nat.cast_nonneg _) pHi_pos.le
  refine ⟨add_nonneg (Finset.sum_nonneg (fun i _ => hnn i)) hfin0, ?_⟩
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith

lemma good_meas (N : PoissonProcess Ω P) (K : ℕ) (u : ℝ) :
    MeasurableSet {ω | GoodPath (fun t => N.count t ω) K u} := by
  have hm : ∀ t : ℝ, Measurable (fun ω => (N.count t ω : ℝ)) :=
    fun t => (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (N.measurable t)
  unfold GoodPath
  simp only [Set.setOf_forall]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => ?_
  rw [Set.setOf_and]
  exact (measurableSet_le ((hm _).sub (hm _)) measurable_const).inter
    (measurableSet_le measurable_const ((hm _).sub (hm _)))

lemma exp_lower (S : OptimizerSelection D F) (N : PoissonProcess Ω P) {θ : Fin k → ℝ}
    (n : ℕ) (τ : ℝ) (K : ℕ) (u : ℝ) (hu : 0 ≤ u) (V : ℝ)
    (hV : ∀ ω, GoodPath (fun t => N.count t ω) K u → V ≤ pathRevenue F S N n θ τ ω) :
    V - max V 0 * (((K : ℝ) + 1) ^ 2 * (2 * Real.exp (-u))) ≤ jPolicy F S N n θ τ := by
  haveI : IsProbabilityMeasure P := N.prob
  set q := ((K : ℝ) + 1) ^ 2 * (2 * Real.exp (-u)) with hq
  have hq0 : 0 ≤ q := by positivity
  set G := {ω | GoodPath (fun t => N.count t ω) K u} with hGdef
  have hGm : MeasurableSet G := good_meas N K u
  have hbad := good_event N K u hu
  have hcomp : Gᶜ = {ω | ¬ GoodPath (fun t => N.count t ω) K u} := by
    ext ω; simp [hGdef]
  have hofq : ENNReal.ofReal q = ((K : ENNReal) + 1) ^ 2 * ENNReal.ofReal (2 * Real.exp (-u)) := by
    rw [hq, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ 2),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [← hcomp, ← hofq] at hbad
  have hbadR : P.real Gᶜ ≤ q := ENNReal.toReal_le_of_le_ofReal hq0 hbad
  have hPG : 1 - q ≤ P.real G := by
    have := measureReal_compl (μ := P) hGm
    rw [probReal_univ] at this
    linarith
  have hexp0 : 0 ≤ jPolicy F S N n θ τ := ENNReal.toReal_nonneg
  rcases le_or_gt V 0 with hV0 | hV0
  · rw [max_eq_right hV0, zero_mul, sub_zero]; linarith
  rw [max_eq_left hV0.le]
  have hpos := fun ω => rev_bounds S N θ n τ ω
  have hlow : G.indicator (fun _ => ENNReal.ofReal V)
      ≤ fun ω => ENNReal.ofReal (pathRevenue F S N n θ τ ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem hω]; exact ENNReal.ofReal_le_ofReal (hV ω hω)
    · rw [Set.indicator_of_notMem hω]; exact bot_le
  have hup : (∫⁻ ω, ENNReal.ofReal (pathRevenue F S N n θ τ ω) ∂P)
      ≤ ENNReal.ofReal (((k : ℝ) + 1) * (D.pHi * (cap D n : ℝ))) := by
    calc _ ≤ ∫⁻ _, ENNReal.ofReal (((k : ℝ) + 1) * (D.pHi * (cap D n : ℝ))) ∂P :=
          lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hpos ω).2)
      _ = ENNReal.ofReal (((k : ℝ) + 1) * (D.pHi * (cap D n : ℝ))) := by
          rw [lintegral_const, measure_univ, mul_one]
  have hmono' := lintegral_mono (μ := P) hlow
  rw [lintegral_indicator_const hGm] at hmono'
  have hfin : (∫⁻ ω, ENNReal.ofReal (pathRevenue F S N n θ τ ω) ∂P) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  have := ENNReal.toReal_mono hfin hmono'
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hV0.le] at this
  unfold jPolicy
  have h2 : V * (1 - q) ≤ V * (P G).toReal := mul_le_mul_of_nonneg_left hPG hV0.le
  nlinarith

lemma regret_arith (E J W Err q U Ul : ℝ) (hJ : 0 < Ul) (hUl : Ul ≤ J) (hJW : J ≤ W)
    (hW0 : 0 ≤ W) (hWU : W ≤ U) (hErr : 0 ≤ Err) (hq : 0 ≤ q)
    (hE : (W - Err) - max (W - Err) 0 * q ≤ E) :
    1 - E / J ≤ (Err + U * q) / Ul := by
  have hJ0 : 0 < J := lt_of_lt_of_le hJ hUl
  have hmax : max (W - Err) 0 ≤ W := max_le (by linarith) hW0
  have hE' : W - Err - W * q ≤ E := by
    have := mul_le_mul_of_nonneg_right hmax hq
    linarith
  have h1 : 1 - E / J = (J - E) / J := by field_simp
  rw [h1]
  have hnum : J - E ≤ Err + U * q := by
    have := mul_le_mul_of_nonneg_right hWU hq
    linarith
  have hnum0 : 0 ≤ Err + U * q := by
    have : 0 ≤ U := le_trans hW0 hWU
    positivity
  calc (J - E) / J ≤ (Err + U * q) / J := div_le_div_of_nonneg_right hnum hJ0.le
    _ ≤ (Err + U * q) / Ul := div_le_div_of_nonneg_left hnum0 hJ hUl

end BZA25

open MeasureTheory ProbabilityTheory BesbesZeevi.Parametric

namespace BZA25

variable {k : ℕ} {D : Market} {F : Family k D}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

noncomputable def errE (D : Market) (F : Family k D) (n : ℕ) (τ u : ℝ) : ℝ :=
  F.alpha * (Edev u ((n : ℝ) * D.M * delta k τ) / ((n : ℝ) * delta k τ))

noncomputable def Errn (D : Market) (F : Family k D) (n : ℕ) (τ u : ℝ) : ℝ :=
  (n : ℝ) * (2 * (D.pHi * D.T * F.K2 * errE D F n τ u))
    + D.pHi * (1 + (n : ℝ) * D.M * τ + Edev u ((n : ℝ) * D.M * D.T))

lemma errE_nonneg (n : ℕ) {τ : ℝ} (hτ : 0 < τ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ errE D F n τ u := by
  unfold errE
  have hδ := delta_pos F.k_pos hτ
  exact mul_nonneg F.alpha_pos.le (div_nonneg (Edev_nonneg _ _ hu) (mul_nonneg (Nat.cast_nonneg n) hδ.le))

lemma Errn_nonneg (n : ℕ) {τ : ℝ} (hτ : 0 < τ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ Errn D F n τ u := by
  unfold Errn
  have h1 := errE_nonneg (D := D) (F := F) n hτ hu
  have h2 := Edev_nonneg u ((n : ℝ) * D.M * D.T) hu
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp := pHi_pos (D := D)
  have hK := F.K2_pos
  have hT := D.T_pos
  have hM := D.M_pos
  have h3 : 0 ≤ (n : ℝ) * D.M * τ := mul_nonneg (mul_nonneg hn hM.le) hτ.le
  have h4 : 0 ≤ (n : ℝ) * (2 * (D.pHi * D.T * F.K2 * errE D F n τ u)) := by positivity
  have h5 : 0 ≤ D.pHi * (1 + (n : ℝ) * D.M * τ + Edev u ((n : ℝ) * D.M * D.T)) :=
    mul_nonneg hp.le (by linarith)
  linarith

lemma regret_pre (S : OptimizerSelection D F) (N : PoissonProcess Ω P) {θ : Fin k → ℝ}
    (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ D.T)
    (u : ℝ) (hu : 0 ≤ u) :
    regret F S N n θ τ
      ≤ (Errn D F n τ u + ((n : ℝ) * (D.pHi * D.x))
          * ((((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-u))))
        / ((n : ℝ) * (D.m * min D.T (D.x / D.M))) := by
  set K := ⌈(n : ℝ) * D.M * D.T⌉₊ with hKdef
  have hK : (n : ℝ) * D.M * D.T ≤ K := Nat.le_ceil _
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hAm : 0 < D.m * min D.T (D.x / D.M) :=
    mul_pos D.m_pos (lt_min D.T_pos (div_pos D.x_pos D.M_pos))
  have hUl : 0 < (n : ℝ) * (D.m * min D.T (D.x / D.M)) := mul_pos hn' hAm
  have hq0 : 0 ≤ (((K : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-u)) := by positivity
  have hErr := Errn_nonneg (D := D) (F := F) n hτ hu
  set W := (n : ℝ) * fval D F θ (pD S θ) with hW
  have hV : ∀ ω, GoodPath (fun t => N.count t ω) K u →
      W - Errn D F n τ u ≤ pathRevenue F S N n θ τ ω := by
    intro ω hω
    have h1 := rev_lower S N hθ n hn hτ hτT ω K hK u hu hω
    have h2 := stab S hθ (F.g_range (estimate F N n θ τ ω))
      (theta_close N hθ n hn hτ hτT ω K hK u hu hω)
    have h3 := mul_le_mul_of_nonneg_left h2 hn'.le
    have h4 : (n : ℝ) * fval D F θ (priceHat F S N n θ τ ω)
        = (n : ℝ) * fval D F θ (pD S (F.g (estimate F N n θ τ ω))) := rfl
    unfold Errn
    unfold errE at *
    nlinarith
  have hE := exp_lower S N n τ K u hu (W - Errn D F n τ u) hV
  have hJ : jDetScaled D F θ n = (n : ℝ) * jDet D (fun p => F.demand p θ) D.x := by
    unfold jDetScaled
    exact jDet_scale_b58 D (fun p => F.demand p θ) D.x n hn'
  have hJW : jDetScaled D F θ n ≤ W := by
    rw [hJ]; exact mul_le_mul_of_nonneg_left (jDet_le_fval S hθ) hn'.le
  have hUlJ : (n : ℝ) * (D.m * min D.T (D.x / D.M)) ≤ jDetScaled D F θ n := by
    rw [hJ]
    exact mul_le_mul_of_nonneg_left (jDet_lower_b58 D _ _ (F.regular θ hθ)) hn'.le
  have hW0 : 0 ≤ W := mul_nonneg hn'.le (fval_nonneg hθ (pD_mem S hθ))
  have hWU : W ≤ (n : ℝ) * (D.pHi * D.x) :=
    mul_le_mul_of_nonneg_left (fval_le_pHi_x (pD_mem S hθ)) hn'.le
  unfold regret
  exact regret_arith _ _ W _ _ _ _ hUl hUlJ hJW hW0 hWU hErr hq0 hE

end BZA25

open MeasureTheory ProbabilityTheory BesbesZeevi.Parametric

namespace BZA25

lemma edev_div (u w μ : ℝ) (hu1 : 1 ≤ u) (huw : u ≤ w) (hw1 : 1 ≤ w) (hμ : 0 ≤ μ) :
    Edev u (μ * w) / w ≤ (6 + 2 * Real.sqrt (μ + 2)) * (Real.sqrt u / Real.sqrt w) := by
  unfold Edev
  have hw0 : 0 < w := by linarith
  have hu0 : 0 ≤ u := by linarith
  set a := Real.sqrt u with ha
  set b := Real.sqrt w with hb
  set c := Real.sqrt (μ + 2) with hc
  have ha1 : 1 ≤ a := by rw [ha, Real.one_le_sqrt]; exact hu1
  have hb1 : 1 ≤ b := by rw [hb, Real.one_le_sqrt]; exact hw1
  have hab : a ≤ b := Real.sqrt_le_sqrt huw
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hua : u = a ^ 2 := (Real.sq_sqrt hu0).symm
  have hwb : w = b ^ 2 := (Real.sq_sqrt hw0.le).symm
  have hsq : Real.sqrt (u * (μ * w + 2)) ≤ a * c * b := by
    have h1 : u * (μ * w + 2) ≤ u * ((μ + 2) * w) := by
      apply mul_le_mul_of_nonneg_left _ hu0
      nlinarith
    have h2 : Real.sqrt (u * ((μ + 2) * w)) = a * (c * b) := by
      rw [Real.sqrt_mul hu0, Real.sqrt_mul (by linarith)]
    calc Real.sqrt (u * (μ * w + 2)) ≤ Real.sqrt (u * ((μ + 2) * w)) := Real.sqrt_le_sqrt h1
      _ = a * (c * b) := h2
      _ = a * c * b := by ring
  rw [div_le_iff₀ hw0]
  have hfin : (6 + 2 * c) * (a / b) * w = (6 + 2 * c) * (a * b) := by
    rw [hwb]; field_simp
  rw [hfin]
  have h3 : 2 * Real.sqrt (u * (μ * w + 2)) ≤ 2 * (a * c * b) := by linarith
  have h4 : 2 ≤ 2 * (a * b) := by nlinarith
  have h5 : 4 * u ≤ 4 * (a * b) := by rw [hua]; nlinarith
  have h6 : 2 * (a * c * b) = 2 * c * (a * b) := by ring
  nlinarith

noncomputable def uu (D : Market) (n : ℕ) : ℝ :=
  3 * Real.log n + Real.log (2 * (D.M * D.T + 2) ^ 2)

lemma c0_nonneg (D : Market) : 0 ≤ Real.log (2 * (D.M * D.T + 2) ^ 2) := by
  apply Real.log_nonneg
  have := mul_pos D.M_pos D.T_pos
  nlinarith

lemma log_two_le (n : ℕ) (hn : 2 ≤ n) : Real.log 2 ≤ Real.log n :=
  Real.log_le_log (by norm_num) (by exact_mod_cast hn)

lemma uu_ge (D : Market) (n : ℕ) (hn : 2 ≤ n) : 1 ≤ uu D n := by
  unfold uu
  have h1 := log_two_le n hn
  have h2 := c0_nonneg D
  have h3 := Real.log_two_gt_d9
  linarith

noncomputable def cuC (D : Market) : ℝ :=
  3 + Real.log (2 * (D.M * D.T + 2) ^ 2) / Real.log 2

lemma cuC_nonneg (D : Market) : 0 ≤ cuC D := by
  unfold cuC
  have := c0_nonneg D
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

lemma uu_le (D : Market) (n : ℕ) (hn : 2 ≤ n) : uu D n ≤ cuC D * Real.log n := by
  unfold uu cuC
  have h1 := log_two_le n hn
  have h2 := c0_nonneg D
  have h3 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have : Real.log (2 * (D.M * D.T + 2) ^ 2) ≤ Real.log (2 * (D.M * D.T + 2) ^ 2) / Real.log 2 * Real.log n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h3]
    exact mul_le_mul_of_nonneg_left h1 h2
  nlinarith

lemma q_le (D : Market) (n : ℕ) (hn : 1 ≤ n) :
    ((((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(uu D n)))) ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hMT := mul_pos D.M_pos D.T_pos
  set c2 := 2 * (D.M * D.T + 2) ^ 2 with hc2
  have hc2pos : 0 < c2 := by positivity
  have hexp : Real.exp (uu D n) = (n : ℝ) ^ 3 * c2 := by
    unfold uu
    rw [Real.exp_add, Real.exp_log hc2pos,
      show (3 : ℝ) * Real.log n = ((3 : ℕ) : ℝ) * Real.log n by norm_num, Real.exp_nat_mul,
      Real.exp_log hn']
  have hK : ((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1 ≤ n * (D.M * D.T + 2) := by
    have := Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hn'.le D.M_pos.le) D.T_pos.le)
    nlinarith
  have hK0 : 0 ≤ ((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1 := by positivity
  have hsq : (((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 ≤ (n * (D.M * D.T + 2)) ^ 2 :=
    pow_le_pow_left₀ hK0 hK 2
  rw [Real.exp_neg, hexp]
  have hcc : (n * (D.M * D.T + 2)) ^ 2 * (2 * ((n : ℝ) ^ 3 * c2)⁻¹) = 1 / n := by
    rw [hc2]; field_simp
  calc (((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) ^ 3 * c2)⁻¹)
      ≤ (n * (D.M * D.T + 2)) ^ 2 * (2 * ((n : ℝ) ^ 3 * c2)⁻¹) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = 1 / n := hcc

lemma sqrtn_bound (n : ℕ) (T τ : ℝ) (hn : 1 ≤ n) (hτ : 0 < τ) (hτT : τ ≤ T) :
    Real.sqrt (n * τ) ≤ Real.sqrt T * Real.sqrt n := by
  rw [← Real.sqrt_mul (by linarith)]
  apply Real.sqrt_le_sqrt
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma inv_n_le (n : ℕ) (T τ : ℝ) (hn : 2 ≤ n) (hτ : 0 < τ) (hτT : τ ≤ T) :
    1 / (n : ℝ) ≤ (Real.sqrt T / Real.sqrt (Real.log 2)) *
      (Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hT : 0 < T := lt_of_lt_of_le hτ hτT
  have hl2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  have hs : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log n) :=
    Real.sqrt_le_sqrt (log_two_le n hn)
  have hr : 0 < Real.sqrt (n * τ) := Real.sqrt_pos.mpr (by positivity)
  have hv : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hrb := sqrtn_bound n T τ (by omega) hτ hτT
  have hvle : Real.sqrt n ≤ n := by
    have : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    have h1 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn1
    nlinarith
  have h1 : 1 / (n : ℝ) ≤ 1 / Real.sqrt n := one_div_le_one_div_of_le hv hvle
  have h2 : 1 / Real.sqrt n ≤ Real.sqrt T / Real.sqrt (n * τ) := by
    rw [div_le_div_iff₀ hv hr]
    nlinarith
  have h3 : Real.sqrt T / Real.sqrt (n * τ) ≤
      (Real.sqrt T / Real.sqrt (Real.log 2)) * (Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by
    rw [div_mul_div_comm, div_le_div_iff₀ hr (mul_pos hl2 hr)]
    nlinarith [mul_pos hsT hr]
  linarith

lemma s_over_sqrt (n : ℕ) (T τ : ℝ) (hn : 1 ≤ n) (hτ : 0 < τ) (hτT : τ ≤ T) :
    Real.sqrt (Real.log n) / Real.sqrt n ≤
      Real.sqrt T * (Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < Real.sqrt (n * τ) := Real.sqrt_pos.mpr (by positivity)
  have hv : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hrb := sqrtn_bound n T τ hn hτ hτT
  have hs0 : 0 ≤ Real.sqrt (Real.log n) := Real.sqrt_nonneg _
  rw [mul_div_assoc', div_le_div_iff₀ hv hr]
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hrb)]

end BZA25

open MeasureTheory ProbabilityTheory BesbesZeevi.Parametric

namespace BZA25

noncomputable def a1C {k : ℕ} (D : Market) (F : Family k D) : ℝ :=
  F.alpha * ((6 + 2 * Real.sqrt (D.M + 2)) * (Real.sqrt (cuC D) * Real.sqrt (k : ℝ)))

noncomputable def a2C (D : Market) : ℝ := Real.sqrt D.T / Real.sqrt (Real.log 2)

noncomputable def a3C (D : Market) : ℝ :=
  (6 + 2 * Real.sqrt (D.M * D.T + 2)) * (Real.sqrt (cuC D) * Real.sqrt D.T)

lemma a1C_nonneg {k : ℕ} (D : Market) (F : Family k D) : 0 ≤ a1C D F := by
  unfold a1C
  have := F.alpha_pos
  positivity

lemma a2C_nonneg (D : Market) : 0 ≤ a2C D := by unfold a2C; positivity

lemma a3C_nonneg (D : Market) : 0 ≤ a3C D := by unfold a3C; positivity

lemma sqrt_u_le (D : Market) (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt (uu D n) ≤ Real.sqrt (cuC D) * Real.sqrt (Real.log n) := by
  rw [← Real.sqrt_mul (cuC_nonneg D)]
  exact Real.sqrt_le_sqrt (uu_le D n hn)

lemma errE_le {k : ℕ} (D : Market) (F : Family k D) (n : ℕ) (τ : ℝ) (hn : 2 ≤ n) (hτ : 0 < τ)
    (hku : (k : ℝ) * uu D n ≤ n * τ) :
    errE D F n τ (uu D n) ≤ a1C D F * (Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr F.k_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hu1 : 1 ≤ uu D n := uu_ge D n hn
  have hδ : 0 < delta k τ := delta_pos F.k_pos hτ
  have hwdef : (n : ℝ) * delta k τ = n * τ / k := by unfold delta; ring
  have hwu : uu D n ≤ (n : ℝ) * delta k τ := by
    rw [hwdef, le_div_iff₀ hkR]; linarith
  have hw1 : 1 ≤ (n : ℝ) * delta k τ := le_trans hu1 hwu
  have he := edev_div (uu D n) ((n : ℝ) * delta k τ) D.M hu1 hwu hw1 D.M_pos.le
  have hEq : errE D F n τ (uu D n)
      = F.alpha * (Edev (uu D n) (D.M * ((n : ℝ) * delta k τ)) / ((n : ℝ) * delta k τ)) := by
    unfold errE
    have : (n : ℝ) * D.M * delta k τ = D.M * ((n : ℝ) * delta k τ) := by ring
    rw [this]
  have hr : 0 < Real.sqrt (n * τ) := Real.sqrt_pos.mpr (by positivity)
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
  have hsw : Real.sqrt ((n : ℝ) * delta k τ) = Real.sqrt (n * τ) / Real.sqrt (k : ℝ) := by
    rw [hwdef, Real.sqrt_div (by positivity)]
  have hsu := sqrt_u_le D n hn
  have hs0 : 0 ≤ Real.sqrt (Real.log n) := Real.sqrt_nonneg _
  have hq : Real.sqrt (uu D n) / Real.sqrt ((n : ℝ) * delta k τ)
      ≤ (Real.sqrt (cuC D) * Real.sqrt (k : ℝ)) * (Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by
    rw [hsw, div_div_eq_mul_div]
    calc Real.sqrt (uu D n) * Real.sqrt (k : ℝ) / Real.sqrt (n * τ)
        ≤ (Real.sqrt (cuC D) * Real.sqrt (Real.log n)) * Real.sqrt (k : ℝ) / Real.sqrt (n * τ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsu hsk.le) hr.le
      _ = (Real.sqrt (cuC D) * Real.sqrt (k : ℝ)) * (Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by
          ring
  rw [hEq]
  unfold a1C
  have h6 : 0 ≤ 6 + 2 * Real.sqrt (D.M + 2) := by positivity
  calc F.alpha * (Edev (uu D n) (D.M * ((n : ℝ) * delta k τ)) / ((n : ℝ) * delta k τ))
      ≤ F.alpha * ((6 + 2 * Real.sqrt (D.M + 2)) *
          (Real.sqrt (uu D n) / Real.sqrt ((n : ℝ) * delta k τ))) :=
        mul_le_mul_of_nonneg_left he F.alpha_pos.le
    _ ≤ F.alpha * ((6 + 2 * Real.sqrt (D.M + 2)) *
          ((Real.sqrt (cuC D) * Real.sqrt (k : ℝ)) * (Real.sqrt (Real.log n) / Real.sqrt (n * τ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq h6) F.alpha_pos.le
    _ = F.alpha * ((6 + 2 * Real.sqrt (D.M + 2)) * (Real.sqrt (cuC D) * Real.sqrt (k : ℝ))) *
          (Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by ring

lemma edevT_le (D : Market) (n : ℕ) (τ : ℝ) (hn : 2 ≤ n) (hτ : 0 < τ) (hτT : τ ≤ D.T)
    (hun : uu D n ≤ n) :
    Edev (uu D n) ((n : ℝ) * D.M * D.T) / n
      ≤ a3C D * (Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hu1 : 1 ≤ uu D n := uu_ge D n hn
  have hMT := mul_pos D.M_pos D.T_pos
  have he := edev_div (uu D n) n (D.M * D.T) hu1 hun hn1 hMT.le
  have hEq : (n : ℝ) * D.M * D.T = D.M * D.T * n := by ring
  rw [hEq]
  have hsu := sqrt_u_le D n hn
  have hv : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hso := s_over_sqrt n D.T τ (by omega) hτ hτT
  have hq : Real.sqrt (uu D n) / Real.sqrt (n : ℝ)
      ≤ (Real.sqrt (cuC D) * Real.sqrt D.T) * (Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by
    calc Real.sqrt (uu D n) / Real.sqrt (n : ℝ)
        ≤ (Real.sqrt (cuC D) * Real.sqrt (Real.log n)) / Real.sqrt (n : ℝ) :=
          div_le_div_of_nonneg_right hsu hv.le
      _ = Real.sqrt (cuC D) * (Real.sqrt (Real.log n) / Real.sqrt (n : ℝ)) := by ring
      _ ≤ Real.sqrt (cuC D) * (Real.sqrt D.T * (Real.sqrt (Real.log n) / Real.sqrt (n * τ))) :=
          mul_le_mul_of_nonneg_left hso (Real.sqrt_nonneg _)
      _ = (Real.sqrt (cuC D) * Real.sqrt D.T) * (Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by
          ring
  unfold a3C
  have h6 : 0 ≤ 6 + 2 * Real.sqrt (D.M * D.T + 2) := by positivity
  calc Edev (uu D n) (D.M * D.T * n) / n
      ≤ (6 + 2 * Real.sqrt (D.M * D.T + 2)) * (Real.sqrt (uu D n) / Real.sqrt (n : ℝ)) := he
    _ ≤ (6 + 2 * Real.sqrt (D.M * D.T + 2)) *
          ((Real.sqrt (cuC D) * Real.sqrt D.T) * (Real.sqrt (Real.log n) / Real.sqrt (n * τ))) :=
        mul_le_mul_of_nonneg_left hq h6
    _ = (6 + 2 * Real.sqrt (D.M * D.T + 2)) * (Real.sqrt (cuC D) * Real.sqrt D.T) *
          (Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by ring

lemma main_bound {k : ℕ} (D : Market) (F : Family k D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (τ : ℝ), 2 ≤ n → 0 < τ → τ ≤ D.T →
      (k : ℝ) * uu D n ≤ (n : ℝ) * τ → uu D n ≤ n →
      (Errn D F n τ (uu D n) + ((n : ℝ) * (D.pHi * D.x)) *
        ((((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(uu D n))))) / (n : ℝ)
        ≤ C * (τ + Real.sqrt (Real.log n) / Real.sqrt (n * τ)) := by
  have hp := pHi_pos (D := D)
  have hK2 := F.K2_pos
  have hT := D.T_pos
  have hx := D.x_pos
  have hM := D.M_pos
  have ha1 := a1C_nonneg D F
  have ha2 := a2C_nonneg D
  have ha3 := a3C_nonneg D
  set c1 := 2 * (D.pHi * D.T * F.K2) * a1C D F + D.pHi * a2C D + D.pHi * a3C D + D.pHi * D.x * a2C D
    with hc1
  have hc1nn : 0 ≤ c1 := by
    have : 0 ≤ 2 * (D.pHi * D.T * F.K2) * a1C D F := by positivity
    have : 0 ≤ D.pHi * D.x * a2C D := by positivity
    have : 0 ≤ D.pHi * a2C D := by positivity
    have : 0 ≤ D.pHi * a3C D := by positivity
    linarith
  refine ⟨c1 + D.pHi * D.M + 1, by positivity, ?_⟩
  intro n τ hn hτ hτT hku hun
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < Real.sqrt (n * τ) := Real.sqrt_pos.mpr (by positivity)
  have hη0 : 0 ≤ Real.sqrt (Real.log n) / Real.sqrt (n * τ) := by positivity
  set η := Real.sqrt (Real.log n) / Real.sqrt (n * τ) with hη
  have hE1 := errE_le D F n τ hn hτ hku
  have hE2 := edevT_le D n τ hn hτ hτT hun
  have hE3 := inv_n_le n D.T τ hn hτ hτT
  have hE4 := q_le D n (by omega)
  have hE3' : 1 / (n : ℝ) ≤ a2C D * η := hE3
  have hq : ((((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(uu D n)))) ≤ a2C D * η :=
    le_trans hE4 hE3'
  have hsplit : (Errn D F n τ (uu D n) + ((n : ℝ) * (D.pHi * D.x)) *
        ((((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(uu D n))))) / (n : ℝ)
      = 2 * (D.pHi * D.T * F.K2 * errE D F n τ (uu D n))
        + D.pHi * (1 / (n : ℝ) + D.M * τ + Edev (uu D n) ((n : ℝ) * D.M * D.T) / n)
        + D.pHi * D.x * ((((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(uu D n)))) := by
    unfold Errn
    field_simp
  rw [hsplit]
  have t1 : 2 * (D.pHi * D.T * F.K2 * errE D F n τ (uu D n))
      ≤ 2 * (D.pHi * D.T * F.K2 * (a1C D F * η)) := by
    have : 0 ≤ D.pHi * D.T * F.K2 := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE1 this) (by norm_num)
  have t2 : D.pHi * (1 / (n : ℝ) + D.M * τ + Edev (uu D n) ((n : ℝ) * D.M * D.T) / n)
      ≤ D.pHi * (a2C D * η + D.M * τ + a3C D * η) :=
    mul_le_mul_of_nonneg_left (by linarith) hp.le
  have t3 : D.pHi * D.x * ((((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(uu D n))))
      ≤ D.pHi * D.x * (a2C D * η) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have hfin : c1 * η + D.pHi * D.M * τ ≤ (c1 + D.pHi * D.M + 1) * (τ + η) := by
    have h1 : 0 ≤ D.pHi * D.M := by positivity
    nlinarith [mul_nonneg hc1nn hτ.le, mul_nonneg h1 hη0, mul_nonneg hτ.le hη0, hτ, hη0]
  have hexp : 2 * (D.pHi * D.T * F.K2 * (a1C D F * η))
      + D.pHi * (a2C D * η + D.M * τ + a3C D * η) + D.pHi * D.x * (a2C D * η)
      = c1 * η + D.pHi * D.M * τ := by
    rw [hc1]; ring
  linarith

end BZA25

open MeasureTheory ProbabilityTheory BesbesZeevi.Parametric
open Asymptotics Filter

namespace BZA25

lemma ev_log (a b c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a * Real.log n + b ≤ c * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  have hlit := isLittleO_log_rpow_atTop (r := (2 : ℝ) / 3) (by norm_num)
  have hε : 0 < c / (2 * (|a| + 1)) := by positivity
  have e1 := hlit.def hε
  have e2 : ∀ᶠ x : ℝ in atTop, (2 * |b| + 1) / c ≤ x ^ ((2 : ℝ) / 3) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).eventually_ge_atTop _
  have e3 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp (e1.and (e2.and e3))
  refine ⟨⌈X⌉₊, fun n hn => ?_⟩
  have hnX : X ≤ (n : ℝ) := le_trans (Nat.le_ceil X) (by exact_mod_cast hn)
  obtain ⟨h1, h2, h3⟩ := hX n hnX
  have hy : 0 ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hy] at h1
  have hb : |b| ≤ c / 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [div_le_iff₀ hc] at h2
    nlinarith
  have ha : |a| * (c / (2 * (|a| + 1))) ≤ c / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg a]
  calc a * Real.log n + b ≤ |a| * |Real.log n| + |b| := by
        have := le_abs_self (a * Real.log n)
        rw [abs_mul] at this
        have := le_abs_self b
        linarith
    _ ≤ |a| * (c / (2 * (|a| + 1)) * (n : ℝ) ^ ((2 : ℝ) / 3)) + c / 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
        have := mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
        linarith
    _ ≤ c / 2 * (n : ℝ) ^ ((2 : ℝ) / 3) + c / 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
        have : |a| * (c / (2 * (|a| + 1)) * (n : ℝ) ^ ((2 : ℝ) / 3))
            = (|a| * (c / (2 * (|a| + 1)))) * (n : ℝ) ^ ((2 : ℝ) / 3) := by ring
        rw [this]
        have := mul_le_mul_of_nonneg_right ha hy
        linarith
    _ = c * (n : ℝ) ^ ((2 : ℝ) / 3) := by ring

lemma jDetScaled_nonneg {k : ℕ} (D : Market) (F : Family k D)
    (θ : Fin k → ℝ) (hθ : θ ∈ F.Θ) (n : ℕ) : 0 ≤ jDetScaled D F θ n := by
  unfold jDetScaled jDet
  have h0 : F.demand D.pOff θ = 0 := (F.regular θ hθ).1
  have hmem : (0 : ℝ) ∈ {v : ℝ | ∃ p : ℝ → ℝ,
      DetFeasible D (fun p => (n : ℝ) * F.demand p θ) ((n : ℝ) * D.x) p ∧
      v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * ((n : ℝ) * F.demand (p t) θ)} := by
    refine ⟨fun _ => D.pOff, ⟨measurable_const, fun _ _ => Or.inr rfl, ?_, ?_, ?_⟩, ?_⟩
    · simp [h0]
    · simp [h0]
    · simp only [h0, mul_zero, integral_zero]
      exact mul_nonneg (Nat.cast_nonneg _) D.x_pos.le
    · simp [h0]
  by_cases hb : BddAbove {v : ℝ | ∃ p : ℝ → ℝ,
      DetFeasible D (fun p => (n : ℝ) * F.demand p θ) ((n : ℝ) * D.x) p ∧
      v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * ((n : ℝ) * F.demand (p t) θ)}
  · exact le_csSup hb hmem
  · rw [Real.sSup_of_not_bddAbove hb]

lemma regret_le_one {k : ℕ} (D : Market) (F : Family k D) (S : OptimizerSelection D F)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (N : PoissonProcess Ω P) (n : ℕ)
    (θ : Fin k → ℝ) (hθ : θ ∈ F.Θ) (τ : ℝ) :
    regret F S N n θ τ ≤ 1 := by
  unfold regret
  have h1 : 0 ≤ jPolicy F S N n θ τ := ENNReal.toReal_nonneg
  have h2 := jDetScaled_nonneg D F θ hθ n
  have : 0 ≤ jPolicy F S N n θ τ / jDetScaled D F θ n := div_nonneg h1 h2
  linarith

theorem a25_main {k : ℕ} (D : Market) (F : Family k D)
    (c c' : ℝ) (hc : 0 < c) (hcc' : c ≤ c') (n0 : ℕ) :
    ∃ C3 : ℝ, 0 < C3 ∧
      ∀ (S : OptimizerSelection D F) (τ : ℕ → ℝ),
      (∀ n : ℕ, 2 ≤ n → 0 < τ n ∧ τ n ≤ D.T) →
      (∀ n : ℕ, n0 ≤ n →
        c * (n : ℝ) ^ (-(1 : ℝ) / 3) ≤ τ n ∧
        τ n ≤ c' * (n : ℝ) ^ (-(1 : ℝ) / 3)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (N : PoissonProcess Ω P) (n : ℕ),
        2 ≤ n → ∀ θstar : Fin k → ℝ, θstar ∈ F.Θ →
        regret F S N n θstar (τ n) ≤
          C3 / (D.m * min D.T (D.x / D.M)) *
            (τ n + Real.sqrt (Real.log (n : ℝ)) /
              Real.sqrt ((n : ℝ) * τ n)) := by
  obtain ⟨C, hC, hmain⟩ := main_bound D F
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc0 := c0_nonneg D
  obtain ⟨N1, hN1⟩ := ev_log (3 * k) (k * Real.log (2 * (D.M * D.T + 2) ^ 2)) c hc
  obtain ⟨N2, hN2⟩ := ev_log 3 (Real.log (2 * (D.M * D.T + 2) ^ 2)) 1 one_pos
  set NN := max (max (max N1 N2) n0) 2 with hNN
  set A := D.m * min D.T (D.x / D.M) with hA
  have hApos : 0 < A := mul_pos D.m_pos (lt_min D.T_pos (div_pos D.x_pos D.M_pos))
  have hl2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  have hNNpos : (0 : ℝ) < NN := by
    have : 2 ≤ NN := le_max_right _ _
    exact_mod_cast (by omega : 0 < NN)
  set C3 := max C (A * (Real.sqrt (NN * D.T) / Real.sqrt (Real.log 2))) with hC3
  refine ⟨C3, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro S τ hτ1 hτ2 Ω _ P N n hn θ hθ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hτpos, hτT⟩ := hτ1 n hn
  rcases lt_or_ge n NN with hsmall | hbig
  · -- small n: regret ≤ 1 ≤ RHS
    refine le_trans (regret_le_one D F S N n θ hθ (τ n)) ?_
    have hr : 0 < Real.sqrt ((n : ℝ) * τ n) := Real.sqrt_pos.mpr (by positivity)
    have hrle : Real.sqrt ((n : ℝ) * τ n) ≤ Real.sqrt (NN * D.T) := by
      apply Real.sqrt_le_sqrt
      have : (n : ℝ) ≤ NN := by exact_mod_cast hsmall.le
      exact mul_le_mul this hτT hτpos.le hNNpos.le
    have hsle : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log n) :=
      Real.sqrt_le_sqrt (log_two_le n hn)
    have hNT : 0 < Real.sqrt (NN * D.T) := Real.sqrt_pos.mpr (mul_pos hNNpos D.T_pos)
    have hη : Real.sqrt (Real.log 2) / Real.sqrt (NN * D.T)
        ≤ Real.sqrt (Real.log n) / Real.sqrt ((n : ℝ) * τ n) := by
      rw [div_le_div_iff₀ hNT hr]
      nlinarith [Real.sqrt_nonneg (Real.log 2), Real.sqrt_nonneg (Real.log n)]
    have hCA : Real.sqrt (NN * D.T) / Real.sqrt (Real.log 2) ≤ C3 / A := by
      rw [le_div_iff₀ hApos]
      have : A * (Real.sqrt (NN * D.T) / Real.sqrt (Real.log 2)) ≤ C3 := le_max_right _ _
      linarith
    have hη0 : 0 ≤ Real.sqrt (Real.log n) / Real.sqrt ((n : ℝ) * τ n) := by positivity
    have hone : 1 = Real.sqrt (NN * D.T) / Real.sqrt (Real.log 2) *
        (Real.sqrt (Real.log 2) / Real.sqrt (NN * D.T)) := by
      field_simp
    calc (1 : ℝ) = Real.sqrt (NN * D.T) / Real.sqrt (Real.log 2) *
          (Real.sqrt (Real.log 2) / Real.sqrt (NN * D.T)) := hone
      _ ≤ C3 / A * (Real.sqrt (Real.log n) / Real.sqrt ((n : ℝ) * τ n)) :=
          mul_le_mul hCA hη (by positivity) (le_trans (by positivity) hCA)
      _ ≤ C3 / A * (τ n + Real.sqrt (Real.log n) / Real.sqrt ((n : ℝ) * τ n)) := by
          apply mul_le_mul_of_nonneg_left _ (le_trans (by positivity) hCA)
          linarith
  · -- large n
    have hnN1 : N1 ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hbig
    have hnN2 : N2 ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hbig
    have hnn0 : n0 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hbig
    have hτlow := (hτ2 n hnn0).1
    have e : (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 3) = (n : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [show (2 : ℝ) / 3 = 1 + (-(1 : ℝ) / 3) by norm_num, Real.rpow_add hn0, Real.rpow_one]
    have hnτ : c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ (n : ℝ) * τ n := by
      rw [← e]
      have := mul_le_mul_of_nonneg_left hτlow hn0.le
      linarith
    have hku : (k : ℝ) * uu D n ≤ (n : ℝ) * τ n := by
      have := hN1 n hnN1
      unfold uu
      nlinarith
    have hun : uu D n ≤ n := by
      have h := hN2 n hnN2
      have h2 : (n : ℝ) ^ ((2 : ℝ) / 3) ≤ (n : ℝ) := by
        have h1n : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        calc (n : ℝ) ^ ((2 : ℝ) / 3) ≤ (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1n (by norm_num)
          _ = n := Real.rpow_one _
      unfold uu
      linarith
    have hu0 : 0 ≤ uu D n := by have := uu_ge D n hn; linarith
    have hpre := regret_pre S N hθ n (by omega) hτpos hτT (uu D n) hu0
    have hM := hmain n (τ n) hn hτpos hτT hku hun
    refine le_trans hpre ?_
    have hAn : 0 < (n : ℝ) * A := mul_pos hn0 hApos
    rw [← div_div]
    have hCle : C ≤ C3 := le_max_left _ _
    have hη0 : 0 ≤ τ n + Real.sqrt (Real.log n) / Real.sqrt ((n : ℝ) * τ n) := by positivity
    calc (Errn D F n (τ n) (uu D n) + ((n : ℝ) * (D.pHi * D.x)) *
          ((((⌈(n : ℝ) * D.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(uu D n))))) / (n : ℝ) / A
        ≤ C * (τ n + Real.sqrt (Real.log n) / Real.sqrt ((n : ℝ) * τ n)) / A :=
          div_le_div_of_nonneg_right hM hApos.le
      _ ≤ C3 * (τ n + Real.sqrt (Real.log n) / Real.sqrt ((n : ℝ) * τ n)) / A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hη0) hApos.le
      _ = C3 / A * (τ n + Real.sqrt (Real.log n) / Real.sqrt ((n : ℝ) * τ n)) := by ring

end BZA25

set_option autoImplicit false

open BesbesZeevi.Parametric MeasureTheory in
theorem solution {k : ℕ} (D : Market) (F : Family k D)
    (c c' : ℝ) (hc : 0 < c) (hcc' : c ≤ c') (n0 : ℕ) :
    ∃ C3 : ℝ, 0 < C3 ∧
      ∀ (S : OptimizerSelection D F) (τ : ℕ → ℝ),
      (∀ n : ℕ, 2 ≤ n → 0 < τ n ∧ τ n ≤ D.T) →
      (∀ n : ℕ, n0 ≤ n →
        c * (n : ℝ) ^ (-(1 : ℝ) / 3) ≤ τ n ∧
        τ n ≤ c' * (n : ℝ) ^ (-(1 : ℝ) / 3)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (N : PoissonProcess Ω P) (n : ℕ),
        2 ≤ n → ∀ θstar : Fin k → ℝ, θstar ∈ F.Θ →
        regret F S N n θstar (τ n) ≤
          C3 / (D.m * min D.T (D.x / D.M)) *
            (τ n + Real.sqrt (Real.log (n : ℝ)) /
              Real.sqrt ((n : ℝ) * τ n)) := by
  exact BZA25.a25_main D F c c' hc hcc' n0
