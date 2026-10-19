-- Prove2me | solution 1 for BesbesZeevi.Nonparametric.case2_revenue_ratio_A15
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T14:44:44.76266+00:00
-- url     : https://prove2.me/submissions/de55c28f-268a-4a35-97ba-dce44a965373

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_BesbesZeevi_Nonparametric_Model
import Definitions.Def_BesbesZeevi_Nonparametric_Algorithm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability
open scoped NNReal

namespace BZ15

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

variable {Ω : Type*} [MeasureSpace Ω]

lemma incr_map (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Measure.map (fun ω => N t ω - N s ω) ℙ = poissonMeasure (Real.toNNReal (t - s)) := by
  obtain ⟨-, -, h⟩ := hN
  have hmono : Monotone (![0, s, t] : Fin 3 → ℝ) := by
    refine Fin.monotone_iff_le_succ.2 (fun i => ?_)
    fin_cases i <;> simp [hs, hst]
  have := (h 2 ![0, s, t] hmono rfl).2 1
  simpa using this

lemma incr_aem (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    AEMeasurable (fun ω => N t ω - N s ω) ℙ := by
  by_contra hne
  have h := incr_map N hN hs hst
  rw [Measure.map_of_not_aemeasurable hne] at h
  have h1 : (poissonMeasure (Real.toNNReal (t - s))) Set.univ = 1 := measure_univ
  rw [← h] at h1
  simp at h1

lemma isProb (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1) : IsProbabilityMeasure (ℙ : Measure Ω) := by
  have hm := incr_map N hN (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
  have ha := incr_aem N hN (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
  constructor
  have h2 : (Measure.map (fun ω => N 0 ω - N 0 ω) ℙ) Set.univ = 1 := by
    rw [hm]; exact measure_univ
  rw [Measure.map_apply_of_aemeasurable ha MeasurableSet.univ, Set.preimage_univ] at h2
  exact h2

lemma incr_law (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (S : Set ℕ) :
    ℙ ((fun ω => N t ω - N s ω) ⁻¹' S) = poissonMeasure (Real.toNNReal (t - s)) S := by
  rw [← Measure.map_apply_of_aemeasurable (incr_aem N hN hs hst) (MeasurableSet.of_discrete),
    incr_map N hN hs hst]

lemma aem_N (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1) {t : ℝ} (ht : 0 ≤ t) :
    AEMeasurable (N t) ℙ := by
  have h := incr_aem N hN (le_refl (0 : ℝ)) ht
  have e : (fun ω => N t ω - N 0 ω) = N t := by
    funext ω; rw [hN.1 ω, Nat.sub_zero]
  rwa [e] at h

lemma bad_pair (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1) (u : ℝ) (hu : 0 ≤ u) (j k : ℕ) :
    ℙ {ω | j ≤ k ∧ ¬ (((N (k : ℝ) ω : ℝ) - N (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N (k : ℝ) ω : ℝ) - N (j : ℝ) ω))}
      ≤ ENNReal.ofReal (2 * Real.exp (-u)) := by
  by_cases hjk : j ≤ k
  · have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
    set r : ℝ≥0 := Real.toNNReal ((k : ℝ) - j) with hr
    have hrr : ((r : ℝ)) = (k : ℝ) - j := Real.coe_toNNReal _ (sub_nonneg.mpr hjkR)
    set X := fun ω => N (k : ℝ) ω - N (j : ℝ) ω with hX
    have hcast : ∀ ω, ((X ω : ℕ) : ℝ) = (N (k : ℝ) ω : ℝ) - N (j : ℝ) ω := by
      intro ω
      have : N (j : ℝ) ω ≤ N (k : ℝ) ω := hN.2.1 ω hjkR
      simp only [hX]
      rw [Nat.cast_sub this]
    set SU : Set ℕ := {m | (r : ℝ) + 2 * Real.sqrt (u * r) + 4 * u ≤ (m : ℝ)} with hSU
    set SL : Set ℕ := {m | (m : ℝ) < (r : ℝ) - 2 * Real.sqrt (u * r)} with hSL
    have hsub : {ω | j ≤ k ∧ ¬ (((N (k : ℝ) ω : ℝ) - N (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N (k : ℝ) ω : ℝ) - N (j : ℝ) ω))}
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
    have e1 : ℙ (X ⁻¹' SU) = poissonMeasure r SU :=
      incr_law N hN (Nat.cast_nonneg j) hjkR SU
    have e2 : ℙ (X ⁻¹' SL) = poissonMeasure r SL :=
      incr_law N hN (Nat.cast_nonneg j) hjkR SL
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
  · have : {ω | j ≤ k ∧ ¬ (((N (k : ℝ) ω : ℝ) - N (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N (k : ℝ) ω : ℝ) - N (j : ℝ) ω))}
        = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hjk h.1
    rw [this, measure_empty]; exact bot_le

lemma good_event (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1) (K : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    ℙ {ω | ¬ GoodPath (fun t => N t ω) K u}
      ≤ ((K : ENNReal) + 1) ^ 2 * ENNReal.ofReal (2 * Real.exp (-u)) := by
  set B : ℕ → ℕ → Set Ω := fun j k => {ω | j ≤ k ∧ ¬ (((N (k : ℝ) ω : ℝ) - N (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N (k : ℝ) ω : ℝ) - N (j : ℝ) ω))}
    with hB
  have hsub : {ω | ¬ GoodPath (fun t => N t ω) K u}
      ⊆ ⋃ j ∈ Finset.range (K + 1), ⋃ k ∈ Finset.range (K + 1), B j k := by
    intro ω hω
    simp only [Set.mem_setOf_eq, GoodPath, not_forall] at hω
    obtain ⟨j, k, hjk, hkK, hbad⟩ := hω
    simp only [Set.mem_iUnion, Finset.mem_range]
    exact ⟨j, by omega, k, by omega, hjk, hbad⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have : ∀ j ∈ Finset.range (K + 1),
      ℙ (⋃ k ∈ Finset.range (K + 1), B j k) ≤ ((K : ENNReal) + 1) * ENNReal.ofReal (2 * Real.exp (-u)) := by
    intro j _
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun k _ => bad_pair N hN u hu j k)) ?_
    simp
  refine le_trans (Finset.sum_le_sum this) ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl

open BesbesZeevi.Nonparametric

lemma firstArgmax_congr (κ : ℕ) (f g : ℕ → ℝ) (h : ∀ j < κ, f j = g j) :
    firstArgmax κ f = firstArgmax κ g := by
  have hiff : ∀ j, (j < κ ∧ ∀ k, k < κ → f k ≤ f j) ↔ (j < κ ∧ ∀ k, k < κ → g k ≤ g j) := by
    intro j; constructor
    · rintro ⟨hj, hk⟩; exact ⟨hj, fun k hk' => by rw [← h k hk', ← h j hj]; exact hk k hk'⟩
    · rintro ⟨hj, hk⟩; exact ⟨hj, fun k hk' => by rw [h k hk', h j hj]; exact hk k hk'⟩
  unfold firstArgmax
  by_cases hf : ∃ j, j < κ ∧ ∀ k, k < κ → f k ≤ f j
  · have hg : ∃ j, j < κ ∧ ∀ k, k < κ → g k ≤ g j := by
      obtain ⟨j, hj⟩ := hf; exact ⟨j, (hiff j).1 hj⟩
    rw [dif_pos hf, dif_pos hg]
    apply le_antisymm
    · exact Nat.find_min' hf ((hiff _).2 (Nat.find_spec hg))
    · exact Nat.find_min' hg ((hiff _).1 (Nat.find_spec hf))
  · have hg : ¬ ∃ j, j < κ ∧ ∀ k, k < κ → g k ≤ g j := by
      rintro ⟨j, hj⟩; exact hf ⟨j, (hiff j).2 hj⟩
    rw [dif_neg hf, dif_neg hg]

lemma firstArgmax_spec (κ : ℕ) (hκ : 1 ≤ κ) (f : ℕ → ℝ) :
    firstArgmax κ f < κ ∧ ∀ k, k < κ → f k ≤ f (firstArgmax κ f) := by
  have hex : ∃ j, j < κ ∧ ∀ k, k < κ → f k ≤ f j := by
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (Finset.range κ) f
      ⟨0, Finset.mem_range.2 (by omega)⟩
    exact ⟨j, Finset.mem_range.1 hj, fun k hk => hjmax k (Finset.mem_range.2 hk)⟩
  unfold firstArgmax
  rw [dif_pos hex]
  exact Nat.find_spec hex

lemma gridPrice_mono (P : PriceSet) (κ : ℕ) : Monotone (gridPrice P κ) := by
  intro a b hab
  unfold gridPrice
  have h1 : (a : ℝ) * (P.pu - P.pl) ≤ (b : ℝ) * (P.pu - P.pl) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (by linarith [P.pl_lt_pu])
  have h2 := div_le_div_of_nonneg_right h1 (Nat.cast_nonneg κ)
  linarith

lemma phat_grid (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ) (hκ : 1 ≤ κ)
    {Ω' : Type*} (N : ℝ → Ω' → ℕ) (ω : Ω') :
    ∃ i, i < κ ∧ phat P lam x T n τ κ N ω = gridPrice P κ i := by
  refine ⟨max (firstArgmax κ (fun j => -|demandEstimate P lam n τ κ N j ω - x / T|))
      (firstArgmax κ (fun j => gridPrice P κ j * demandEstimate P lam n τ κ N j ω)), ?_, ?_⟩
  · exact max_lt (firstArgmax_spec κ hκ _).1 (firstArgmax_spec κ hκ _).1
  · unfold phat phatC phatU
    exact ((gridPrice_mono P κ).map_max).symm

/-- The finitely many deterministic times at which the revenue reads the process. -/
noncomputable def tm (P : PriceSet) (lam : ℝ → ℝ) (T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ) (i : ℕ) : ℝ :=
  if i ≤ κ then learnIntensity P lam n τ κ i
  else learnIntensity P lam n τ κ κ + (n : ℝ) * lam (gridPrice P κ (i - κ - 1)) * (T - τ)

lemma rev_congr (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ) (hκ : 1 ≤ κ)
    {Ω₁ Ω₂ : Type*} (N₁ : ℝ → Ω₁ → ℕ) (N₂ : ℝ → Ω₂ → ℕ) (ω₁ : Ω₁) (ω₂ : Ω₂)
    (h : ∀ i, i ≤ 2 * κ → N₁ (tm P lam T n τ κ i) ω₁ = N₂ (tm P lam T n τ κ i) ω₂) :
    revenue P lam x T n τ κ N₁ ω₁ = revenue P lam x T n τ κ N₂ ω₂ := by
  have hL : ∀ j, j ≤ κ →
      N₁ (learnIntensity P lam n τ κ j) ω₁ = N₂ (learnIntensity P lam n τ κ j) ω₂ := by
    intro j hj
    have := h j (by omega)
    simpa [tm, hj] using this
  have hE : ∀ j, j < κ →
      demandEstimate P lam n τ κ N₁ j ω₁ = demandEstimate P lam n τ κ N₂ j ω₂ := by
    intro j hj
    unfold demandEstimate
    rw [hL (j + 1) hj, hL j hj.le]
  have hU : phatU P lam n τ κ N₁ ω₁ = phatU P lam n τ κ N₂ ω₂ := by
    unfold phatU
    rw [firstArgmax_congr κ (fun j => gridPrice P κ j * demandEstimate P lam n τ κ N₁ j ω₁)
      (fun j => gridPrice P κ j * demandEstimate P lam n τ κ N₂ j ω₂)
      (fun j hj => by simp only [hE j hj])]
  have hC : phatC P lam x T n τ κ N₁ ω₁ = phatC P lam x T n τ κ N₂ ω₂ := by
    unfold phatC
    rw [firstArgmax_congr κ (fun j => -|demandEstimate P lam n τ κ N₁ j ω₁ - x / T|)
      (fun j => -|demandEstimate P lam n τ κ N₂ j ω₂ - x / T|)
      (fun j hj => by simp only [hE j hj])]
  have hP : phat P lam x T n τ κ N₁ ω₁ = phat P lam x T n τ κ N₂ ω₂ := by
    unfold phat; rw [hU, hC]
  obtain ⟨i, hi, hpi⟩ := phat_grid P lam x T n τ κ hκ N₁ ω₁
  have hT1 : endIntensity P lam x T n τ κ N₁ ω₁ = tm P lam T n τ κ (κ + 1 + i) := by
    have e : κ + 1 + i - κ - 1 = i := by omega
    have e2 : ¬ (κ + 1 + i ≤ κ) := by omega
    unfold endIntensity tm; rw [if_neg e2, e, hpi]
  have hT2 : endIntensity P lam x T n τ κ N₂ ω₂ = tm P lam T n τ κ (κ + 1 + i) := by
    rw [← hT1]; unfold endIntensity; rw [hP]
  have hR : requestsTotal P lam x T n τ κ N₁ ω₁ = requestsTotal P lam x T n τ κ N₂ ω₂ := by
    unfold requestsTotal; rw [hT1, hT2]; exact h _ (by omega)
  have hRL : requestsLearn P lam n τ κ N₁ ω₁ = requestsLearn P lam n τ κ N₂ ω₂ := by
    unfold requestsLearn; exact hL κ le_rfl
  unfold revenue
  rw [hR, hRL, hP]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [hL (j + 1) hj, hL j hj.le]

/-- A process on `Unit` reading off a vector of counts at the times `tm`. -/
noncomputable def fakeN (P : PriceSet) (lam : ℝ → ℝ) (T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ)
    (v : Fin (2 * κ + 1) → ℕ) : ℝ → Unit → ℕ :=
  fun s _ => if h : ∃ i : Fin (2 * κ + 1), tm P lam T n τ κ i = s then v (Classical.choose h) else 0

lemma rev_rep (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ) (hκ : 1 ≤ κ)
    {Ω' : Type*} (N : ℝ → Ω' → ℕ) (ω : Ω') :
    revenue P lam x T n τ κ N ω = revenue P lam x T n τ κ
      (fakeN P lam T n τ κ (fun i => N (tm P lam T n τ κ i) ω)) () := by
  apply rev_congr P lam x T n τ κ hκ
  intro i hi
  have hex : ∃ i' : Fin (2 * κ + 1), tm P lam T n τ κ i' = tm P lam T n τ κ i :=
    ⟨⟨i, by omega⟩, rfl⟩
  unfold fakeN
  rw [dif_pos hex]
  have := Classical.choose_spec hex
  show N (tm P lam T n τ κ i) ω = N (tm P lam T n τ κ ((Classical.choose hex : Fin (2 * κ + 1)) : ℕ)) ω
  rw [this]

lemma tm_nonneg (P : PriceSet) (lam : ℝ → ℝ) (hlam : ∀ p, 0 ≤ lam p) (T : ℝ) (n : ℕ) (τ : ℝ)
    (κ : ℕ) (hτ : 0 ≤ τ) (hτT : τ ≤ T) (i : ℕ) : 0 ≤ tm P lam T n τ κ i := by
  have hL : ∀ j, 0 ≤ learnIntensity P lam n τ κ j := by
    intro j
    unfold learnIntensity
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hlam _))
      (div_nonneg hτ (Nat.cast_nonneg _)))
  unfold tm
  split_ifs
  · exact hL i
  · exact add_nonneg (hL κ) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hlam _)) (by linarith))

lemma aem_rev (P : PriceSet) (lam : ℝ → ℝ) (hlam : ∀ p, 0 ≤ lam p) (x T : ℝ) (n : ℕ) (τ : ℝ)
    (κ : ℕ) (hκ : 1 ≤ κ) (hτ : 0 ≤ τ) (hτT : τ ≤ T) (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1) :
    AEMeasurable (revenue P lam x T n τ κ N) ℙ := by
  have hW : AEMeasurable (fun ω => fun i : Fin (2 * κ + 1) => N (tm P lam T n τ κ i) ω) ℙ :=
    aemeasurable_pi_lambda _ (fun i => aem_N N hN (tm_nonneg P lam hlam T n τ κ hτ hτT i))
  have hΨ : Measurable (fun v : Fin (2 * κ + 1) → ℕ =>
      revenue P lam x T n τ κ (fakeN P lam T n τ κ v) ()) := Measurable.of_discrete
  have e : revenue P lam x T n τ κ N = fun ω => revenue P lam x T n τ κ
      (fakeN P lam T n τ κ (fun i => N (tm P lam T n τ κ i) ω)) () :=
    funext (fun ω => rev_rep P lam x T n τ κ hκ N ω)
  rw [e]
  exact hΨ.comp_aemeasurable hW

section Det

variable {P : PriceSet} {L : DemandClass} {lam : ℝ → ℝ}

lemma pl_mem (P : PriceSet) : P.pl ∈ Set.Icc P.pl P.pu := ⟨le_rfl, P.pl_lt_pu.le⟩
lemma pu_mem (P : PriceSet) : P.pu ∈ Set.Icc P.pl P.pu := ⟨P.pl_lt_pu.le, le_rfl⟩
lemma pu_pos (P : PriceSet) : 0 < P.pu := lt_trans P.pl_pos P.pl_lt_pu

lemma lam_le_M (hlam : L.Mem P lam) {p : ℝ} (hp : p ∈ Set.Icc P.pl P.pu) : lam p ≤ L.M :=
  le_trans (le_abs_self _) (hlam.bounded p hp)

lemma lam_cont (hlam : L.Mem P lam) : ContinuousOn lam (Set.Icc P.pl P.pu) := by
  have hK : 0 ≤ L.Khi := le_trans L.Klo_pos.le L.Klo_le_Khi
  have : LipschitzOnWith (Real.toNNReal L.Khi) lam (Set.Icc P.pl P.pu) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
    exact hlam.lipschitz a ha b hb
  exact this.continuousOn

lemma lam_mem_J (hlam : L.Mem P lam) {p : ℝ} (hp : p ∈ Set.Icc P.pl P.pu) :
    lam p ∈ Set.Icc (lam P.pu) (lam P.pl) :=
  ⟨hlam.antitone hp (pu_mem P) hp.2, hlam.antitone (pl_mem P) hp hp.1⟩

lemma gam_lam (hlam : L.Mem P lam) {p : ℝ} (hp : p ∈ Set.Icc P.pl P.pu) :
    invDemand P lam (lam p) = p :=
  hlam.injOn.leftInvOn_invFunOn hp

lemma lam_surj (hlam : L.Mem P lam) {l : ℝ} (hl : l ∈ Set.Icc (lam P.pu) (lam P.pl)) :
    ∃ p ∈ Set.Icc P.pl P.pu, lam p = l :=
  intermediate_value_Icc' P.pl_lt_pu.le (lam_cont hlam) hl

lemma price_lip (hlam : L.Mem P lam) {p q : ℝ} (hp : p ∈ Set.Icc P.pl P.pu)
    (hq : q ∈ Set.Icc P.pl P.pu) : |p - q| ≤ L.Klo⁻¹ * |lam p - lam q| := by
  have h := hlam.inv_lipschitz _ (lam_mem_J hlam hp) _ (lam_mem_J hlam hq)
  rwa [gam_lam hlam hp, gam_lam hlam hq] at h

lemma exists_pU (hlam : L.Mem P lam) :
    ∃ pU ∈ Set.Icc P.pl P.pu, IsMaxOn (fun p => p * lam p) (Set.Icc P.pl P.pu) pU :=
  isCompact_Icc.exists_isMaxOn ⟨P.pl, pl_mem P⟩ (continuousOn_id.mul (lam_cont hlam))

lemma exists_pC (hlam : L.Mem P lam) (x T : ℝ) :
    ∃ pC ∈ Set.Icc P.pl P.pu, IsMinOn (fun p => |lam p - x / T|) (Set.Icc P.pl P.pu) pC :=
  isCompact_Icc.exists_isMinOn ⟨P.pl, pl_mem P⟩
    (((lam_cont hlam).sub continuousOn_const).abs)

variable {x T pU pC : ℝ}

lemma pD_mem (hpU : pU ∈ Set.Icc P.pl P.pu) (hpC : pC ∈ Set.Icc P.pl P.pu) :
    max pU pC ∈ Set.Icc P.pl P.pu :=
  ⟨le_trans hpU.1 (le_max_left _ _), max_le hpU.2 hpC.2⟩

lemma pc_le_max (hlam : L.Mem P lam) (hpC : pC ∈ Set.Icc P.pl P.pu)
    (hmin : IsMinOn (fun p => |lam p - x / T|) (Set.Icc P.pl P.pu) pC) :
    lam pC ≤ max (x / T) (lam P.pu) := by
  by_contra h
  push_neg at h
  have h1 := lt_of_le_of_lt (le_max_left _ _) h
  have h2 := lt_of_le_of_lt (le_max_right _ _) h
  rcases le_or_gt (x / T) (lam P.pu) with hc | hc
  · have := hmin (pu_mem P)
    simp only [Set.mem_setOf_eq] at this
    rw [abs_of_pos (by linarith), abs_of_nonneg (by linarith)] at this
    linarith
  · have hle : lam pC ≤ lam P.pl := hlam.antitone (pl_mem P) hpC hpC.1
    obtain ⟨p, hp, hpe⟩ := lam_surj hlam (l := x / T) ⟨hc.le, by linarith⟩
    have := hmin hp
    simp only [Set.mem_setOf_eq] at this
    rw [hpe, sub_self, abs_zero, abs_of_pos (by linarith)] at this
    linarith

end Det

lemma int_step (T τ A : ℝ) (hτ0 : 0 ≤ τ) (hτT : τ ≤ T) :
    IntervalIntegrable (fun s : ℝ => if s ≤ τ then A else 0) volume 0 T ∧
    ∫ s in (0 : ℝ)..T, (if s ≤ τ then A else 0) = A * τ := by
  have hT : 0 ≤ T := le_trans hτ0 hτT
  have he : (fun s : ℝ => if s ≤ τ then A else 0) = (Set.Iic τ).indicator (fun _ => A) := by
    funext s; simp [Set.indicator, Set.mem_Iic]
  rw [he]
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact (integrableOn_const (C := A) measure_Ioc_lt_top.ne).indicator measurableSet_Iic
  · rw [intervalIntegral.integral_of_le hT, setIntegral_indicator measurableSet_Iic,
      setIntegral_const]
    have : Set.Ioc (0 : ℝ) T ∩ Set.Iic τ = Set.Ioc 0 τ := by
      ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 hτT⟩, h3⟩
    rw [this, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hτ0, smul_eq_mul]
    ring

lemma path_le_line (P : PriceSet) {f : ℝ → ℝ} {T y A s : ℝ} (hT : 0 ≤ T) (hy : 0 ≤ y)
    (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hline : ∀ p ∈ Set.Icc P.pl P.pu, p * f p ≤ A + s * f p)
    (hoff : f P.pinf = 0) {q : ℝ → ℝ} (hq : FeasiblePath P f y T q) :
    pathRevenue f T q ≤ T * A + s * y := by
  obtain ⟨-, hrange, hint1, hle⟩ := hq
  unfold pathRevenue
  by_cases hint2 : IntervalIntegrable (fun t => q t * f (q t)) volume 0 T
  · have hfin : IntervalIntegrable (fun _ : ℝ => A) volume 0 T := intervalIntegrable_const
    calc ∫ t in (0 : ℝ)..T, q t * f (q t)
        ≤ ∫ t in (0 : ℝ)..T, (A + s * f (q t)) := by
          apply intervalIntegral.integral_mono_on hT hint2 (hfin.add (hint1.const_mul s))
          intro t ht
          rcases hrange t ht with h | h
          · exact hline _ h
          · rw [h, hoff, mul_zero, mul_zero, add_zero]; exact hA
      _ = T * A + s * ∫ t in (0 : ℝ)..T, f (q t) := by
          rw [intervalIntegral.integral_add hfin (hint1.const_mul s),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const, sub_zero,
            smul_eq_mul]
      _ ≤ T * A + s * y := by linarith [mul_le_mul_of_nonneg_left hle hs]
  · rw [intervalIntegral.integral_undef hint2]; positivity

lemma JDn_lower {P : PriceSet} {L : DemandClass} {lam : ℝ → ℝ} {x T : ℝ}
    (hx : 0 < x) (hT : 0 < T) (hlam : L.Mem P lam) (n : ℕ) :
    (n : ℝ) * (L.m * min T (x / L.M)) ≤ JDn P lam x T n := by
  obtain ⟨pm, hpm, hm⟩ := hlam.min_revenue
  have hpm0 : 0 < pm := lt_of_lt_of_le P.pl_pos hpm.1
  have hfm : 0 < lam pm := by
    by_contra hc; push_neg at hc
    have : pm * lam pm ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpm0.le hc
    linarith [L.m_pos]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set τ := min T (x / lam pm) with hτ
  have hτ0 : 0 ≤ τ := le_min hT.le (div_pos hx hfm).le
  have hτT : τ ≤ T := min_le_left _ _
  set q : ℝ → ℝ := fun s => if s ≤ τ then pm else P.pinf with hqdef
  have e1 : (fun s => (n : ℝ) * lam (q s)) = fun s => if s ≤ τ then (n : ℝ) * lam pm else 0 := by
    funext s; by_cases hs : s ≤ τ <;> simp [hqdef, hs, hlam.off]
  have e2 : (fun s => q s * ((n : ℝ) * lam (q s)))
      = fun s => if s ≤ τ then pm * ((n : ℝ) * lam pm) else 0 := by
    funext s; by_cases hs : s ≤ τ <;> simp [hqdef, hs, hlam.off]
  obtain ⟨i1, v1⟩ := int_step T τ ((n : ℝ) * lam pm) hτ0 hτT
  obtain ⟨i2, v2⟩ := int_step T τ (pm * ((n : ℝ) * lam pm)) hτ0 hτT
  have hfeas : FeasiblePath P (fun p => (n : ℝ) * lam p) ((n : ℝ) * x) T q := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Measurable.ite measurableSet_Iic measurable_const measurable_const
    · intro s _
      by_cases hs : s ≤ τ
      · left; simp only [hqdef, hs, if_true]; exact hpm
      · right; simp only [hqdef, hs, if_false]
    · show IntervalIntegrable (fun s => (n : ℝ) * lam (q s)) volume 0 T
      rw [e1]; exact i1
    · show ∫ s in (0 : ℝ)..T, (n : ℝ) * lam (q s) ≤ (n : ℝ) * x
      rw [e1, v1]
      have : lam pm * τ ≤ x := by
        have := min_le_right T (x / lam pm)
        rw [← hτ] at this
        calc lam pm * τ ≤ lam pm * (x / lam pm) := mul_le_mul_of_nonneg_left this hfm.le
          _ = x := by field_simp
      nlinarith
  have hbdd : BddAbove (pathRevenue (fun p => (n : ℝ) * lam p) T ''
      {p | FeasiblePath P (fun p => (n : ℝ) * lam p) ((n : ℝ) * x) T p}) := by
    refine ⟨T * 0 + P.pu * ((n : ℝ) * x), ?_⟩
    rintro v ⟨q', hq', rfl⟩
    apply path_le_line P (f := fun p => (n : ℝ) * lam p) (y := (n : ℝ) * x) hT.le (by positivity)
      le_rfl (pu_pos P).le _ (by simp only [hlam.off, mul_zero]) hq'
    intro p hp
    have h1 := hlam.nonneg p
    have h2 := hp.2
    have h3 : (0 : ℝ) ≤ (n : ℝ) * lam p := mul_nonneg hn h1
    nlinarith
  have hval : (n : ℝ) * (pm * lam pm * τ) ≤ JDn P lam x T n := by
    unfold JDn JD
    apply le_csSup hbdd
    refine ⟨q, hfeas, ?_⟩
    simp only [pathRevenue]
    rw [e2, v2]; ring
  refine le_trans ?_ hval
  apply mul_le_mul_of_nonneg_left _ hn
  have hτ2 : min T (x / L.M) ≤ τ := by
    apply min_le_min le_rfl
    exact div_le_div_of_nonneg_left hx.le hfm (lam_le_M hlam hpm)
  have hmin0 : 0 ≤ min T (x / L.M) := le_min hT.le (div_pos hx L.M_pos).le
  calc L.m * min T (x / L.M) ≤ (pm * lam pm) * min T (x / L.M) :=
        mul_le_mul_of_nonneg_right hm hmin0
    _ ≤ (pm * lam pm) * τ := mul_le_mul_of_nonneg_left hτ2 (by positivity)
    _ = pm * lam pm * τ := rfl

section Grid

variable {P : PriceSet} {L : DemandClass} {lam : ℝ → ℝ}

lemma grid_mem (P : PriceSet) {κ j : ℕ} (hj : j < κ) : gridPrice P κ j ∈ Set.Icc P.pl P.pu := by
  have hκ : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  have hd : 0 < P.pu - P.pl := sub_pos.2 P.pl_lt_pu
  have hjk : (j : ℝ) ≤ κ := by exact_mod_cast hj.le
  unfold gridPrice
  constructor
  · have : 0 ≤ (j : ℝ) * (P.pu - P.pl) / κ := by positivity
    linarith
  · have : (j : ℝ) * (P.pu - P.pl) / κ ≤ P.pu - P.pl := by
      rw [div_le_iff₀ hκ]; nlinarith
    linarith

lemma grid_near (P : PriceSet) {κ : ℕ} (hκ1 : 1 ≤ κ) {p : ℝ} (hp : p ∈ Set.Icc P.pl P.pu) :
    ∃ j, j < κ ∧ |p - gridPrice P κ j| ≤ (P.pu - P.pl) / κ := by
  have hκ : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  have hd : 0 < P.pu - P.pl := sub_pos.2 P.pl_lt_pu
  set δ := (P.pu - P.pl) / κ with hδ
  have hδ0 : 0 < δ := div_pos hd hκ
  have hδκ : δ * κ = P.pu - P.pl := by rw [hδ]; field_simp
  set t := (p - P.pl) / δ with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hp.1]) hδ0.le
  have htk : t ≤ κ := by
    rw [ht, div_le_iff₀ hδ0]; nlinarith [hp.2]
  have hpt : p = P.pl + t * δ := by rw [ht]; field_simp; ring
  refine ⟨min ⌊t⌋₊ (κ - 1), by omega, ?_⟩
  set j := min ⌊t⌋₊ (κ - 1) with hj
  have hg : gridPrice P κ j = P.pl + (j : ℝ) * δ := by
    unfold gridPrice; rw [hδ]; ring
  have hj1 : (j : ℝ) ≤ t := le_trans (by exact_mod_cast min_le_left _ _) (Nat.floor_le ht0)
  have hj2 : t ≤ j + 1 := by
    rcases le_total ⌊t⌋₊ (κ - 1) with h | h
    · rw [hj, min_eq_left h]; exact (Nat.lt_floor_add_one t).le
    · rw [hj, min_eq_right h]
      have : ((κ - 1 : ℕ) : ℝ) = κ - 1 := by rw [Nat.cast_sub hκ1]; simp
      rw [this]; linarith
  rw [hg, hpt, abs_le]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hj1) hδ0.le, mul_nonneg (show (0 : ℝ) ≤ j + 1 - t by linarith) hδ0.le]
  · nlinarith [mul_nonneg (sub_nonneg.2 hj1) hδ0.le, mul_nonneg (show (0 : ℝ) ≤ j + 1 - t by linarith) hδ0.le]

lemma LR_nonneg (P : PriceSet) (L : DemandClass) : 0 ≤ L.M + P.pu * L.Khi := by
  have := L.M_pos.le; have := (pu_pos P).le; have := le_trans L.Klo_pos.le L.Klo_le_Khi
  positivity

lemma rev_lip (hlam : L.Mem P lam) {p q : ℝ} (hp : p ∈ Set.Icc P.pl P.pu)
    (hq : q ∈ Set.Icc P.pl P.pu) :
    |p * lam p - q * lam q| ≤ (L.M + P.pu * L.Khi) * |p - q| := by
  have h1 := hlam.lipschitz p hp q hq
  have h2 : |lam q| ≤ L.M := hlam.bounded q hq
  have e : p * lam p - q * lam q = p * (lam p - lam q) + (p - q) * lam q := by ring
  rw [e]
  have hp0 : 0 ≤ p := le_trans P.pl_pos.le hp.1
  have k1 : p * |lam p - lam q| ≤ P.pu * (L.Khi * |p - q|) :=
    mul_le_mul hp.2 h1 (abs_nonneg _) (pu_pos P).le
  have k2 : |p - q| * |lam q| ≤ |p - q| * L.M := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  calc |p * (lam p - lam q) + (p - q) * lam q|
      ≤ |p * (lam p - lam q)| + |(p - q) * lam q| := abs_add_le _ _
    _ = p * |lam p - lam q| + |p - q| * |lam q| := by rw [abs_mul, abs_mul, abs_of_nonneg hp0]
    _ ≤ P.pu * (L.Khi * |p - q|) + |p - q| * L.M := add_le_add k1 k2
    _ = (L.M + P.pu * L.Khi) * |p - q| := by ring


end Grid


/-- The deviation bound of `path_dev` at interval length `r`. -/
noncomputable def devB (u r : ℝ) : ℝ := 2 + 2 * Real.sqrt (u * (r + 2)) + 4 * u

lemma devB_nonneg {u : ℝ} (hu : 0 ≤ u) (r : ℝ) : 0 ≤ devB u r := by
  unfold devB; have := Real.sqrt_nonneg (u * (r + 2)); positivity

lemma devB_mono {u : ℝ} (hu : 0 ≤ u) {r r' : ℝ} (h : r ≤ r') : devB u r ≤ devB u r' := by
  unfold devB
  have : Real.sqrt (u * (r + 2)) ≤ Real.sqrt (u * (r' + 2)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) hu)
  linarith

lemma sales_lb (a b c : ℝ) (hab : a ≤ b) : min (b - a) (c - a) ≤ min b c - min a c := by
  rcases le_or_gt a c with h | h
  · rw [min_eq_left h, min_sub_sub_right]
  · rw [min_eq_right h.le, min_eq_right (le_trans h.le hab)]
    have := min_le_right (b - a) (c - a)
    linarith

section Pathwise

variable {P : PriceSet} {L : DemandClass} {lam : ℝ → ℝ}

lemma learn_succ (P : PriceSet) (lam : ℝ → ℝ) (n : ℕ) (τ : ℝ) (κ j : ℕ) :
    learnIntensity P lam n τ κ (j + 1)
      = learnIntensity P lam n τ κ j + (n : ℝ) * lam (gridPrice P κ j) * (τ / (κ : ℝ)) := by
  unfold learnIntensity; rw [Finset.sum_range_succ]

lemma learn_mono (hlam : L.Mem P lam) (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (κ : ℕ) :
    Monotone (learnIntensity P lam n τ κ) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [learn_succ]
  have : 0 ≤ (n : ℝ) * lam (gridPrice P κ j) * (τ / (κ : ℝ)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hlam.nonneg _)) (div_nonneg hτ (Nat.cast_nonneg _))
  linarith

lemma learn_nonneg (hlam : L.Mem P lam) (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (κ j : ℕ) :
    0 ≤ learnIntensity P lam n τ κ j := by
  have := learn_mono hlam n hτ κ (Nat.zero_le j)
  unfold learnIntensity at this ⊢
  simpa using this

lemma learn_le (hlam : L.Mem P lam) (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) {κ : ℕ} (hκ : 1 ≤ κ) :
    learnIntensity P lam n τ κ κ ≤ (n : ℝ) * L.M * τ := by
  unfold learnIntensity
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  have hb : ∀ i ∈ Finset.range κ, (n : ℝ) * lam (gridPrice P κ i) * (τ / (κ : ℝ))
      ≤ (n : ℝ) * L.M * (τ / (κ : ℝ)) := by
    intro i hi
    have := lam_le_M hlam (grid_mem P (Finset.mem_range.1 hi))
    have h2 : 0 ≤ τ / (κ : ℝ) := div_nonneg hτ hκ0.le
    have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h3) h2
  refine le_trans (Finset.sum_le_sum hb) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (κ : ℝ) * ((n : ℝ) * L.M * (τ / (κ : ℝ))) = (n : ℝ) * L.M * τ := by
    field_simp
  rw [this]

lemma est_err (hlam : L.Mem P lam) (n : ℕ) (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 < τ) {κ : ℕ} (hκ : 1 ≤ κ)
    {Ω' : Type*} (N : ℝ → Ω' → ℕ) (ω : Ω') (hmono : Monotone (fun t => N t ω))
    (K : ℕ) (u : ℝ) (hu : 0 ≤ u) (hG : GoodPath (fun t => N t ω) K u)
    (hK : learnIntensity P lam n τ κ κ ≤ K) (j : ℕ) (hj : j < κ) :
    |demandEstimate P lam n τ κ N j ω - lam (gridPrice P κ j)|
      ≤ devB u ((n : ℝ) * L.M * (τ / (κ : ℝ))) / ((n : ℝ) * (τ / (κ : ℝ))) := by
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hw : 0 < (n : ℝ) * (τ / (κ : ℝ)) := mul_pos hn0 (div_pos hτ hκ0)
  set a := learnIntensity P lam n τ κ j with ha
  set b := learnIntensity P lam n τ κ (j + 1) with hb
  have hab : b = a + (n : ℝ) * lam (gridPrice P κ j) * (τ / (κ : ℝ)) := learn_succ P lam n τ κ j
  have ha0 : 0 ≤ a := learn_nonneg hlam n hτ.le κ j
  have hlj : 0 ≤ lam (gridPrice P κ j) := hlam.nonneg _
  have hab' : a ≤ b := by
    rw [hab]; have := mul_nonneg (mul_nonneg hn0.le hlj) (div_pos hτ hκ0).le; linarith
  have hbK : b ≤ K := le_trans (learn_mono hlam n hτ.le κ (show j + 1 ≤ κ by omega)) hK
  have hd := path_dev (fun t => N t ω) (fun s t _ hst => hmono hst) K u hu hG a b ha0 hab' hbK
  have hlen : b - a ≤ (n : ℝ) * L.M * (τ / (κ : ℝ)) := by
    rw [hab]
    have := lam_le_M hlam (grid_mem P hj)
    have h2 : 0 ≤ τ / (κ : ℝ) := (div_pos hτ hκ0).le
    have : (n : ℝ) * lam (gridPrice P κ j) * (τ / (κ : ℝ)) ≤ (n : ℝ) * L.M * (τ / (κ : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hn0.le) h2
    linarith
  have hd' : |((N b ω : ℝ) - N a ω) - (b - a)| ≤ devB u ((n : ℝ) * L.M * (τ / (κ : ℝ))) := by
    refine le_trans hd ?_
    have := devB_mono hu hlen
    unfold devB at this ⊢
    linarith
  have e : demandEstimate P lam n τ κ N j ω - lam (gridPrice P κ j)
      = (((N b ω : ℝ) - N a ω) - (b - a)) / ((n : ℝ) * (τ / (κ : ℝ))) := by
    unfold demandEstimate
    rw [← ha, ← hb, hab]
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hw]
  exact div_le_div_of_nonneg_right hd' hw.le

end Pathwise

lemma term_bounds (a b c : ℕ) (hab : b ≤ a) :
    0 ≤ (((min a c : ℕ) : ℝ) - ((min b c : ℕ) : ℝ)) ∧
    (((min a c : ℕ) : ℝ) - ((min b c : ℕ) : ℝ)) ≤ (c : ℝ) := by
  have h1 : min b c ≤ min a c := min_le_min_right _ hab
  have h2 : ((min b c : ℕ) : ℝ) ≤ ((min a c : ℕ) : ℝ) := by exact_mod_cast h1
  have h3 : ((min a c : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast min_le_right a c
  have h4 : (0 : ℝ) ≤ ((min b c : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

lemma rev_bounds {P : PriceSet} {L : DemandClass} {lam : ℝ → ℝ} (hlam : L.Mem P lam)
    (x T : ℝ) (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (hτT : τ ≤ T) {κ : ℕ} (hκ : 1 ≤ κ)
    {Ω' : Type*} (N : ℝ → Ω' → ℕ) (ω : Ω') (hmono : Monotone (fun t => N t ω)) :
    0 ≤ revenue P lam x T n τ κ N ω ∧
    revenue P lam x T n τ κ N ω ≤ ((κ : ℝ) + 1) * (P.pu * (salesCap n x : ℝ)) := by
  have hph := (phat_grid P lam x T n τ κ hκ N ω)
  obtain ⟨i, hi, hpi⟩ := hph
  have hphm : phat P lam x T n τ κ N ω ∈ Set.Icc P.pl P.pu := by rw [hpi]; exact grid_mem P hi
  have hΛE : learnIntensity P lam n τ κ κ ≤ endIntensity P lam x T n τ κ N ω := by
    unfold endIntensity
    have := mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (hlam.nonneg (phat P lam x T n τ κ N ω)))
      (sub_nonneg.2 hτT)
    linarith
  have hfin := term_bounds (requestsTotal P lam x T n τ κ N ω) (requestsLearn P lam n τ κ N ω)
    (salesCap n x) (hmono hΛE)
  have hterm : ∀ j ∈ Finset.range κ,
      0 ≤ gridPrice P κ j * (((min (N (learnIntensity P lam n τ κ (j + 1)) ω) (salesCap n x) : ℕ) : ℝ)
        - ((min (N (learnIntensity P lam n τ κ j) ω) (salesCap n x) : ℕ) : ℝ)) ∧
      gridPrice P κ j * (((min (N (learnIntensity P lam n τ κ (j + 1)) ω) (salesCap n x) : ℕ) : ℝ)
        - ((min (N (learnIntensity P lam n τ κ j) ω) (salesCap n x) : ℕ) : ℝ))
        ≤ P.pu * (salesCap n x : ℝ) := by
    intro j hj
    have hg := grid_mem P (Finset.mem_range.1 hj)
    have hb := term_bounds (N (learnIntensity P lam n τ κ (j + 1)) ω)
      (N (learnIntensity P lam n τ κ j) ω) (salesCap n x)
      (hmono (learn_mono hlam n hτ κ (Nat.le_succ j)))
    have hg0 : 0 ≤ gridPrice P κ j := le_trans P.pl_pos.le hg.1
    exact ⟨mul_nonneg hg0 hb.1, mul_le_mul hg.2 hb.2 hb.1 (pu_pos P).le⟩
  have hph0 : 0 ≤ phat P lam x T n τ κ N ω := le_trans P.pl_pos.le hphm.1
  have hs0 := Finset.sum_nonneg (fun j hj => (hterm j hj).1)
  have hs1 := Finset.sum_le_sum (fun j hj => (hterm j hj).2)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs1
  have hp1 := mul_nonneg hph0 hfin.1
  have hp2 := mul_le_mul hphm.2 hfin.2 hfin.1 (pu_pos P).le
  unfold revenue
  constructor
  · linarith
  · linarith

variable {Ω : Type*} [MeasureSpace Ω]

lemma exp_lower {P : PriceSet} {L : DemandClass} {lam : ℝ → ℝ} (hlam : L.Mem P lam)
    (x T : ℝ) (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (hτT : τ ≤ T) {κ : ℕ} (hκ : 1 ≤ κ)
    (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1) (K : ℕ) (u : ℝ) (hu : 0 ≤ u) (V : ℝ)
    (hV : ∀ ω, GoodPath (fun t => N t ω) K u → V ≤ revenue P lam x T n τ κ N ω) :
    V - max V 0 * (((K : ℝ) + 1) ^ 2 * (2 * Real.exp (-u)))
      ≤ expectedRevenue P lam x T n τ κ N := by
  haveI := isProb N hN
  set q := ((K : ℝ) + 1) ^ 2 * (2 * Real.exp (-u)) with hq
  have hq0 : 0 ≤ q := by positivity
  set G := {ω | GoodPath (fun t => N t ω) K u} with hGdef
  have hbad := good_event N hN K u hu
  set G0 := (toMeasurable ℙ Gᶜ)ᶜ with hG0def
  have hG0m : MeasurableSet G0 := (measurableSet_toMeasurable _ _).compl
  have hG0sub : G0 ⊆ G := by
    intro ω hω
    by_contra hc
    exact hω (subset_toMeasurable _ _ hc)
  have hG0c : ℙ G0ᶜ = ℙ {ω | ¬ GoodPath (fun t => N t ω) K u} := by
    rw [hG0def, compl_compl, measure_toMeasurable]
    rfl
  have hofq : ENNReal.ofReal q = ((K : ENNReal) + 1) ^ 2 * ENNReal.ofReal (2 * Real.exp (-u)) := by
    rw [hq, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ 2),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [← hG0c, ← hofq] at hbad
  have hbadR : (ℙ : Measure Ω).real G0ᶜ ≤ q := ENNReal.toReal_le_of_le_ofReal hq0 hbad
  have hPG : 1 - q ≤ (ℙ : Measure Ω).real G0 := by
    have := measureReal_compl (μ := (ℙ : Measure Ω)) hG0m
    rw [probReal_univ] at this
    linarith
  have hb := fun ω => rev_bounds hlam x T n hτ hτT hκ N ω (hN.2.1 ω)
  have hint : Integrable (revenue P lam x T n τ κ N) ℙ := by
    refine (integrable_const (((κ : ℝ) + 1) * (P.pu * (salesCap n x : ℝ)))).mono'
      (aem_rev P lam hlam.nonneg x T n τ κ hκ hτ hτT N hN).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hb ω).1]
    exact (hb ω).2
  unfold expectedRevenue
  rcases le_or_gt V 0 with hV0 | hV0
  · rw [max_eq_right hV0, zero_mul, sub_zero]
    exact le_trans hV0 (integral_nonneg (fun ω => (hb ω).1))
  rw [max_eq_left hV0.le]
  have hind : ∫ ω, G0.indicator (fun _ => V) ω ∂ℙ = (ℙ : Measure Ω).real G0 * V := by
    rw [integral_indicator_const _ hG0m, smul_eq_mul]
  have hmono : ∫ ω, G0.indicator (fun _ => V) ω ∂ℙ ≤ ∫ ω, revenue P lam x T n τ κ N ω ∂ℙ := by
    apply integral_mono ((integrable_const V).indicator hG0m) hint
    intro ω
    by_cases hω : ω ∈ G0
    · rw [Set.indicator_of_mem hω]; exact hV ω (hG0sub hω)
    · rw [Set.indicator_of_notMem hω]; exact (hb ω).1
  rw [hind] at hmono
  have := mul_le_mul_of_nonneg_left hPG hV0.le
  nlinarith

lemma ratio_arith (E J mD Err n : ℝ) (hn : 0 < n) (hmD : 0 < mD) (hJ : n * mD ≤ J)
    (hErr : 0 ≤ Err) (hE : J - n * Err ≤ E) : 1 - Err / mD ≤ E / J := by
  have hJ0 : 0 < J := lt_of_lt_of_le (mul_pos hn hmD) hJ
  rw [le_div_iff₀ hJ0]
  have h1 : n ≤ J / mD := by rw [le_div_iff₀ hmD]; linarith
  have h2 : (1 - Err / mD) * J = J - Err * (J / mD) := by field_simp
  rw [h2]
  have := mul_le_mul_of_nonneg_left h1 hErr
  linarith

noncomputable def uu (L : DemandClass) (T : ℝ) (n : ℕ) : ℝ :=
  Real.log (2 * (L.M * T + 2) ^ 2) + 3 * Real.log n

lemma c0_nonneg (L : DemandClass) {T : ℝ} (hT : 0 < T) : 0 ≤ Real.log (2 * (L.M * T + 2) ^ 2) := by
  apply Real.log_nonneg
  have := mul_pos L.M_pos hT
  nlinarith

lemma uu_nonneg (L : DemandClass) {T : ℝ} (hT : 0 < T) (n : ℕ) (hn : 1 ≤ n) : 0 ≤ uu L T n := by
  unfold uu
  have := c0_nonneg L hT
  have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  linarith

lemma q_le (L : DemandClass) {T : ℝ} (hT : 0 < T) (n : ℕ) (hn : 1 ≤ n) :
    ((((⌈(n : ℝ) * L.M * T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(uu L T n)))) ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hMT := mul_pos L.M_pos hT
  set c2 := 2 * (L.M * T + 2) ^ 2 with hc2
  have hc2pos : 0 < c2 := by positivity
  have hexp : Real.exp (uu L T n) = (n : ℝ) ^ 3 * c2 := by
    unfold uu
    rw [Real.exp_add, Real.exp_log hc2pos,
      show (3 : ℝ) * Real.log n = ((3 : ℕ) : ℝ) * Real.log n by norm_num, Real.exp_nat_mul,
      Real.exp_log hn']
    ring
  have hK : ((⌈(n : ℝ) * L.M * T⌉₊ : ℕ) : ℝ) + 1 ≤ n * (L.M * T + 2) := by
    have := Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hn'.le L.M_pos.le) hT.le)
    nlinarith
  have hK0 : 0 ≤ ((⌈(n : ℝ) * L.M * T⌉₊ : ℕ) : ℝ) + 1 := by positivity
  have hsq : (((⌈(n : ℝ) * L.M * T⌉₊ : ℕ) : ℝ) + 1) ^ 2 ≤ (n * (L.M * T + 2)) ^ 2 :=
    pow_le_pow_left₀ hK0 hK 2
  rw [Real.exp_neg, hexp]
  have hcc : (n * (L.M * T + 2)) ^ 2 * (2 * ((n : ℝ) ^ 3 * c2)⁻¹) = 1 / n := by
    rw [hc2]; field_simp
  calc (((⌈(n : ℝ) * L.M * T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) ^ 3 * c2)⁻¹)
      ≤ (n * (L.M * T + 2)) ^ 2 * (2 * ((n : ℝ) ^ 3 * c2)⁻¹) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = 1 / n := hcc

noncomputable def epsF (L : DemandClass) (T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ) : ℝ :=
  devB (uu L T n) ((n : ℝ) * L.M * (τ / (κ : ℝ))) / ((n : ℝ) * (τ / (κ : ℝ)))

noncomputable def errF (P : PriceSet) (L : DemandClass) (T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ) : ℝ :=
  τ * P.pu * L.M
  + T * ((2 * P.pu * epsF L T n τ κ + (L.M + P.pu * L.Khi) * ((P.pu - P.pl) / κ))
      + (L.M + P.pu * L.Khi) * (L.Klo⁻¹ * (2 * epsF L T n τ κ + L.Khi * ((P.pu - P.pl) / κ)))
      + P.pu * (2 * epsF L T n τ κ + L.Khi * ((P.pu - P.pl) / κ)))
  + P.pu * (1 + (n : ℝ) * L.M * τ + devB (uu L T n) ((n : ℝ) * L.M * T)) / n
  + T * P.pu * L.M * ((((⌈(n : ℝ) * L.M * T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(uu L T n))))

lemma eventually_log (a : ℝ) (ha : 0 < a) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → Real.log n ≤ a * Real.sqrt n := by
  have ho := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num))
  have hb := ho.bound ha
  have hb' : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x ∧ ‖Real.log x‖ ≤ a * ‖x ^ (1 / 2 : ℝ)‖ :=
    (Filter.eventually_ge_atTop 1).and hb
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hb')
  refine ⟨n₁, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hn₁ n hn
  have hx0 : (0 : ℝ) ≤ n := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1),
    abs_of_nonneg (Real.rpow_nonneg hx0 _), ← Real.sqrt_eq_rpow] at h2
  exact h2

set_option maxHeartbeats 1000000 in
lemma err_rate (P : PriceSet) (L : DemandClass) {T : ℝ} (hT : 0 < T) {c c' : ℝ} {τ : ℕ → ℝ}
    {κ : ℕ → ℕ} (htune : Tuning T c c' τ κ) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      errF P L T n (τ n) (κ n) ≤ Cs * (uSeq n (τ n) (κ n) + τ n) := by
  have hc := htune.c_pos
  have hc' : 0 < c' := lt_of_lt_of_le hc htune.c_le
  have hM := L.M_pos
  have hpu := pu_pos P
  have hd : 0 < P.pu - P.pl := sub_pos.2 P.pl_lt_pu
  have hK : 0 ≤ L.Khi := le_trans L.Klo_pos.le L.Klo_le_Khi
  have hKi : 0 ≤ L.Klo⁻¹ := inv_nonneg.2 L.Klo_pos.le
  have hLR := LR_nonneg P L
  have hc00 := c0_nonneg L hT
  set c0 := Real.log (2 * (L.M * T + 2) ^ 2) with hc0
  set cu := c0 + 3 with hcu
  have hcu0 : 0 ≤ cu := by linarith
  set Cε := 2 + 2 * Real.sqrt (cu * (L.M + 2)) + 4 * cu with hCε
  set Cd := 2 + 2 * Real.sqrt (cu * (L.M * T + 2)) + 4 * cu with hCd
  have hCε0 : 0 ≤ Cε := by have := Real.sqrt_nonneg (cu * (L.M + 2)); linarith
  have hCd0 : 0 ≤ Cd := by have := Real.sqrt_nonneg (cu * (L.M * T + 2)); linarith
  set A1 := 2 * P.pu + (L.M + P.pu * L.Khi) * (L.Klo⁻¹ * 2) + P.pu * 2 with hA1
  set A2 := (L.M + P.pu * L.Khi) + (L.M + P.pu * L.Khi) * (L.Klo⁻¹ * L.Khi) + P.pu * L.Khi
    with hA2
  have hA10 : 0 ≤ A1 := by
    have := mul_nonneg hLR (mul_nonneg hKi (by norm_num : (0 : ℝ) ≤ 2)); linarith
  have hA20 : 0 ≤ A2 := by
    have := mul_nonneg hLR (mul_nonneg hKi hK); have := mul_nonneg hpu.le hK; linarith
  have hpuM : 0 ≤ P.pu * L.M := mul_nonneg hpu.le hM.le
  set Cs := P.pu * L.M + T * (A1 * Cε + A2 * (P.pu - P.pl)) + P.pu / c + P.pu * L.M
      + P.pu * Cd / c + T * P.pu * L.M / c + 1 with hCs
  have hCs1 : 1 ≤ Cs := by
    have t2 : 0 ≤ T * (A1 * Cε + A2 * (P.pu - P.pl)) :=
      mul_nonneg hT.le (add_nonneg (mul_nonneg hA10 hCε0) (mul_nonneg hA20 hd.le))
    have t3 : 0 ≤ P.pu / c := div_nonneg hpu.le hc.le
    have t5 : 0 ≤ P.pu * Cd / c := div_nonneg (mul_nonneg hpu.le hCd0) hc.le
    have t6 : 0 ≤ T * P.pu * L.M / c := div_nonneg (by positivity) hc.le
    linarith
  obtain ⟨n1, hn1⟩ := eventually_log (min 1 (c / c')) (lt_min one_pos (div_pos hc hc'))
  refine ⟨Cs, by linarith, max n1 3, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnn1 : n1 ≤ n := le_trans (le_max_left _ _) hn
  have hn1' : 1 ≤ n := by omega
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < n := by linarith
  have hℓa := hn1 n hnn1
  set ℓ := Real.log n with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    have h3 : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_le_log (by norm_num) hnR
    linarith
  have hapos : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hneg : (n : ℝ) ^ (-(1 / 4 : ℝ)) = ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ := Real.rpow_neg hnpos.le _
  have ha4 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have ha2 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have ha1 : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hτl := htune.tau_lower n hn1'
  have hκl := htune.kappa_lower n hn1'
  have hκu := htune.kappa_upper n hn1'
  rw [hneg] at hτl
  have hτpos := htune.tau_pos n hn1'
  set a := (n : ℝ) ^ (1 / 4 : ℝ) with ha
  have hκpos : 0 < (κ n : ℝ) := lt_of_lt_of_le (by positivity) hκl
  have e3 : c * a ^ 3 ≤ (n : ℝ) * τ n := by
    rw [← ha4]
    have : c * a ^ 3 = a ^ 4 * (c * a⁻¹) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hτl (by positivity)
  have e1 : (c / c') * a ^ 2 * (κ n : ℝ) ≤ c * a ^ 3 := by
    calc (c / c') * a ^ 2 * (κ n : ℝ) ≤ (c / c') * a ^ 2 * (c' * a) := by
          exact mul_le_mul_of_nonneg_left hκu (by positivity)
      _ = c * a ^ 3 := by field_simp
  set w := (n : ℝ) * (τ n / (κ n : ℝ)) with hw
  have hqw : (c / c') * a ^ 2 ≤ w := by
    rw [hw, ← mul_div_assoc, le_div_iff₀ hκpos]; linarith
  have hmin1 : min 1 (c / c') ≤ 1 := min_le_left _ _
  have hmin2 : min 1 (c / c') ≤ c / c' := min_le_right _ _
  have hsqn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hℓw : ℓ ≤ w := by
    have : min 1 (c / c') * Real.sqrt n ≤ (c / c') * a ^ 2 := by
      rw [ha2]; exact mul_le_mul_of_nonneg_right hmin2 hsqn
    linarith
  have hℓa2 : ℓ ≤ a ^ 2 := by
    have : min 1 (c / c') * Real.sqrt n ≤ 1 * a ^ 2 := by
      rw [ha2]; exact mul_le_mul_of_nonneg_right hmin1 hsqn
    linarith
  have hw1 : 1 ≤ w := by linarith
  have hwpos : 0 < w := by linarith
  set sl := Real.sqrt ℓ with hsl
  set sw := Real.sqrt w with hsw
  have hsl1 : 1 ≤ sl := Real.one_le_sqrt.2 hℓ1
  have hsw1 : 1 ≤ sw := Real.one_le_sqrt.2 hw1
  have hswsq : sw * sw = w := Real.mul_self_sqrt hwpos.le
  have hslsq : sl * sl = ℓ := Real.mul_self_sqrt (by linarith)
  have hslsw : sl ≤ sw := Real.sqrt_le_sqrt hℓw
  have hsla : sl ≤ a := by
    rw [hsl, show a = Real.sqrt (a ^ 2) by rw [Real.sqrt_sq hapos.le]]
    exact Real.sqrt_le_sqrt hℓa2
  have hu0 : 0 ≤ uSeq n (τ n) (κ n) := by unfold uSeq; positivity
  set Q := uSeq n (τ n) (κ n) + τ n with hQ
  have hu_r : sl / sw ≤ Q := by
    have : sl / sw ≤ uSeq n (τ n) (κ n) := by
      unfold uSeq
      rw [← hℓ, ← hsl, ← hw, ← hsw]
      calc sl / sw = sl * (1 / sw) := by ring
        _ ≤ sl * max (1 / (κ n : ℝ)) (1 / sw) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
    linarith
  have hu_k : sl / (κ n : ℝ) ≤ Q := by
    have : sl / (κ n : ℝ) ≤ uSeq n (τ n) (κ n) := by
      unfold uSeq
      rw [← hℓ, ← hsl, ← hw, ← hsw]
      calc sl / (κ n : ℝ) = sl * (1 / (κ n : ℝ)) := by ring
        _ ≤ sl * max (1 / (κ n : ℝ)) (1 / sw) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
    linarith
  have hτQ : τ n ≤ Q := by linarith
  have huu : uu L T n ≤ cu * ℓ := by
    unfold uu; rw [← hc0, ← hℓ, hcu]
    have := mul_nonneg hc00 (sub_nonneg.2 hℓ1); linarith
  have huu0 := uu_nonneg L hT n hn1'
  -- r-facts
  have hr0 : 0 ≤ sl / sw := by positivity
  have hr1 : 1 / w ≤ sl / sw := by
    rw [← hswsq, div_le_div_iff₀ (by positivity) (by positivity)]
    have k1 : sw ≤ sw * sw := le_mul_of_one_le_left (by linarith) hsw1
    have k2 : sw * sw ≤ sl * (sw * sw) := le_mul_of_one_le_left (by positivity) hsl1
    linarith
  have hr2 : sl * sw / w = sl / sw := by
    rw [← hswsq]; field_simp
  have hr3 : ℓ / w ≤ sl / sw := by
    rw [← hswsq, ← hslsq, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hslsw (mul_nonneg (by linarith : (0 : ℝ) ≤ sl) (by linarith : (0 : ℝ) ≤ sw))
    linarith
  -- epsilon bound
  have heps : epsF L T n (τ n) (κ n) ≤ Cε * Q := by
    have hMw : (n : ℝ) * L.M * (τ n / (κ n : ℝ)) = L.M * w := by rw [hw]; ring
    unfold epsF devB
    rw [hMw, ← hw]
    have hX : Real.sqrt (uu L T n * (L.M * w + 2)) ≤ Real.sqrt (cu * (L.M + 2)) * sl * sw := by
      have h1 : uu L T n * (L.M * w + 2) ≤ (cu * (L.M + 2)) * ℓ * w := by
        have h2 : L.M * w + 2 ≤ (L.M + 2) * w := by linarith
        have h3 : 0 ≤ L.M * w + 2 := by positivity
        calc uu L T n * (L.M * w + 2) ≤ (cu * ℓ) * (L.M * w + 2) :=
              mul_le_mul_of_nonneg_right huu h3
          _ ≤ (cu * ℓ) * ((L.M + 2) * w) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = (cu * (L.M + 2)) * ℓ * w := by ring
      calc Real.sqrt (uu L T n * (L.M * w + 2)) ≤ Real.sqrt ((cu * (L.M + 2)) * ℓ * w) :=
            Real.sqrt_le_sqrt h1
        _ = Real.sqrt (cu * (L.M + 2)) * sl * sw := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    have hsplit : (2 + 2 * Real.sqrt (uu L T n * (L.M * w + 2)) + 4 * uu L T n) / w
        = 2 * (1 / w) + 2 * (Real.sqrt (uu L T n * (L.M * w + 2)) / w) + 4 * (uu L T n / w) := by
      field_simp
    rw [hsplit]
    have k1 : Real.sqrt (uu L T n * (L.M * w + 2)) / w ≤ Real.sqrt (cu * (L.M + 2)) * (sl / sw) := by
      calc Real.sqrt (uu L T n * (L.M * w + 2)) / w ≤ Real.sqrt (cu * (L.M + 2)) * sl * sw / w :=
            div_le_div_of_nonneg_right hX hwpos.le
        _ = Real.sqrt (cu * (L.M + 2)) * (sl * sw / w) := by ring
        _ = Real.sqrt (cu * (L.M + 2)) * (sl / sw) := by rw [hr2]
    have k2 : uu L T n / w ≤ cu * (sl / sw) := by
      calc uu L T n / w ≤ cu * ℓ / w := div_le_div_of_nonneg_right huu hwpos.le
        _ = cu * (ℓ / w) := by ring
        _ ≤ cu * (sl / sw) := mul_le_mul_of_nonneg_left hr3 hcu0
    have k3 : 2 * (1 / w) + 2 * (Real.sqrt (uu L T n * (L.M * w + 2)) / w) + 4 * (uu L T n / w)
        ≤ Cε * (sl / sw) := by
      rw [hCε]; linarith
    exact le_trans k3 (mul_le_mul_of_nonneg_left hu_r hCε0)
  -- delta bound
  have hdel : (P.pu - P.pl) / (κ n : ℝ) ≤ (P.pu - P.pl) * Q := by
    calc (P.pu - P.pl) / (κ n : ℝ) ≤ (P.pu - P.pl) * (sl / (κ n : ℝ)) := by
          rw [mul_div_assoc']; exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hd.le hsl1) hκpos.le
      _ ≤ (P.pu - P.pl) * Q := mul_le_mul_of_nonneg_left hu_k hd.le
  -- s = a⁻¹ facts
  have hsQ : a⁻¹ ≤ Q / c := by
    rw [le_div_iff₀ hc]; have : c * a⁻¹ ≤ τ n := hτl; linarith [mul_comm (a⁻¹) c]
  have ha_le : a ≤ a ^ 4 := by
    have h3 : 1 ≤ a ^ 3 := one_le_pow₀ ha1
    calc a = a * 1 := (mul_one a).symm
      _ ≤ a * a ^ 3 := mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = a ^ 4 := by ring
  have hinvn : 1 / (n : ℝ) ≤ a⁻¹ := by
    rw [← ha4, one_div]; exact inv_anti₀ hapos ha_le
  have hsn : Real.sqrt n = a ^ 2 := ha2.symm
  -- dv / n bound
  have hdvn : devB (uu L T n) ((n : ℝ) * L.M * T) / n ≤ Cd * a⁻¹ := by
    unfold devB
    have hX : Real.sqrt (uu L T n * ((n : ℝ) * L.M * T + 2))
        ≤ Real.sqrt (cu * (L.M * T + 2)) * sl * Real.sqrt n := by
      have h1 : uu L T n * ((n : ℝ) * L.M * T + 2) ≤ (cu * (L.M * T + 2)) * ℓ * n := by
        have h2 : (n : ℝ) * L.M * T + 2 ≤ (L.M * T + 2) * n := by linarith
        have h3 : 0 ≤ (n : ℝ) * L.M * T + 2 := by positivity
        calc uu L T n * ((n : ℝ) * L.M * T + 2) ≤ (cu * ℓ) * ((n : ℝ) * L.M * T + 2) :=
              mul_le_mul_of_nonneg_right huu h3
          _ ≤ (cu * ℓ) * ((L.M * T + 2) * n) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = (cu * (L.M * T + 2)) * ℓ * n := by ring
      calc Real.sqrt (uu L T n * ((n : ℝ) * L.M * T + 2))
          ≤ Real.sqrt ((cu * (L.M * T + 2)) * ℓ * n) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt (cu * (L.M * T + 2)) * sl * Real.sqrt n := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    have hsplit : (2 + 2 * Real.sqrt (uu L T n * ((n : ℝ) * L.M * T + 2)) + 4 * uu L T n) / n
        = 2 * (1 / n) + 2 * (Real.sqrt (uu L T n * ((n : ℝ) * L.M * T + 2)) / n)
          + 4 * (uu L T n / n) := by
      field_simp
    rw [hsplit]
    have hn4 : (n : ℝ) = a ^ 4 := ha4.symm
    have k1 : Real.sqrt (uu L T n * ((n : ℝ) * L.M * T + 2)) / n
        ≤ Real.sqrt (cu * (L.M * T + 2)) * a⁻¹ := by
      have : sl * Real.sqrt n / n ≤ a⁻¹ := by
        rw [hsn, hn4, div_le_iff₀ (by positivity)]
        have : a⁻¹ * a ^ 4 = a ^ 3 := by field_simp
        rw [this]
        have : sl * a ^ 2 ≤ a * a ^ 2 := mul_le_mul_of_nonneg_right hsla (by positivity)
        have e : a * a ^ 2 = a ^ 3 := by ring
        linarith
      calc Real.sqrt (uu L T n * ((n : ℝ) * L.M * T + 2)) / n
          ≤ Real.sqrt (cu * (L.M * T + 2)) * sl * Real.sqrt n / n :=
            div_le_div_of_nonneg_right hX hnpos.le
        _ = Real.sqrt (cu * (L.M * T + 2)) * (sl * Real.sqrt n / n) := by ring
        _ ≤ Real.sqrt (cu * (L.M * T + 2)) * a⁻¹ :=
            mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
    have k2 : uu L T n / n ≤ cu * a⁻¹ := by
      have : ℓ / n ≤ a⁻¹ := by
        rw [hn4, div_le_iff₀ (by positivity)]
        have : a⁻¹ * a ^ 4 = a ^ 3 := by field_simp
        rw [this]
        have : a ^ 2 ≤ a ^ 2 * a := le_mul_of_one_le_right (by positivity) ha1
        have e : a ^ 2 * a = a ^ 3 := by ring
        linarith
      calc uu L T n / n ≤ cu * ℓ / n := div_le_div_of_nonneg_right huu hnpos.le
        _ = cu * (ℓ / n) := by ring
        _ ≤ cu * a⁻¹ := mul_le_mul_of_nonneg_left this hcu0
    rw [hCd]; linarith
  have hq := q_le L hT n hn1'
  -- expansion of errF
  set ε := epsF L T n (τ n) (κ n) with hε
  set δ := (P.pu - P.pl) / (κ n : ℝ) with hδ
  set dv := devB (uu L T n) ((n : ℝ) * L.M * T) with hdv
  set q := ((((⌈(n : ℝ) * L.M * T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(uu L T n)))) with hqdef
  have herr : errF P L T n (τ n) (κ n) = τ n * P.pu * L.M + T * (A1 * ε + A2 * δ)
      + P.pu * (1 / n) + P.pu * L.M * τ n + P.pu * (dv / n) + T * P.pu * L.M * q := by
    unfold errF
    rw [← hε, ← hδ, ← hdv, ← hqdef, hA1, hA2]
    field_simp
    ring
  rw [herr]
  have hQ0 : 0 ≤ Q := by linarith
  have hQc : 0 ≤ Q / c := div_nonneg hQ0 hc.le
  have b1 : τ n * P.pu * L.M ≤ P.pu * L.M * Q := by
    have := mul_le_mul_of_nonneg_left hτQ hpuM; linarith
  have b2 : T * (A1 * ε + A2 * δ) ≤ T * ((A1 * Cε + A2 * (P.pu - P.pl)) * Q) := by
    apply mul_le_mul_of_nonneg_left _ hT.le
    have := mul_le_mul_of_nonneg_left heps hA10
    have := mul_le_mul_of_nonneg_left hdel hA20
    linarith
  have b3 : P.pu * (1 / n) ≤ P.pu * (Q / c) :=
    mul_le_mul_of_nonneg_left (le_trans hinvn hsQ) hpu.le
  have b4 : P.pu * L.M * τ n ≤ P.pu * L.M * Q := mul_le_mul_of_nonneg_left hτQ hpuM
  have b5 : P.pu * (dv / n) ≤ P.pu * (Cd * (Q / c)) :=
    mul_le_mul_of_nonneg_left (le_trans hdvn (mul_le_mul_of_nonneg_left hsQ hCd0)) hpu.le
  have b6 : T * P.pu * L.M * q ≤ T * P.pu * L.M * (Q / c) :=
    mul_le_mul_of_nonneg_left (le_trans hq (le_trans hinvn hsQ)) (by positivity)
  have hfin : P.pu * L.M * Q + T * ((A1 * Cε + A2 * (P.pu - P.pl)) * Q) + P.pu * (Q / c)
      + P.pu * L.M * Q + P.pu * (Cd * (Q / c)) + T * P.pu * L.M * (Q / c) + Q = Cs * Q := by
    rw [hCs]; ring
  linarith


/-! ## Case 2 (`x / T < λ(p̄)`): new material for (A-15). -/

lemma grid2 {P : PriceSet} {L : DemandClass} {lam : ℝ → ℝ} (hlam : L.Mem P lam)
    {κ : ℕ} (hκ1 : 1 ≤ κ) (lh : ℕ → ℝ) {ε : ℝ}
    (hgood : ∀ j, j < κ → |lh j - lam (gridPrice P κ j)| ≤ ε) {x T : ℝ}
    (h : x / T < lam P.pu) :
    P.pu - (P.pu - P.pl) / κ - L.Klo⁻¹ * (2 * ε)
      ≤ gridPrice P κ (firstArgmax κ (fun j => -|lh j - x / T|)) := by
  obtain ⟨hjk, hjmax⟩ := firstArgmax_spec κ hκ1 (fun j => -|lh j - x / T|)
  set j := firstArgmax κ (fun j => -|lh j - x / T|) with hjdef
  have htop : κ - 1 < κ := by omega
  have hg : -|lh (κ - 1) - x / T| ≤ -|lh j - x / T| := hjmax (κ - 1) htop
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  have hgt : gridPrice P κ (κ - 1) = P.pu - (P.pu - P.pl) / κ := by
    unfold gridPrice
    rw [Nat.cast_sub hκ1, Nat.cast_one]
    field_simp
    ring
  set pt := gridPrice P κ (κ - 1) with hpt
  set pj := gridPrice P κ j with hpj
  have hptm := grid_mem P htop
  have hpjm := grid_mem P hjk
  have hlt : x / T < lam pt := lt_of_lt_of_le h (hlam.antitone hptm (pu_mem P) hptm.2)
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hgood 0 (by omega))
  have e1 := abs_le.mp (hgood (κ - 1) htop)
  have e2 := abs_le.mp (hgood j hjk)
  have a1 : |lh (κ - 1) - x / T| ≤ lam pt - x / T + ε :=
    abs_le.mpr ⟨by linarith [e1.1, e1.2], by linarith [e1.1, e1.2]⟩
  have a2 : lam pj - ε - x / T ≤ |lh j - x / T| :=
    le_trans (by linarith [e2.1]) (le_abs_self _)
  have hle : lam pj ≤ lam pt + 2 * ε := by linarith
  have hKi : 0 ≤ L.Klo⁻¹ := inv_nonneg.2 L.Klo_pos.le
  rcases le_total pt pj with hc | hc
  · have := mul_nonneg hKi (show (0 : ℝ) ≤ 2 * ε by linarith)
    linarith
  · have hl : lam pt ≤ lam pj := hlam.antitone hpjm hptm hc
    have hpl := price_lip hlam hptm hpjm
    rw [abs_of_nonneg (sub_nonneg.2 hc), abs_of_nonpos (by linarith)] at hpl
    have : L.Klo⁻¹ * -(lam pt - lam pj) ≤ L.Klo⁻¹ * (2 * ε) :=
      mul_le_mul_of_nonneg_left (by linarith) hKi
    linarith

lemma rev_good2 {P : PriceSet} {L : DemandClass} {lam : ℝ → ℝ} (hlam : L.Mem P lam)
    {x T : ℝ} (hx : 0 < x) (hT : 0 < T) (h : x / T < lam P.pu)
    (n : ℕ) (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T)
    {κ : ℕ} (hκ : 1 ≤ κ) {Ω' : Type*} (N : ℝ → Ω' → ℕ) (ω : Ω')
    (hmono : Monotone (fun t => N t ω)) (hN0 : N 0 ω = 0)
    (K : ℕ) (u : ℝ) (hu : 0 ≤ u) (hG : GoodPath (fun t => N t ω) K u)
    (hK : (n : ℝ) * L.M * T ≤ K) (ε : ℝ)
    (hε : ε = devB u ((n : ℝ) * L.M * (τ / (κ : ℝ))) / ((n : ℝ) * (τ / (κ : ℝ)))) :
    (n : ℝ) * (P.pu * x) - (P.pu * (1 + (n : ℝ) * L.M * τ + devB u ((n : ℝ) * L.M * T))
      + (n : ℝ) * (L.M * T) * ((P.pu - P.pl) / κ + L.Klo⁻¹ * (2 * ε)))
      ≤ revenue P lam x T n τ κ N ω := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  have hM := L.M_pos
  have hΛ := learn_le hlam n hτ.le hκ
  have hΛ0 := learn_nonneg hlam n hτ.le κ κ
  have hnMτ : (n : ℝ) * L.M * τ ≤ (n : ℝ) * L.M * T :=
    mul_le_mul_of_nonneg_left hτT (by positivity)
  have hΛK : learnIntensity P lam n τ κ κ ≤ K := by linarith
  have hgood := est_err hlam n hn hτ hκ N ω hmono K u hu hG hΛK
  have hgood' : ∀ j, j < κ →
      |(fun j => demandEstimate P lam n τ κ N j ω) j - lam (gridPrice P κ j)| ≤ ε := by
    intro j hj; rw [hε]; exact hgood j hj
  have hε0 : 0 ≤ ε := by
    rw [hε]; exact div_nonneg (devB_nonneg hu _) (mul_pos hn0 (div_pos hτ hκ0)).le
  have hδ : 0 ≤ (P.pu - P.pl) / κ := div_nonneg (by linarith [P.pl_lt_pu]) (Nat.cast_nonneg _)
  set D := (P.pu - P.pl) / κ + L.Klo⁻¹ * (2 * ε) with hD
  have hD0 : 0 ≤ D := by
    have := mul_nonneg (inv_nonneg.2 L.Klo_pos.le) (show (0 : ℝ) ≤ 2 * ε by linarith)
    rw [hD]; linarith
  have hC2 := grid2 hlam hκ (fun j => demandEstimate P lam n τ κ N j ω) hgood' h
  set ph := phat P lam x T n τ κ N ω with hph
  have hphc : P.pu - D ≤ ph := by
    have : gridPrice P κ (firstArgmax κ
        (fun j => -|(fun j => demandEstimate P lam n τ κ N j ω) j - x / T|))
        ≤ ph := by
      rw [hph]; unfold phat phatC; exact le_max_left _ _
    rw [hD]; linarith
  obtain ⟨i, hi, hpi⟩ := phat_grid P lam x T n τ κ hκ N ω
  have hphm : ph ∈ Set.Icc P.pl P.pu := by rw [hph, hpi]; exact grid_mem P hi
  set Λ := learnIntensity P lam n τ κ κ with hΛdef
  set E := endIntensity P lam x T n τ κ N ω with hE
  have hEdef : E = Λ + (n : ℝ) * lam ph * (T - τ) := rfl
  have hlph0 : 0 ≤ lam ph := hlam.nonneg _
  have hlphM : lam ph ≤ L.M := lam_le_M hlam hphm
  have hlpu : lam P.pu ≤ lam ph := hlam.antitone hphm (pu_mem P) hphm.2
  have hTτ : 0 ≤ T - τ := sub_nonneg.2 hτT
  have hb1 : (n : ℝ) * lam ph * (T - τ) ≤ (n : ℝ) * L.M * (T - τ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlphM hn0.le) hTτ
  have hb0 : 0 ≤ (n : ℝ) * lam ph * (T - τ) := by positivity
  have hsplit : (n : ℝ) * L.M * τ + (n : ℝ) * L.M * (T - τ) = (n : ℝ) * L.M * T := by ring
  have hΛE : Λ ≤ E := by rw [hEdef]; linarith
  have hEK : E ≤ K := by rw [hEdef]; linarith
  set dv := devB u ((n : ℝ) * L.M * T) with hdv
  have hdv0 : 0 ≤ dv := devB_nonneg hu _
  have hd2 := path_dev (fun t => N t ω) (fun s t _ hst => hmono hst) K u hu hG Λ E hΛ0 hΛE hEK
  have hd2' : |((N E ω : ℝ) - N Λ ω) - (E - Λ)| ≤ dv := by
    refine le_trans hd2 ?_
    have := devB_mono hu (show E - Λ ≤ (n : ℝ) * L.M * T by rw [hEdef]; linarith)
    rw [hdv]; unfold devB at this ⊢; linarith
  have hd3 := path_dev (fun t => N t ω) (fun s t _ hst => hmono hst) K u hu hG 0 Λ le_rfl hΛ0 hΛK
  have hd3' : |((N Λ ω : ℝ) - N 0 ω) - (Λ - 0)| ≤ dv := by
    refine le_trans hd3 ?_
    have := devB_mono hu (show Λ - 0 ≤ (n : ℝ) * L.M * T by linarith)
    rw [hdv]; unfold devB at this ⊢; linarith
  rw [hN0, Nat.cast_zero, sub_zero, sub_zero] at hd3'
  have hYL : (N Λ ω : ℝ) ≤ Λ + dv := by have := (abs_le.mp hd3').2; linarith
  have hYP : (E - Λ) - dv ≤ (N E ω : ℝ) - N Λ ω := by have := (abs_le.mp hd2').1; linarith
  have hph0 : 0 < ph := lt_of_lt_of_le P.pl_pos hphm.1
  have hnx0 : 0 ≤ (n : ℝ) * x := by positivity
  have hcap : (n : ℝ) * x - 1 ≤ (salesCap n x : ℝ) := by
    unfold salesCap; have := Nat.lt_floor_add_one ((n : ℝ) * x); linarith
  have hcap2 : (salesCap n x : ℝ) ≤ (n : ℝ) * x := by
    unfold salesCap; exact Nat.floor_le hnx0
  have hYmono : (N Λ ω : ℝ) ≤ N E ω := by exact_mod_cast hmono hΛE
  have hsl := sales_lb (N Λ ω : ℝ) (N E ω : ℝ) (salesCap n x : ℝ) hYmono
  have hxM : x / T ≤ L.M := le_trans h.le (lam_le_M hlam (pu_mem P))
  have hxMT : x ≤ L.M * T := by
    have := (div_le_iff₀ hT).mp hxM; linarith
  -- demand of the pricing phase covers the inventory up to `n M τ`
  have hEΛ : (n : ℝ) * x - (n : ℝ) * L.M * τ ≤ E - Λ := by
    have k1 : (n : ℝ) * (x / T) * (T - τ) ≤ (n : ℝ) * lam ph * (T - τ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hn0.le) hTτ
    have k2 : (n : ℝ) * (x / T) * (T - τ) = (n : ℝ) * x - (n : ℝ) * τ * (x / T) := by
      field_simp
    have k3 : (n : ℝ) * τ * (x / T) ≤ (n : ℝ) * τ * L.M :=
      mul_le_mul_of_nonneg_left hxM (by positivity)
    have k4 : E - Λ = (n : ℝ) * lam ph * (T - τ) := by rw [hEdef]; ring
    linarith
  set S := (((min (requestsTotal P lam x T n τ κ N ω) (salesCap n x) : ℕ) : ℝ)
        - ((min (requestsLearn P lam n τ κ N ω) (salesCap n x) : ℕ) : ℝ)) with hS
  have e3 : requestsTotal P lam x T n τ κ N ω = N E ω := rfl
  have e4 : requestsLearn P lam n τ κ N ω = N Λ ω := rfl
  have hSb := term_bounds (requestsTotal P lam x T n τ κ N ω) (requestsLearn P lam n τ κ N ω)
    (salesCap n x) (by rw [e3, e4]; exact hmono hΛE)
  have hSlow : (n : ℝ) * x - (1 + (n : ℝ) * L.M * τ + dv) ≤ S := by
    rw [hS, e3, e4, Nat.cast_min, Nat.cast_min]
    refine le_trans ?_ hsl
    apply le_min
    · linarith
    · linarith
  have hSup : S ≤ (n : ℝ) * x := le_trans hSb.2 hcap2
  have hlearn : 0 ≤ ∑ j ∈ Finset.range κ, gridPrice P κ j *
      (((min (N (learnIntensity P lam n τ κ (j + 1)) ω) (salesCap n x) : ℕ) : ℝ)
        - ((min (N (learnIntensity P lam n τ κ j) ω) (salesCap n x) : ℕ) : ℝ)) := by
    apply Finset.sum_nonneg
    intro j hj
    have hg := grid_mem P (Finset.mem_range.1 hj)
    apply mul_nonneg (le_trans P.pl_pos.le hg.1)
    have h1 : min (N (learnIntensity P lam n τ κ j) ω) (salesCap n x)
        ≤ min (N (learnIntensity P lam n τ κ (j + 1)) ω) (salesCap n x) :=
      min_le_min_right _ (hmono (learn_mono hlam n hτ.le κ (Nat.le_succ j)))
    have h2 : ((min (N (learnIntensity P lam n τ κ j) ω) (salesCap n x) : ℕ) : ℝ)
        ≤ ((min (N (learnIntensity P lam n τ κ (j + 1)) ω) (salesCap n x) : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  have hrev : revenue P lam x T n τ κ N ω = (∑ j ∈ Finset.range κ, gridPrice P κ j *
      (((min (N (learnIntensity P lam n τ κ (j + 1)) ω) (salesCap n x) : ℕ) : ℝ)
        - ((min (N (learnIntensity P lam n τ κ j) ω) (salesCap n x) : ℕ) : ℝ)))
      + ph * S := rfl
  rw [hrev]
  have hpu := pu_pos P
  have f1 : (P.pu - D) * S ≤ ph * S := mul_le_mul_of_nonneg_right hphc hSb.1
  have f2 : (P.pu - D) * S = P.pu * S - D * S := by ring
  have f3 : P.pu * ((n : ℝ) * x - (1 + (n : ℝ) * L.M * τ + dv)) ≤ P.pu * S :=
    mul_le_mul_of_nonneg_left hSlow hpu.le
  have f4 : D * S ≤ D * ((n : ℝ) * x) := mul_le_mul_of_nonneg_left hSup hD0
  have f5 : D * ((n : ℝ) * x) ≤ D * ((n : ℝ) * (L.M * T)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxMT hn0.le) hD0
  have f6 : (n : ℝ) * (L.M * T) * D = D * ((n : ℝ) * (L.M * T)) := by ring
  have f7 : P.pu * ((n : ℝ) * x - (1 + (n : ℝ) * L.M * τ + dv))
      = (n : ℝ) * (P.pu * x) - P.pu * (1 + (n : ℝ) * L.M * τ + dv) := by ring
  linarith

lemma JDn_upper2 {P : PriceSet} {L : DemandClass} {lam : ℝ → ℝ} {x T : ℝ}
    (hx : 0 < x) (hT : 0 < T) (hlam : L.Mem P lam) (n : ℕ) :
    JDn P lam x T n ≤ (n : ℝ) * (P.pu * x) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpu := pu_pos P
  unfold JDn JD
  refine Real.sSup_le ?_ (by positivity)
  rintro v ⟨q', hq', rfl⟩
  have := path_le_line P (f := fun p => (n : ℝ) * lam p) (y := (n : ℝ) * x) hT.le (by positivity)
    le_rfl hpu.le (fun p hp => by
      have h1 := hlam.nonneg p
      have h2 := hp.2
      have h3 : (0 : ℝ) ≤ (n : ℝ) * lam p := mul_nonneg hn h1
      nlinarith) (by simp only [hlam.off, mul_zero]) hq'
  have e : T * 0 + P.pu * ((n : ℝ) * x) = (n : ℝ) * (P.pu * x) := by ring
  linarith

lemma ratio2 (E J A Err n : ℝ) (hn : 0 < n) (hA : 0 < A) (hJ0 : 0 < J) (hJ : J ≤ n * A)
    (hE0 : 0 ≤ E) (hErr : 0 ≤ Err) (hE : n * A - n * Err ≤ E) : 1 - Err / A ≤ E / J := by
  rcases le_or_gt A Err with h1 | h1
  · have h2 : 1 ≤ Err / A := by rw [le_div_iff₀ hA]; linarith
    have h3 : 0 ≤ E / J := div_nonneg hE0 hJ0.le
    linarith
  · rw [le_div_iff₀ hJ0]
    have hp : 0 ≤ 1 - Err / A := by
      have : Err / A ≤ 1 := by rw [div_le_one hA]; exact h1.le
      linarith
    have e : (1 - Err / A) * (n * A) = n * A - n * Err := by
      have : Err / A * A = Err := div_mul_cancel₀ Err hA.ne'
      calc (1 - Err / A) * (n * A) = n * A - n * (Err / A * A) := by ring
        _ = n * A - n * Err := by rw [this]
    calc (1 - Err / A) * J ≤ (1 - Err / A) * (n * A) := mul_le_mul_of_nonneg_left hJ hp
      _ = n * A - n * Err := e
      _ ≤ E := hE

lemma exp_main2 {P : PriceSet} {L : DemandClass} {lam : ℝ → ℝ} (hlam : L.Mem P lam)
    {x T : ℝ} (hx : 0 < x) (hT : 0 < T) (h : x / T < lam P.pu) (n : ℕ) (hn : 1 ≤ n)
    {τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T)
    {κ : ℕ} (hκ : 1 ≤ κ) (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1) :
    (n : ℝ) * (P.pu * x) - (n : ℝ) * errF P L T n τ κ ≤ expectedRevenue P lam x T n τ κ N := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hu := uu_nonneg L hT n hn
  have hK : (n : ℝ) * L.M * T ≤ (⌈(n : ℝ) * L.M * T⌉₊ : ℕ) := Nat.le_ceil _
  have hV := fun ω (hG : GoodPath (fun t => N t ω) ⌈(n : ℝ) * L.M * T⌉₊ (uu L T n)) =>
    rev_good2 hlam hx hT h n hn hτ hτT hκ N ω (hN.2.1 ω) (hN.1 ω)
      ⌈(n : ℝ) * L.M * T⌉₊ (uu L T n) hu hG hK (epsF L T n τ κ) rfl
  have hE := exp_lower hlam x T n hτ.le hτT hκ N hN ⌈(n : ℝ) * L.M * T⌉₊ (uu L T n) hu _ hV
  set ε := epsF L T n τ κ with hε
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  have hε0 : 0 ≤ ε := by
    rw [hε]; unfold epsF; exact div_nonneg (devB_nonneg hu _) (mul_pos hn0 (div_pos hτ hκ0)).le
  have hKh : 0 ≤ L.Khi := le_trans L.Klo_pos.le L.Klo_le_Khi
  have hKi : 0 ≤ L.Klo⁻¹ := inv_nonneg.2 L.Klo_pos.le
  have hδ : 0 ≤ (P.pu - P.pl) / κ := div_nonneg (by linarith [P.pl_lt_pu]) (Nat.cast_nonneg _)
  have hLR := LR_nonneg P L
  have hpu := (pu_pos P).le
  have hM := L.M_pos
  set X := (2 * P.pu * ε + (L.M + P.pu * L.Khi) * ((P.pu - P.pl) / κ))
      + (L.M + P.pu * L.Khi) * (L.Klo⁻¹ * (2 * ε + L.Khi * ((P.pu - P.pl) / κ)))
      + P.pu * (2 * ε + L.Khi * ((P.pu - P.pl) / κ)) with hX
  set D := (P.pu - P.pl) / κ + L.Klo⁻¹ * (2 * ε) with hD
  have hD0 : 0 ≤ D := by
    have := mul_nonneg hKi (show (0 : ℝ) ≤ 2 * ε by linarith)
    rw [hD]; linarith
  have hMD : L.M * D ≤ X := by
    have a1 : 0 ≤ 2 * P.pu * ε := by positivity
    have a2 : L.M * ((P.pu - P.pl) / κ) ≤ (L.M + P.pu * L.Khi) * ((P.pu - P.pl) / κ) :=
      mul_le_mul_of_nonneg_right (by have := mul_nonneg hpu hKh; linarith) hδ
    have a3 : L.M * (L.Klo⁻¹ * (2 * ε)) ≤ (L.M + P.pu * L.Khi) * (L.Klo⁻¹ * (2 * ε)) :=
      mul_le_mul_of_nonneg_right (by have := mul_nonneg hpu hKh; linarith)
        (mul_nonneg hKi (by linarith))
    have a4 : (L.M + P.pu * L.Khi) * (L.Klo⁻¹ * (2 * ε))
        ≤ (L.M + P.pu * L.Khi) * (L.Klo⁻¹ * (2 * ε + L.Khi * ((P.pu - P.pl) / κ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (by have := mul_nonneg hKh hδ; linarith) hKi) hLR
    have a5 : 0 ≤ P.pu * (2 * ε + L.Khi * ((P.pu - P.pl) / κ)) := by positivity
    have e : L.M * D = L.M * ((P.pu - P.pl) / κ) + L.M * (L.Klo⁻¹ * (2 * ε)) := by
      rw [hD]; ring
    rw [e, hX]; linarith
  set dv := devB (uu L T n) ((n : ℝ) * L.M * T) with hdv
  have hdv0 : 0 ≤ dv := devB_nonneg hu _
  set q := (((⌈(n : ℝ) * L.M * T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(uu L T n))) with hq
  have hq0 : 0 ≤ q := by positivity
  set V := (n : ℝ) * (P.pu * x) - (P.pu * (1 + (n : ℝ) * L.M * τ + dv)
      + (n : ℝ) * (L.M * T) * ((P.pu - P.pl) / κ + L.Klo⁻¹ * (2 * ε))) with hVdef
  have hVD : V = (n : ℝ) * (P.pu * x) - P.pu * (1 + (n : ℝ) * L.M * τ + dv)
      - (n : ℝ) * T * (L.M * D) := by rw [hVdef, hD]; ring
  have hE1 : 0 ≤ 1 + (n : ℝ) * L.M * τ + dv := by positivity
  have hxM : x / T ≤ L.M := le_trans h.le (lam_le_M hlam (pu_mem P))
  have hxMT : x ≤ L.M * T := by
    have := (div_le_iff₀ hT).mp hxM; linarith
  have hVup : V ≤ (n : ℝ) * T * (P.pu * L.M) := by
    rw [hVD]
    have k1 : (n : ℝ) * (P.pu * x) ≤ (n : ℝ) * (P.pu * (L.M * T)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxMT hpu) hn0.le
    have k2 := mul_nonneg hpu hE1
    have k3 : 0 ≤ (n : ℝ) * T * (L.M * D) := by positivity
    have e : (n : ℝ) * (P.pu * (L.M * T)) = (n : ℝ) * T * (P.pu * L.M) := by ring
    linarith
  have hmaxV : max V 0 ≤ (n : ℝ) * T * (P.pu * L.M) :=
    max_le hVup (by positivity)
  have hmq := mul_le_mul_of_nonneg_right hmaxV hq0
  have hE' : V - max V 0 * q ≤ expectedRevenue P lam x T n τ κ N := hE
  have hnTMD : (n : ℝ) * T * (L.M * D) ≤ (n : ℝ) * T * X :=
    mul_le_mul_of_nonneg_left hMD (by positivity)
  have herr : (n : ℝ) * errF P L T n τ κ = (n : ℝ) * τ * (P.pu * L.M) + (n : ℝ) * T * X
      + P.pu * (1 + (n : ℝ) * L.M * τ + dv) + (n : ℝ) * T * (P.pu * L.M) * q := by
    unfold errF
    rw [← hε, ← hdv, ← hq, hX]
    field_simp
  have hτM : 0 ≤ (n : ℝ) * τ * (P.pu * L.M) := by positivity
  linarith

lemma u_lower {T c c' : ℝ} {τ : ℕ → ℝ} {κ : ℕ → ℕ} (htune : Tuning T c c' τ κ)
    (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt (Real.log 2) / (c' * (n : ℝ) ^ (1 / 4 : ℝ)) ≤ uSeq n (τ n) (κ n) := by
  have hn1 : 1 ≤ n := by omega
  have hκu := htune.kappa_upper n hn1
  have hκpos : (0 : ℝ) < (κ n : ℝ) := by
    have := htune.kappa_pos n hn1; exact_mod_cast (show 0 < κ n by omega)
  have h1 : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log n) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have h2 : Real.sqrt (Real.log 2) / (c' * (n : ℝ) ^ (1 / 4 : ℝ))
      ≤ Real.sqrt (Real.log 2) / (κ n : ℝ) :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hκpos hκu
  have h3 : Real.sqrt (Real.log 2) / (κ n : ℝ) ≤ Real.sqrt (Real.log n) * (1 / (κ n : ℝ)) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right h1 hκpos.le
  have h4 : Real.sqrt (Real.log n) * (1 / (κ n : ℝ)) ≤ uSeq n (τ n) (κ n) := by
    unfold uSeq
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg _)
  linarith

lemma tau_le_u {T c c' : ℝ} {τ : ℕ → ℝ} {κ : ℕ → ℕ} (htune : Tuning T c c' τ κ)
    (n : ℕ) (hn : 2 ≤ n) :
    τ n ≤ c' ^ 2 / Real.sqrt (Real.log 2) * uSeq n (τ n) (κ n) := by
  have hn1 : 1 ≤ n := by omega
  have hc' : 0 < c' := lt_of_lt_of_le htune.c_pos htune.c_le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 (Real.log_pos (by norm_num))
  have hapos : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hτu := htune.tau_upper n hn1
  rw [Real.rpow_neg hnpos.le] at hτu
  have hl := u_lower htune n hn
  have hk : 0 ≤ c' ^ 2 / Real.sqrt (Real.log 2) := by positivity
  have e : c' ^ 2 / Real.sqrt (Real.log 2)
      * (Real.sqrt (Real.log 2) / (c' * (n : ℝ) ^ (1 / 4 : ℝ)))
      = c' * ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ := by
    field_simp
  calc τ n ≤ c' * ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ := hτu
    _ = c' ^ 2 / Real.sqrt (Real.log 2)
      * (Real.sqrt (Real.log 2) / (c' * (n : ℝ) ^ (1 / 4 : ℝ))) := e.symm
    _ ≤ c' ^ 2 / Real.sqrt (Real.log 2) * uSeq n (τ n) (κ n) :=
      mul_le_mul_of_nonneg_left hl hk

theorem main_thm2 (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x) (hT : 0 < T)
    (c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ) :
    ∃ C₁₁ : ℝ, 0 < C₁₁ ∧
      ∀ (Ω : Type*) [MeasureSpace Ω] (N : ℝ → Ω → ℕ), IsPoissonProcess N 1 →
      ∀ lam : ℝ → ℝ, L.Mem P lam → x / T < lam P.pu →
        ∀ n : ℕ, 2 ≤ n →
          1 - C₁₁ / (P.pu * x) * uSeq n (τ n) (κ n)
            ≤ expectedRevenue P lam x T n (τ n) (κ n) N / JDn P lam x T n := by
  obtain ⟨Cs, hCs, n0, hn0⟩ := err_rate P L hT htune
  have hc := htune.c_pos
  have hc' : 0 < c' := lt_of_lt_of_le hc htune.c_le
  have hpu := pu_pos P
  have hA : 0 < P.pu * x := mul_pos hpu hx
  have hs2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 (Real.log_pos (by norm_num))
  set s2 := Real.sqrt (Real.log 2) with hs2def
  set k := c' ^ 2 / s2 with hk
  have hk0 : 0 ≤ k := by positivity
  have hn01 : (0 : ℝ) < (n0 : ℝ) + 1 := by positivity
  set C11 := Cs * (1 + k) + P.pu * x * (c' * ((n0 : ℝ) + 1)) / s2 with hC11
  have hB0 : 0 < P.pu * x * (c' * ((n0 : ℝ) + 1)) / s2 := by positivity
  have hA0 : 0 ≤ Cs * (1 + k) := by positivity
  have hC11pos : 0 < C11 := by linarith
  refine ⟨C11, hC11pos, ?_⟩
  intro Ω _ N hN lam hlam h n hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hτ := htune.tau_pos n hn1
  have hτT := htune.tau_le n hn1
  have hκ := htune.kappa_pos n hn1
  have hu0 : 0 ≤ uSeq n (τ n) (κ n) := by unfold uSeq; positivity
  have hmD : 0 < L.m * min T (x / L.M) := mul_pos L.m_pos (lt_min hT (div_pos hx L.M_pos))
  have hJ : (n : ℝ) * (L.m * min T (x / L.M)) ≤ JDn P lam x T n := JDn_lower hx hT hlam n
  have hJpos : 0 < JDn P lam x T n := lt_of_lt_of_le (mul_pos hnpos hmD) hJ
  have hJup := JDn_upper2 (P := P) (L := L) (lam := lam) hx hT hlam n
  haveI := isProb N hN
  have hE0 : 0 ≤ expectedRevenue P lam x T n (τ n) (κ n) N :=
    integral_nonneg (fun ω => (rev_bounds hlam x T n hτ.le hτT hκ N ω (hN.2.1 ω)).1)
  have hratio0 : 0 ≤ expectedRevenue P lam x T n (τ n) (κ n) N / JDn P lam x T n :=
    div_nonneg hE0 hJpos.le
  rcases lt_or_ge n n0 with hsmall | hbig
  · have hl := u_lower htune n hn
    have hapos : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hnpos _
    have han : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le (x := (n : ℝ)) (by exact_mod_cast hn1)
        (show (1 / 4 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have hn0' : (n : ℝ) ≤ (n0 : ℝ) + 1 := by
      have : n ≤ n0 + 1 := by omega
      exact_mod_cast this
    have hden : c' * (n : ℝ) ^ (1 / 4 : ℝ) ≤ c' * ((n0 : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (le_trans han hn0') hc'.le
    have hl2 : s2 / (c' * ((n0 : ℝ) + 1)) ≤ uSeq n (τ n) (κ n) :=
      le_trans (div_le_div_of_nonneg_left hs2.le (by positivity) hden) hl
    have hC : c' * ((n0 : ℝ) + 1) / s2 ≤ C11 / (P.pu * x) := by
      rw [le_div_iff₀ hA]
      have e : c' * ((n0 : ℝ) + 1) / s2 * (P.pu * x) = P.pu * x * (c' * ((n0 : ℝ) + 1)) / s2 := by
        ring
      rw [e, hC11]; linarith
    have h1 : 1 ≤ c' * ((n0 : ℝ) + 1) / s2 * uSeq n (τ n) (κ n) := by
      have e : c' * ((n0 : ℝ) + 1) / s2 * (s2 / (c' * ((n0 : ℝ) + 1))) = 1 := by
        field_simp
      calc (1 : ℝ) = c' * ((n0 : ℝ) + 1) / s2 * (s2 / (c' * ((n0 : ℝ) + 1))) := e.symm
        _ ≤ c' * ((n0 : ℝ) + 1) / s2 * uSeq n (τ n) (κ n) :=
          mul_le_mul_of_nonneg_left hl2 (by positivity)
    have h2 : c' * ((n0 : ℝ) + 1) / s2 * uSeq n (τ n) (κ n)
        ≤ C11 / (P.pu * x) * uSeq n (τ n) (κ n) := mul_le_mul_of_nonneg_right hC hu0
    linarith
  · have herr := hn0 n hbig
    have hτu := tau_le_u htune n hn
    have hmain := exp_main2 hlam hx hT h n hn1 hτ hτT hκ N hN
    have hmain' : (n : ℝ) * (P.pu * x) - (n : ℝ) * max (errF P L T n (τ n) (κ n)) 0
        ≤ expectedRevenue P lam x T n (τ n) (κ n) N := by
      have := mul_le_mul_of_nonneg_left (le_max_left (errF P L T n (τ n) (κ n)) 0) hnpos.le
      linarith
    have hr := ratio2 _ _ (P.pu * x) (max (errF P L T n (τ n) (κ n)) 0) n hnpos hA hJpos hJup
      hE0 (le_max_right _ _) hmain'
    have hbnd : Cs * (uSeq n (τ n) (κ n) + τ n) ≤ C11 * uSeq n (τ n) (κ n) := by
      have k1 : Cs * (uSeq n (τ n) (κ n) + τ n) ≤ Cs * (uSeq n (τ n) (κ n) + k * uSeq n (τ n) (κ n)) :=
        mul_le_mul_of_nonneg_left (by linarith) hCs.le
      have k2 : Cs * (uSeq n (τ n) (κ n) + k * uSeq n (τ n) (κ n)) = Cs * (1 + k) * uSeq n (τ n) (κ n) := by
        ring
      have k3 : Cs * (1 + k) * uSeq n (τ n) (κ n) ≤ C11 * uSeq n (τ n) (κ n) :=
        mul_le_mul_of_nonneg_right (by rw [hC11]; linarith) hu0
      linarith
    have hm : max (errF P L T n (τ n) (κ n)) 0 ≤ C11 * uSeq n (τ n) (κ n) :=
      max_le (le_trans herr hbnd) (by positivity)
    have hm2 : max (errF P L T n (τ n) (κ n)) 0 / (P.pu * x)
        ≤ C11 / (P.pu * x) * uSeq n (τ n) (κ n) := by
      rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hm hA.le
    linarith

end BZ15

open BesbesZeevi.Nonparametric MeasureTheory ProbabilityTheory ProcessingNetworks.Stability in
theorem solution (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x) (hT : 0 < T)
    (c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ) :
    ∃ C₁₁ : ℝ, 0 < C₁₁ ∧
      ∀ (Ω : Type*) [MeasureSpace Ω] (N : ℝ → Ω → ℕ), IsPoissonProcess N 1 →
      ∀ lam : ℝ → ℝ, L.Mem P lam → x / T < lam P.pu →
        ∀ n : ℕ, 2 ≤ n →
          1 - C₁₁ / (P.pu * x) * uSeq n (τ n) (κ n)
            ≤ expectedRevenue P lam x T n (τ n) (κ n) N / JDn P lam x T n := by
  exact BZ15.main_thm2 P L x T hx hT c c' τ κ htune
