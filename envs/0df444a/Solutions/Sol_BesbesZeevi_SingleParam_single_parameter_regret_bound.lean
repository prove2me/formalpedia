-- Prove2me | solution 1 for BesbesZeevi.SingleParam.single_parameter_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T23:04:22.673239+00:00
-- url     : https://prove2.me/submissions/1daeb041-3dd1-423d-b8e0-f1ec364bb393

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_PoissonProcess
import Definitions.Def_BesbesZeevi_SingleParam_Model
import Definitions.Def_BesbesZeevi_SingleParam_Family
import Definitions.Def_BesbesZeevi_SingleParam_Tuning
import Definitions.Def_BesbesZeevi_SingleParam_Algorithm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BZ635

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

end BZ635

open MeasureTheory ProbabilityTheory BesbesZeevi.SingleParam
open scoped NNReal

namespace BZ635

/-- Deviation bound at all integer pairs `j ≤ k ≤ K`. -/
def GoodPath (Nω : ℝ → ℕ) (K : ℕ) (u : ℝ) : Prop :=
  ∀ j k : ℕ, j ≤ k → k ≤ K →
    ((Nω (k : ℝ) : ℝ) - Nω (j : ℝ) ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
    (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (Nω (k : ℝ) : ℝ) - Nω (j : ℝ))

lemma path_dev (Nω : ℝ → ℕ) (hmono : Monotone Nω) (K : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hG : GoodPath Nω K u) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbK : b ≤ K) :
    |((Nω b : ℝ) - Nω a) - (b - a)| ≤ 2 + 2 * Real.sqrt (u * (b - a + 2)) + 4 * u := by
  have hsq0 : 0 ≤ Real.sqrt (u * (b - a + 2)) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := le_trans ha hab
  apply abs_le.mpr
  constructor
  · rcases lt_or_ge (b - a) 2 with hsmall | hbig
    · have : (Nω a : ℝ) ≤ Nω b := by exact_mod_cast hmono hab
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
    have m1 : (Nω a : ℝ) ≤ Nω (j : ℝ) := by exact_mod_cast hmono hj1
    have m2 : (Nω (k : ℝ) : ℝ) ≤ Nω b := by exact_mod_cast hmono hk1
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
    have m1 : (Nω (j : ℝ) : ℝ) ≤ Nω a := by exact_mod_cast hmono hj1
    have m2 : (Nω b : ℝ) ≤ Nω (k : ℝ) := by exact_mod_cast hmono hk1
    have hs : Real.sqrt (u * ((k : ℝ) - j)) ≤ Real.sqrt (u * (b - a + 2)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ hu
      linarith
    linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma incr_law (N : PoissonProcess Ω P) (j k : ℕ) (hjk : j ≤ k) (S : Set ℕ) :
    P ((fun ω => N.N (k : ℝ) ω - N.N (j : ℝ) ω) ⁻¹' S)
      = poissonMeasure ⟨(k : ℝ) - j, sub_nonneg.mpr (by exact_mod_cast hjk)⟩ S := by
  have hmeas : Measurable (fun ω => N.N (k : ℝ) ω - N.N (j : ℝ) ω) :=
    (N.meas _).sub (N.meas _)
  rw [← Measure.map_apply hmeas (MeasurableSet.of_discrete),
    N.law (j : ℝ) (k : ℝ) (by exact_mod_cast hjk) (Nat.cast_nonneg j)]

lemma bad_pair (N : PoissonProcess Ω P) (u : ℝ) (hu : 0 ≤ u) (j k : ℕ) :
    P {ω | j ≤ k ∧ ¬ (((N.N (k : ℝ) ω : ℝ) - N.N (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N.N (k : ℝ) ω : ℝ) - N.N (j : ℝ) ω))}
      ≤ ENNReal.ofReal (2 * Real.exp (-u)) := by
  by_cases hjk : j ≤ k
  · set r : ℝ≥0 := ⟨(k : ℝ) - j, sub_nonneg.mpr (by exact_mod_cast hjk)⟩ with hr
    have hrr : ((r : ℝ)) = (k : ℝ) - j := rfl
    set X := fun ω => N.N (k : ℝ) ω - N.N (j : ℝ) ω with hX
    have hcast : ∀ ω, ((X ω : ℕ) : ℝ) = (N.N (k : ℝ) ω : ℝ) - N.N (j : ℝ) ω := by
      intro ω
      have : N.N (j : ℝ) ω ≤ N.N (k : ℝ) ω := N.mono ω (by exact_mod_cast hjk)
      simp only [hX]
      rw [Nat.cast_sub this]
    set SU : Set ℕ := {m | (r : ℝ) + 2 * Real.sqrt (u * r) + 4 * u ≤ (m : ℝ)} with hSU
    set SL : Set ℕ := {m | (m : ℝ) < (r : ℝ) - 2 * Real.sqrt (u * r)} with hSL
    have hsub : {ω | j ≤ k ∧ ¬ (((N.N (k : ℝ) ω : ℝ) - N.N (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N.N (k : ℝ) ω : ℝ) - N.N (j : ℝ) ω))}
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
  · have : {ω | j ≤ k ∧ ¬ (((N.N (k : ℝ) ω : ℝ) - N.N (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N.N (k : ℝ) ω : ℝ) - N.N (j : ℝ) ω))}
        = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hjk h.1
    rw [this, measure_empty]; exact bot_le

lemma good_event (N : PoissonProcess Ω P) (K : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    P {ω | ¬ GoodPath (fun t => N.N t ω) K u}
      ≤ ((K : ENNReal) + 1) ^ 2 * ENNReal.ofReal (2 * Real.exp (-u)) := by
  set B : ℕ → ℕ → Set Ω := fun j k => {ω | j ≤ k ∧ ¬ (((N.N (k : ℝ) ω : ℝ) - N.N (j : ℝ) ω
          ≤ ((k : ℝ) - j) + 2 * Real.sqrt (u * ((k : ℝ) - j)) + 4 * u) ∧
        (((k : ℝ) - j) - 2 * Real.sqrt (u * ((k : ℝ) - j)) ≤ (N.N (k : ℝ) ω : ℝ) - N.N (j : ℝ) ω))}
    with hB
  have hsub : {ω | ¬ GoodPath (fun t => N.N t ω) K u}
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

end BZ635

open MeasureTheory BesbesZeevi.SingleParam

namespace BZ635

variable {D : Market} {F : Family D}

lemma lam_nonneg {θ : ℝ} (hθ : θ ∈ F.Θ) {p : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi) :
    0 ≤ F.lam p θ := (F.inClass θ hθ).2.1 p hp

lemma lam_anti {θ : ℝ} (hθ : θ ∈ F.Θ) : AntitoneOn (fun p => F.lam p θ) (Set.Icc D.pLo D.pHi) :=
  (F.inClass θ hθ).2.2.1

lemma lam_inj {θ : ℝ} (hθ : θ ∈ F.Θ) : Set.InjOn (fun p => F.lam p θ) (Set.Icc D.pLo D.pHi) :=
  (F.inClass θ hθ).2.2.2.1

lemma lam_le_M {θ : ℝ} (hθ : θ ∈ F.Θ) {p : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi) :
    F.lam p θ ≤ F.M := le_trans (le_abs_self _) ((F.inClass θ hθ).2.2.2.2.2.1 p hp)

lemma lam_cont {θ : ℝ} (hθ : θ ∈ F.Θ) : ContinuousOn (fun p => F.lam p θ) (Set.Icc D.pLo D.pHi) := by
  have hL := (F.inClass θ hθ).2.2.2.2.2.2.1
  have hK : 0 ≤ F.KHi := le_trans F.KLo_pos.le F.KLo_le_KHi
  have : LipschitzOnWith (Real.toNNReal F.KHi) (fun p => F.lam p θ) (Set.Icc D.pLo D.pHi) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
    exact hL a ha b hb
  exact this.continuousOn

lemma pLo_mem : D.pLo ∈ Set.Icc D.pLo D.pHi := ⟨le_rfl, D.pLo_lt_pHi.le⟩
lemma pHi_mem : D.pHi ∈ Set.Icc D.pLo D.pHi := ⟨D.pLo_lt_pHi.le, le_rfl⟩

lemma lam_mem_J {θ : ℝ} (hθ : θ ∈ F.Θ) {p : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi) :
    F.lam p θ ∈ Set.Icc (F.lam D.pHi θ) (F.lam D.pLo θ) :=
  ⟨lam_anti hθ hp pHi_mem hp.2, lam_anti hθ pLo_mem hp hp.1⟩

lemma gam_lam {θ : ℝ} (hθ : θ ∈ F.Θ) {p : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi) :
    invDemand D (fun p => F.lam p θ) (F.lam p θ) = p :=
  (lam_inj hθ).leftInvOn_invFunOn hp

lemma lam_surj {θ : ℝ} (hθ : θ ∈ F.Θ) {l : ℝ}
    (hl : l ∈ Set.Icc (F.lam D.pHi θ) (F.lam D.pLo θ)) :
    ∃ p ∈ Set.Icc D.pLo D.pHi, F.lam p θ = l :=
  intermediate_value_Icc' D.pLo_lt_pHi.le (lam_cont hθ) hl

/-- `|p - q| ≤ K̲⁻¹ |λ(p) - λ(q)|`. -/
lemma price_lip {θ : ℝ} (hθ : θ ∈ F.Θ) {p q : ℝ} (hp : p ∈ Set.Icc D.pLo D.pHi)
    (hq : q ∈ Set.Icc D.pLo D.pHi) : |p - q| ≤ F.KLo⁻¹ * |F.lam p θ - F.lam q θ| := by
  have h := (F.inClass θ hθ).2.2.2.2.2.2.2.1 _ (lam_mem_J hθ hp) _ (lam_mem_J hθ hq)
  rwa [gam_lam hθ hp, gam_lam hθ hq] at h

variable (σ : Selection D F)

lemma pD_mem {θ : ℝ} (hθ : θ ∈ F.Θ) : σ.pD θ ∈ Set.Icc D.pLo D.pHi := by
  unfold Selection.pD
  exact ⟨le_trans (σ.pu_mem θ hθ).1 (le_max_left _ _), max_le (σ.pu_mem θ hθ).2 (σ.pc_mem θ hθ).2⟩

lemma pc_le_max {θ : ℝ} (hθ : θ ∈ F.Θ) :
    F.lam (σ.pc θ) θ ≤ max (D.x / D.T) (F.lam D.pHi θ) := by
  by_contra h
  push_neg at h
  have h1 := lt_of_le_of_lt (le_max_left _ _) h
  have h2 := lt_of_le_of_lt (le_max_right _ _) h
  have hmin := σ.pc_min θ hθ
  have hpc := σ.pc_mem θ hθ
  rcases le_or_gt (D.x / D.T) (F.lam D.pHi θ) with hc | hc
  · have := hmin (pHi_mem (D := D))
    simp only [Set.mem_setOf_eq] at this
    rw [abs_of_pos (by linarith), abs_of_nonneg (by linarith)] at this
    linarith
  · have hle : F.lam (σ.pc θ) θ ≤ F.lam D.pLo θ := lam_anti hθ pLo_mem hpc hpc.1
    obtain ⟨p, hp, hpe⟩ := lam_surj hθ (l := D.x / D.T) ⟨hc.le, by linarith⟩
    have := hmin hp
    simp only [Set.mem_setOf_eq] at this
    rw [hpe, sub_self, abs_zero, abs_of_pos (by linarith)] at this
    linarith

lemma pD_rate_le {θ : ℝ} (hθ : θ ∈ F.Θ) :
    F.lam (σ.pD θ) θ ≤ max (D.x / D.T) (F.lam D.pHi θ) := by
  refine le_trans ?_ (pc_le_max σ hθ)
  exact lam_anti hθ (σ.pc_mem θ hθ) (pD_mem σ hθ) (le_max_right _ _)

lemma case2_pD_eq {θ : ℝ} (hθ : θ ∈ F.Θ) (h : D.x / D.T < F.lam D.pHi θ) : σ.pD θ = D.pHi := by
  have hpc := σ.pc_mem θ hθ
  have h1 := pc_le_max σ hθ
  rw [max_eq_right h.le] at h1
  have h2 : F.lam D.pHi θ ≤ F.lam (σ.pc θ) θ := lam_anti hθ hpc pHi_mem hpc.2
  have heq : σ.pc θ = D.pHi := lam_inj hθ hpc pHi_mem (le_antisymm h1 h2)
  unfold Selection.pD
  rw [heq]
  exact max_eq_right (σ.pu_mem θ hθ).2

/-- Case 2 price loss: `p̄ - p^D(θ') ≤ K₂ e / K̲`. -/
lemma case2_price {θ θ' e : ℝ} (hθ : θ ∈ F.Θ) (hθ' : θ' ∈ F.Θ) (h : D.x / D.T < F.lam D.pHi θ)
    (he : |θ' - θ| ≤ e) : D.pHi - σ.pD θ' ≤ F.K2 * e / F.KLo := by
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) he
  have hpc := σ.pc_mem θ' hθ'
  have hpar := F.lipschitz_param D.pHi pHi_mem θ hθ θ' hθ'
  have hgap : F.lam (σ.pc θ') θ' - F.lam D.pHi θ' ≤ F.K2 * e := by
    have h1 := pc_le_max σ hθ'
    rcases le_total (D.x / D.T) (F.lam D.pHi θ') with hc | hc
    · rw [max_eq_right hc] at h1
      have : 0 ≤ F.K2 * e := mul_nonneg F.K2_pos.le he0
      linarith
    · rw [max_eq_left hc] at h1
      have h3 : F.lam D.pHi θ - F.lam D.pHi θ' ≤ F.K2 * e := by
        have := le_trans (le_abs_self _) hpar
        have h4 : |θ - θ'| ≤ e := by rw [abs_sub_comm]; exact he
        nlinarith [F.K2_pos]
      linarith
  have hge : F.lam D.pHi θ' ≤ F.lam (σ.pc θ') θ' := lam_anti hθ' hpc pHi_mem hpc.2
  have hl := price_lip hθ' hpc (pHi_mem (D := D))
  rw [abs_of_nonneg (by linarith : 0 ≤ F.lam (σ.pc θ') θ' - F.lam D.pHi θ'),
    abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hpc.2)] at hl
  have hK := F.KLo_pos
  have h5 : D.pHi - σ.pc θ' ≤ F.K2 * e / F.KLo := by
    calc D.pHi - σ.pc θ' ≤ F.KLo⁻¹ * (F.K2 * e) := le_trans hl
            (mul_le_mul_of_nonneg_left hgap (inv_nonneg.mpr hK.le))
      _ = F.K2 * e / F.KLo := by field_simp
  have : σ.pc θ' ≤ σ.pD θ' := le_max_right _ _
  linarith

/-- Case 1 rate overshoot: `λ(p^D(θ'); θ) ≤ x/T + 2 K₂ e`. -/
lemma case1_rate {θ θ' e : ℝ} (hθ : θ ∈ F.Θ) (hθ' : θ' ∈ F.Θ) (h : F.lam D.pHi θ ≤ D.x / D.T)
    (he : |θ' - θ| ≤ e) : F.lam (σ.pD θ') θ ≤ D.x / D.T + 2 * F.K2 * e := by
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) he
  have hK2e : 0 ≤ F.K2 * e := mul_nonneg F.K2_pos.le he0
  have h1 := le_trans (le_abs_self _) (F.lipschitz_param _ (pD_mem σ hθ') θ hθ θ' hθ')
  have h2 := le_trans (le_abs_self _) (F.lipschitz_param _ (pHi_mem (D := D)) θ' hθ' θ hθ)
  have h3 := pD_rate_le σ hθ'
  have he' : |θ - θ'| ≤ e := by rw [abs_sub_comm]; exact he
  have h1' : F.lam (σ.pD θ') θ - F.lam (σ.pD θ') θ' ≤ F.K2 * e :=
    le_trans h1 (mul_le_mul_of_nonneg_left he' F.K2_pos.le)
  have h2' : F.lam D.pHi θ' - F.lam D.pHi θ ≤ F.K2 * e :=
    le_trans h2 (mul_le_mul_of_nonneg_left he F.K2_pos.le)
  rcases le_total (D.x / D.T) (F.lam D.pHi θ') with hc | hc
  · rw [max_eq_right hc] at h3; linarith
  · rw [max_eq_left hc] at h3; linarith

/-- Supergradient (Lagrange multiplier) for the constrained revenue maximisation. -/
lemma sg {θ : ℝ} (hθ : θ ∈ F.Θ) (h : F.lam D.pHi θ ≤ D.x / D.T) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ σ.pD θ ∧ (s = 0 ∨ F.lam (σ.pD θ) θ = D.x / D.T) ∧
      ∀ p ∈ Set.Icc D.pLo D.pHi,
        p * F.lam p θ ≤ σ.pD θ * F.lam (σ.pD θ) θ + s * (F.lam p θ - F.lam (σ.pD θ) θ) := by
  have hpu := σ.pu_mem θ hθ
  have hpc := σ.pc_mem θ hθ
  have hmax := σ.pu_max θ hθ
  rcases le_or_gt (σ.pc θ) (σ.pu θ) with hcu | hcu
  · have hpD : σ.pD θ = σ.pu θ := max_eq_left hcu
    refine ⟨0, le_rfl, ?_, Or.inl rfl, fun p hp => ?_⟩
    · rw [hpD]; linarith [hpu.1, D.pLo_pos]
    · rw [hpD, zero_mul, add_zero]; exact hmax hp
  have hpD : σ.pD θ = σ.pc θ := max_eq_right hcu.le
  set c := D.x / D.T with hcdef
  set f : ℝ → ℝ := fun p => F.lam p θ with hfdef
  -- f(pc) = c
  have hfpc : f (σ.pc θ) = c := by
    have hcl : c ≤ f D.pLo := by
      by_contra hlt
      push_neg at hlt
      have := σ.pc_min θ hθ (pLo_mem (D := D))
      simp only [Set.mem_setOf_eq] at this
      have hle : f (σ.pc θ) ≤ f D.pLo := lam_anti hθ pLo_mem hpc hpc.1
      rw [abs_of_neg (by simp only [hfdef] at hle hlt ⊢; linarith),
        abs_of_neg (by simp only [hfdef] at hlt ⊢; linarith)] at this
      have heq : f (σ.pc θ) = f D.pLo := le_antisymm hle (by linarith)
      have : σ.pc θ = D.pLo := lam_inj hθ hpc pLo_mem heq
      linarith [hpu.1]
    obtain ⟨p0, hp0, hp0e⟩ := lam_surj hθ (l := c) ⟨h, hcl⟩
    have := σ.pc_min θ hθ hp0
    simp only [Set.mem_setOf_eq] at this
    rw [hp0e, sub_self, abs_zero] at this
    have := abs_nonpos_iff.mp this
    simp only [hfdef]; linarith
  set γ := invDemand D f with hγ
  set R : ℝ → ℝ := fun l => l * γ l with hR
  have hconc : ConcaveOn ℝ (Set.Icc (f D.pHi) (f D.pLo)) R := (F.inClass θ hθ).2.2.2.2.1
  have hRf : ∀ p ∈ Set.Icc D.pLo D.pHi, R (f p) = p * f p := by
    intro p hp
    simp only [hR, hγ]
    rw [gam_lam hθ hp]; ring
  -- γ l ≤ pc for l ≥ c in J
  have hγle : ∀ l ∈ Set.Ioc c (f D.pLo), γ l ≤ σ.pc θ ∧ f (γ l) = l ∧ γ l ∈ Set.Icc D.pLo D.pHi := by
    intro l hl
    have hlJ : l ∈ Set.Icc (f D.pHi) (f D.pLo) := ⟨by linarith [hl.1], hl.2⟩
    obtain ⟨q, hq, hqe⟩ := lam_surj hθ hlJ
    have hq' : γ l = q := by
      simp only [hγ]; rw [← hqe]; exact gam_lam hθ hq
    refine ⟨?_, by rw [hq']; exact hqe, by rw [hq']; exact hq⟩
    rw [hq']
    by_contra hgt
    push_neg at hgt
    have : f q ≤ f (σ.pc θ) := lam_anti hθ hpc hq hgt.le
    simp only [hfdef] at hqe this hfpc
    linarith [hl.1]
  set S : Set ℝ := (fun l => (R l - R c) / (l - c)) '' Set.Ioc c (f D.pLo) with hS
  have hRc : R c = σ.pc θ * c := by rw [← hfpc, hRf _ hpc, hfpc]
  have hSbdd : ∀ y ∈ S, y ≤ σ.pc θ := by
    rintro y ⟨l, hl, rfl⟩
    obtain ⟨h1, -, -⟩ := hγle l hl
    have hlc : 0 < l - c := by linarith [hl.1]
    rw [div_le_iff₀ hlc, hRc]
    simp only [hR]
    have : 0 ≤ l := by linarith [hl.1, lam_nonneg hθ (pHi_mem (D := D)), h]
    nlinarith
  have hfu : c < f (σ.pu θ) := by
    have h1 : f (σ.pc θ) ≤ f (σ.pu θ) := lam_anti hθ hpu hpc hcu.le
    have h2 : f (σ.pc θ) ≠ f (σ.pu θ) := fun he => hcu.ne' (lam_inj hθ hpc hpu he)
    rw [← hfpc]; exact lt_of_le_of_ne h1 h2
  have hfuJ : f (σ.pu θ) ∈ Set.Ioc c (f D.pLo) := ⟨hfu, lam_anti hθ pLo_mem hpu hpu.1⟩
  have hSne : S.Nonempty := ⟨_, Set.mem_image_of_mem _ hfuJ⟩
  have hSB : BddAbove S := ⟨σ.pc θ, hSbdd⟩
  refine ⟨sSup S, ?_, ?_, Or.inr (by rw [hpD]; exact hfpc), ?_⟩
  · have hmem : (R (f (σ.pu θ)) - R c) / (f (σ.pu θ) - c) ∈ S := Set.mem_image_of_mem _ hfuJ
    refine le_trans ?_ (le_csSup hSB hmem)
    apply div_nonneg _ (by linarith)
    rw [hRf _ hpu, ← hfpc, hRf _ hpc]
    have := hmax hpc
    simp only [Set.mem_setOf_eq] at this
    linarith
  · rw [hpD]; exact csSup_le hSne hSbdd
  · intro p hp
    rw [hpD]
    show p * f p ≤ σ.pc θ * f (σ.pc θ) + sSup S * (f p - f (σ.pc θ))
    rw [← hRf _ hp, hfpc, ← hRc]
    have hlJ := lam_mem_J hθ hp
    rcases lt_trichotomy (f p) c with hlt | heq | hgt
    · -- left of c: concavity
      have hcJ : c ∈ Set.Icc (f D.pHi) (f D.pLo) := by rw [← hfpc]; exact lam_mem_J hθ hpc
      have key : sSup S ≤ (R c - R (f p)) / (c - f p) := by
        apply csSup_le hSne
        rintro y ⟨l, hl, rfl⟩
        have hlJ' : l ∈ Set.Icc (f D.pHi) (f D.pLo) := ⟨by linarith [hl.1, hcJ.1], hl.2⟩
        exact hconc.slope_anti_adjacent hlJ hlJ' hlt hl.1
      have hpos : 0 < c - f p := by linarith
      rw [le_div_iff₀ hpos] at key
      nlinarith
    · rw [heq]; simp
    · have hmem : (R (f p) - R c) / (f p - c) ∈ S := Set.mem_image_of_mem _ ⟨hgt, hlJ.2⟩
      have := le_csSup hSB hmem
      have hpos : 0 < f p - c := by linarith
      rw [div_le_iff₀ hpos] at this
      linarith

/-- Case 1 revenue-rate loss: `r(p^D(θ)) ≤ r(p^D(θ')) + 3 p̄ K₂ e` (rates under the true `θ`). -/
lemma case1_rev {θ θ' e : ℝ} (hθ : θ ∈ F.Θ) (hθ' : θ' ∈ F.Θ) (h : F.lam D.pHi θ ≤ D.x / D.T)
    (he : |θ' - θ| ≤ e) :
    σ.pD θ * F.lam (σ.pD θ) θ ≤ σ.pD θ' * F.lam (σ.pD θ') θ + 3 * D.pHi * F.K2 * e := by
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) he
  have hK2e : 0 ≤ F.K2 * e := mul_nonneg F.K2_pos.le he0
  have he' : |θ - θ'| ≤ e := by rw [abs_sub_comm]; exact he
  have hq := pD_mem σ hθ
  have hq' := pD_mem σ hθ'
  have hpHi0 : 0 < D.pHi := lt_trans D.pLo_pos D.pLo_lt_pHi
  have hfq : F.lam (σ.pD θ) θ ≤ D.x / D.T := by
    have := pD_rate_le σ hθ; rwa [max_eq_left h] at this
  rcases le_or_gt (F.lam D.pHi θ') (D.x / D.T) with h' | h'
  · obtain ⟨s, hs0, hsq, hsor, hsg⟩ := sg σ hθ' h'
    have hsp : s ≤ D.pHi := le_trans hsq hq'.2
    have k1 := hsg _ hq
    -- parameter perturbations
    have p1 : |F.lam (σ.pD θ) θ - F.lam (σ.pD θ) θ'| ≤ F.K2 * e :=
      le_trans (F.lipschitz_param _ hq θ hθ θ' hθ') (mul_le_mul_of_nonneg_left he' F.K2_pos.le)
    have p2 : |F.lam (σ.pD θ') θ - F.lam (σ.pD θ') θ'| ≤ F.K2 * e :=
      le_trans (F.lipschitz_param _ hq' θ hθ θ' hθ') (mul_le_mul_of_nonneg_left he' F.K2_pos.le)
    have a1 := abs_le.mp p1
    have a2 := abs_le.mp p2
    have hmul1 : σ.pD θ * F.lam (σ.pD θ) θ ≤ σ.pD θ * F.lam (σ.pD θ) θ' + D.pHi * (F.K2 * e) := by
      have : σ.pD θ * (F.lam (σ.pD θ) θ - F.lam (σ.pD θ) θ') ≤ D.pHi * (F.K2 * e) :=
        le_trans (mul_le_mul_of_nonneg_left a1.2 (by linarith [hq.1, D.pLo_pos]))
          (mul_le_mul_of_nonneg_right hq.2 hK2e)
      nlinarith
    have hmul2 : σ.pD θ' * F.lam (σ.pD θ') θ' ≤ σ.pD θ' * F.lam (σ.pD θ') θ + D.pHi * (F.K2 * e) := by
      have : σ.pD θ' * (F.lam (σ.pD θ') θ' - F.lam (σ.pD θ') θ) ≤ D.pHi * (F.K2 * e) :=
        le_trans (mul_le_mul_of_nonneg_left (by linarith [a2.1]) (by linarith [hq'.1, D.pLo_pos]))
          (mul_le_mul_of_nonneg_right hq'.2 hK2e)
      nlinarith
    have hlag : s * (F.lam (σ.pD θ) θ' - F.lam (σ.pD θ') θ') ≤ D.pHi * (F.K2 * e) := by
      rcases hsor with hs | hs
      · rw [hs, zero_mul]; exact mul_nonneg hpHi0.le hK2e
      · rw [hs]
        have : F.lam (σ.pD θ) θ' - D.x / D.T ≤ F.K2 * e := by linarith [a1.1]
        calc s * (F.lam (σ.pD θ) θ' - D.x / D.T) ≤ s * (F.K2 * e) :=
              mul_le_mul_of_nonneg_left this hs0
          _ ≤ D.pHi * (F.K2 * e) := mul_le_mul_of_nonneg_right hsp hK2e
    nlinarith
  · have hpD' : σ.pD θ' = D.pHi := case2_pD_eq σ hθ' h'
    rw [hpD']
    have p3 := le_trans (le_abs_self _) (F.lipschitz_param _ (pHi_mem (D := D)) θ' hθ' θ hθ)
    have p3' : F.lam D.pHi θ' - F.lam D.pHi θ ≤ F.K2 * e :=
      le_trans p3 (mul_le_mul_of_nonneg_left he F.K2_pos.le)
    have hf0 : 0 ≤ F.lam (σ.pD θ) θ := lam_nonneg hθ hq
    have h1 : σ.pD θ * F.lam (σ.pD θ) θ ≤ D.pHi * F.lam (σ.pD θ) θ :=
      mul_le_mul_of_nonneg_right hq.2 hf0
    have h2 : D.pHi * (F.lam (σ.pD θ) θ - F.lam D.pHi θ) ≤ D.pHi * (F.K2 * e) :=
      mul_le_mul_of_nonneg_left (by linarith) hpHi0.le
    have h3 : 0 ≤ D.pHi * F.K2 * e := mul_nonneg (mul_nonneg hpHi0.le F.K2_pos.le) he0
    nlinarith

end BZ635

open MeasureTheory BesbesZeevi.SingleParam

namespace BZ635

/-- `min(a, C) = a - max(a - C, 0)`. -/
lemma min_eq_sub_max (a C : ℝ) : min a C = a - max (a - C) 0 := by
  rcases le_total a C with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

/-- Revenue with capped sales loses at most `p̄ · overflow`. -/
lemma cap_lower (p x : ℕ → ℝ) (C Pb : ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∀ i, p i ≤ Pb)
    (hx : ∀ i, x i ≤ x (i + 1)) (ℓ : ℕ) :
    ∑ i ∈ Finset.Icc 1 ℓ, p i * (x i - x (i - 1))
        - Pb * (max (x ℓ - C) 0 - max (x 0 - C) 0)
      ≤ ∑ i ∈ Finset.Icc 1 ℓ, p i * (min (x i) C - min (x (i - 1)) C) := by
  induction ℓ with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [min_eq_sub_max (x (k + 1)) C, min_eq_sub_max (x k) C]
    have hb : 0 ≤ max (x (k + 1) - C) 0 - max (x k - C) 0 := by
      have := hx k
      have : max (x k - C) 0 ≤ max (x (k + 1) - C) 0 := max_le_max (by linarith) le_rfl
      linarith
    have hpb : p (k + 1) * (max (x (k + 1) - C) 0 - max (x k - C) 0)
        ≤ Pb * (max (x (k + 1) - C) 0 - max (x k - C) 0) := mul_le_mul_of_nonneg_right (hp _) hb
    nlinarith

/-- Capped revenue is at most `p̄ · (min(x_ℓ, C) - min(x_0, C))`. -/
lemma cap_upper (p x : ℕ → ℝ) (C Pb : ℝ) (hp : ∀ i, p i ≤ Pb)
    (hx : ∀ i, x i ≤ x (i + 1)) (ℓ : ℕ) :
    ∑ i ∈ Finset.Icc 1 ℓ, p i * (min (x i) C - min (x (i - 1)) C)
      ≤ Pb * (min (x ℓ) C - min (x 0) C) := by
  induction ℓ with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    have hb : 0 ≤ min (x (k + 1)) C - min (x k) C := by
      have : min (x k) C ≤ min (x (k + 1)) C := min_le_min (hx k) le_rfl
      linarith
    have := mul_le_mul_of_nonneg_right (hp (k + 1)) hb
    nlinarith

lemma cap_nonneg (p x : ℕ → ℝ) (C : ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hx : ∀ i, x i ≤ x (i + 1)) (ℓ : ℕ) :
    0 ≤ ∑ i ∈ Finset.Icc 1 ℓ, p i * (min (x i) C - min (x (i - 1)) C) := by
  apply Finset.sum_nonneg
  intro i hi
  have h1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have : x (i - 1) ≤ x i := by
    have := hx (i - 1); rwa [Nat.sub_add_cancel h1] at this
  exact mul_nonneg (hp0 i) (by linarith [min_le_min this (le_refl C)])

variable {D : Market} {F : Family D}

/-- Every feasible path earns at most `p̄ · y` (bounded above). -/
lemma path_le_pHi {f : ℝ → ℝ} {y : ℝ} (hf0 : ∀ p ∈ Set.Icc D.pLo D.pHi, 0 ≤ f p)
    (hoff : f D.pOff = 0) {q : ℝ → ℝ} (hq : Feasible D f y q) :
    ∫ s in Set.Icc (0 : ℝ) D.T, q s * f (q s) ≤ D.pHi * y := by
  obtain ⟨-, hrange, hint1, hint2, hle⟩ := hq
  have hpHi0 : 0 ≤ D.pHi := le_of_lt (lt_trans D.pLo_pos D.pLo_lt_pHi)
  calc ∫ s in Set.Icc (0 : ℝ) D.T, q s * f (q s)
      ≤ ∫ s in Set.Icc (0 : ℝ) D.T, D.pHi * f (q s) := by
        apply setIntegral_mono_on hint2 (hint1.const_mul D.pHi) measurableSet_Icc
        intro s hs
        rcases hrange s hs with h | h
        · exact mul_le_mul_of_nonneg_right h.2 (hf0 _ h)
        · rw [h, hoff]; simp
    _ = D.pHi * ∫ s in Set.Icc (0 : ℝ) D.T, f (q s) := integral_const_mul _ _
    _ ≤ D.pHi * y := mul_le_mul_of_nonneg_left hle hpHi0

/-- Upper bound through a Lagrange line `r(p) ≤ A + s λ(p)` with `A ≥ 0`, `s ≥ 0`. -/
lemma path_le_line {f : ℝ → ℝ} {y A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hline : ∀ p ∈ Set.Icc D.pLo D.pHi, p * f p ≤ A + s * f p)
    (hoff : f D.pOff = 0) {q : ℝ → ℝ} (hq : Feasible D f y q) :
    ∫ s in Set.Icc (0 : ℝ) D.T, q s * f (q s) ≤ D.T * A + s * y := by
  obtain ⟨-, hrange, hint1, hint2, hle⟩ := hq
  have hfin : IntegrableOn (fun _ : ℝ => A) (Set.Icc (0 : ℝ) D.T) := integrableOn_const measure_Icc_lt_top.ne
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
        rw [measureReal_def, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal D.T_pos.le, smul_eq_mul]
    _ ≤ D.T * A + s * y := by linarith [mul_le_mul_of_nonneg_left hle hs]

end BZ635

open MeasureTheory BesbesZeevi.SingleParam

namespace BZ635

variable {D : Market} {F : Family D}

lemma lam_off {θ : ℝ} (hθ : θ ∈ F.Θ) : F.lam D.pOff θ = 0 := (F.inClass θ hθ).1

lemma detS_upper_pHi {θ : ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) :
    detValueScaled D (fun p => F.lam p θ) n ≤ (n : ℝ) * (D.pHi * D.x) := by
  have hpHi0 : 0 ≤ D.pHi := le_of_lt (lt_trans D.pLo_pos D.pLo_lt_pHi)
  unfold detValueScaled detValue
  apply Real.sSup_le _ (by have := D.x_pos.le; positivity)
  rintro v ⟨q, hq, rfl⟩
  have := path_le_pHi (D := D) (f := fun p => (n : ℝ) * F.lam p θ) (y := (n : ℝ) * D.x)
    (fun p hp => mul_nonneg (Nat.cast_nonneg n) (lam_nonneg hθ hp))
    (by simp only [lam_off hθ, mul_zero]) hq
  calc _ ≤ D.pHi * ((n : ℝ) * D.x) := this
    _ = (n : ℝ) * (D.pHi * D.x) := by ring

variable (σ : Selection D F)

lemma detS_upper_case1 {θ : ℝ} (hθ : θ ∈ F.Θ) (h : F.lam D.pHi θ ≤ D.x / D.T) (n : ℕ) :
    detValueScaled D (fun p => F.lam p θ) n
      ≤ (n : ℝ) * (D.T * (σ.pD θ * F.lam (σ.pD θ) θ)) := by
  obtain ⟨s0, hs0, hsq, hsor, hsg⟩ := sg σ hθ h
  have hq := pD_mem σ hθ
  have hf0 : 0 ≤ F.lam (σ.pD θ) θ := lam_nonneg hθ hq
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set A := (n : ℝ) * (σ.pD θ * F.lam (σ.pD θ) θ - s0 * F.lam (σ.pD θ) θ) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]; apply mul_nonneg hn
    have := mul_le_mul_of_nonneg_right hsq hf0
    linarith
  have hfin : D.T * A + s0 * ((n : ℝ) * D.x) = (n : ℝ) * (D.T * (σ.pD θ * F.lam (σ.pD θ) θ)) := by
    rw [hA]
    rcases hsor with hs | hs
    · rw [hs]; ring
    · have : D.T * F.lam (σ.pD θ) θ = D.x := by rw [hs]; field_simp [D.T_pos.ne']
      linear_combination (-(s0 * (n : ℝ))) * this
  unfold detValueScaled detValue
  apply Real.sSup_le _ (by
    have := D.T_pos.le
    have := mul_nonneg (le_trans D.pLo_pos.le hq.1) hf0
    positivity)
  rintro v ⟨q, hq', rfl⟩
  rw [← hfin]
  apply path_le_line (D := D) (f := fun p => (n : ℝ) * F.lam p θ) hA0 hs0 _
    (by simp only [lam_off hθ, mul_zero]) hq'
  intro p hp
  have := hsg p hp
  have := mul_le_mul_of_nonneg_left this hn
  simp only [hA]
  nlinarith

lemma int_step (τ A : ℝ) (hτ0 : 0 ≤ τ) (hτT : τ ≤ D.T) :
    IntegrableOn (fun s : ℝ => if s ≤ τ then A else 0) (Set.Icc (0 : ℝ) D.T) ∧
    ∫ s in Set.Icc (0 : ℝ) D.T, (if s ≤ τ then A else 0) = A * τ := by
  have he : (fun s : ℝ => if s ≤ τ then A else 0) = (Set.Iic τ).indicator (fun _ => A) := by
    funext s; simp [Set.indicator, Set.mem_Iic]
  rw [he]
  refine ⟨(integrableOn_const (C := A) measure_Icc_lt_top.ne).indicator measurableSet_Iic, ?_⟩
  rw [setIntegral_indicator measurableSet_Iic, setIntegral_const]
  have : Set.Icc (0 : ℝ) D.T ∩ Set.Iic τ = Set.Icc 0 τ := by
    ext s; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 hτT⟩, h3⟩
  rw [this, measureReal_def, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hτ0, smul_eq_mul]
  ring

lemma detS_lower {θ : ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) :
    (n : ℝ) * (F.m * min D.T (D.x / F.M)) ≤ detValueScaled D (fun p => F.lam p θ) n := by
  obtain ⟨pm, hpm, hm⟩ := (F.inClass θ hθ).2.2.2.2.2.2.2.2
  have hpm0 : 0 < pm := lt_of_lt_of_le D.pLo_pos hpm.1
  have hfm : 0 < F.lam pm θ := by
    by_contra hc; push_neg at hc
    have : pm * F.lam pm θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpm0.le hc
    linarith [F.m_pos]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set τ := min D.T (D.x / F.lam pm θ) with hτ
  have hτ0 : 0 ≤ τ := le_min D.T_pos.le (div_pos D.x_pos hfm).le
  have hτT : τ ≤ D.T := min_le_left _ _
  set q : ℝ → ℝ := fun s => if s ≤ τ then pm else D.pOff with hqdef
  have e1 : (fun s => (n : ℝ) * F.lam (q s) θ) = fun s => if s ≤ τ then (n : ℝ) * F.lam pm θ else 0 := by
    funext s; by_cases hs : s ≤ τ <;> simp [hqdef, hs, lam_off hθ]
  have e2 : (fun s => q s * ((n : ℝ) * F.lam (q s) θ))
      = fun s => if s ≤ τ then pm * ((n : ℝ) * F.lam pm θ) else 0 := by
    funext s; by_cases hs : s ≤ τ <;> simp [hqdef, hs, lam_off hθ]
  obtain ⟨i1, v1⟩ := int_step (D := D) τ ((n : ℝ) * F.lam pm θ) hτ0 hτT
  obtain ⟨i2, v2⟩ := int_step (D := D) τ (pm * ((n : ℝ) * F.lam pm θ)) hτ0 hτT
  have hfeas : Feasible D (fun p => (n : ℝ) * F.lam p θ) ((n : ℝ) * D.x) q := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact Measurable.ite measurableSet_Iic measurable_const measurable_const
    · intro s _
      by_cases hs : s ≤ τ
      · left; simp only [hqdef, hs, if_true]; exact hpm
      · right; simp only [hqdef, hs, if_false]
    · show IntegrableOn (fun s => (n : ℝ) * F.lam (q s) θ) (Set.Icc (0 : ℝ) D.T)
      rw [e1]; exact i1
    · show IntegrableOn (fun s => q s * ((n : ℝ) * F.lam (q s) θ)) (Set.Icc (0 : ℝ) D.T)
      rw [e2]; exact i2
    · show ∫ s in Set.Icc (0 : ℝ) D.T, (n : ℝ) * F.lam (q s) θ ≤ (n : ℝ) * D.x
      rw [e1, v1]
      have : F.lam pm θ * τ ≤ D.x := by
        have := min_le_right D.T (D.x / F.lam pm θ)
        rw [← hτ] at this
        calc F.lam pm θ * τ ≤ F.lam pm θ * (D.x / F.lam pm θ) :=
              mul_le_mul_of_nonneg_left this hfm.le
          _ = D.x := by field_simp
      nlinarith
  have hbdd : BddAbove {v : ℝ | ∃ p : ℝ → ℝ, Feasible D (fun p => (n : ℝ) * F.lam p θ) ((n : ℝ) * D.x) p ∧
      v = ∫ s in Set.Icc (0 : ℝ) D.T, p s * ((fun p => (n : ℝ) * F.lam p θ) (p s))} := by
    refine ⟨D.pHi * ((n : ℝ) * D.x), ?_⟩
    rintro v ⟨q', hq', rfl⟩
    exact path_le_pHi (D := D) (f := fun p => (n : ℝ) * F.lam p θ)
      (fun p hp => mul_nonneg hn (lam_nonneg hθ hp)) (by simp only [lam_off hθ, mul_zero]) hq'
  have hval : (n : ℝ) * (pm * F.lam pm θ * τ)
      ≤ detValueScaled D (fun p => F.lam p θ) n := by
    unfold detValueScaled detValue
    apply le_csSup hbdd
    refine ⟨q, hfeas, ?_⟩
    show _ = ∫ s in Set.Icc (0 : ℝ) D.T, q s * ((n : ℝ) * F.lam (q s) θ)
    rw [e2, v2]; ring
  refine le_trans ?_ hval
  apply mul_le_mul_of_nonneg_left _ hn
  have hτ2 : min D.T (D.x / F.M) ≤ τ := by
    apply min_le_min le_rfl
    apply div_le_div_of_nonneg_left D.x_pos.le hfm (lam_le_M hθ hpm)
  have hmin0 : 0 ≤ min D.T (D.x / F.M) := le_min D.T_pos.le (div_pos D.x_pos F.M_pos).le
  calc F.m * min D.T (D.x / F.M) ≤ (pm * F.lam pm θ) * min D.T (D.x / F.M) :=
        mul_le_mul_of_nonneg_right hm hmin0
    _ ≤ (pm * F.lam pm θ) * τ := mul_le_mul_of_nonneg_left hτ2 (by positivity)
    _ = pm * F.lam pm θ * τ := rfl

end BZ635

open BesbesZeevi.SingleParam

namespace BZ635

lemma aCoef_eq (m : ℕ) (hm : 1 ≤ m) :
    aCoef m = (2 : ℝ) ^ (m - 1) / (2 * (2 : ℝ) ^ (m - 1) - 1) := by
  unfold aCoef
  congr 2
  rw [← pow_succ']; congr 1; omega

lemma aCoef_pos (m : ℕ) (hm : 1 ≤ m) : 0 < aCoef m := by
  rw [aCoef_eq m hm]
  have : (1 : ℝ) ≤ 2 ^ (m - 1) := one_le_pow₀ (by norm_num)
  apply div_pos (by positivity); linarith

lemma aCoef_one : aCoef 1 = 1 := by unfold aCoef; norm_num

lemma aCoef_anti {m m' : ℕ} (hm : 1 ≤ m) (hmm : m ≤ m') : aCoef m' ≤ aCoef m := by
  rw [aCoef_eq m hm, aCoef_eq m' (le_trans hm hmm)]
  have hq : (1 : ℝ) ≤ 2 ^ (m - 1) := one_le_pow₀ (by norm_num)
  have hqq : (2 : ℝ) ^ (m - 1) ≤ 2 ^ (m' - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma aCoef_ge_half (m : ℕ) (hm : 1 ≤ m) : 1 / 2 ≤ aCoef m := by
  rw [aCoef_eq m hm]
  have hq : (1 : ℝ) ≤ 2 ^ (m - 1) := one_le_pow₀ (by norm_num)
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  linarith

lemma aCoef_le_one (m : ℕ) (hm : 1 ≤ m) : aCoef m ≤ 1 := by
  have := aCoef_anti (le_refl 1) hm; rwa [aCoef_one] at this

/-- `2 / a_i = 2 + 1 / a_{i-1}` for `i ≥ 2`. -/
lemma aCoef_rec (i : ℕ) (hi : 2 ≤ i) : 2 / aCoef i = 2 + 1 / aCoef (i - 1) := by
  rw [aCoef_eq i (by omega), aCoef_eq (i - 1) (by omega)]
  have hq : (1 : ℝ) ≤ 2 ^ (i - 1 - 1) := one_le_pow₀ (by norm_num)
  have h2 : (2 : ℝ) ^ (i - 1) = 2 * 2 ^ (i - 1 - 1) := by rw [← pow_succ']; congr 1; omega
  rw [h2]
  have hq0 : (0 : ℝ) < 2 ^ (i - 1 - 1) := by positivity
  field_simp
  ring

lemma numStages_pos (n : ℕ) (hn : 3 ≤ n) : 1 ≤ numStages n := by
  unfold numStages
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have : 0 < Real.logb 2 (Real.log n) := Real.logb_pos (by norm_num) hlog
  exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr this))

/-- Exponent `e_m = a_ℓ / a_m - 1`. -/
lemma expo_bounds (ℓ m : ℕ) (hm : 1 ≤ m) (hmℓ : m ≤ ℓ) :
    aCoef ℓ - 1 ≤ aCoef ℓ / aCoef m - 1 ∧ aCoef ℓ / aCoef m - 1 ≤ 0 := by
  have ha := aCoef_pos m hm
  have hl := aCoef_pos ℓ (le_trans hm hmℓ)
  have h1 := aCoef_le_one m hm
  have h2 := aCoef_anti hm hmℓ
  constructor
  · have : aCoef ℓ ≤ aCoef ℓ / aCoef m := by
      rw [le_div_iff₀ ha]; nlinarith
    linarith
  · have : aCoef ℓ / aCoef m ≤ 1 := by rw [div_le_one ha]; exact h2
    linarith

lemma sum_bounds (n : ℕ) (hn : 3 ≤ n) :
    1 ≤ ∑ m ∈ Finset.Icc 1 (numStages n), (n : ℝ) ^ (aCoef (numStages n) / aCoef m - 1) ∧
    ∑ m ∈ Finset.Icc 1 (numStages n), (n : ℝ) ^ (aCoef (numStages n) / aCoef m - 1)
      ≤ (numStages n : ℝ) := by
  set ℓ := numStages n with hℓ
  have hℓ1 : 1 ≤ ℓ := numStages_pos n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  constructor
  · have hmem : ℓ ∈ Finset.Icc 1 ℓ := Finset.mem_Icc.mpr ⟨hℓ1, le_rfl⟩
    have := Finset.single_le_sum (f := fun m => (n : ℝ) ^ (aCoef ℓ / aCoef m - 1))
      (fun m _ => Real.rpow_nonneg (by linarith) _) hmem
    rwa [div_self (aCoef_pos ℓ hℓ1).ne', sub_self, Real.rpow_zero] at this
  · have := Finset.sum_le_card_nsmul (Finset.Icc 1 ℓ) (fun m => (n : ℝ) ^ (aCoef ℓ / aCoef m - 1)) 1
      (fun m hm => by
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (expo_bounds ℓ m h1 h2).2)
    simpa using this

lemma beta_bounds (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 3 ≤ n) :
    0 < betaNorm T n ∧ betaNorm T n ≤ T ∧ T / (numStages n : ℝ) ≤ betaNorm T n := by
  obtain ⟨h1, h2⟩ := sum_bounds n hn
  have hpos : 0 < ∑ m ∈ Finset.Icc 1 (numStages n), (n : ℝ) ^ (aCoef (numStages n) / aCoef m - 1) :=
    lt_of_lt_of_le one_pos h1
  unfold betaNorm
  refine ⟨div_pos hT hpos, div_le_self hT.le h1, div_le_div_of_nonneg_left hT.le hpos h2⟩

lemma stage_pos (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 3 ≤ n) (m : ℕ) : 0 < stageLength T n m := by
  unfold stageLength
  exact mul_pos (beta_bounds T hT n hn).1 (Real.rpow_pos_of_pos (by norm_cast; omega) _)

lemma stage_sum (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 3 ≤ n) :
    ∑ m ∈ Finset.Icc 1 (numStages n), stageLength T n m = T := by
  unfold stageLength
  rw [← Finset.mul_sum]
  unfold betaNorm
  have := (sum_bounds n hn).1
  field_simp

lemma stage_one_le (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 3 ≤ n) :
    stageLength T n 1 ≤ T * (n : ℝ) ^ (aCoef (numStages n) - 1) := by
  unfold stageLength
  rw [aCoef_one, div_one]
  exact mul_le_mul_of_nonneg_right (beta_bounds T hT n hn).2.1 (Real.rpow_nonneg (by positivity) _)

lemma stage_ge (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 3 ≤ n) (m : ℕ) (hm : 1 ≤ m)
    (hmℓ : m ≤ numStages n) :
    T / (numStages n : ℝ) * (n : ℝ) ^ (aCoef (numStages n) - 1) ≤ stageLength T n m := by
  unfold stageLength
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  apply mul_le_mul (beta_bounds T hT n hn).2.2
    (Real.rpow_le_rpow_of_exponent_le hn1 (expo_bounds _ m hm hmℓ).1)
    (Real.rpow_nonneg (by linarith) _) (beta_bounds T hT n hn).1.le

/-- `Δ_i² = β n^{2(a_ℓ-1)} (n Δ_{i-1})` for `2 ≤ i`. -/
lemma stage_sq (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 3 ≤ n) (i : ℕ) (hi : 2 ≤ i) :
    stageLength T n i ^ 2
      = betaNorm T n * (n : ℝ) ^ (2 * (aCoef (numStages n) - 1)) * ((n : ℝ) * stageLength T n (i - 1)) := by
  unfold stageLength
  have hn0 : (0 : ℝ) < n := by norm_cast; omega
  set a := aCoef (numStages n)
  have hrec := aCoef_rec i hi
  have hai := aCoef_pos i (by omega)
  have hai1 := aCoef_pos (i - 1) (by omega)
  have hexp : 2 * (a / aCoef i - 1) = 2 * (a - 1) + (1 + (a / aCoef (i - 1) - 1)) := by
    have : a / aCoef i = a * (1 + 1 / (2 * aCoef (i - 1))) := by
      have h2 : 1 / aCoef i = 1 + 1 / (2 * aCoef (i - 1)) := by
        have := hrec; field_simp at this ⊢; linarith
      rw [div_eq_mul_one_div, h2]
    rw [this]; field_simp; ring
  have e1 : ((n : ℝ) ^ (a / aCoef i - 1)) ^ 2 = (n : ℝ) ^ (2 * (a / aCoef i - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
  have e2 : (n : ℝ) ^ (2 * (a / aCoef i - 1))
      = (n : ℝ) ^ (2 * (a - 1)) * ((n : ℝ) * (n : ℝ) ^ (a / aCoef (i - 1) - 1)) := by
    rw [hexp, Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one]
  rw [mul_pow, e1, e2]
  ring

lemma stage_ratio (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 3 ≤ n) (i : ℕ) (hi : 2 ≤ i) :
    stageLength T n i
      ≤ Real.sqrt T * (n : ℝ) ^ (aCoef (numStages n) - 1) * Real.sqrt ((n : ℝ) * stageLength T n (i - 1)) := by
  have hn0 : (0 : ℝ) < n := by norm_cast; omega
  have hsq := stage_sq T hT n hn i hi
  have hpos := stage_pos T hT n hn i
  obtain ⟨hb0, hbT, -⟩ := beta_bounds T hT n hn
  set a := aCoef (numStages n)
  have h1 : stageLength T n i = Real.sqrt (stageLength T n i ^ 2) := (Real.sqrt_sq hpos.le).symm
  rw [h1, hsq, Real.sqrt_mul (by positivity), Real.sqrt_mul hb0.le]
  have h2 : Real.sqrt ((n : ℝ) ^ (2 * (a - 1))) = (n : ℝ) ^ (a - 1) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← Real.rpow_add hn0]
    ring_nf
  rw [h2]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hbT) (by positivity)

end BZ635

open MeasureTheory BesbesZeevi.SingleParam

namespace BZ635

/-- The deviation envelope from `path_dev`. -/
noncomputable def Edev (u L : ℝ) : ℝ := 2 + 2 * Real.sqrt (u * (L + 2)) + 4 * u

lemma Edev_mono (u : ℝ) (hu : 0 ≤ u) {L L' : ℝ} (h : L ≤ L') : Edev u L ≤ Edev u L' := by
  unfold Edev
  have : Real.sqrt (u * (L + 2)) ≤ Real.sqrt (u * (L' + 2)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) hu)
  linarith

lemma Edev_nonneg (u L : ℝ) (hu : 0 ≤ u) : 0 ≤ Edev u L := by
  unfold Edev; have := Real.sqrt_nonneg (u * (L + 2)); linarith

variable {D : Market} {F : Family D} (σ : Selection D F)

lemma alg_succ (n : ℕ) (Δ : ℕ → ℝ) (θ : ℝ) (Nω : ℝ → ℕ) (k : ℕ) :
    algState D F σ n Δ θ Nω (k + 1) =
      (σ.pD (F.g (algState D F σ n Δ θ Nω k).1
        (((Nω ((algState D F σ n Δ θ Nω k).2
            + (n : ℝ) * F.lam (algState D F σ n Δ θ Nω k).1 θ * Δ (k + 1)) : ℝ)
          - (Nω (algState D F σ n Δ θ Nω k).2 : ℝ)) / ((n : ℝ) * Δ (k + 1)))),
        (algState D F σ n Δ θ Nω k).2 + (n : ℝ) * F.lam (algState D F σ n Δ θ Nω k).1 θ * Δ (k + 1)) :=
  rfl

lemma alg_inv {θ : ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 0 < n) (Δ : ℕ → ℝ) (hΔ : ∀ m, 0 < Δ m)
    (Nω : ℝ → ℕ) (hmono : Monotone Nω) :
    ∀ k, (algState D F σ n Δ θ Nω k).1 ∈ Set.Icc D.pLo D.pHi ∧ 0 ≤ (algState D F σ n Δ θ Nω k).2 := by
  intro k
  induction k with
  | zero => exact ⟨F.p1_mem, le_rfl⟩
  | succ k ih =>
    rw [alg_succ]
    obtain ⟨hp, hΛ⟩ := ih
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hL : 0 ≤ (n : ℝ) * F.lam (algState D F σ n Δ θ Nω k).1 θ * Δ (k + 1) :=
      mul_nonneg (mul_nonneg hn'.le (lam_nonneg hθ hp)) (hΔ _).le
    have hd : 0 ≤ (((Nω ((algState D F σ n Δ θ Nω k).2
            + (n : ℝ) * F.lam (algState D F σ n Δ θ Nω k).1 θ * Δ (k + 1)) : ℝ)
          - (Nω (algState D F σ n Δ θ Nω k).2 : ℝ)) / ((n : ℝ) * Δ (k + 1))) := by
      apply div_nonneg _ (mul_pos hn' (hΔ _)).le
      have : Nω (algState D F σ n Δ θ Nω k).2 ≤ Nω ((algState D F σ n Δ θ Nω k).2
            + (n : ℝ) * F.lam (algState D F σ n Δ θ Nω k).1 θ * Δ (k + 1)) := hmono (by linarith)
      have : (Nω (algState D F σ n Δ θ Nω k).2 : ℝ) ≤ Nω ((algState D F σ n Δ θ Nω k).2
            + (n : ℝ) * F.lam (algState D F σ n Δ θ Nω k).1 θ * Δ (k + 1)) := by exact_mod_cast this
      linarith
    exact ⟨pD_mem σ (F.g_mem _ hp _ hd), by linarith⟩

lemma price_mem {θ : ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 0 < n) (Δ : ℕ → ℝ) (hΔ : ∀ m, 0 < Δ m)
    (Nω : ℝ → ℕ) (hmono : Monotone Nω) (i : ℕ) :
    stagePrice D F σ n Δ θ Nω i ∈ Set.Icc D.pLo D.pHi :=
  (alg_inv σ hθ n hn Δ hΔ Nω hmono (i - 1)).1

lemma cum_succ (n : ℕ) (Δ : ℕ → ℝ) (θ : ℝ) (Nω : ℝ → ℕ) (k : ℕ) :
    cumIntensity D F σ n Δ θ Nω (k + 1) = cumIntensity D F σ n Δ θ Nω k
      + (n : ℝ) * F.lam (stagePrice D F σ n Δ θ Nω (k + 1)) θ * Δ (k + 1) := by
  unfold cumIntensity stagePrice
  rw [alg_succ]
  simp

lemma cum_zero (n : ℕ) (Δ : ℕ → ℝ) (θ : ℝ) (Nω : ℝ → ℕ) :
    cumIntensity D F σ n Δ θ Nω 0 = 0 := rfl

lemma cum_eq_sum (n : ℕ) (Δ : ℕ → ℝ) (θ : ℝ) (Nω : ℝ → ℕ) (k : ℕ) :
    cumIntensity D F σ n Δ θ Nω k
      = ∑ i ∈ Finset.Icc 1 k, (n : ℝ) * F.lam (stagePrice D F σ n Δ θ Nω i) θ * Δ i := by
  induction k with
  | zero => simp [cum_zero]
  | succ k ih => rw [cum_succ, ih, Finset.sum_Icc_succ_top (by omega)]

lemma cum_mono {θ : ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 0 < n) (Δ : ℕ → ℝ) (hΔ : ∀ m, 0 < Δ m)
    (Nω : ℝ → ℕ) (hmono : Monotone Nω) (k : ℕ) :
    cumIntensity D F σ n Δ θ Nω k ≤ cumIntensity D F σ n Δ θ Nω (k + 1) := by
  rw [cum_succ]
  have hp := price_mem σ hθ n hn Δ hΔ Nω hmono (k + 1)
  have : 0 ≤ (n : ℝ) * F.lam (stagePrice D F σ n Δ θ Nω (k + 1)) θ * Δ (k + 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (lam_nonneg hθ hp)) (hΔ _).le
  linarith

lemma price_succ (n : ℕ) (Δ : ℕ → ℝ) (θ : ℝ) (Nω : ℝ → ℕ) (i : ℕ) (hi : 1 ≤ i) :
    stagePrice D F σ n Δ θ Nω (i + 1) =
      σ.pD (F.g (stagePrice D F σ n Δ θ Nω i)
        (((Nω (cumIntensity D F σ n Δ θ Nω i) : ℝ) - (Nω (cumIntensity D F σ n Δ θ Nω (i - 1)) : ℝ))
          / ((n : ℝ) * Δ i))) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  unfold stagePrice cumIntensity
  simp only [Nat.add_sub_cancel]
  rw [alg_succ]

/-- One stage on a good path: demand deviation and estimation error. -/
lemma stage_est {θ : ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 0 < n) (Δ : ℕ → ℝ) (hΔ : ∀ m, 0 < Δ m)
    (Nω : ℝ → ℕ) (hmono : Monotone Nω) (K : ℕ) (u : ℝ) (hu : 0 ≤ u) (hG : GoodPath Nω K u)
    (i : ℕ) (hi : 1 ≤ i) (hK : cumIntensity D F σ n Δ θ Nω i ≤ K) :
    |((Nω (cumIntensity D F σ n Δ θ Nω i) : ℝ) - (Nω (cumIntensity D F σ n Δ θ Nω (i - 1)) : ℝ))
        - (n : ℝ) * F.lam (stagePrice D F σ n Δ θ Nω i) θ * Δ i|
      ≤ Edev u ((n : ℝ) * F.lam (stagePrice D F σ n Δ θ Nω i) θ * Δ i) ∧
    |F.g (stagePrice D F σ n Δ θ Nω i)
        (((Nω (cumIntensity D F σ n Δ θ Nω i) : ℝ) - (Nω (cumIntensity D F σ n Δ θ Nω (i - 1)) : ℝ))
          / ((n : ℝ) * Δ i)) - θ|
      ≤ F.α * Edev u ((n : ℝ) * F.lam (stagePrice D F σ n Δ θ Nω i) θ * Δ i) / ((n : ℝ) * Δ i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set a := cumIntensity D F σ n Δ θ Nω j with ha
  set L := (n : ℝ) * F.lam (stagePrice D F σ n Δ θ Nω (j + 1)) θ * Δ (j + 1) with hL
  have hb : cumIntensity D F σ n Δ θ Nω (j + 1) = a + L := cum_succ σ n Δ θ Nω j
  have ha0 : 0 ≤ a := (alg_inv σ hθ n hn Δ hΔ Nω hmono j).2
  have hp := price_mem σ hθ n hn Δ hΔ Nω hmono (j + 1)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 ≤ L := mul_nonneg (mul_nonneg hn'.le (lam_nonneg hθ hp)) (hΔ _).le
  have hdev := path_dev Nω hmono K u hu hG a (a + L) ha0 (by linarith) (by rw [← hb]; exact hK)
  rw [show a + L - a = L by ring] at hdev
  rw [hb]
  have h1 : |((Nω (a + L) : ℝ) - Nω a) - L| ≤ Edev u L := by
    unfold Edev; exact hdev
  refine ⟨h1, ?_⟩
  set p := stagePrice D F σ n Δ θ Nω (j + 1)
  have hnd : 0 < (n : ℝ) * Δ (j + 1) := mul_pos hn' (hΔ _)
  have hd0 : 0 ≤ ((Nω (a + L) : ℝ) - Nω a) / ((n : ℝ) * Δ (j + 1)) := by
    apply div_nonneg _ hnd.le
    have : (Nω a : ℝ) ≤ Nω (a + L) := by exact_mod_cast hmono (by linarith)
    linarith
  have hg := F.g_lipschitz p hp _ (F.lam p θ) hd0 (lam_nonneg hθ hp)
  rw [F.g_inv p hp θ hθ] at hg
  have hfL : F.lam p θ = L / ((n : ℝ) * Δ (j + 1)) := by
    rw [hL, eq_div_iff hnd.ne']; ring
  rw [hfL, ← sub_div, abs_div, abs_of_pos hnd] at hg
  calc _ ≤ F.α * (|((Nω (a + L) : ℝ) - Nω a) - L| / ((n : ℝ) * Δ (j + 1))) := hg
    _ ≤ F.α * (Edev u L / ((n : ℝ) * Δ (j + 1))) := by
        apply mul_le_mul_of_nonneg_left _ F.α_pos.le
        exact div_le_div_of_nonneg_right h1 hnd.le
    _ = F.α * Edev u L / ((n : ℝ) * Δ (j + 1)) := by ring

end BZ635

open MeasureTheory BesbesZeevi.SingleParam

namespace BZ635

lemma telescope (x : ℕ → ℝ) (ℓ : ℕ) :
    ∑ i ∈ Finset.Icc 1 ℓ, (x i - x (i - 1)) = x ℓ - x 0 := by
  induction ℓ with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; simp

variable {D : Market} {F : Family D}

noncomputable def pr (σ : Selection D F) (n : ℕ) (θ : ℝ) (Nω : ℝ → ℕ) (i : ℕ) : ℝ :=
  stagePrice D F σ n (stageLength D.T n) θ Nω i
noncomputable def cum (σ : Selection D F) (n : ℕ) (θ : ℝ) (Nω : ℝ → ℕ) (i : ℕ) : ℝ :=
  cumIntensity D F σ n (stageLength D.T n) θ Nω i
noncomputable def sal (σ : Selection D F) (n : ℕ) (θ : ℝ) (Nω : ℝ → ℕ) (i : ℕ) : ℝ :=
  (Nω (cum σ n θ Nω i) : ℝ) - (Nω (cum σ n θ Nω (i - 1)) : ℝ)
noncomputable def lst (σ : Selection D F) (n : ℕ) (θ : ℝ) (Nω : ℝ → ℕ) (i : ℕ) : ℝ :=
  (n : ℝ) * F.lam (pr σ n θ Nω i) θ * stageLength D.T n i

variable (F) in
noncomputable def Ei (n : ℕ) (u : ℝ) (i : ℕ) : ℝ := Edev u ((n : ℝ) * F.M * stageLength D.T n i)
variable (F) in
noncomputable def eps (n : ℕ) (u : ℝ) (i : ℕ) : ℝ :=
  F.α * Ei F n u i / ((n : ℝ) * stageLength D.T n i)
variable (F) in
noncomputable def ErrB (n : ℕ) (u : ℝ) : ℝ :=
  2 * D.pHi * F.M * n * stageLength D.T n 1
    + (5 * D.pHi * F.K2 + F.K2 * F.M / F.KLo) * n
        * ∑ i ∈ Finset.Ioc 1 (numStages n), eps F n u (i - 1) * stageLength D.T n i
    + D.pHi * ∑ i ∈ Finset.Icc 1 (numStages n), Ei F n u i
    + D.pHi * (Edev u ((n : ℝ) * F.M * D.T) + 1)

variable (σ : Selection D F)

lemma path_common {θ : ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 3 ≤ n) (Nω : ℝ → ℕ) (hmono : Monotone Nω)
    (h0 : Nω 0 = 0) (K : ℕ) (hK : (n : ℝ) * F.M * D.T ≤ K) (u : ℝ) (hu : 0 ≤ u)
    (hG : GoodPath Nω K u) :
    (∀ i, pr σ n θ Nω i ∈ Set.Icc D.pLo D.pHi) ∧
    (∀ i ∈ Finset.Icc 1 (numStages n), |sal σ n θ Nω i - lst σ n θ Nω i| ≤ Ei F n u i ∧
        0 ≤ lst σ n θ Nω i ∧ lst σ n θ Nω i ≤ (n : ℝ) * F.M * stageLength D.T n i) ∧
    (∀ i ∈ Finset.Ioc 1 (numStages n), ∃ θ' ∈ F.Θ, pr σ n θ Nω i = σ.pD θ' ∧
        |θ' - θ| ≤ eps F n u (i - 1)) ∧
    |(Nω (cum σ n θ Nω (numStages n)) : ℝ) - cum σ n θ Nω (numStages n)|
        ≤ Edev u ((n : ℝ) * F.M * D.T) ∧
    cum σ n θ Nω (numStages n) = ∑ i ∈ Finset.Icc 1 (numStages n), lst σ n θ Nω i ∧
    (∑ i ∈ Finset.Icc 1 (numStages n), pr σ n θ Nω i * sal σ n θ Nω i
        - D.pHi * max ((Nω (cum σ n θ Nω (numStages n)) : ℝ) - (capacity D n : ℝ)) 0
      ≤ revenue D F σ n (numStages n) (stageLength D.T n) θ Nω) ∧
    (∑ i ∈ Finset.Icc 1 (numStages n), sal σ n θ Nω i = (Nω (cum σ n θ Nω (numStages n)) : ℝ)) ∧
    (∀ i, 1 ≤ i → 0 ≤ sal σ n θ Nω i) := by
  set ℓ := numStages n with hℓ
  set Δ := stageLength D.T n with hΔdef
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hΔ : ∀ m, 0 < Δ m := fun m => stage_pos D.T D.T_pos n hn m
  have hpr : ∀ i, pr σ n θ Nω i ∈ Set.Icc D.pLo D.pHi := fun i => price_mem σ hθ n hn0 Δ hΔ Nω hmono i
  have hcmono : Monotone (cum σ n θ Nω) :=
    monotone_nat_of_le_succ (fun k => cum_mono σ hθ n hn0 Δ hΔ Nω hmono k)
  have hlst : ∀ i, 0 ≤ lst σ n θ Nω i ∧ lst σ n θ Nω i ≤ (n : ℝ) * F.M * Δ i := by
    intro i
    have hp := hpr i
    unfold lst
    constructor
    · exact mul_nonneg (mul_nonneg hn'.le (lam_nonneg hθ hp)) (hΔ i).le
    · apply mul_le_mul_of_nonneg_right _ (hΔ i).le
      exact mul_le_mul_of_nonneg_left (lam_le_M hθ hp) hn'.le
  have hcumsum : cum σ n θ Nω ℓ = ∑ i ∈ Finset.Icc 1 ℓ, lst σ n θ Nω i := cum_eq_sum σ n Δ θ Nω ℓ
  have hcumT : cum σ n θ Nω ℓ ≤ (n : ℝ) * F.M * D.T := by
    rw [hcumsum, ← stage_sum D.T D.T_pos n hn, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hlst i).2)
  have hcumK : ∀ i, i ≤ ℓ → cum σ n θ Nω i ≤ K :=
    fun i hi => le_trans (hcmono hi) (le_trans hcumT hK)
  have hc0 : cum σ n θ Nω 0 = 0 := rfl
  have hsal0 : ∀ i, 1 ≤ i → 0 ≤ sal σ n θ Nω i := by
    intro i hi
    unfold sal
    have : (Nω (cum σ n θ Nω (i - 1)) : ℝ) ≤ Nω (cum σ n θ Nω i) := by
      exact_mod_cast hmono (hcmono (Nat.sub_le i 1))
    linarith
  refine ⟨hpr, ?_, ?_, ?_, hcumsum, ?_, ?_, hsal0⟩
  · intro i hi
    obtain ⟨hi1, hiℓ⟩ := Finset.mem_Icc.mp hi
    have hest := (stage_est σ hθ n hn0 Δ hΔ Nω hmono K u hu hG i hi1 (hcumK i hiℓ)).1
    refine ⟨le_trans hest (Edev_mono u hu (hlst i).2), (hlst i).1, (hlst i).2⟩
  · intro i hi
    obtain ⟨hi1, hiℓ⟩ := Finset.mem_Ioc.mp hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : 1 ≤ j := by omega
    have hest := (stage_est σ hθ n hn0 Δ hΔ Nω hmono K u hu hG j hj (hcumK j (by omega))).2
    refine ⟨_, F.g_mem _ (hpr j) _ ?_, price_succ σ n Δ θ Nω j hj, ?_⟩
    · apply div_nonneg _ (mul_pos hn' (hΔ j)).le
      have := hsal0 j hj
      unfold sal cum at this
      exact this
    · simp only [Nat.add_sub_cancel]
      refine le_trans hest ?_
      unfold eps Ei
      apply div_le_div_of_nonneg_right _ (mul_pos hn' (hΔ j)).le
      exact mul_le_mul_of_nonneg_left (Edev_mono u hu (hlst j).2) F.α_pos.le
  · have hdev := path_dev Nω hmono K u hu hG 0 (cum σ n θ Nω ℓ) le_rfl
      (by rw [← hc0]; exact hcmono (Nat.zero_le _)) (hcumK ℓ le_rfl)
    simp only [h0, Nat.cast_zero, sub_zero] at hdev
    refine le_trans hdev ?_
    have := Edev_mono u hu (by linarith : cum σ n θ Nω ℓ ≤ (n : ℝ) * F.M * D.T)
    unfold Edev at this ⊢
    linarith
  · have hx : ∀ i, (Nω (cum σ n θ Nω i) : ℝ) ≤ Nω (cum σ n θ Nω (i + 1)) := by
      intro i; exact_mod_cast hmono (hcmono (Nat.le_succ i))
    have hcl := cap_lower (pr σ n θ Nω) (fun i => (Nω (cum σ n θ Nω i) : ℝ)) (capacity D n : ℝ) D.pHi
      (fun i => le_trans D.pLo_pos.le (hpr i).1) (fun i => (hpr i).2) hx ℓ
    have hx0 : (Nω (cum σ n θ Nω 0) : ℝ) = 0 := by rw [hc0, h0]; simp
    simp only [hx0, zero_sub] at hcl
    have hcap0 : max (-(capacity D n : ℝ)) 0 = 0 := max_eq_right (by simp)
    rw [hcap0, sub_zero] at hcl
    unfold revenue
    convert hcl using 2
    · simp only [sal]
    · push_cast
      rfl
  · unfold sal
    rw [telescope (fun i => (Nω (cum σ n θ Nω i) : ℝ)) ℓ]
    rw [hc0, h0]; simp

end BZ635

open MeasureTheory BesbesZeevi.SingleParam

namespace BZ635

variable {D : Market} {F : Family D} (σ : Selection D F)

lemma eps_nonneg (n : ℕ) (hn : 3 ≤ n) (u : ℝ) (hu : 0 ≤ u) (i : ℕ) : 0 ≤ eps F n u i := by
  unfold eps Ei
  have hn' : (0 : ℝ) < n := by norm_cast; omega
  exact div_nonneg (mul_nonneg F.α_pos.le (Edev_nonneg _ _ hu))
    (mul_pos hn' (stage_pos D.T D.T_pos n hn i)).le

lemma sum_split (g : ℕ → ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∑ i ∈ Finset.Icc 1 ℓ, g i = g 1 + ∑ i ∈ Finset.Ioc 1 ℓ, g i :=
  (Finset.add_sum_Ioc_eq_sum_Icc hℓ).symm

lemma cap_ge (n : ℕ) : (n : ℝ) * D.x - 1 ≤ (capacity D n : ℝ) := by
  unfold capacity
  exact (Nat.sub_one_lt_floor _).le

lemma path_case1 {θ : ℝ} (hθ : θ ∈ F.Θ) (h : F.lam D.pHi θ ≤ D.x / D.T) (n : ℕ) (hn : 3 ≤ n)
    (Nω : ℝ → ℕ) (hmono : Monotone Nω) (h0 : Nω 0 = 0) (K : ℕ) (hK : (n : ℝ) * F.M * D.T ≤ K)
    (u : ℝ) (hu : 0 ≤ u) (hG : GoodPath Nω K u) :
    (n : ℝ) * (D.T * (σ.pD θ * F.lam (σ.pD θ) θ)) - ErrB F n u
      ≤ revenue D F σ n (numStages n) (stageLength D.T n) θ Nω := by
  obtain ⟨hpr, hst, hθ', hdevℓ, hcumsum, hrev, -, -⟩ :=
    path_common σ hθ n hn Nω hmono h0 K hK u hu hG
  set ℓ := numStages n with hℓ
  set Δ := stageLength D.T n with hΔdef
  have hℓ1 : 1 ≤ ℓ := numStages_pos n hn
  have hn' : (0 : ℝ) < n := by norm_cast; omega
  have hpHi0 : 0 < D.pHi := lt_trans D.pLo_pos D.pLo_lt_pHi
  set r := σ.pD θ * F.lam (σ.pD θ) θ with hr
  have hq := pD_mem σ hθ
  have hr_le : r ≤ D.pHi * F.M :=
    mul_le_mul hq.2 (lam_le_M hθ hq) (lam_nonneg hθ hq) hpHi0.le
  have hTsplit : Δ 1 + ∑ i ∈ Finset.Ioc 1 ℓ, Δ i = D.T := by
    rw [← sum_split Δ ℓ hℓ1]; exact stage_sum D.T D.T_pos n hn
  set Se := ∑ i ∈ Finset.Ioc 1 ℓ, eps F n u (i - 1) * Δ i with hSe
  have hSe0 : 0 ≤ Se := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (eps_nonneg n hn u hu _) (stage_pos D.T D.T_pos n hn i).le)
  set SE := ∑ i ∈ Finset.Icc 1 ℓ, Ei F n u i with hSE
  -- S1: sales vs intensities
  have S1 : ∑ i ∈ Finset.Icc 1 ℓ, (pr σ n θ Nω i * lst σ n θ Nω i - D.pHi * Ei F n u i)
      ≤ ∑ i ∈ Finset.Icc 1 ℓ, pr σ n θ Nω i * sal σ n θ Nω i := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨hdev, -, -⟩ := hst i hi
    have hp := hpr i
    have hp0 : 0 ≤ pr σ n θ Nω i := le_trans D.pLo_pos.le hp.1
    have hE0 : 0 ≤ Ei F n u i := Edev_nonneg _ _ hu
    have h1 : lst σ n θ Nω i - Ei F n u i ≤ sal σ n θ Nω i := by
      have := (abs_le.mp hdev).1; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hp0
    have h3 : pr σ n θ Nω i * Ei F n u i ≤ D.pHi * Ei F n u i := mul_le_mul_of_nonneg_right hp.2 hE0
    nlinarith
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at S1
  -- S2: revenue rates
  have S2 : (n : ℝ) * r * (D.T - Δ 1) - 3 * D.pHi * F.K2 * n * Se
      ≤ ∑ i ∈ Finset.Icc 1 ℓ, pr σ n θ Nω i * lst σ n θ Nω i := by
    rw [sum_split _ ℓ hℓ1]
    have h1 : 0 ≤ pr σ n θ Nω 1 * lst σ n θ Nω 1 :=
      mul_nonneg (le_trans D.pLo_pos.le (hpr 1).1) (hst 1 (Finset.mem_Icc.mpr ⟨le_rfl, hℓ1⟩)).2.1
    have h2 : ∑ i ∈ Finset.Ioc 1 ℓ, ((n : ℝ) * r * Δ i - 3 * D.pHi * F.K2 * n * (eps F n u (i - 1) * Δ i))
        ≤ ∑ i ∈ Finset.Ioc 1 ℓ, pr σ n θ Nω i * lst σ n θ Nω i := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨θ', hθ'm, hpe, he⟩ := hθ' i hi
      have hrev' := case1_rev σ hθ hθ'm h he
      have hlst : pr σ n θ Nω i * lst σ n θ Nω i
          = (n : ℝ) * (σ.pD θ' * F.lam (σ.pD θ') θ) * Δ i := by
        unfold lst; rw [hpe]; ring
      rw [hlst]
      have hΔi := (stage_pos D.T D.T_pos n hn i).le
      have := mul_le_mul_of_nonneg_right hrev' (mul_nonneg hn'.le hΔi)
      nlinarith
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
    have hT : ∑ i ∈ Finset.Ioc 1 ℓ, Δ i = D.T - Δ 1 := by linarith
    rw [hT] at h2
    linarith
  -- S3: overflow
  have S3 : max ((Nω (cum σ n θ Nω ℓ) : ℝ) - (capacity D n : ℝ)) 0
      ≤ (n : ℝ) * F.M * Δ 1 + 2 * F.K2 * n * Se + Edev u ((n : ℝ) * F.M * D.T) + 1 := by
    have hE0 := Edev_nonneg u ((n : ℝ) * F.M * D.T) hu
    have hΔ1 := (stage_pos D.T D.T_pos n hn 1).le
    have a1 : 0 ≤ (n : ℝ) * F.M * Δ 1 := mul_nonneg (mul_nonneg hn'.le F.M_pos.le) hΔ1
    have a2 : 0 ≤ 2 * F.K2 * n * Se := mul_nonneg (mul_nonneg (by linarith [F.K2_pos]) hn'.le) hSe0
    apply max_le _ (by linarith)
    have hx := (abs_le.mp hdevℓ).2
    have hcap := cap_ge (D := D) n
    have hc : cum σ n θ Nω ℓ ≤ (n : ℝ) * F.M * Δ 1 + (n : ℝ) * D.x + 2 * F.K2 * n * Se := by
      rw [hcumsum, sum_split _ ℓ hℓ1]
      have h1 := (hst 1 (Finset.mem_Icc.mpr ⟨le_rfl, hℓ1⟩)).2.2
      have h2 : ∑ i ∈ Finset.Ioc 1 ℓ, lst σ n θ Nω i
          ≤ ∑ i ∈ Finset.Ioc 1 ℓ, ((n : ℝ) * (D.x / D.T) * Δ i + 2 * F.K2 * n * (eps F n u (i - 1) * Δ i)) := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨θ', hθ'm, hpe, he⟩ := hθ' i hi
        have hrate := case1_rate σ hθ hθ'm h he
        unfold lst; rw [hpe]
        have hΔi := (stage_pos D.T D.T_pos n hn i).le
        have := mul_le_mul_of_nonneg_right hrate (mul_nonneg hn'.le hΔi)
        nlinarith
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
      have hT : ∑ i ∈ Finset.Ioc 1 ℓ, Δ i = D.T - Δ 1 := by linarith
      rw [hT] at h2
      have hcx : (n : ℝ) * (D.x / D.T) * (D.T - Δ 1) ≤ (n : ℝ) * D.x := by
        have hc0 : 0 ≤ (n : ℝ) * (D.x / D.T) := mul_nonneg hn'.le (div_pos D.x_pos D.T_pos).le
        have : (n : ℝ) * (D.x / D.T) * D.T = (n : ℝ) * D.x := by field_simp [D.T_pos.ne']
        nlinarith
      linarith
    linarith
  have hrev2 := hrev
  have hfin : (n : ℝ) * r * Δ 1 ≤ D.pHi * F.M * n * Δ 1 := by
    have hΔ1 := (stage_pos D.T D.T_pos n hn 1).le
    have := mul_le_mul_of_nonneg_right hr_le (mul_nonneg hn'.le hΔ1)
    nlinarith
  have hK0 : 0 ≤ F.K2 * F.M / F.KLo * n * Se := by
    have := F.K2_pos.le; have := F.M_pos.le; have := F.KLo_pos.le; positivity
  have hpm : D.pHi * max ((Nω (cum σ n θ Nω ℓ) : ℝ) - (capacity D n : ℝ)) 0
      ≤ D.pHi * ((n : ℝ) * F.M * Δ 1 + 2 * F.K2 * n * Se + Edev u ((n : ℝ) * F.M * D.T) + 1) :=
    mul_le_mul_of_nonneg_left S3 hpHi0.le
  unfold ErrB
  rw [← hSe, ← hSE]
  nlinarith

lemma path_case2 {θ : ℝ} (hθ : θ ∈ F.Θ) (h : D.x / D.T < F.lam D.pHi θ) (n : ℕ) (hn : 3 ≤ n)
    (Nω : ℝ → ℕ) (hmono : Monotone Nω) (h0 : Nω 0 = 0) (K : ℕ) (hK : (n : ℝ) * F.M * D.T ≤ K)
    (u : ℝ) (hu : 0 ≤ u) (hG : GoodPath Nω K u) :
    (n : ℝ) * (D.pHi * D.x) - ErrB F n u
      ≤ revenue D F σ n (numStages n) (stageLength D.T n) θ Nω := by
  obtain ⟨hpr, hst, hθ', hdevℓ, hcumsum, hrev, hsum, hsal0⟩ :=
    path_common σ hθ n hn Nω hmono h0 K hK u hu hG
  set ℓ := numStages n with hℓ
  set Δ := stageLength D.T n with hΔdef
  have hℓ1 : 1 ≤ ℓ := numStages_pos n hn
  have hn' : (0 : ℝ) < n := by norm_cast; omega
  have hpHi0 : 0 < D.pHi := lt_trans D.pLo_pos D.pLo_lt_pHi
  have hTsplit : Δ 1 + ∑ i ∈ Finset.Ioc 1 ℓ, Δ i = D.T := by
    rw [← sum_split Δ ℓ hℓ1]; exact stage_sum D.T D.T_pos n hn
  set Se := ∑ i ∈ Finset.Ioc 1 ℓ, eps F n u (i - 1) * Δ i with hSe
  have hSe0 : 0 ≤ Se := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (eps_nonneg n hn u hu _) (stage_pos D.T D.T_pos n hn i).le)
  set SE := ∑ i ∈ Finset.Icc 1 ℓ, Ei F n u i with hSE
  have hcM : D.x / D.T ≤ F.M := le_trans h.le (lam_le_M hθ pHi_mem)
  -- rewrite the price-weighted sales
  have hrw : ∑ i ∈ Finset.Icc 1 ℓ, pr σ n θ Nω i * sal σ n θ Nω i
      = D.pHi * (Nω (cum σ n θ Nω ℓ) : ℝ)
        - ∑ i ∈ Finset.Icc 1 ℓ, (D.pHi - pr σ n θ Nω i) * sal σ n θ Nω i := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  -- bound on the price loss
  have hloss : ∑ i ∈ Finset.Icc 1 ℓ, (D.pHi - pr σ n θ Nω i) * sal σ n θ Nω i
      ≤ D.pHi * ((n : ℝ) * F.M * Δ 1) + D.pHi * SE + F.K2 * F.M / F.KLo * n * Se := by
    have hb : ∀ i ∈ Finset.Icc 1 ℓ, sal σ n θ Nω i ≤ (n : ℝ) * F.M * Δ i + Ei F n u i := by
      intro i hi
      obtain ⟨hdev, -, hl⟩ := hst i hi
      have := (abs_le.mp hdev).2; linarith
    rw [sum_split _ ℓ hℓ1]
    have hmem1 : 1 ∈ Finset.Icc 1 ℓ := Finset.mem_Icc.mpr ⟨le_rfl, hℓ1⟩
    have h1 : (D.pHi - pr σ n θ Nω 1) * sal σ n θ Nω 1
        ≤ D.pHi * ((n : ℝ) * F.M * Δ 1 + Ei F n u 1) := by
      have hp := hpr 1
      have hs0 := hsal0 1 le_rfl
      calc (D.pHi - pr σ n θ Nω 1) * sal σ n θ Nω 1 ≤ D.pHi * sal σ n θ Nω 1 :=
            mul_le_mul_of_nonneg_right (by linarith [hp.1, D.pLo_pos]) hs0
        _ ≤ D.pHi * ((n : ℝ) * F.M * Δ 1 + Ei F n u 1) :=
            mul_le_mul_of_nonneg_left (hb 1 hmem1) hpHi0.le
    have h2 : ∑ i ∈ Finset.Ioc 1 ℓ, (D.pHi - pr σ n θ Nω i) * sal σ n θ Nω i
        ≤ ∑ i ∈ Finset.Ioc 1 ℓ, (F.K2 * F.M / F.KLo * n * (eps F n u (i - 1) * Δ i)
            + D.pHi * Ei F n u i) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨θ', hθ'm, hpe, he⟩ := hθ' i hi
      have hpl := case2_price σ hθ hθ'm h he
      have hiI : i ∈ Finset.Icc 1 ℓ := Finset.mem_Icc.mpr
        ⟨by linarith [(Finset.mem_Ioc.mp hi).1], (Finset.mem_Ioc.mp hi).2⟩
      have hs0 := hsal0 i (Finset.mem_Icc.mp hiI).1
      have hsb := hb i hiI
      have hp := hpr i
      have hd0 : 0 ≤ D.pHi - pr σ n θ Nω i := by linarith [hp.2]
      have hdle : D.pHi - pr σ n θ Nω i ≤ D.pHi := by linarith [hp.1, D.pLo_pos]
      rw [← hpe] at hpl
      have hE0 : 0 ≤ Ei F n u i := Edev_nonneg _ _ hu
      have hΔi := (stage_pos D.T D.T_pos n hn i).le
      have hnM : 0 ≤ (n : ℝ) * F.M * Δ i := by have := F.M_pos.le; positivity
      have k1 : (D.pHi - pr σ n θ Nω i) * sal σ n θ Nω i
          ≤ (D.pHi - pr σ n θ Nω i) * ((n : ℝ) * F.M * Δ i) + (D.pHi - pr σ n θ Nω i) * Ei F n u i := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left hsb hd0
      have k2 : (D.pHi - pr σ n θ Nω i) * ((n : ℝ) * F.M * Δ i)
          ≤ F.K2 * eps F n u (i - 1) / F.KLo * ((n : ℝ) * F.M * Δ i) :=
        mul_le_mul_of_nonneg_right hpl hnM
      have k3 : (D.pHi - pr σ n θ Nω i) * Ei F n u i ≤ D.pHi * Ei F n u i :=
        mul_le_mul_of_nonneg_right hdle hE0
      have k4 : F.K2 * eps F n u (i - 1) / F.KLo * ((n : ℝ) * F.M * Δ i)
          = F.K2 * F.M / F.KLo * n * (eps F n u (i - 1) * Δ i) := by ring
      linarith
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
    have hSEsplit : SE = Ei F n u 1 + ∑ i ∈ Finset.Ioc 1 ℓ, Ei F n u i := sum_split _ ℓ hℓ1
    rw [hSEsplit]
    linarith
  -- lower bound on total sales
  have hsales : (n : ℝ) * D.x - (n : ℝ) * F.M * Δ 1 - Edev u ((n : ℝ) * F.M * D.T) - 1
      ≤ min (Nω (cum σ n θ Nω ℓ) : ℝ) (capacity D n : ℝ) := by
    have hcap := cap_ge (D := D) n
    have hΔ1 := (stage_pos D.T D.T_pos n hn 1).le
    have hE0 := Edev_nonneg u ((n : ℝ) * F.M * D.T) hu
    have a1 : 0 ≤ (n : ℝ) * F.M * Δ 1 := mul_nonneg (mul_nonneg hn'.le F.M_pos.le) hΔ1
    apply le_min _ (by linarith)
    have hx := (abs_le.mp hdevℓ).1
    have hc : (n : ℝ) * D.x - (n : ℝ) * F.M * Δ 1 ≤ cum σ n θ Nω ℓ := by
      rw [hcumsum, sum_split _ ℓ hℓ1]
      have h1 := (hst 1 (Finset.mem_Icc.mpr ⟨le_rfl, hℓ1⟩)).2.1
      have h2 : ∑ i ∈ Finset.Ioc 1 ℓ, (n : ℝ) * (D.x / D.T) * Δ i
          ≤ ∑ i ∈ Finset.Ioc 1 ℓ, lst σ n θ Nω i := by
        apply Finset.sum_le_sum
        intro i _
        unfold lst
        have hp := hpr i
        have hf : D.x / D.T ≤ F.lam (pr σ n θ Nω i) θ :=
          le_trans h.le (lam_anti hθ hp pHi_mem hp.2)
        have hΔi := (stage_pos D.T D.T_pos n hn i).le
        have := mul_le_mul_of_nonneg_right hf (mul_nonneg hn'.le hΔi)
        nlinarith
      rw [← Finset.mul_sum] at h2
      have hT : ∑ i ∈ Finset.Ioc 1 ℓ, Δ i = D.T - Δ 1 := by linarith
      rw [hT] at h2
      have : (n : ℝ) * (D.x / D.T) * D.T = (n : ℝ) * D.x := by field_simp [D.T_pos.ne']
      have h3 : (n : ℝ) * (D.x / D.T) * Δ 1 ≤ (n : ℝ) * F.M * Δ 1 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcM hn'.le) hΔ1
      nlinarith
    linarith
  have hmin := min_eq_sub_max (Nω (cum σ n θ Nω ℓ) : ℝ) (capacity D n : ℝ)
  have hpm := mul_le_mul_of_nonneg_left hsales hpHi0.le
  have hK0 : 0 ≤ 5 * D.pHi * F.K2 * n * Se := by
    have := F.K2_pos.le; positivity
  unfold ErrB
  rw [← hSe, ← hSE]
  rw [hrw] at hrev
  nlinarith

end BZ635

open MeasureTheory ProbabilityTheory BesbesZeevi.SingleParam

namespace BZ635

variable {D : Market} {F : Family D} (σ : Selection D F)

lemma rev_bounds {θ : ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 3 ≤ n) (Nω : ℝ → ℕ) (hmono : Monotone Nω) :
    0 ≤ revenue D F σ n (numStages n) (stageLength D.T n) θ Nω ∧
    revenue D F σ n (numStages n) (stageLength D.T n) θ Nω ≤ D.pHi * (capacity D n : ℝ) := by
  have hn0 : 0 < n := by omega
  have hΔ : ∀ m, 0 < stageLength D.T n m := fun m => stage_pos D.T D.T_pos n hn m
  have hpr : ∀ i, pr σ n θ Nω i ∈ Set.Icc D.pLo D.pHi :=
    fun i => price_mem σ hθ n hn0 _ hΔ Nω hmono i
  have hcmono : Monotone (cum σ n θ Nω) :=
    monotone_nat_of_le_succ (fun k => cum_mono σ hθ n hn0 _ hΔ Nω hmono k)
  have hx : ∀ i, (Nω (cum σ n θ Nω i) : ℝ) ≤ Nω (cum σ n θ Nω (i + 1)) := by
    intro i; exact_mod_cast hmono (hcmono (Nat.le_succ i))
  have heq : revenue D F σ n (numStages n) (stageLength D.T n) θ Nω
      = ∑ i ∈ Finset.Icc 1 (numStages n), pr σ n θ Nω i *
          (min (Nω (cum σ n θ Nω i) : ℝ) (capacity D n : ℝ)
            - min (Nω (cum σ n θ Nω (i - 1)) : ℝ) (capacity D n : ℝ)) := by
    unfold revenue pr cum
    push_cast
    rfl
  rw [heq]
  refine ⟨cap_nonneg _ _ _ (fun i => le_trans D.pLo_pos.le (hpr i).1) hx _, ?_⟩
  refine le_trans (cap_upper _ _ _ D.pHi (fun i => (hpr i).2) hx _) ?_
  have hpHi0 : 0 ≤ D.pHi := le_of_lt (lt_trans D.pLo_pos D.pLo_lt_pHi)
  apply mul_le_mul_of_nonneg_left _ hpHi0
  have h1 : min (Nω (cum σ n θ Nω (numStages n)) : ℝ) (capacity D n : ℝ) ≤ capacity D n := min_le_right _ _
  have h2 : 0 ≤ min (Nω (cum σ n θ Nω 0) : ℝ) (capacity D n : ℝ) := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma good_meas (N : PoissonProcess Ω P) (K : ℕ) (u : ℝ) :
    MeasurableSet {ω | GoodPath (fun t => N.N t ω) K u} := by
  have hm : ∀ t : ℝ, Measurable (fun ω => (N.N t ω : ℝ)) :=
    fun t => (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (N.meas t)
  unfold GoodPath
  simp only [Set.setOf_forall]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => ?_
  rw [Set.setOf_and]
  exact (measurableSet_le ((hm _).sub (hm _)) measurable_const).inter
    (measurableSet_le measurable_const ((hm _).sub (hm _)))

lemma exp_lower (N : PoissonProcess Ω P) {θ : ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 3 ≤ n)
    (K : ℕ) (u : ℝ) (hu : 0 ≤ u) (V : ℝ)
    (hV : ∀ ω, GoodPath (fun t => N.N t ω) K u →
      V ≤ revenue D F σ n (numStages n) (stageLength D.T n) θ (fun t => N.N t ω)) :
    V - max V 0 * (((K : ℝ) + 1) ^ 2 * (2 * Real.exp (-u)))
      ≤ expRevenue N D F σ n (numStages n) (stageLength D.T n) θ := by
  set q := ((K : ℝ) + 1) ^ 2 * (2 * Real.exp (-u)) with hq
  have hq0 : 0 ≤ q := by positivity
  set G := {ω | GoodPath (fun t => N.N t ω) K u} with hGdef
  have hGm : MeasurableSet G := good_meas N K u
  have hbad := good_event N K u hu
  have hcomp : Gᶜ = {ω | ¬ GoodPath (fun t => N.N t ω) K u} := by
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
  have hexp0 : 0 ≤ expRevenue N D F σ n (numStages n) (stageLength D.T n) θ := ENNReal.toReal_nonneg
  rcases le_or_gt V 0 with hV0 | hV0
  · rw [max_eq_right hV0, zero_mul, sub_zero]; linarith
  rw [max_eq_left hV0.le]
  have hpos := fun ω => (rev_bounds σ hθ n hn (fun t => N.N t ω) (N.mono ω))
  have hlow : G.indicator (fun _ => ENNReal.ofReal V)
      ≤ fun ω => ENNReal.ofReal (revenue D F σ n (numStages n) (stageLength D.T n) θ (fun t => N.N t ω)) := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem hω]; exact ENNReal.ofReal_le_ofReal (hV ω hω)
    · rw [Set.indicator_of_notMem hω]; exact bot_le
  have hup : (∫⁻ ω, ENNReal.ofReal (revenue D F σ n (numStages n) (stageLength D.T n) θ (fun t => N.N t ω)) ∂P)
      ≤ ENNReal.ofReal (D.pHi * (capacity D n : ℝ)) := by
    calc _ ≤ ∫⁻ _, ENNReal.ofReal (D.pHi * (capacity D n : ℝ)) ∂P :=
          lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hpos ω).2)
      _ = ENNReal.ofReal (D.pHi * (capacity D n : ℝ)) := by rw [lintegral_const, measure_univ, mul_one]
  have hmono' := lintegral_mono (μ := P) hlow
  rw [lintegral_indicator_const hGm] at hmono'
  have hfin : (∫⁻ ω, ENNReal.ofReal (revenue D F σ n (numStages n) (stageLength D.T n) θ (fun t => N.N t ω)) ∂P) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  have := ENNReal.toReal_mono hfin hmono'
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hV0.le] at this
  unfold expRevenue
  have h2 : V * (1 - q) ≤ V * (P G).toReal := mul_le_mul_of_nonneg_left hPG hV0.le
  nlinarith

/-- Pure real bookkeeping for the regret. -/
lemma regret_arith (E J W Err q U Ul : ℝ) (hJ : 0 < Ul) (hUl : Ul ≤ J) (hJW : J ≤ W) (hW0 : 0 ≤ W)
    (hWU : W ≤ U) (hErr : 0 ≤ Err) (hq : 0 ≤ q)
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

end BZ635

open MeasureTheory ProbabilityTheory BesbesZeevi.SingleParam

namespace BZ635

variable {D : Market} {F : Family D}

lemma ErrB_nonneg (n : ℕ) (hn : 3 ≤ n) (u : ℝ) (hu : 0 ≤ u) : 0 ≤ ErrB F n u := by
  unfold ErrB
  have hpHi0 : 0 ≤ D.pHi := le_of_lt (lt_trans D.pLo_pos D.pLo_lt_pHi)
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 0 ≤ 2 * D.pHi * F.M * n * stageLength D.T n 1 :=
    mul_nonneg (by have := F.M_pos.le; positivity) (stage_pos D.T D.T_pos n hn 1).le
  have h2 : 0 ≤ ∑ i ∈ Finset.Ioc 1 (numStages n), eps F n u (i - 1) * stageLength D.T n i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (eps_nonneg n hn u hu _) (stage_pos D.T D.T_pos n hn i).le)
  have h3 : 0 ≤ ∑ i ∈ Finset.Icc 1 (numStages n), Ei F n u i :=
    Finset.sum_nonneg (fun i _ => Edev_nonneg _ _ hu)
  have hc : 0 ≤ (5 * D.pHi * F.K2 + F.K2 * F.M / F.KLo) * n := by
    have := F.K2_pos.le; have := F.M_pos.le; have := F.KLo_pos.le; positivity
  have h4 := Edev_nonneg u ((n : ℝ) * F.M * D.T) hu
  have := mul_nonneg hc h2
  have := mul_nonneg hpHi0 h3
  have := mul_nonneg hpHi0 (by linarith : 0 ≤ Edev u ((n : ℝ) * F.M * D.T) + 1)
  linarith

variable (σ : Selection D F)

lemma regret_pre {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (N : PoissonProcess Ω P) {θ : ℝ} (hθ : θ ∈ F.Θ) (n : ℕ) (hn : 3 ≤ n) (u : ℝ) (hu : 0 ≤ u) :
    tunedRegret N D F σ n θ
      ≤ (ErrB F n u + ((n : ℝ) * (D.pHi * (D.T * F.M + D.x)))
          * ((((⌈(n : ℝ) * F.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-u))))
        / ((n : ℝ) * (F.m * min D.T (D.x / F.M))) := by
  set K := ⌈(n : ℝ) * F.M * D.T⌉₊ with hKdef
  have hK : (n : ℝ) * F.M * D.T ≤ K := Nat.le_ceil _
  have hn' : (0 : ℝ) < n := by norm_cast; omega
  have hUl : 0 < (n : ℝ) * (F.m * min D.T (D.x / F.M)) :=
    mul_pos hn' (mul_pos F.m_pos (lt_min D.T_pos (div_pos D.x_pos F.M_pos)))
  have hpHi0 : 0 < D.pHi := lt_trans D.pLo_pos D.pLo_lt_pHi
  have hq0 : 0 ≤ (((K : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-u)) := by positivity
  have hErr := ErrB_nonneg (F := F) n hn u hu
  unfold tunedRegret regret
  rcases le_or_gt (F.lam D.pHi θ) (D.x / D.T) with h | h
  · set W := (n : ℝ) * (D.T * (σ.pD θ * F.lam (σ.pD θ) θ)) with hW
    have hV : ∀ ω, GoodPath (fun t => N.N t ω) K u →
        W - ErrB F n u ≤ revenue D F σ n (numStages n) (stageLength D.T n) θ (fun t => N.N t ω) :=
      fun ω hω => path_case1 σ hθ h n hn (fun t => N.N t ω) (N.mono ω) (N.zero ω) K hK u hu hω
    have hE := exp_lower σ N hθ n hn K u hu (W - ErrB F n u) hV
    have hq := pD_mem σ hθ
    have hr0 : 0 ≤ σ.pD θ * F.lam (σ.pD θ) θ := mul_nonneg (le_trans D.pLo_pos.le hq.1) (lam_nonneg hθ hq)
    have hrM : σ.pD θ * F.lam (σ.pD θ) θ ≤ D.pHi * F.M :=
      mul_le_mul hq.2 (lam_le_M hθ hq) (lam_nonneg hθ hq) hpHi0.le
    have hW0 : 0 ≤ W := mul_nonneg hn'.le (mul_nonneg D.T_pos.le hr0)
    have hWU : W ≤ (n : ℝ) * (D.pHi * (D.T * F.M + D.x)) := by
      apply mul_le_mul_of_nonneg_left _ hn'.le
      have := mul_le_mul_of_nonneg_left hrM D.T_pos.le
      have := mul_pos hpHi0 D.x_pos
      nlinarith
    exact regret_arith _ _ W _ _ _ _ hUl (detS_lower hθ n) (detS_upper_case1 σ hθ h n) hW0 hWU hErr hq0 hE
  · set W := (n : ℝ) * (D.pHi * D.x) with hW
    have hV : ∀ ω, GoodPath (fun t => N.N t ω) K u →
        W - ErrB F n u ≤ revenue D F σ n (numStages n) (stageLength D.T n) θ (fun t => N.N t ω) :=
      fun ω hω => path_case2 σ hθ h n hn (fun t => N.N t ω) (N.mono ω) (N.zero ω) K hK u hu hω
    have hE := exp_lower σ N hθ n hn K u hu (W - ErrB F n u) hV
    have hW0 : 0 ≤ W := mul_nonneg hn'.le (mul_nonneg hpHi0.le D.x_pos.le)
    have hWU : W ≤ (n : ℝ) * (D.pHi * (D.T * F.M + D.x)) := by
      apply mul_le_mul_of_nonneg_left _ hn'.le
      have := mul_pos (mul_pos hpHi0 D.T_pos) F.M_pos
      nlinarith
    exact regret_arith _ _ W _ _ _ _ hUl (detS_lower hθ n) (detS_upper_pHi hθ n) hW0 hWU hErr hq0 hE

end BZ635

open MeasureTheory ProbabilityTheory BesbesZeevi.SingleParam

namespace BZ635

lemma log_ge_one (n : ℕ) (hn : 16 ≤ n) : 1 ≤ Real.log n := by
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9; linarith

lemma rho_facts (n : ℕ) (hn : 16 ≤ n) :
    0 < (n : ℝ) ^ (aCoef (numStages n) - 1) ∧
    Real.sqrt n ≤ (n : ℝ) * (n : ℝ) ^ (aCoef (numStages n) - 1) ∧ 1 ≤ Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hℓ := numStages_pos n (by omega)
  refine ⟨Real.rpow_pos_of_pos hn0 _, ?_, Real.one_le_sqrt.mpr hn1⟩
  have h1 : (n : ℝ) * (n : ℝ) ^ (aCoef (numStages n) - 1) = (n : ℝ) ^ (aCoef (numStages n)) := by
    rw [Real.rpow_sub hn0, Real.rpow_one]; field_simp
  rw [h1, Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hn1 (aCoef_ge_half _ hℓ)

lemma ell_le (n : ℕ) (hn : 16 ≤ n) : (numStages n : ℝ) ≤ 3 * Real.log n := by
  have hL := log_ge_one n hn
  have hl2 := Real.log_two_gt_d9
  have h1 : (numStages n : ℝ) < Real.logb 2 (Real.log n) + 1 := by
    unfold numStages
    exact Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hL)
  have h2 : Real.log (Real.log n) ≤ Real.log n - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h3 : Real.logb 2 (Real.log n) ≤ 2 * (Real.log n - 1) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

lemma Edev_le (u M Y : ℝ) (hu : 0 ≤ u) (hM : 0 ≤ M) (hY1 : 1 ≤ Y) (huY : u ≤ Y) :
    Edev u (M * Y) ≤ (2 + 4 * Real.sqrt u + 2 * Real.sqrt u * Real.sqrt (M + 2)) * Real.sqrt Y := by
  unfold Edev
  have hsY : 1 ≤ Real.sqrt Y := Real.one_le_sqrt.mpr hY1
  have hsu : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have h1 : u ≤ Real.sqrt u * Real.sqrt Y := by
    calc u = Real.sqrt u * Real.sqrt u := (Real.mul_self_sqrt hu).symm
      _ ≤ Real.sqrt u * Real.sqrt Y := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt huY) hsu
  have h2 : Real.sqrt (u * (M * Y + 2)) ≤ Real.sqrt u * Real.sqrt (M + 2) * Real.sqrt Y := by
    rw [← Real.sqrt_mul hu, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hu
    nlinarith
  nlinarith

lemma Ehat_le (M : ℝ) (hM : 0 ≤ M) (n : ℕ) (hn : 16 ≤ n) :
    2 + 4 * Real.sqrt (3 * Real.log n) + 2 * Real.sqrt (3 * Real.log n) * Real.sqrt (M + 2)
      ≤ Real.sqrt (Real.log n) * (10 + 4 * Real.sqrt (M + 2)) := by
  have hL := log_ge_one n hn
  have hs1 : 1 ≤ Real.sqrt (Real.log n) := Real.one_le_sqrt.mpr hL
  have h3 : Real.sqrt (3 * Real.log n) ≤ 2 * Real.sqrt (Real.log n) := by
    rw [Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hm : 0 ≤ Real.sqrt (M + 2) := Real.sqrt_nonneg _
  have := mul_le_mul_of_nonneg_right h3 hm
  nlinarith

variable {D : Market} (F : Family D)

lemma ErrB_le (n : ℕ) (hn : 16 ≤ n) (hbig : 12 * Real.log n ^ 2 ≤ D.T * Real.sqrt n) :
    ErrB F n (3 * Real.log n)
      ≤ (n : ℝ) * (n : ℝ) ^ (aCoef (numStages n) - 1) * (numStages n : ℝ) * Real.sqrt (Real.log n)
        * (2 * D.pHi * F.M * D.T
          + (5 * D.pHi * F.K2 + F.K2 * F.M / F.KLo) * F.α * Real.sqrt D.T * (10 + 4 * Real.sqrt (F.M + 2))
          + 2 * D.pHi * (10 + 4 * Real.sqrt (F.M + 2)) * Real.sqrt D.T + D.pHi) := by
  have hn3 : 3 ≤ n := by omega
  set ℓ := numStages n with hℓ
  set Δ := stageLength D.T n with hΔ
  set ρ := (n : ℝ) ^ (aCoef ℓ - 1) with hρ
  set s := Real.sqrt (Real.log n) with hs
  set u := 3 * Real.log n with hu
  set cE := 10 + 4 * Real.sqrt (F.M + 2) with hcE
  set Eh := 2 + 4 * Real.sqrt u + 2 * Real.sqrt u * Real.sqrt (F.M + 2) with hEh
  obtain ⟨hρ0, hρn, hsn1⟩ := rho_facts n hn
  have hL := log_ge_one n hn
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hL
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast numStages_pos n hn3
  have hℓ3 := ell_le n hn
  have hu0 : 0 ≤ u := by positivity
  have hn' : (0 : ℝ) < n := by norm_cast; omega
  have hpHi0 : 0 < D.pHi := lt_trans D.pLo_pos D.pLo_lt_pHi
  have hT0 := D.T_pos
  have hα0 := F.α_pos
  have hM0 := F.M_pos
  have hK20 := F.K2_pos
  have hKLo0 := F.KLo_pos
  have hEh : Eh ≤ s * cE := Ehat_le F.M F.M_pos.le n hn
  have hEh0 : 0 ≤ Eh := by positivity
  have hcE0 : 0 ≤ cE := by positivity
  have hsT := Real.sqrt_nonneg D.T
  -- every stage is long
  have hY : ∀ i ∈ Finset.Icc 1 ℓ, 1 ≤ (n : ℝ) * Δ i ∧ u ≤ (n : ℝ) * Δ i := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    have hge := stage_ge D.T D.T_pos n hn3 i h1 h2
    have hge' : D.T / ℓ * Real.sqrt n ≤ (n : ℝ) * Δ i := by
      have := mul_le_mul_of_nonneg_left hge hn'.le
      have h3 : D.T / ℓ * Real.sqrt n ≤ D.T / ℓ * ((n : ℝ) * ρ) :=
        mul_le_mul_of_nonneg_left hρn (by positivity)
      nlinarith
    have hbig' : 4 * Real.log n ≤ D.T / ℓ * Real.sqrt n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    constructor <;> linarith
  have hΔT : ∀ i ∈ Finset.Icc 1 ℓ, Δ i ≤ D.T := by
    intro i hi
    rw [← stage_sum D.T D.T_pos n hn3]
    exact Finset.single_le_sum (fun j _ => (stage_pos D.T D.T_pos n hn3 j).le) hi
  have hEi : ∀ i ∈ Finset.Icc 1 ℓ, Ei F n u i ≤ Eh * Real.sqrt ((n : ℝ) * Δ i) := by
    intro i hi
    unfold Ei
    rw [show (n : ℝ) * F.M * stageLength D.T n i = F.M * ((n : ℝ) * Δ i) by rw [hΔ]; ring]
    exact Edev_le u F.M _ hu0 F.M_pos.le (hY i hi).1 (hY i hi).2
  -- term B
  have hB : ∑ i ∈ Finset.Ioc 1 ℓ, eps F n u (i - 1) * Δ i ≤ ℓ * (F.α * Eh * Real.sqrt D.T * ρ) := by
    have hterm : ∀ i ∈ Finset.Ioc 1 ℓ, eps F n u (i - 1) * Δ i ≤ F.α * Eh * Real.sqrt D.T * ρ := by
      intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hi
      have hj : i - 1 ∈ Finset.Icc 1 ℓ := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      set Y := (n : ℝ) * Δ (i - 1) with hYdef
      have hY1 := (hY _ hj).1
      have hYp : 0 < Y := by linarith
      have hsY : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hYp.le
      have hsYp : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hYp
      have hr := stage_ratio D.T D.T_pos n hn3 i (by omega)
      have he := hEi _ hj
      unfold eps
      rw [← hYdef]
      have hΔi0 := (stage_pos D.T D.T_pos n hn3 i).le
      calc F.α * Ei F n u (i - 1) / Y * Δ i ≤ F.α * (Eh * Real.sqrt Y) / Y * (Real.sqrt D.T * ρ * Real.sqrt Y) := by
            apply mul_le_mul _ hr hΔi0 (by positivity)
            apply div_le_div_of_nonneg_right _ hYp.le
            exact mul_le_mul_of_nonneg_left he F.α_pos.le
        _ = F.α * Eh * Real.sqrt D.T * ρ * (Real.sqrt Y * Real.sqrt Y / Y) := by ring
        _ = F.α * Eh * Real.sqrt D.T * ρ := by rw [hsY, div_self hYp.ne', mul_one]
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    rw [nsmul_eq_mul, Nat.card_Ioc]
    apply mul_le_mul_of_nonneg_right _ (by have := F.α_pos.le; positivity)
    have : ((ℓ - 1 : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast Nat.sub_le ℓ 1
    exact this
  -- term C
  have hsq : Real.sqrt ((n : ℝ) * D.T) ≤ (n : ℝ) * ρ * Real.sqrt D.T := by
    rw [Real.sqrt_mul hn'.le]
    exact mul_le_mul_of_nonneg_right hρn hsT
  have hC : ∑ i ∈ Finset.Icc 1 ℓ, Ei F n u i ≤ ℓ * (Eh * ((n : ℝ) * ρ * Real.sqrt D.T)) := by
    have hterm : ∀ i ∈ Finset.Icc 1 ℓ, Ei F n u i ≤ Eh * ((n : ℝ) * ρ * Real.sqrt D.T) := by
      intro i hi
      refine le_trans (hEi i hi) (mul_le_mul_of_nonneg_left (le_trans ?_ hsq) hEh0)
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hΔT i hi) hn'.le)
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    rw [nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
  -- term D
  have hD : Edev u ((n : ℝ) * F.M * D.T) + 1 ≤ Eh * ((n : ℝ) * ρ * Real.sqrt D.T) + (n : ℝ) * ρ := by
    have hT1 := hY 1 (Finset.mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hℓ1⟩)
    have hΔ1T := hΔT 1 (Finset.mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hℓ1⟩)
    have hnT1 : 1 ≤ (n : ℝ) * D.T := le_trans hT1.1 (mul_le_mul_of_nonneg_left hΔ1T hn'.le)
    have hnTu : u ≤ (n : ℝ) * D.T := le_trans hT1.2 (mul_le_mul_of_nonneg_left hΔ1T hn'.le)
    have h1 := Edev_le u F.M ((n : ℝ) * D.T) hu0 F.M_pos.le hnT1 hnTu
    rw [show F.M * ((n : ℝ) * D.T) = (n : ℝ) * F.M * D.T by ring] at h1
    have h2 := mul_le_mul_of_nonneg_left hsq hEh0
    linarith
  -- term A
  have hA : stageLength D.T n 1 ≤ D.T * ρ := stage_one_le D.T D.T_pos n hn3
  -- assemble
  unfold ErrB
  rw [← hΔ, ← hℓ]
  have hc2 : 0 ≤ 5 * D.pHi * F.K2 + F.K2 * F.M / F.KLo := by positivity
  have hnρ : 0 ≤ (n : ℝ) * ρ := by positivity
  have hls : 1 ≤ (ℓ : ℝ) * s := one_le_mul_of_one_le_of_one_le hℓ1 hs1
  have k1 : 2 * D.pHi * F.M * n * Δ 1 ≤ (n : ℝ) * ρ * (2 * D.pHi * F.M * D.T) := by
    have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 * D.pHi * F.M * n)
    linarith
  have k2 : (5 * D.pHi * F.K2 + F.K2 * F.M / F.KLo) * n * ∑ i ∈ Finset.Ioc 1 ℓ, eps F n u (i - 1) * Δ i
      ≤ (n : ℝ) * ρ * ℓ * s * ((5 * D.pHi * F.K2 + F.K2 * F.M / F.KLo) * F.α * Real.sqrt D.T * cE) := by
    have h1 := mul_le_mul_of_nonneg_left hB (mul_nonneg hc2 hn'.le)
    have h2 : (5 * D.pHi * F.K2 + F.K2 * F.M / F.KLo) * n * (ℓ * (F.α * Eh * Real.sqrt D.T * ρ))
        ≤ (5 * D.pHi * F.K2 + F.K2 * F.M / F.KLo) * n * (ℓ * (F.α * (s * cE) * Real.sqrt D.T * ρ)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc2 hn'.le)
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      apply mul_le_mul_of_nonneg_right _ hρ0.le
      apply mul_le_mul_of_nonneg_right _ hsT
      exact mul_le_mul_of_nonneg_left hEh hα0.le
    have h3 : (5 * D.pHi * F.K2 + F.K2 * F.M / F.KLo) * n * (ℓ * (F.α * (s * cE) * Real.sqrt D.T * ρ))
        = (n : ℝ) * ρ * ℓ * s * ((5 * D.pHi * F.K2 + F.K2 * F.M / F.KLo) * F.α * Real.sqrt D.T * cE) := by
      ring
    linarith
  have k3 : D.pHi * ∑ i ∈ Finset.Icc 1 ℓ, Ei F n u i ≤ (n : ℝ) * ρ * ℓ * s * (D.pHi * cE * Real.sqrt D.T) := by
    have h1 := mul_le_mul_of_nonneg_left hC hpHi0.le
    have h2 : D.pHi * (ℓ * (Eh * ((n : ℝ) * ρ * Real.sqrt D.T)))
        ≤ D.pHi * (ℓ * ((s * cE) * ((n : ℝ) * ρ * Real.sqrt D.T))) := by
      apply mul_le_mul_of_nonneg_left _ hpHi0.le
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_right hEh (mul_nonneg hnρ hsT)
    have h3 : D.pHi * (ℓ * ((s * cE) * ((n : ℝ) * ρ * Real.sqrt D.T)))
        = (n : ℝ) * ρ * ℓ * s * (D.pHi * cE * Real.sqrt D.T) := by ring
    linarith
  have k4 : D.pHi * (Edev u ((n : ℝ) * F.M * D.T) + 1)
      ≤ (n : ℝ) * ρ * ℓ * s * (D.pHi * cE * Real.sqrt D.T + D.pHi) := by
    have h1 := mul_le_mul_of_nonneg_left hD hpHi0.le
    have h2 : Eh * ((n : ℝ) * ρ * Real.sqrt D.T) ≤ s * cE * ((n : ℝ) * ρ * Real.sqrt D.T) :=
      mul_le_mul_of_nonneg_right hEh (mul_nonneg hnρ hsT)
    have h2' := mul_le_mul_of_nonneg_left h2 hpHi0.le
    have hs' : s ≤ ℓ * s := le_mul_of_one_le_left (by linarith) hℓ1
    have h3 : s * cE * ((n : ℝ) * ρ * Real.sqrt D.T) ≤ (ℓ * s) * cE * ((n : ℝ) * ρ * Real.sqrt D.T) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs' hcE0) (mul_nonneg hnρ hsT)
    have h3' := mul_le_mul_of_nonneg_left h3 hpHi0.le
    have h4 : (n : ℝ) * ρ ≤ (n : ℝ) * ρ * (ℓ * s) := le_mul_of_one_le_right hnρ hls
    have h4' := mul_le_mul_of_nonneg_left h4 hpHi0.le
    have e1 : D.pHi * ((ℓ * s) * cE * ((n : ℝ) * ρ * Real.sqrt D.T)) + D.pHi * ((n : ℝ) * ρ * (ℓ * s))
        = (n : ℝ) * ρ * ℓ * s * (D.pHi * cE * Real.sqrt D.T + D.pHi) := by ring
    linarith
  have k1' : (n : ℝ) * ρ * (2 * D.pHi * F.M * D.T) ≤ (n : ℝ) * ρ * ℓ * s * (2 * D.pHi * F.M * D.T) := by
    have h0 : 0 ≤ (n : ℝ) * ρ * (2 * D.pHi * F.M * D.T) := by positivity
    have := mul_le_mul_of_nonneg_left hls h0
    linarith
  linarith [k1, k1', k2, k3, k4]

end BZ635

open MeasureTheory ProbabilityTheory BesbesZeevi.SingleParam

namespace BZ635

theorem rate_bound_aux (n : ℕ) (hn : 8 ≤ n) :
    (n : ℝ) ^ (aCoef (numStages n) - 1) ≤ Real.exp 1 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hn8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set x := Real.log (n : ℝ) with hxdef
  have hx1 : 1 < x := by
    rw [hxdef, Real.lt_log_iff_exp_lt hnpos]
    have := Real.exp_one_lt_d9
    linarith
  set L := numStages n with hLdef
  have hlogb_le : Real.logb 2 x ≤ (L : ℝ) := by
    rw [hLdef]; unfold numStages; exact Nat.le_ceil _
  have hlogb_pos : 0 < Real.logb 2 x := Real.logb_pos (by norm_num) hx1
  have hL1 : 1 ≤ L := by
    rw [hLdef]; unfold numStages
    exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hlogb_pos))
  have hxle : x ≤ (2 : ℝ) ^ L := by
    have h1 : (2 : ℝ) ^ (Real.logb 2 x) = x := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (Real.logb 2 x) ≤ (2 : ℝ) ^ (L : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hlogb_le
    rw [h1, Real.rpow_natCast] at h2
    exact h2
  set M : ℝ := (2 : ℝ) ^ (L - 1) with hMdef
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num)
  have h2L : (2 : ℝ) ^ L = 2 * M := by
    rw [hMdef, ← pow_succ']
    congr 1; omega
  have ha : aCoef L = M / (2 * M - 1) := by
    unfold aCoef; rw [h2L]
  have hden : 0 < 2 * M - 1 := by linarith
  have key : x * (aCoef L - 1) ≤ 1 + x * (-(1 / 2 : ℝ)) := by
    rw [ha]
    have hx2 : x ≤ 2 * M := by rw [← h2L]; exact hxle
    rw [div_sub_one hden.ne', mul_div_assoc']
    rw [div_le_iff₀ hden]
    nlinarith
  rw [Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos, ← Real.exp_add]
  exact Real.exp_le_exp.mpr key

lemma ls_rate (n : ℕ) (hn : 16 ≤ n) :
    (n : ℝ) ^ (aCoef (numStages n) - 1) * (numStages n : ℝ) * Real.sqrt (Real.log n)
      ≤ Real.exp 1 * (1 / Real.log 2 + 1) * Real.log (Real.log n) * Real.sqrt (Real.log n) / Real.sqrt n := by
  have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrb := rate_bound_aux n (by omega)
  set L := Real.log (n : ℝ) with hL
  have hL1 : Real.exp 1 < L := by
    have h16 : Real.log 16 ≤ L := Real.log_le_log (by norm_num) hn16
    have h16' : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.exp_one_lt_d9
    have := Real.log_two_gt_d9
    linarith
  have hLL : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL1.le
    rw [Real.log_exp] at this; exact this
  have hlogb : Real.logb 2 L = Real.log L / Real.log 2 := rfl
  have hl : (numStages n : ℝ) ≤ Real.log L / Real.log 2 + 1 := by
    have h1 : (numStages n : ℝ) < Real.logb 2 L + 1 := by
      unfold numStages
      exact Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num)
        (show (1:ℝ) ≤ Real.log (n:ℝ) by linarith [hL1, Real.add_one_le_exp (1:ℝ)]))
    rw [hlogb] at h1; exact h1.le
  have hl' : (numStages n : ℝ) ≤ (1 / Real.log 2 + 1) * Real.log L := by
    have : Real.log L / Real.log 2 = (1 / Real.log 2) * Real.log L := by ring
    nlinarith
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hrb' : (n : ℝ) ^ (aCoef (numStages n) - 1) ≤ Real.exp 1 / Real.sqrt (n : ℝ) := by
    have : (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (n : ℝ) := by
      rw [Real.rpow_neg hnpos.le, Real.sqrt_eq_rpow]
      exact (one_div _).symm
    rw [this, mul_one_div] at hrb
    exact hrb
  have hρ0 : 0 ≤ (n : ℝ) ^ (aCoef (numStages n) - 1) := by positivity
  have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hℓ0 : (0 : ℝ) ≤ numStages n := Nat.cast_nonneg _
  calc (n : ℝ) ^ (aCoef (numStages n) - 1) * (numStages n : ℝ) * Real.sqrt L
      ≤ (Real.exp 1 / Real.sqrt (n : ℝ)) * ((1 / Real.log 2 + 1) * Real.log L) * Real.sqrt L := by
        apply mul_le_mul_of_nonneg_right _ hs0
        exact mul_le_mul hrb' hl' hℓ0 (by positivity)
    _ = Real.exp 1 * (1 / Real.log 2 + 1) * Real.log L * Real.sqrt L / Real.sqrt n := by ring

lemma eventually_big (T : ℝ) (hT : 0 < T) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → 12 * Real.log n ^ 2 ≤ T * Real.sqrt n := by
  have ho := (isLittleO_log_rpow_atTop (r := (1 / 4 : ℝ)) (by norm_num))
  have hc : 0 < Real.sqrt (T / 12) := Real.sqrt_pos.mpr (by positivity)
  have hb := ho.bound hc
  have hb' : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x ∧ ‖Real.log x‖ ≤ Real.sqrt (T / 12) * ‖x ^ (1 / 4 : ℝ)‖ :=
    (Filter.eventually_ge_atTop 1).and hb
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hb')
  refine ⟨n₁, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hn₁ n hn
  have hx0 : (0 : ℝ) ≤ n := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1),
    abs_of_nonneg (Real.rpow_nonneg hx0 _)] at h2
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg h1
  have hsq := mul_self_le_mul_self hl0 h2
  have e1 : (Real.sqrt (T / 12) * (n : ℝ) ^ (1 / 4 : ℝ)) * (Real.sqrt (T / 12) * (n : ℝ) ^ (1 / 4 : ℝ))
      = T / 12 * Real.sqrt n := by
    have : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) = Real.sqrt n := by
      rw [← Real.rpow_add' hx0 (by norm_num), Real.sqrt_eq_rpow]; norm_num
    have h2 : Real.sqrt (T / 12) * Real.sqrt (T / 12) = T / 12 := Real.mul_self_sqrt (by positivity)
    calc _ = (Real.sqrt (T / 12) * Real.sqrt (T / 12)) * ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ)) := by ring
      _ = T / 12 * Real.sqrt n := by rw [h2, this]
  rw [e1] at hsq
  nlinarith

end BZ635

open MeasureTheory ProbabilityTheory BesbesZeevi.SingleParam

namespace BZ635

lemma q_le (M T : ℝ) (hM : 0 < M) (hT : 0 < T) (n : ℕ) (hn : 16 ≤ n) :
    ((((⌈(n : ℝ) * M * T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(3 * Real.log n))))
      ≤ 2 * (M * T + 2) ^ 2 / n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hK : (((⌈(n : ℝ) * M * T⌉₊ : ℕ) : ℝ)) < (n : ℝ) * M * T + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hK1 : (((⌈(n : ℝ) * M * T⌉₊ : ℕ) : ℝ)) + 1 ≤ (n : ℝ) * (M * T + 2) := by nlinarith
  have hK0 : (0 : ℝ) ≤ (((⌈(n : ℝ) * M * T⌉₊ : ℕ) : ℝ)) + 1 := by positivity
  have hsq := mul_self_le_mul_self hK0 hK1
  have hexp : Real.exp (-(3 * Real.log n)) = 1 / (n : ℝ) ^ 3 := by
    rw [Real.exp_neg, one_div]
    congr 1
    rw [show (3 : ℝ) * Real.log n = Real.log ((n : ℝ) ^ 3) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [hexp, sq]
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  rw [show 2 * (M * T + 2) ^ 2 / (n : ℝ) = 2 * ((n : ℝ) * (M * T + 2) * ((n : ℝ) * (M * T + 2))) / (n : ℝ) ^ 3 by
    field_simp]
  rw [show ∀ a : ℝ, a * (2 * (1 / (n : ℝ) ^ 3)) = 2 * a / (n : ℝ) ^ 3 from fun a => by ring]
  apply div_le_div_of_nonneg_right _ hn3.le
  linarith

variable {D : Market} (F : Family D) (σ : Selection D F)

set_option maxHeartbeats 1000000 in
theorem main_thm :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : PoissonProcess Ω P), ∀ n : ℕ, n₀ ≤ n → ∀ θ ∈ F.Θ,
          tunedRegret N D F σ n θ
            ≤ C * Real.log (Real.log n) * Real.sqrt (Real.log n) / Real.sqrt n := by
  have hpHi0 : 0 < D.pHi := lt_trans D.pLo_pos D.pLo_lt_pHi
  have hT0 := D.T_pos
  have hα0 := F.α_pos
  have hM0 := F.M_pos
  have hK20 := F.K2_pos
  have hKLo0 := F.KLo_pos
  have hx0 := D.x_pos
  set cE := 10 + 4 * Real.sqrt (F.M + 2) with hcE
  set C3 := 2 * D.pHi * F.M * D.T
          + (5 * D.pHi * F.K2 + F.K2 * F.M / F.KLo) * F.α * Real.sqrt D.T * cE
          + 2 * D.pHi * cE * Real.sqrt D.T + D.pHi with hC3
  set Umax := D.pHi * (D.T * F.M + D.x) with hUmax
  set Q := Umax * (2 * (F.M * D.T + 2) ^ 2) with hQ
  set Ulow := F.m * min D.T (D.x / F.M) with hUlow
  have hUlow0 : 0 < Ulow := mul_pos F.m_pos (lt_min D.T_pos (div_pos D.x_pos F.M_pos))
  have hcE0 : 0 ≤ cE := by positivity
  have hC30 : 0 ≤ C3 := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C := Real.exp 1 * (1 / Real.log 2 + 1) * (C3 + Q) / Ulow with hC
  have hCpos : 0 < C := by
    have : 0 < C3 + Q := by
      have h3 : 0 < C3 := by rw [hC3]; positivity
      linarith
    positivity
  obtain ⟨n₁, hn₁⟩ := eventually_big D.T D.T_pos
  refine ⟨C, hCpos, max 16 n₁, fun Ω _ P _ N n hn θ hθ => ?_⟩
  have hn16 : 16 ≤ n := le_trans (le_max_left _ _) hn
  have hbig := hn₁ n (le_trans (le_max_right _ _) hn)
  have hn3 : 3 ≤ n := by omega
  have hn' : (0 : ℝ) < n := by norm_cast; omega
  have hu0 : 0 ≤ 3 * Real.log n := by have := log_ge_one n hn16; linarith
  have hpre := regret_pre σ N hθ n hn3 (3 * Real.log n) hu0
  have hE := ErrB_le F n hn16 hbig
  rw [← hcE, ← hC3] at hE
  have hq := q_le F.M D.T F.M_pos D.T_pos n hn16
  obtain ⟨hρ0, hρn, hsn1⟩ := rho_facts n hn16
  set ρ := (n : ℝ) ^ (aCoef (numStages n) - 1) with hρ
  set ℓ := (numStages n : ℝ) with hℓ
  set s := Real.sqrt (Real.log n) with hs
  have hℓ1 : (1 : ℝ) ≤ ℓ := by rw [hℓ]; exact_mod_cast numStages_pos n hn3
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (log_ge_one n hn16)
  have hnρ1 : 1 ≤ (n : ℝ) * ρ := le_trans hsn1 hρn
  have hall : 1 ≤ (n : ℝ) * ρ * ℓ * s := by
    have : 1 ≤ ℓ * s := by nlinarith
    nlinarith
  -- the q-term
  have hqt : (n : ℝ) * Umax
        * ((((⌈(n : ℝ) * F.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(3 * Real.log n))))
      ≤ (n : ℝ) * ρ * ℓ * s * Q := by
    have hU0 : 0 ≤ Umax := by rw [hUmax]; positivity
    have h1 := mul_le_mul_of_nonneg_left hq (mul_nonneg hn'.le hU0)
    have h2 : (n : ℝ) * Umax * (2 * (F.M * D.T + 2) ^ 2 / n) = Q := by
      rw [hQ]; field_simp
    rw [h2] at h1
    have h3 : Q ≤ (n : ℝ) * ρ * ℓ * s * Q := le_mul_of_one_le_left hQ0 hall
    exact le_trans h1 h3
  have hnum : ErrB F n (3 * Real.log n) + (n : ℝ) * Umax
        * ((((⌈(n : ℝ) * F.M * D.T⌉₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * Real.exp (-(3 * Real.log n))))
      ≤ (n : ℝ) * (ρ * ℓ * s * (C3 + Q)) := by
    have : (n : ℝ) * (ρ * ℓ * s * (C3 + Q)) = (n : ℝ) * ρ * ℓ * s * C3 + (n : ℝ) * ρ * ℓ * s * Q := by ring
    rw [this]; linarith
  have hrate := ls_rate n hn16
  rw [← hρ, ← hs, ← hℓ] at hrate
  have hrate' : ρ * ℓ * s ≤ Real.exp 1 * (1 / Real.log 2 + 1) * Real.log (Real.log n) * s / Real.sqrt n :=
    hrate
  refine le_trans hpre ?_
  rw [← hUmax, ← hUlow]
  have hden : 0 < (n : ℝ) * Ulow := mul_pos hn' hUlow0
  calc _ ≤ (n : ℝ) * (ρ * ℓ * s * (C3 + Q)) / ((n : ℝ) * Ulow) :=
        div_le_div_of_nonneg_right hnum hden.le
    _ = ρ * ℓ * s * (C3 + Q) / Ulow := by field_simp
    _ ≤ (Real.exp 1 * (1 / Real.log 2 + 1) * Real.log (Real.log n) * s / Real.sqrt n) * (C3 + Q) / Ulow := by
        apply div_le_div_of_nonneg_right _ hUlow0.le
        exact mul_le_mul_of_nonneg_right hrate' (by linarith)
    _ = C * Real.log (Real.log n) * s / Real.sqrt n := by rw [hC]; field_simp

end BZ635

open MeasureTheory BesbesZeevi.SingleParam in
theorem solution (D : Market) (F : Family D) (σ : Selection D F) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : PoissonProcess Ω P), ∀ n : ℕ, n₀ ≤ n → ∀ θ ∈ F.Θ,
          tunedRegret N D F σ n θ
            ≤ C * Real.log (Real.log n) * Real.sqrt (Real.log n) / Real.sqrt n := by
  exact BZ635.main_thm F σ
