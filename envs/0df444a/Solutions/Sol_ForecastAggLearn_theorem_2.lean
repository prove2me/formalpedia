-- Prove2me | solution 1 for ForecastAggLearn.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T12:13:27.589611+00:00
-- url     : https://prove2.me/submissions/e2dcb6a8-05c4-46e2-ac67-35798461eee7

import Mathlib
import Definitions.Def_ForecastAggLearn_jointLaw
import Definitions.Def_ForecastAggLearn_post
import Definitions.Def_ForecastAggLearn_logLoss
import Definitions.Def_ForecastAggLearn_evidenceMatrix
import Definitions.Def_ForecastAggLearn_PriorAwareAggregator
import Definitions.Def_ForecastAggLearn_aggregatorLoss
import Definitions.Def_ForecastAggLearn_benchmarkLoss

open MeasureTheory Matrix ForecastAggLearn Filter Topology

set_option autoImplicit false

universe u

namespace FAL77


lemma lintegral_pi_prod {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)] (f : ∀ i, α i → ENNReal)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi ν) = ∏ i, ∫⁻ y, f i y ∂(ν i) := by
  classical
  have hind := ProbabilityTheory.iIndepFun_pi (μ := ν) (X := fun i => f i)
    (fun i => (hf i).aemeasurable)
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (MeasureTheory.measurePreserving_eval ν i).lintegral_comp (hf i)

lemma indicator_pi_prod {ι : Type*} [Fintype ι] {α : ι → Type*} (s : ∀ i, Set (α i))
    (f : ∀ i, α i → ENNReal) (x : ∀ i, α i) :
    (Set.univ.pi s).indicator (fun y => ∏ i, f i (y i)) x = ∏ i, (s i).indicator (f i) (x i) := by
  classical
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
  · rw [Set.indicator_of_notMem hx]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

lemma pi_withDensity {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)] (f : ∀ i, α i → ENNReal)
    (hf : ∀ i, Measurable (f i)) (Q : ∀ i, Measure (α i)) [∀ i, SigmaFinite (Q i)]
    (hQ : ∀ i, Q i = (ν i).withDensity (f i)) :
    Measure.pi Q = (Measure.pi ν).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  refine Measure.pi_eq (μ := Q) (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [indicator_pi_prod]
  rw [lintegral_pi_prod ν _ (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [hQ i, withDensity_apply _ (hs i), lintegral_indicator (hs i)]

/-- Restricting a product of probability measures to a sub-family of coordinates. -/
lemma pi_map_restrict {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    (B : Finset ι) :
    (Measure.pi ν).map B.restrict = Measure.pi (fun j : B => ν j) := by
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply (Finset.measurable_restrict B) (MeasurableSet.univ_pi hs)]
  have hpre : B.restrict ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i => if h : i ∈ B then s ⟨i, h⟩ else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Finset.restrict]
    constructor
    · intro hx i
      by_cases h : i ∈ B
      · rw [dif_pos h]; exact hx ⟨i, h⟩
      · rw [dif_neg h]; trivial
    · intro hx i
      have := hx i
      rw [dif_pos i.2] at this
      exact this
  rw [hpre, Measure.pi_pi]
  have : ∀ i, ν i (if h : i ∈ B then s ⟨i, h⟩ else Set.univ) =
      (if h : i ∈ B then ν i (s ⟨i, h⟩) else 1) := by
    intro i
    by_cases h : i ∈ B
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, measure_univ]
  simp_rw [this]
  rw [Fintype.prod_dite]
  simp only [Finset.prod_const_one, mul_one]
  exact Finset.prod_congr (by ext x; simp) (fun _ _ => rfl)

/-- ENNReal arithmetic for the `ω = 1` calibration bound. -/
lemma enn_true (N D : ENNReal) (a : ℝ) (ha : 0 < a) (h : (N / (N + D)).toReal ≤ a) :
    N ≤ ENNReal.ofReal a * (N + D) := by
  by_cases hND : N + D = ⊤
  · rw [hND, ENNReal.mul_top (ENNReal.ofReal_pos.mpr ha).ne']
    exact le_top
  by_cases h0 : N + D = 0
  · have hN : N = 0 := (add_eq_zero.mp h0).1
    rw [hN]
    simp
  have hNt : N ≠ ⊤ := ne_top_of_le_ne_top hND le_self_add
  have hle : N / (N + D) ≠ ⊤ := ENNReal.div_ne_top hNt h0
  have h2 : N / (N + D) ≤ ENNReal.ofReal a := (ENNReal.le_ofReal_iff_toReal_le hle ha.le).mpr h
  exact (ENNReal.div_le_iff h0 hND).mp h2

/-- ENNReal arithmetic for the `ω = 0` calibration bound. -/
lemma enn_false (N D : ENNReal) (a : ℝ) (h : 1 - a ≤ (N / (N + D)).toReal) :
    D ≤ ENNReal.ofReal a * (D + N) := by
  by_cases ha1 : 1 ≤ a
  · calc D ≤ D + N := le_self_add
      _ = 1 * (D + N) := (one_mul _).symm
      _ ≤ ENNReal.ofReal a * (D + N) := by
        gcongr
        exact ENNReal.one_le_ofReal.mpr ha1
  rw [not_le] at ha1
  have hpos : 0 < (N / (N + D)).toReal := by linarith
  have hne0 : N / (N + D) ≠ 0 := fun h' => by rw [h', ENNReal.toReal_zero] at hpos; exact lt_irrefl _ hpos
  have hnetop : N / (N + D) ≠ ⊤ := fun h' => by rw [h', ENNReal.toReal_top] at hpos; exact lt_irrefl _ hpos
  rw [ne_eq, ENNReal.div_eq_zero_iff, not_or] at hne0
  obtain ⟨hN0, hNDt⟩ := hne0
  have hNt : N ≠ ⊤ := ne_top_of_le_ne_top hNDt le_self_add
  have hDt : D ≠ ⊤ := ne_top_of_le_ne_top hNDt le_add_self
  have hn0 : 0 < N.toReal := ENNReal.toReal_pos hN0 hNt
  have hd0 : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  rw [ENNReal.toReal_div, ENNReal.toReal_add hNt hDt] at h
  have hsum : 0 < N.toReal + D.toReal := by linarith
  rw [le_div_iff₀ hsum] at h
  have hfrac : N.toReal / (N.toReal + D.toReal) ≤ 1 := by
    rw [div_le_one hsum]; linarith
  have ha0 : 0 ≤ a := by nlinarith
  have hR : ENNReal.ofReal a * (D + N) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨hDt, hNt⟩)
  rw [← ENNReal.toReal_le_toReal hDt hR, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0,
    ENNReal.toReal_add hDt hNt]
  nlinarith

/-- Core of the calibration bound: a posterior-type ratio bounded on `E` bounds the mass of `E`. -/
lemma calib_core {X : Type*} [MeasurableSpace X] (ρ : Measure X) (D1 D0 : X → ENNReal)
    (hD1 : Measurable D1) (hD0 : Measurable D0) (c1 c0 a : ENNReal) (E : Set X)
    (hE : MeasurableSet E) (hpt : ∀ x ∈ E, c1 * D1 x ≤ a * (c1 * D1 x + c0 * D0 x))
    (h1 : ρ.withDensity D1 Set.univ ≤ 1) (h0 : ρ.withDensity D0 Set.univ ≤ 1) :
    c1 * ρ.withDensity D1 E ≤ a * (c1 + c0) := by
  have e1 : ∫⁻ x in E, D1 x ∂ρ ≤ 1 := by
    rw [← withDensity_apply _ hE]; exact le_trans (measure_mono (Set.subset_univ _)) h1
  have e0 : ∫⁻ x in E, D0 x ∂ρ ≤ 1 := by
    rw [← withDensity_apply _ hE]; exact le_trans (measure_mono (Set.subset_univ _)) h0
  rw [withDensity_apply _ hE, ← lintegral_const_mul _ hD1]
  calc ∫⁻ x in E, c1 * D1 x ∂ρ ≤ ∫⁻ x in E, a * (c1 * D1 x + c0 * D0 x) ∂ρ :=
        setLIntegral_mono' hE hpt
    _ = a * (c1 * ∫⁻ x in E, D1 x ∂ρ + c0 * ∫⁻ x in E, D0 x ∂ρ) := by
        have hm : Measurable (fun x => c1 * D1 x + c0 * D0 x) := by fun_prop
        rw [lintegral_const_mul a hm, lintegral_add_left (hD1.const_mul c1),
          lintegral_const_mul _ hD1, lintegral_const_mul _ hD0]
    _ ≤ a * (c1 * 1 + c0 * 1) := by gcongr
    _ = a * (c1 + c0) := by rw [mul_one, mul_one]

/-- The posterior as a function of the restricted signal profile. -/
noncomputable def postG {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℝ) (P : (j : Fin m) → Bool → Measure (S j)) (B : Finset (Fin m))
    (r : ∀ j : B, S j) : ℝ :=
  ((ENNReal.ofReal μ * ∏ j : B, (P j true).rnDeriv (P j false + P j true) (r j)) /
    (ENNReal.ofReal μ * ∏ j : B, (P j true).rnDeriv (P j false + P j true) (r j) +
      ENNReal.ofReal (1 - μ) * ∏ j : B, (P j false).rnDeriv (P j false + P j true) (r j))).toReal

lemma post_eq_postG {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℝ) (P : (j : Fin m) → Bool → Measure (S j)) (B : Finset (Fin m)) (s : ∀ j, S j) :
    post μ P B s = postG μ P B (B.restrict s) := by
  simp only [post, postG, Finset.restrict]
  rw [Finset.prod_coe_sort B (fun j => (P j true).rnDeriv (P j false + P j true) (s j)),
    Finset.prod_coe_sort B (fun j => (P j false).rnDeriv (P j false + P j true) (s j))]

lemma measurable_postG {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℝ) (P : (j : Fin m) → Bool → Measure (S j)) (B : Finset (Fin m)) :
    Measurable (postG μ P B) := by
  have h1 : ∀ b, Measurable (fun r : (∀ j : B, S j) =>
      ∏ j : B, (P j b).rnDeriv (P j false + P j true) (r j)) := fun b =>
    Finset.measurable_prod _ (fun j _ => (Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply j))
  unfold postG
  exact (((h1 true).const_mul _).div (((h1 true).const_mul _).add ((h1 false).const_mul _))).ennreal_toReal

lemma measurable_post {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℝ) (P : (j : Fin m) → Bool → Measure (S j)) (B : Finset (Fin m)) :
    Measurable (post μ P B) := by
  have : post μ P B = postG μ P B ∘ B.restrict := funext (post_eq_postG μ P B)
  rw [this]
  exact (measurable_postG μ P B).comp (Finset.measurable_restrict B)

/-- The half-mixture reference measure (a probability measure). -/
noncomputable def refm {X : Type*} [MeasurableSpace X] (P0 P1 : Measure X) : Measure X :=
  (2 : ENNReal)⁻¹ • (P0 + P1)

lemma refm_prob {X : Type*} [MeasurableSpace X] (P0 P1 : Measure X) [IsProbabilityMeasure P0]
    [IsProbabilityMeasure P1] : IsProbabilityMeasure (refm P0 P1) := by
  constructor
  rw [refm, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

lemma eq_half_withDensity {X : Type*} [MeasurableSpace X] (Pb ν0 : Measure X)
    [IsFiniteMeasure Pb] [IsFiniteMeasure ν0] (hac : Pb ≪ ν0) :
    Pb = ((2 : ENNReal)⁻¹ • ν0).withDensity (fun x => 2 * Pb.rnDeriv ν0 x) := by
  have h2 : (fun x => 2 * Pb.rnDeriv ν0 x) = (2 : ENNReal) • Pb.rnDeriv ν0 := by
    funext x; simp [smul_eq_mul]
  rw [h2, withDensity_smul _ (Measure.measurable_rnDeriv _ _), withDensity_smul_measure,
    Measure.withDensity_rnDeriv_eq _ _ hac, smul_smul,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_smul]

lemma eq_refm_withDensity {X : Type*} [MeasurableSpace X] (P0 P1 : Measure X)
    [IsFiniteMeasure P0] [IsFiniteMeasure P1] (b : Bool) :
    (if b then P1 else P0) = (refm P0 P1).withDensity
      (fun x => 2 * (if b then P1 else P0).rnDeriv (P0 + P1) x) := by
  cases b
  · exact eq_half_withDensity P0 (P0 + P1)
      (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl))
  · exact eq_half_withDensity P1 (P0 + P1)
      (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))

/-- Product density of the restricted conditional law wrt the restricted half-mixture. -/
noncomputable def dens {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (P : (j : Fin m) → Bool → Measure (S j)) (B : Finset (Fin m)) (b : Bool)
    (r : ∀ j : B, S j) : ENNReal :=
  ∏ j : B, 2 * (if b then P j true else P j false).rnDeriv (P j false + P j true) (r j)

lemma measurable_dens {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (P : (j : Fin m) → Bool → Measure (S j)) (B : Finset (Fin m)) (b : Bool) :
    Measurable (dens P B b) :=
  Finset.measurable_prod _ (fun j _ =>
    ((Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply j)).const_mul 2)

lemma pi_eq_dens {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (P : (j : Fin m) → Bool → Measure (S j)) [∀ j b, IsProbabilityMeasure (P j b)]
    (B : Finset (Fin m)) (b : Bool) :
    Measure.pi (fun j : B => P j b) =
      (Measure.pi (fun j : B => refm (P j false) (P j true))).withDensity (dens P B b) := by
  have : ∀ j, IsProbabilityMeasure (refm (P j false) (P j true)) := fun j => refm_prob _ _
  refine pi_withDensity _ (fun (j : B) x =>
    2 * (if b then P j true else P j false).rnDeriv (P j false + P j true) x)
    (fun j => ((Measure.measurable_rnDeriv _ _).const_mul 2)) _ (fun j => ?_)
  have := eq_refm_withDensity (P j false) (P j true) b
  cases b <;> simpa using this

lemma dens_eq {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (P : (j : Fin m) → Bool → Measure (S j)) (B : Finset (Fin m)) (b : Bool)
    (r : ∀ j : B, S j) :
    dens P B b r = 2 ^ (Fintype.card B) *
      ∏ j : B, (if b then P j true else P j false).rnDeriv (P j false + P j true) (r j) := by
  simp only [dens, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

lemma dens_univ_le {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (P : (j : Fin m) → Bool → Measure (S j)) [∀ j b, IsProbabilityMeasure (P j b)]
    (B : Finset (Fin m)) (b : Bool) :
    (Measure.pi (fun j : B => refm (P j false) (P j true))).withDensity (dens P B b) Set.univ ≤ 1 := by
  rw [← pi_eq_dens]; exact le_of_eq measure_univ

lemma scale_le (K X Y a : ENNReal) (h : X ≤ a * (X + Y)) : K * X ≤ a * (K * X + K * Y) :=
  calc K * X ≤ K * (a * (X + Y)) := by gcongr
    _ = a * (K * X + K * Y) := by ring

lemma ofReal_sum_one {μ : ℝ} (hμ : μ ∈ Set.Icc (0:ℝ) 1) :
    ENNReal.ofReal μ + ENNReal.ofReal (1 - μ) = 1 := by
  rw [← ENNReal.ofReal_add hμ.1 (by linarith [hμ.2])]; simp

/-- C1 (true side): `P(ω = 1, F_B ≤ a) ≤ a`. -/
theorem calib_true {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)] (μ : ℝ)
    (hμ : μ ∈ Set.Icc (0:ℝ) 1) (P : (j : Fin m) → Bool → Measure (S j))
    [∀ j b, IsProbabilityMeasure (P j b)] (B : Finset (Fin m)) (a : ℝ) (ha : 0 < a) :
    jointLaw μ P {x | x.1 = true ∧ post μ P B x.2 ≤ a} ≤ ENNReal.ofReal a := by
  classical
  set E' : Set (∀ j : B, S j) := {r | postG μ P B r ≤ a} with hE'
  have hE'm : MeasurableSet E' := measurableSet_le (measurable_postG μ P B) measurable_const
  have hset : {x : Bool × (∀ j, S j) | x.1 = true ∧ post μ P B x.2 ≤ a} =
      {true} ×ˢ (B.restrict ⁻¹' E') := by
    ext ⟨b, s⟩
    simp [hE', post_eq_postG]
  have hJ : jointLaw μ P ({true} ×ˢ (B.restrict ⁻¹' E')) =
      ENNReal.ofReal μ * Measure.pi (fun j => P j true) (B.restrict ⁻¹' E') := by
    simp only [jointLaw, Measure.add_apply, Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
    simp
  rw [hset, hJ, ← Measure.map_apply (Finset.measurable_restrict B) hE'm, pi_map_restrict,
    pi_eq_dens, ← mul_one (ENNReal.ofReal a), ← ofReal_sum_one hμ]
  refine calib_core _ _ _ (measurable_dens P B true) (measurable_dens P B false) _ _ _ E' hE'm
    ?_ (dens_univ_le P B true) (dens_univ_le P B false)
  intro r hr
  have key := enn_true _ _ a ha hr
  rw [dens_eq, dens_eq]
  simp only [if_true, Bool.false_eq_true, if_false]
  have := scale_le (2 ^ Fintype.card B) _ _ _ key
  calc _ = 2 ^ Fintype.card B * (ENNReal.ofReal μ *
          ∏ j : B, (P j true).rnDeriv (P j false + P j true) (r j)) := by ring
    _ ≤ _ := this
    _ = _ := by ring

/-- C1 (false side): `P(ω = 0, F_B ≥ 1 - a) ≤ a`. -/
theorem calib_false {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)] (μ : ℝ)
    (hμ : μ ∈ Set.Icc (0:ℝ) 1) (P : (j : Fin m) → Bool → Measure (S j))
    [∀ j b, IsProbabilityMeasure (P j b)] (B : Finset (Fin m)) (a : ℝ) :
    jointLaw μ P {x | x.1 = false ∧ 1 - a ≤ post μ P B x.2} ≤ ENNReal.ofReal a := by
  classical
  set E' : Set (∀ j : B, S j) := {r | 1 - a ≤ postG μ P B r} with hE'
  have hE'm : MeasurableSet E' := measurableSet_le measurable_const (measurable_postG μ P B)
  have hset : {x : Bool × (∀ j, S j) | x.1 = false ∧ 1 - a ≤ post μ P B x.2} =
      {false} ×ˢ (B.restrict ⁻¹' E') := by
    ext ⟨b, s⟩
    simp [hE', post_eq_postG]
  have hJ : jointLaw μ P ({false} ×ˢ (B.restrict ⁻¹' E')) =
      ENNReal.ofReal (1 - μ) * Measure.pi (fun j => P j false) (B.restrict ⁻¹' E') := by
    simp only [jointLaw, Measure.add_apply, Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
    simp
  rw [hset, hJ, ← Measure.map_apply (Finset.measurable_restrict B) hE'm, pi_map_restrict,
    pi_eq_dens, ← mul_one (ENNReal.ofReal a), ← ofReal_sum_one hμ, add_comm (ENNReal.ofReal μ)]
  refine calib_core _ _ _ (measurable_dens P B false) (measurable_dens P B true) _ _ _ E' hE'm
    ?_ (dens_univ_le P B false) (dens_univ_le P B true)
  intro r hr
  have key := enn_false _ _ a hr
  rw [dens_eq, dens_eq]
  simp only [if_true, Bool.false_eq_true, if_false]
  have := scale_le (2 ^ Fintype.card B) _ _ _ key
  calc _ = 2 ^ Fintype.card B * (ENNReal.ofReal (1 - μ) *
          ∏ j : B, (P j false).rnDeriv (P j false + P j true) (r j)) := by ring
    _ ≤ _ := this
    _ = _ := by ring

lemma post_empty {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)] (μ : ℝ)
    (hμ : μ ∈ Set.Icc (0:ℝ) 1) (P : (j : Fin m) → Bool → Measure (S j)) (s : ∀ j, S j) :
    post μ P ∅ s = μ := by
  simp only [post, Finset.prod_empty, mul_one]
  rw [ofReal_sum_one hμ, div_one, ENNReal.toReal_ofReal hμ.1]

/-- Forecast used in an extreme period. -/
noncomputable def extF (δ : ℝ) (lo hi : Prop) [Decidable lo] [Decidable hi] : ℝ :=
  if lo ∧ hi then 1 / 2 else if lo then δ else 1 - δ

lemma neg_log_one_sub_le {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) : -Real.log (1 - δ) ≤ 2 * δ := by
  have h1 : 0 < 1 - δ := by linarith
  have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  rw [Real.log_inv] at this
  have h2 : (1 - δ)⁻¹ - 1 ≤ 2 * δ := by
    rw [inv_eq_one_div, div_sub_one h1.ne', div_le_iff₀ h1]; nlinarith
  linarith

lemma ext_loss (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (lo hi : Prop) [Decidable lo] [Decidable hi]
    (h : lo ∨ hi) (ω : Bool) :
    logLoss (extF δ lo hi) ω ≤ ENNReal.ofReal (2 * δ) + ENNReal.ofReal (Real.log (1 / δ)) *
      ((if ω = true ∧ lo then 1 else 0) + (if ω = false ∧ hi then 1 else 0)) := by
  have hL2 : Real.log 2 ≤ Real.log (1 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ0]; linarith)
  have hA : ∀ x : ℝ, x ≤ 2 * δ → ∀ c : ENNReal,
      ENNReal.ofReal x ≤ ENNReal.ofReal (2 * δ) + c := fun x hx c =>
    le_trans (ENNReal.ofReal_le_ofReal hx) le_self_add
  have hB : ∀ x : ℝ, x ≤ Real.log (1 / δ) →
      ENNReal.ofReal x ≤ ENNReal.ofReal (2 * δ) + ENNReal.ofReal (Real.log (1 / δ)) * 1 := by
    intro x hx
    rw [mul_one]
    exact le_trans (ENNReal.ofReal_le_ofReal hx) le_add_self
  have hlogd : -Real.log δ ≤ Real.log (1 / δ) := by rw [one_div, Real.log_inv]
  have hlog2 : -Real.log (1 - 1 / 2) ≤ Real.log (1 / δ) := by
    rw [(by norm_num : (1:ℝ) - 1 / 2 = (2:ℝ)⁻¹), Real.log_inv, neg_neg]; exact hL2
  have hlog2' : -Real.log (1 / 2) ≤ Real.log (1 / δ) := by
    rw [one_div, Real.log_inv, neg_neg]; exact hL2
  have h1d : -Real.log (1 - (1 - δ)) ≤ Real.log (1 / δ) := by rw [sub_sub_cancel]; exact hlogd
  have hn1 : ¬ (1 : ℝ) ≤ 1 / 2 := by norm_num
  have hn2 : ¬ (1 / 2 : ℝ) ≤ 0 := by norm_num
  have hn3 : ¬ (1 : ℝ) ≤ δ := by linarith
  have hn4 : ¬ (δ ≤ 0) := by linarith
  have hn5 : ¬ (1 - δ ≤ 0) := by linarith
  have hn6 : ¬ (1 : ℝ) ≤ 1 - δ := by linarith
  have hlo1 := neg_log_one_sub_le hδ0 hδ
  unfold extF logLoss
  cases ω <;> by_cases hl : lo <;> by_cases hh : hi <;>
    simp only [hl, hh, and_self, and_true, and_false, if_true, if_false,
      Bool.false_eq_true, hn1, hn2, hn3, hn4, hn5, hn6, add_zero, zero_add, Bool.true_eq_false]
  all_goals first
    | exact absurd h (by tauto)
    | exact hA _ hlo1 _
    | exact hB _ hlogd
    | exact hB _ hlog2
    | exact hB _ hlog2'
    | exact hB _ h1d

abbrev loP {n : ℕ} (τ μ : ℝ) (F : Fin n → ℝ) : Prop := μ < τ ∨ ∃ i, F i < τ

abbrev hiP {n : ℕ} (τ μ : ℝ) (F : Fin n → ℝ) : Prop := 1 - τ < μ ∨ ∃ i, 1 - τ < F i

/-- Expert forecast profile. -/
noncomputable def Fv {n m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)] (μ : ℝ)
    (P : (j : Fin m) → Bool → Measure (S j)) (A : Fin n → Finset (Fin m)) (s : ∀ j, S j) :
    Fin n → ℝ := fun i => post μ P (A i) s

lemma jointLaw_univ {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)] (μ : ℝ)
    (hμ : μ ∈ Set.Icc (0:ℝ) 1) (P : (j : Fin m) → Bool → Measure (S j))
    [∀ j b, IsProbabilityMeasure (P j b)] : jointLaw μ P Set.univ = 1 := by
  simp only [jointLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ofReal_sum_one hμ

/-- C5': expected loss of an extreme period. -/
theorem ext_major {n m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)] (μ : ℝ)
    (hμ : μ ∈ Set.Icc (0:ℝ) 1) (P : (j : Fin m) → Bool → Measure (S j))
    [∀ j b, IsProbabilityMeasure (P j b)] (A : Fin n → Finset (Fin m)) (τ δ : ℝ) (hτ : 0 < τ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hnτ : (n + 1) * τ ≤ δ) :
    ∃ g : Bool × (∀ j, S j) → ENNReal, Measurable g ∧
      (∀ y, (if loP τ μ (Fv μ P A y.2) ∨ hiP τ μ (Fv μ P A y.2) then
        logLoss (extF δ (loP τ μ (Fv μ P A y.2)) (hiP τ μ (Fv μ P A y.2))) y.1 else 0) ≤ g y) ∧
      ∫⁻ y, g y ∂(jointLaw μ P) ≤ ENNReal.ofReal (2 * δ + 2 * δ * Real.log (1 / δ)) := by
  classical
  set L := Real.log (1 / δ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  set Sa := {y : Bool × (∀ j, S j) | y.1 = true ∧ loP τ μ (Fv μ P A y.2)} with hSa
  set Sb := {y : Bool × (∀ j, S j) | y.1 = false ∧ hiP τ μ (Fv μ P A y.2)} with hSb
  have hmF : ∀ i, Measurable (fun y : Bool × (∀ j, S j) => post μ P (A i) y.2) := fun i =>
    (measurable_post μ P (A i)).comp measurable_snd
  have hfst : ∀ b : Bool, Measurable (fun y : Bool × (∀ j, S j) => y.1 = b) := fun b =>
    measurableSet_setOfPred.mp (measurable_fst (measurableSet_singleton b))
  have hSam : MeasurableSet Sa := by
    refine measurableSet_setOfPred.mpr ((hfst true).and (measurable_const.or
      (Measurable.exists fun i => ?_)))
    exact measurableSet_setOfPred.mp (measurableSet_lt (hmF i) measurable_const)
  have hSbm : MeasurableSet Sb := by
    refine measurableSet_setOfPred.mpr ((hfst false).and (measurable_const.or
      (Measurable.exists fun i => ?_)))
    exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const (hmF i))
  have hpt : ∀ y : Bool × (∀ j, S j),
      (if loP τ μ (Fv μ P A y.2) ∨ hiP τ μ (Fv μ P A y.2) then
        logLoss (extF δ (loP τ μ (Fv μ P A y.2)) (hiP τ μ (Fv μ P A y.2))) y.1 else 0) ≤
      ENNReal.ofReal (2 * δ) + ENNReal.ofReal L * (Sa.indicator 1 y + Sb.indicator 1 y) := by
    intro y
    split_ifs with hy
    · have := ext_loss δ hδ0 hδ _ _ hy y.1
      simp only [Set.indicator_apply, hSa, hSb, Set.mem_ofPred_eq, Pi.one_apply]
      exact this
    · exact bot_le
  have hcount : ENNReal.ofReal τ + ∑ _i : Fin n, ENNReal.ofReal τ ≤ ENNReal.ofReal δ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
      ← ENNReal.ofReal_add hτ.le (mul_nonneg (Nat.cast_nonneg n) hτ.le)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hJa : jointLaw μ P Sa ≤ ENNReal.ofReal δ := by
    have hsub : Sa ⊆ {y | y.1 = true ∧ post μ P ∅ y.2 ≤ τ} ∪
        ⋃ i, {y | y.1 = true ∧ post μ P (A i) y.2 ≤ τ} := by
      intro y hy
      obtain ⟨h1, h2⟩ := hy
      rcases h2 with h2 | ⟨i, hi⟩
      · left; exact ⟨h1, by rw [post_empty μ hμ]; exact h2.le⟩
      · right; exact Set.mem_iUnion.mpr ⟨i, h1, hi.le⟩
    calc jointLaw μ P Sa ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal τ + ∑ _i : Fin n, ENNReal.ofReal τ := by
        gcongr
        · exact calib_true μ hμ P ∅ τ hτ
        · exact le_trans (measure_iUnion_fintype_le _ _)
            (Finset.sum_le_sum fun i _ => calib_true μ hμ P (A i) τ hτ)
      _ ≤ _ := hcount
  have hJb : jointLaw μ P Sb ≤ ENNReal.ofReal δ := by
    have hsub : Sb ⊆ {y | y.1 = false ∧ 1 - τ ≤ post μ P ∅ y.2} ∪
        ⋃ i, {y | y.1 = false ∧ 1 - τ ≤ post μ P (A i) y.2} := by
      intro y hy
      obtain ⟨h1, h2⟩ := hy
      rcases h2 with h2 | ⟨i, hi⟩
      · left; exact ⟨h1, by rw [post_empty μ hμ]; exact h2.le⟩
      · right; exact Set.mem_iUnion.mpr ⟨i, h1, hi.le⟩
    calc jointLaw μ P Sb ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal τ + ∑ _i : Fin n, ENNReal.ofReal τ := by
        gcongr
        · exact calib_false μ hμ P ∅ τ
        · exact le_trans (measure_iUnion_fintype_le _ _)
            (Finset.sum_le_sum fun i _ => calib_false μ hμ P (A i) τ)
      _ ≤ _ := hcount
  have hind : Measurable (fun y : Bool × (∀ j, S j) =>
      Sa.indicator (1 : Bool × (∀ j, S j) → ENNReal) y +
        Sb.indicator (1 : Bool × (∀ j, S j) → ENNReal) y) :=
    by
      have h1 : Measurable (Sa.indicator (1 : Bool × (∀ j, S j) → ENNReal)) :=
        measurable_one.indicator hSam
      have h2 : Measurable (Sb.indicator (1 : Bool × (∀ j, S j) → ENNReal)) :=
        measurable_one.indicator hSbm
      exact h1.add h2
  refine ⟨fun y => ENNReal.ofReal (2 * δ) + ENNReal.ofReal L * (Sa.indicator 1 y + Sb.indicator 1 y),
    measurable_const.add (measurable_const.mul hind), hpt, ?_⟩
  show ∫⁻ y, ENNReal.ofReal (2 * δ) + ENNReal.ofReal L * (Sa.indicator 1 y + Sb.indicator 1 y)
      ∂(jointLaw μ P) ≤ _
  calc
    _ = ENNReal.ofReal (2 * δ) * jointLaw μ P Set.univ +
        ENNReal.ofReal L * (jointLaw μ P Sa + jointLaw μ P Sb) := by
      rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ hind,
        lintegral_add_left (measurable_one.indicator hSam), lintegral_indicator_one hSam,
        lintegral_indicator_one hSbm]
    _ ≤ ENNReal.ofReal (2 * δ) * 1 + ENNReal.ofReal L * (ENNReal.ofReal δ + ENNReal.ofReal δ) := by
      rw [jointLaw_univ μ hμ P]
      gcongr
    _ = ENNReal.ofReal (2 * δ + 2 * δ * L) := by
      rw [mul_one, ← ENNReal.ofReal_add hδ0.le hδ0.le, ← ENNReal.ofReal_mul hL0,
        ← ENNReal.ofReal_add (by linarith) (by positivity)]
      congr 1
      ring


/-- C3: a dual weight vector `h` with `Aᵀ h = 1` and coordinates bounded by `√m / σ`. -/
lemma exists_dual_weights {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hA : ∀ y : EuclideanSpace ℝ (Fin m), σ * ‖y‖ ≤
      ‖(WithLp.toLp 2 (A.mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖) :
    ∃ h : Fin n → ℝ, (∀ j, ∑ i, h i * A i j = 1) ∧ ∀ i, |h i| ≤ Real.sqrt m / σ := by
  have hnorm : ∀ {k : ℕ} (v : Fin k → ℝ),
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin k))‖ = Real.sqrt (v ⬝ᵥ v) := by
    intro k v
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [dotProduct, Real.norm_eq_abs, sq_abs, sq]
  have hdd : ∀ {k : ℕ} (v : Fin k → ℝ), 0 ≤ v ⬝ᵥ v := by
    intro k v
    simp only [dotProduct]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have hA' : ∀ y : Fin m → ℝ, σ * Real.sqrt (y ⬝ᵥ y) ≤ Real.sqrt ((A *ᵥ y) ⬝ᵥ (A *ᵥ y)) := by
    intro y
    have h1 := hA (WithLp.toLp 2 y)
    have h2 := hnorm (k := m) y
    have h3 := hnorm (k := n) (A *ᵥ y)
    simp only [WithLp.ofLp_toLp] at h1
    rw [h2, h3] at h1
    exact h1
  have hquad : ∀ y : Fin m → ℝ, y ⬝ᵥ ((Aᵀ * A) *ᵥ y) = (A *ᵥ y) ⬝ᵥ (A *ᵥ y) := by
    intro y
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have hinj : Function.Injective (Aᵀ * A).mulVec := by
    intro y1 y2 h12
    have hz : (Aᵀ * A) *ᵥ (y1 - y2) = 0 := by rw [mulVec_sub, h12, sub_self]
    have h0 : (A *ᵥ (y1 - y2)) ⬝ᵥ (A *ᵥ (y1 - y2)) = 0 := by
      rw [← hquad, hz, dotProduct_zero]
    have h4 := hA' (y1 - y2)
    rw [h0, Real.sqrt_zero] at h4
    have h5 : Real.sqrt ((y1 - y2) ⬝ᵥ (y1 - y2)) = 0 :=
      le_antisymm (by
        by_contra hc
        rw [not_le] at hc
        have := mul_pos hσ hc
        linarith) (Real.sqrt_nonneg _)
    have h6 : (y1 - y2) ⬝ᵥ (y1 - y2) = 0 := by
      have := (Real.sqrt_eq_zero (hdd (y1 - y2))).mp h5
      exact this
    have h7 : y1 - y2 = 0 := dotProduct_self_eq_zero.mp h6
    exact sub_eq_zero.mp h7
  have hunit : IsUnit (Aᵀ * A) := (Matrix.mulVec_injective_iff_isUnit).mp hinj
  have hdet : IsUnit (Aᵀ * A).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  set y : Fin m → ℝ := (Aᵀ * A)⁻¹ *ᵥ (fun _ => (1 : ℝ)) with hy
  have hGy : (Aᵀ * A) *ᵥ y = fun _ => (1 : ℝ) := by
    rw [hy, mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  refine ⟨A *ᵥ y, ?_, ?_⟩
  · intro j
    have h1 : (A *ᵥ y) ᵥ* A = fun _ => (1 : ℝ) := by
      rw [← mulVec_transpose, mulVec_mulVec, hGy]
    have h2 := congrFun h1 j
    simpa [vecMul, dotProduct] using h2
  · intro i
    set h : Fin n → ℝ := A *ᵥ y with hh
    have hhh : h ⬝ᵥ h = ∑ j, y j := by
      rw [hh, ← hquad, hGy]
      simp [dotProduct]
    have hcs : (∑ j, y j) ^ 2 ≤ (m : ℝ) * (y ⬝ᵥ y) := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := y)
      simpa [dotProduct, sq, Finset.card_univ, Fintype.card_fin] using this
    have hσy := hA' y
    rw [← hh] at hσy
    set H := Real.sqrt (h ⬝ᵥ h) with hH
    set Y := Real.sqrt (y ⬝ᵥ y) with hY
    have hH0 : 0 ≤ H := Real.sqrt_nonneg _
    have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
    have hHsq : H ^ 2 = ∑ j, y j := by rw [hH, Real.sq_sqrt (hdd h), hhh]
    have hYsq : Y ^ 2 = y ⬝ᵥ y := by rw [hY, Real.sq_sqrt (hdd y)]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hsm : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0
    have hsm0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
    -- H^2 = Σ y ≤ √m Y
    have hsumle : ∑ j, y j ≤ Real.sqrt m * Y := by
      have h1 : (∑ j, y j) ^ 2 ≤ (Real.sqrt m * Y) ^ 2 := by
        rw [mul_pow, hsm, hYsq]; exact hcs
      exact abs_le_of_sq_le_sq' h1 (mul_nonneg hsm0 hY0) |>.2
    have hHle : H ≤ Real.sqrt m / σ := by
      rw [le_div_iff₀ hσ]
      -- H^2 ≤ √m Y and σ Y ≤ H
      have h1 : H ^ 2 ≤ Real.sqrt m * Y := hHsq ▸ hsumle
      rcases eq_or_lt_of_le hH0 with h0 | hpos
      · rw [← h0]; simp
      · have h2 : σ * (H ^ 2) ≤ Real.sqrt m * (σ * Y) := by nlinarith
        have h3 : σ * (H ^ 2) ≤ Real.sqrt m * H := by nlinarith
        nlinarith
    have hi : |h i| ≤ H := by
      rw [hH]
      apply Real.abs_le_sqrt
      simp only [dotProduct]
      have := Finset.single_le_sum (f := fun j => h j * h j) (fun j _ => mul_self_nonneg (h j))
        (Finset.mem_univ i)
      simpa [sq] using this
    exact le_trans hi hHle






/-- Logistic function. -/
noncomputable def sig (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-- Log-odds. -/
noncomputable def logit (p : ℝ) : ℝ := Real.log p - Real.log (1 - p)

lemma sig_pos (x : ℝ) : 0 < sig x := by
  unfold sig; positivity

lemma sig_lt_one (x : ℝ) : sig x < 1 := by
  unfold sig
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos (-x)]

lemma one_sub_sig (x : ℝ) : 1 - sig x = sig (-x) := by
  unfold sig
  have h1 : 0 < 1 + Real.exp (-x) := by positivity
  have h2 : 0 < 1 + Real.exp (- -x) := by positivity
  rw [neg_neg]
  field_simp
  have : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

lemma sig_logit {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : sig (logit p) = p := by
  unfold sig logit
  have hq : 0 < 1 - p := by linarith
  rw [neg_sub, Real.exp_sub, Real.exp_log hq, Real.exp_log h0]
  field_simp
  ring

/-- `-log (sig a) ≤ -log (sig b) + |a - b|`. -/
lemma neg_log_sig_le (a b : ℝ) : -Real.log (sig a) ≤ -Real.log (sig b) + |a - b| := by
  unfold sig
  rw [one_div, Real.log_inv, neg_neg, one_div, Real.log_inv, neg_neg]
  have hb : 0 < 1 + Real.exp (-b) := by positivity
  have key : 1 + Real.exp (-a) ≤ Real.exp |a - b| * (1 + Real.exp (-b)) := by
    have e1 : 1 ≤ Real.exp |a - b| := Real.one_le_exp (abs_nonneg _)
    have e2 : Real.exp (-a) ≤ Real.exp |a - b| * Real.exp (-b) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := le_abs_self (b - a)
      rw [abs_sub_comm] at this
      linarith
    nlinarith [Real.exp_pos (-b)]
  have := Real.log_le_log (by positivity) key
  rw [Real.log_mul (Real.exp_pos _).ne' hb.ne', Real.log_exp] at this
  linarith

/-- Weight of hypothesis `h` before round `t`: product of its likelihoods over active rounds. -/
noncomputable def Wt {H : Type*} (L : H → ℕ → ℝ) (N : ℕ → Prop) [DecidablePred N] (h : H)
    (t : ℕ) : ℝ :=
  ∏ u ∈ (Finset.range t).filter N, L h u

lemma Wt_pos {H : Type*} (L : H → ℕ → ℝ) (hL : ∀ h u, 0 < L h u) (N : ℕ → Prop)
    [DecidablePred N] (h : H) (t : ℕ) : 0 < Wt L N h t :=
  Finset.prod_pos (fun u _ => hL h u)

lemma Wt_succ {H : Type*} (L : H → ℕ → ℝ) (N : ℕ → Prop) [DecidablePred N] (h : H) (t : ℕ) :
    Wt L N h (t + 1) = if N t then Wt L N h t * L h t else Wt L N h t := by
  unfold Wt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with hN
  · rw [Finset.prod_insert (by simp), mul_comm]
  · rfl

/-- Telescoping identity of the Bayes mixture. -/
lemma mixture_prod {H : Type*} [Fintype H] [Nonempty H] (L : H → ℕ → ℝ) (hL : ∀ h u, 0 < L h u)
    (N : ℕ → Prop) [DecidablePred N] (T : ℕ) :
    ∏ u ∈ (Finset.range T).filter N, ((∑ h, Wt L N h u * L h u) / ∑ h, Wt L N h u) =
      (∑ h, Wt L N h T) / ∑ h, Wt L N h 0 := by
  have hpos : ∀ t, 0 < ∑ h, Wt L N h t := fun t =>
    Finset.sum_pos (fun h _ => Wt_pos L hL N h t) Finset.univ_nonempty
  induction T with
  | zero =>
    simp only [Finset.range_zero, Finset.filter_empty, Finset.prod_empty]
    rw [div_self (hpos 0).ne']
  | succ T ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with hN
    · rw [Finset.prod_insert (by simp), ih]
      simp_rw [Wt_succ L N _ T, if_pos hN]
      have := (hpos T).ne'
      have := (hpos 0).ne'
      field_simp
    · rw [ih]
      simp_rw [Wt_succ L N _ T, if_neg hN]

/-- C4: regret of the Bayes mixture over a finite class (log loss), pointwise. -/
theorem mixture_regret {H : Type*} [Fintype H] [Nonempty H] (L : H → ℕ → ℝ)
    (hL : ∀ h u, 0 < L h u) (N : ℕ → Prop) [DecidablePred N] (T : ℕ) (h' : H) :
    ∑ u ∈ (Finset.range T).filter N,
        -Real.log ((∑ h, Wt L N h u * L h u) / ∑ h, Wt L N h u) ≤
      Real.log (Fintype.card H) + ∑ u ∈ (Finset.range T).filter N, -Real.log (L h' u) := by
  have hpos : ∀ t, 0 < ∑ h, Wt L N h t := fun t =>
    Finset.sum_pos (fun h _ => Wt_pos L hL N h t) Finset.univ_nonempty
  have hterm : ∀ u, 0 < (∑ h, Wt L N h u * L h u) / ∑ h, Wt L N h u := fun u =>
    div_pos (Finset.sum_pos (fun h _ => mul_pos (Wt_pos L hL N h u) (hL h u))
      Finset.univ_nonempty) (hpos u)
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, ← Real.log_prod (fun u _ => (hterm u).ne'),
    ← Real.log_prod (fun u _ => (hL h' u).ne'), mixture_prod L hL N T]
  have h0 : ∑ h, Wt L N h 0 = Fintype.card H := by
    simp [Wt]
  rw [h0, Real.log_div (hpos T).ne' (by positivity)]
  have hle : Wt L N h' T ≤ ∑ h, Wt L N h T :=
    Finset.single_le_sum (fun h _ => (Wt_pos L hL N h T).le) (Finset.mem_univ h')
  have := Real.log_le_log (Wt_pos L hL N h' T) hle
  unfold Wt at this ⊢
  linarith




/-- Likelihood density of signal `j` under state `b`. -/
noncomputable def lik {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (P : (j : Fin m) → Bool → Measure (S j)) (b : Bool) (j : Fin m) (s : ∀ j, S j) : ENNReal :=
  (P j b).rnDeriv (P j false + P j true) (s j)

/-- Log-likelihood ratio of signal `j`. -/
noncomputable def llr {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (P : (j : Fin m) → Bool → Measure (S j)) (j : Fin m) (s : ∀ j, S j) : ℝ :=
  Real.log (lik P true j s).toReal - Real.log (lik P false j s).toReal

lemma post_eq_lik {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)] (μ : ℝ)
    (P : (j : Fin m) → Bool → Measure (S j)) (B : Finset (Fin m)) (s : ∀ j, S j) :
    post μ P B s = ((ENNReal.ofReal μ * ∏ j ∈ B, lik P true j s) /
      (ENNReal.ofReal μ * ∏ j ∈ B, lik P true j s +
        ENNReal.ofReal (1 - μ) * ∏ j ∈ B, lik P false j s)).toReal := rfl

lemma factor_of_prod {ι : Type*} {B : Finset ι} {f : ι → ENNReal} (h0 : ∏ j ∈ B, f j ≠ 0)
    (ht : ∏ j ∈ B, f j ≠ ⊤) : ∀ j ∈ B, f j ≠ 0 ∧ f j ≠ ⊤ := by
  classical
  intro j hj
  have hz : f j ≠ 0 := (Finset.prod_ne_zero_iff.mp h0) j hj
  refine ⟨hz, fun htop => ht ?_⟩
  rw [← Finset.mul_prod_erase B f hj, htop]
  have : ∏ k ∈ B.erase j, f k ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k hk => (Finset.prod_ne_zero_iff.mp h0) k (Finset.mem_of_mem_erase hk))
  exact ENNReal.top_mul this

/-- L1: a non-degenerate posterior forces a non-degenerate prior and finite positive likelihoods. -/
lemma factors_of_post {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)] (μ : ℝ)
    (P : (j : Fin m) → Bool → Measure (S j)) (B : Finset (Fin m)) (s : ∀ j, S j)
    (h0 : 0 < post μ P B s) (h1 : post μ P B s < 1) :
    0 < μ ∧ μ < 1 ∧ ∀ j ∈ B, ∀ b, lik P b j s ≠ 0 ∧ lik P b j s ≠ ⊤ := by
  rw [post_eq_lik] at h0 h1
  set N := ENNReal.ofReal μ * ∏ j ∈ B, lik P true j s with hN
  set D := ENNReal.ofReal (1 - μ) * ∏ j ∈ B, lik P false j s with hD
  have hne0 : N / (N + D) ≠ 0 := fun h' => by rw [h', ENNReal.toReal_zero] at h0; exact lt_irrefl _ h0
  rw [ne_eq, ENNReal.div_eq_zero_iff, not_or] at hne0
  obtain ⟨hN0, hNDt⟩ := hne0
  have hNt : N ≠ ⊤ := ne_top_of_le_ne_top hNDt le_self_add
  have hDt : D ≠ ⊤ := ne_top_of_le_ne_top hNDt le_add_self
  have hD0 : D ≠ 0 := by
    intro hD0
    rw [hD0, add_zero, ENNReal.div_self hN0 hNt, ENNReal.toReal_one] at h1
    exact lt_irrefl _ h1
  rw [hN] at hN0 hNt
  rw [hD] at hD0 hDt
  have hμ0 : ENNReal.ofReal μ ≠ 0 := left_ne_zero_of_mul hN0
  have hμ1 : ENNReal.ofReal (1 - μ) ≠ 0 := left_ne_zero_of_mul hD0
  have hp1 : ∏ j ∈ B, lik P true j s ≠ 0 := right_ne_zero_of_mul hN0
  have hp0 : ∏ j ∈ B, lik P false j s ≠ 0 := right_ne_zero_of_mul hD0
  have hp1t : ∏ j ∈ B, lik P true j s ≠ ⊤ := fun h => hNt (by rw [h]; exact ENNReal.mul_top hμ0)
  have hp0t : ∏ j ∈ B, lik P false j s ≠ ⊤ := fun h => hDt (by rw [h]; exact ENNReal.mul_top hμ1)
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc; exact hμ0 (ENNReal.ofReal_eq_zero.mpr (not_lt.mp hc))
  · by_contra hc; exact hμ1 (ENNReal.ofReal_eq_zero.mpr (by linarith [not_lt.mp hc]))
  · intro j hj b
    cases b
    · exact factor_of_prod hp0 hp0t j hj
    · exact factor_of_prod hp1 hp1t j hj

/-- L2: the logit of the posterior is the prior logit plus the log-likelihood ratios. -/
lemma logit_post {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)] (μ : ℝ)
    (P : (j : Fin m) → Bool → Measure (S j)) (B : Finset (Fin m)) (s : ∀ j, S j)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hf : ∀ j ∈ B, ∀ b, lik P b j s ≠ 0 ∧ lik P b j s ≠ ⊤) :
    0 < post μ P B s ∧ post μ P B s < 1 ∧
      logit (post μ P B s) = logit μ + ∑ j ∈ B, llr P j s := by
  rw [post_eq_lik]
  have hpos : ∀ b, 0 < ∏ j ∈ B, (lik P b j s).toReal := fun b =>
    Finset.prod_pos (fun j hj => ENNReal.toReal_pos (hf j hj b).1 (hf j hj b).2)
  have hfin : ∀ b, ∏ j ∈ B, lik P b j s ≠ ⊤ := fun b =>
    ENNReal.prod_ne_top (fun j hj => (hf j hj b).2)
  have hNt : ENNReal.ofReal μ * ∏ j ∈ B, lik P true j s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin true)
  have hDt : ENNReal.ofReal (1 - μ) * ∏ j ∈ B, lik P false j s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin false)
  rw [ENNReal.toReal_div, ENNReal.toReal_add hNt hDt, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hμ0.le, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_prod,
    ENNReal.toReal_prod]
  set n := μ * ∏ j ∈ B, (lik P true j s).toReal with hn
  set d := (1 - μ) * ∏ j ∈ B, (lik P false j s).toReal with hd
  have hn0 : 0 < n := mul_pos hμ0 (hpos true)
  have hd0 : 0 < d := mul_pos (by linarith) (hpos false)
  refine ⟨div_pos hn0 (by linarith), (div_lt_one (by linarith)).mpr (by linarith), ?_⟩
  have h1 : 1 - n / (n + d) = d / (n + d) := by field_simp; ring
  unfold logit
  rw [h1, Real.log_div hn0.ne' (by linarith), Real.log_div hd0.ne' (by linarith), hn, hd,
    Real.log_mul hμ0.ne' (hpos true).ne', Real.log_mul (by linarith) (hpos false).ne',
    Real.log_prod (fun j hj => (ENNReal.toReal_pos (hf j hj true).1 (hf j hj true).2).ne'),
    Real.log_prod (fun j hj => (ENNReal.toReal_pos (hf j hj false).1 (hf j hj false).2).ne')]
  unfold llr
  rw [Finset.sum_sub_distrib]
  ring

/-- C2: on non-degenerate forecasts, `r* = sig (logit μ + Σ h_i (logit F_i - logit μ))`. -/
theorem post_univ_eq_sig {n m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)] (μ : ℝ)
    (P : (j : Fin m) → Bool → Measure (S j)) (Aset : Fin n → Finset (Fin m)) (s : ∀ j, S j)
    (h : Fin n → ℝ) (hh : ∀ j, ∑ i, h i * evidenceMatrix Aset i j = 1)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hF : ∀ i, 0 < post μ P (Aset i) s ∧ post μ P (Aset i) s < 1) :
    post μ P Finset.univ s =
      sig (logit μ + ∑ i, h i * (logit (post μ P (Aset i) s) - logit μ)) := by
  classical
  have hcov : ∀ j, ∃ i, j ∈ Aset i := by
    intro j
    by_contra hc
    simp only [not_exists] at hc
    have := hh j
    simp [evidenceMatrix, hc] at this
  have hf : ∀ j ∈ (Finset.univ : Finset (Fin m)), ∀ b, lik P b j s ≠ 0 ∧ lik P b j s ≠ ⊤ := by
    intro j _ b
    obtain ⟨i, hi⟩ := hcov j
    exact (factors_of_post μ P (Aset i) s (hF i).1 (hF i).2).2.2 j hi b
  obtain ⟨hr0, hr1, hr⟩ := logit_post μ P Finset.univ s hμ0 hμ1 hf
  have hFi : ∀ i, logit (post μ P (Aset i) s) - logit μ = ∑ j ∈ Aset i, llr P j s := by
    intro i
    have hfi := (factors_of_post μ P (Aset i) s (hF i).1 (hF i).2).2.2
    rw [(logit_post μ P (Aset i) s hμ0 hμ1 hfi).2.2]
    ring
  have e : ∀ i, ∑ j ∈ Aset i, llr P j s = ∑ j, evidenceMatrix Aset i j * llr P j s := by
    intro i
    simp only [evidenceMatrix, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsum : ∑ i, h i * (logit (post μ P (Aset i) s) - logit μ) = ∑ j, llr P j s := by
    simp_rw [hFi, e, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hh j, one_mul]
  rw [hsum, ← hr, sig_logit hr0 hr1]


section Agg

lemma measurable_sig : Measurable sig := by
  unfold sig; fun_prop

lemma measurable_logit : Measurable logit := by
  unfold logit; fun_prop

/-- Grid point `k` of the hypothesis grid. -/
def hv {n K : ℕ} (W ε : ℝ) (k : Fin n → Fin K) (i : Fin n) : ℝ := -W + ε * ((k i : ℕ) : ℝ)

/-- Predictor of hypothesis `k`. -/
noncomputable def pr {n K : ℕ} (W ε : ℝ) (k : Fin n → Fin K) (μ : ℝ) (F : Fin n → ℝ) : ℝ :=
  sig (logit μ + ∑ i, hv W ε k i * (logit (F i) - logit μ))

/-- Likelihood of the realized state under hypothesis `k`. -/
noncomputable def lk {n K : ℕ} (W ε : ℝ) (k : Fin n → Fin K) (μ : ℝ) (F : Fin n → ℝ)
    (ω : Bool) : ℝ :=
  if ω then pr W ε k μ F else 1 - pr W ε k μ F

lemma lk_pos {n K : ℕ} (W ε : ℝ) (k : Fin n → Fin K) (μ : ℝ) (F : Fin n → ℝ) (ω : Bool) :
    0 < lk W ε k μ F ω := by
  unfold lk; split_ifs
  · exact sig_pos _
  · exact sub_pos.mpr (sig_lt_one _)

/-- Non-extreme ("normal") period. -/
abbrev Np {n : ℕ} (τ μ : ℝ) (F : Fin n → ℝ) : Prop := ¬ (loP τ μ F ∨ hiP τ μ F)

/-- Mixture weight of hypothesis `k` before period `t`. -/
noncomputable def wt {n K : ℕ} (τ W ε : ℝ) (t : ℕ) (μs : Fin (t + 1) → ℝ)
    (Fs : Fin (t + 1) → Fin n → ℝ) (ωs : Fin t → Bool) (k : Fin n → Fin K) : ℝ :=
  ∏ u : Fin t, (if Np τ (μs u.castSucc) (Fs u.castSucc) then
    lk W ε k (μs u.castSucc) (Fs u.castSucc) (ωs u) else 1)

lemma wt_pos {n K : ℕ} (τ W ε : ℝ) (t : ℕ) (μs : Fin (t + 1) → ℝ)
    (Fs : Fin (t + 1) → Fin n → ℝ) (ωs : Fin t → Bool) (k : Fin n → Fin K) :
    0 < wt τ W ε t μs Fs ωs k := by
  unfold wt
  refine Finset.prod_pos (fun u _ => ?_)
  split_ifs
  · exact lk_pos _ _ _ _ _ _
  · exact one_pos

/-- Bayes-mixture forecast. -/
noncomputable def mixF {n K : ℕ} (τ W ε : ℝ) (t : ℕ) (μs : Fin (t + 1) → ℝ)
    (Fs : Fin (t + 1) → Fin n → ℝ) (ωs : Fin t → Bool) : ℝ :=
  (∑ k : Fin n → Fin K, wt τ W ε t μs Fs ωs k * pr W ε k (μs (Fin.last t)) (Fs (Fin.last t))) /
    ∑ k : Fin n → Fin K, wt τ W ε t μs Fs ωs k

/-- The aggregator's forecast. -/
noncomputable def fcast {n : ℕ} (K : ℕ) (τ δ W ε : ℝ) (t : ℕ) (μs : Fin (t + 1) → ℝ)
    (Fs : Fin (t + 1) → Fin n → ℝ) (ωs : Fin t → Bool) : ℝ :=
  if loP τ (μs (Fin.last t)) (Fs (Fin.last t)) ∨ hiP τ (μs (Fin.last t)) (Fs (Fin.last t)) then
    extF δ (loP τ (μs (Fin.last t)) (Fs (Fin.last t))) (hiP τ (μs (Fin.last t)) (Fs (Fin.last t)))
  else mixF (K := K) τ W ε t μs Fs ωs

lemma extF_mem {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (lo hi : Prop) [Decidable lo]
    [Decidable hi] : extF δ lo hi ∈ Set.Icc (0:ℝ) 1 := by
  unfold extF
  split_ifs <;> constructor <;> linarith

lemma mixF_mem {n K : ℕ} (τ W ε : ℝ) (t : ℕ) (μs : Fin (t + 1) → ℝ)
    (Fs : Fin (t + 1) → Fin n → ℝ) (ωs : Fin t → Bool) :
    mixF (K := K) τ W ε t μs Fs ωs ∈ Set.Icc (0:ℝ) 1 := by
  unfold mixF
  have hden : 0 ≤ ∑ k : Fin n → Fin K, wt τ W ε t μs Fs ωs k :=
    Finset.sum_nonneg (fun k _ => (wt_pos _ _ _ _ _ _ _ k).le)
  have hnum0 : 0 ≤ ∑ k : Fin n → Fin K,
      wt τ W ε t μs Fs ωs k * pr W ε k (μs (Fin.last t)) (Fs (Fin.last t)) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (wt_pos _ _ _ _ _ _ _ k).le (sig_pos _).le)
  have hle : ∑ k : Fin n → Fin K,
      wt τ W ε t μs Fs ωs k * pr W ε k (μs (Fin.last t)) (Fs (Fin.last t)) ≤
      ∑ k : Fin n → Fin K, wt τ W ε t μs Fs ωs k :=
    Finset.sum_le_sum (fun k _ => by
      have := (sig_lt_one (logit (μs (Fin.last t)) + ∑ i, hv W ε k i *
        (logit (Fs (Fin.last t) i) - logit (μs (Fin.last t))))).le
      have h0 := (wt_pos τ W ε t μs Fs ωs k).le
      unfold pr
      nlinarith)
  exact ⟨div_nonneg hnum0 hden, div_le_one_of_le₀ hle hden⟩

section Meas
variable {X : Type*} [MeasurableSpace X]

lemma measurable_pr {n K : ℕ} (W ε : ℝ) (k : Fin n → Fin K) {fμ : X → ℝ} {fF : X → Fin n → ℝ}
    (hμ : Measurable fμ) (hF : Measurable fF) :
    Measurable (fun x => pr W ε k (fμ x) (fF x)) := by
  unfold pr
  refine measurable_sig.comp ((measurable_logit.comp hμ).add
    (Finset.measurable_sum _ (fun i _ => measurable_const.mul
      ((measurable_logit.comp ((measurable_pi_apply i).comp hF)).sub
        (measurable_logit.comp hμ)))))

lemma measurable_lk {n K : ℕ} (W ε : ℝ) (k : Fin n → Fin K) {fμ : X → ℝ} {fF : X → Fin n → ℝ}
    {fω : X → Bool} (hμ : Measurable fμ) (hF : Measurable fF) (hω : Measurable fω) :
    Measurable (fun x => lk W ε k (fμ x) (fF x) (fω x)) := by
  unfold lk
  exact Measurable.ite (hω (measurableSet_singleton true)) (measurable_pr W ε k hμ hF)
    (measurable_const.sub (measurable_pr W ε k hμ hF))

lemma measurableSet_loP {n : ℕ} (τ : ℝ) {fμ : X → ℝ} {fF : X → Fin n → ℝ}
    (hμ : Measurable fμ) (hF : Measurable fF) : MeasurableSet {x | loP τ (fμ x) (fF x)} :=
  measurableSet_setOfPred.mpr ((measurableSet_setOfPred.mp (measurableSet_lt hμ measurable_const)).or
    (Measurable.exists fun i => measurableSet_setOfPred.mp
      (measurableSet_lt ((measurable_pi_apply i).comp hF) measurable_const)))

lemma measurableSet_hiP {n : ℕ} (τ : ℝ) {fμ : X → ℝ} {fF : X → Fin n → ℝ}
    (hμ : Measurable fμ) (hF : Measurable fF) : MeasurableSet {x | hiP τ (fμ x) (fF x)} :=
  measurableSet_setOfPred.mpr ((measurableSet_setOfPred.mp (measurableSet_lt measurable_const hμ)).or
    (Measurable.exists fun i => measurableSet_setOfPred.mp
      (measurableSet_lt measurable_const ((measurable_pi_apply i).comp hF))))

lemma measurable_extF {n : ℕ} (τ δ : ℝ) {fμ : X → ℝ} {fF : X → Fin n → ℝ}
    (hμ : Measurable fμ) (hF : Measurable fF) :
    Measurable (fun x => extF δ (loP τ (fμ x) (fF x)) (hiP τ (fμ x) (fF x))) := by
  unfold extF
  exact Measurable.ite ((measurableSet_loP τ hμ hF).inter (measurableSet_hiP τ hμ hF))
    measurable_const (Measurable.ite (measurableSet_loP τ hμ hF) measurable_const measurable_const)

end Meas

lemma measurable_fcast {n : ℕ} (K : ℕ) (τ δ W ε : ℝ) (t : ℕ) :
    Measurable (fun p : (Fin (t + 1) → ℝ) × (Fin (t + 1) → Fin n → ℝ) × (Fin t → Bool) =>
      fcast K τ δ W ε t p.1 p.2.1 p.2.2) := by
  have hμ : ∀ u, Measurable (fun p : (Fin (t + 1) → ℝ) × (Fin (t + 1) → Fin n → ℝ) ×
      (Fin t → Bool) => p.1 u) := fun u => (measurable_pi_apply u).comp measurable_fst
  have hF : ∀ u, Measurable (fun p : (Fin (t + 1) → ℝ) × (Fin (t + 1) → Fin n → ℝ) ×
      (Fin t → Bool) => p.2.1 u) := fun u =>
    (measurable_pi_apply u).comp (measurable_fst.comp measurable_snd)
  have hω : ∀ u, Measurable (fun p : (Fin (t + 1) → ℝ) × (Fin (t + 1) → Fin n → ℝ) ×
      (Fin t → Bool) => p.2.2 u) := fun u =>
    (measurable_pi_apply u).comp (measurable_snd.comp measurable_snd)
  have hwt : ∀ k : Fin n → Fin K, Measurable (fun p : (Fin (t + 1) → ℝ) ×
      (Fin (t + 1) → Fin n → ℝ) × (Fin t → Bool) => wt τ W ε t p.1 p.2.1 p.2.2 k) := by
    intro k
    unfold wt
    refine Finset.measurable_prod _ (fun u _ => Measurable.ite ?_ ?_ measurable_const)
    · exact (measurableSet_loP τ (hμ _) (hF _)).union (measurableSet_hiP τ (hμ _) (hF _)) |>.compl
    · exact measurable_lk W ε k (hμ _) (hF _) (hω u)
  unfold fcast mixF
  refine Measurable.ite ((measurableSet_loP τ (hμ _) (hF _)).union (measurableSet_hiP τ (hμ _) (hF _)))
    (measurable_extF τ δ (hμ _) (hF _)) ?_
  exact (Finset.measurable_sum _ (fun k _ => (hwt k).mul (measurable_pr W ε k (hμ _) (hF _)))).div
    (Finset.measurable_sum _ (fun k _ => hwt k))

/-- The main-branch aggregator. -/
noncomputable def mainAgg (n T K : ℕ) (τ δ W ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    PriorAwareAggregator n T where
  forecast t μs Fs ωs := fcast K τ δ W ε t.val μs Fs ωs
  measurable_forecast t := measurable_fcast K τ δ W ε t.val
  forecast_mem_Icc t μs Fs ωs := by
    unfold fcast
    split_ifs
    · exact extF_mem hδ0 hδ _ _
    · exact mixF_mem _ _ _ _ _ _ _

end Agg

section Regret

/-- Likelihood of state `ω` under forecast `q`. -/
noncomputable def likF (q : ℝ) (ω : Bool) : ℝ := if ω then q else 1 - q

lemma lk_eq {n K : ℕ} (W ε : ℝ) (k : Fin n → Fin K) (μ : ℝ) (F : Fin n → ℝ) (ω : Bool) :
    lk W ε k μ F ω = likF (pr W ε k μ F) ω := rfl

lemma neg_log_likF_sig_le (a b : ℝ) (ω : Bool) :
    -Real.log (likF (sig a) ω) ≤ -Real.log (likF (sig b) ω) + |a - b| := by
  unfold likF
  cases ω
  · simp only [Bool.false_eq_true, if_false, one_sub_sig]
    have := neg_log_sig_le (-a) (-b)
    rwa [show -a - -b = -(a - b) by ring, abs_neg] at this
  · simp only [if_true]
    exact neg_log_sig_le a b

lemma wt_eq_Wt {n K : ℕ} (τ W ε : ℝ) (μg : ℕ → ℝ) (Fg : ℕ → Fin n → ℝ) (ωg : ℕ → Bool)
    (t : ℕ) (k : Fin n → Fin K) :
    wt τ W ε t (fun u => μg u) (fun u => Fg u) (fun u => ωg u) k =
      Wt (fun k u => lk W ε k (μg u) (Fg u) (ωg u)) (fun u => Np τ (μg u) (Fg u)) k t := by
  unfold wt Wt
  rw [Finset.prod_filter]
  exact Fin.prod_univ_eq_prod_range
    (fun u => if Np τ (μg u) (Fg u) then lk W ε k (μg u) (Fg u) (ωg u) else 1) t

lemma likF_mixF {n K : ℕ} [Nonempty (Fin n → Fin K)] (τ W ε : ℝ) (μg : ℕ → ℝ)
    (Fg : ℕ → Fin n → ℝ) (ωg : ℕ → Bool) (t : ℕ) :
    likF (mixF (K := K) τ W ε t (fun u => μg u) (fun u => Fg u) (fun u => ωg u)) (ωg t) =
      (∑ k : Fin n → Fin K, Wt (fun k u => lk W ε k (μg u) (Fg u) (ωg u))
          (fun u => Np τ (μg u) (Fg u)) k t * likF (pr W ε k (μg t) (Fg t)) (ωg t)) /
        ∑ k : Fin n → Fin K, Wt (fun k u => lk W ε k (μg u) (Fg u) (ωg u))
          (fun u => Np τ (μg u) (Fg u)) k t := by
  have hpos : 0 < ∑ k : Fin n → Fin K, Wt (fun k u => lk W ε k (μg u) (Fg u) (ωg u))
      (fun u => Np τ (μg u) (Fg u)) k t :=
    Finset.sum_pos (fun k _ => Wt_pos _ (fun k u => lk_pos _ _ _ _ _ _) _ k t) Finset.univ_nonempty
  unfold mixF
  simp_rw [wt_eq_Wt]
  simp only [Fin.val_last]
  generalize ωg t = b
  cases b
  · simp only [likF, Bool.false_eq_true, if_false]
    rw [eq_div_iff hpos.ne', sub_mul, div_mul_cancel₀ _ hpos.ne', one_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  · simp only [likF, if_true]

/-- C6b: pointwise regret of the mixture on normal periods against a grid hypothesis. -/
theorem normal_regret {n K : ℕ} [Nonempty (Fin n → Fin K)] (τ W ε : ℝ) (μg : ℕ → ℝ)
    (Fg : ℕ → Fin n → ℝ) (ωg : ℕ → Bool) (T : ℕ) (k' : Fin n → Fin K) :
    ∑ t ∈ (Finset.range T).filter (fun u => Np τ (μg u) (Fg u)),
        -Real.log (likF (mixF (K := K) τ W ε t (fun u => μg u) (fun u => Fg u)
          (fun u => ωg u)) (ωg t)) ≤
      Real.log (Fintype.card (Fin n → Fin K)) +
        ∑ t ∈ (Finset.range T).filter (fun u => Np τ (μg u) (Fg u)),
          -Real.log (lk W ε k' (μg t) (Fg t) (ωg t)) := by
  simp_rw [likF_mixF]
  exact mixture_regret (fun k u => lk W ε k (μg u) (Fg u) (ωg u))
    (fun k u => lk_pos _ _ _ _ _ _) (fun u => Np τ (μg u) (Fg u)) T k'

end Regret

section Lip

lemma abs_logit_le {τ p : ℝ} (hτ : 0 < τ) (h1 : τ ≤ p) (h2 : p ≤ 1 - τ) :
    |logit p| ≤ Real.log (1 / τ) := by
  have hp : 0 < p := lt_of_lt_of_le hτ h1
  have hq : 0 < 1 - p := by linarith
  have a1 : Real.log τ ≤ Real.log p := Real.log_le_log hτ h1
  have a2 : Real.log τ ≤ Real.log (1 - p) := Real.log_le_log hτ (by linarith)
  have a3 : Real.log p ≤ 0 := Real.log_nonpos hp.le (by linarith)
  have a4 : Real.log (1 - p) ≤ 0 := Real.log_nonpos hq.le (by linarith)
  rw [one_div, Real.log_inv]
  unfold logit
  rw [abs_le]
  constructor <;> linarith

lemma Np_bounds {n : ℕ} {τ μ : ℝ} {F : Fin n → ℝ} (h : Np τ μ F) :
    τ ≤ μ ∧ μ ≤ 1 - τ ∧ ∀ i, τ ≤ F i ∧ F i ≤ 1 - τ := by
  simp only [Np, loP, hiP, not_or, not_lt, not_exists] at h
  exact ⟨h.1.1, h.2.1, fun i => ⟨h.1.2 i, h.2.2 i⟩⟩

/-- Per-period Lipschitz step: grid hypothesis vs. exact dual weights. -/
lemma grid_step {n K : ℕ} (W ε τ : ℝ) (hτ : 0 < τ) (hε : 0 ≤ ε) (k : Fin n → Fin K)
    (h : Fin n → ℝ) (hk : ∀ i, |hv W ε k i - h i| ≤ ε) (μ : ℝ) (F : Fin n → ℝ)
    (hN : Np τ μ F) (ω : Bool) :
    -Real.log (lk W ε k μ F ω) ≤
      -Real.log (likF (sig (logit μ + ∑ i, h i * (logit (F i) - logit μ))) ω) +
        n * ε * (2 * Real.log (1 / τ)) := by
  obtain ⟨hμ1, hμ2, hF⟩ := Np_bounds hN
  have hz : ∀ i, |logit (F i) - logit μ| ≤ 2 * Real.log (1 / τ) := fun i =>
    le_trans (abs_sub _ _) (by
      have := abs_logit_le hτ (hF i).1 (hF i).2
      have := abs_logit_le hτ hμ1 hμ2
      linarith)
  have step := neg_log_likF_sig_le (logit μ + ∑ i, hv W ε k i * (logit (F i) - logit μ))
    (logit μ + ∑ i, h i * (logit (F i) - logit μ)) ω
  have hdiff : |(logit μ + ∑ i, hv W ε k i * (logit (F i) - logit μ)) -
      (logit μ + ∑ i, h i * (logit (F i) - logit μ))| ≤ n * ε * (2 * Real.log (1 / τ)) := by
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        |hv W ε k i * (logit (F i) - logit μ) - h i * (logit (F i) - logit μ)| ≤
          ε * (2 * Real.log (1 / τ)) := by
      intro i _
      rw [← sub_mul, abs_mul]
      exact mul_le_mul (hk i) (hz i) (abs_nonneg _) hε
    refine le_trans (Finset.sum_le_sum this) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    exact le_refl _
  rw [lk_eq]
  unfold pr
  linarith

end Lip

/-- Every point of the box `[-W, W]^n` is within `ε` of the grid (coordinatewise). -/
lemma grid_near {n K : ℕ} (W ε : ℝ) (hW : 0 ≤ W) (hε : 0 < ε) (hK : 2 * W / ε < K)
    (h : Fin n → ℝ) (hh : ∀ i, |h i| ≤ W) : ∃ k : Fin n → Fin K, ∀ i, |hv W ε k i - h i| ≤ ε := by
  have hb : ∀ i, ⌊(h i + W) / ε⌋₊ < K := by
    intro i
    have h0 : (h i + W) / ε ≤ 2 * W / ε := by
      apply div_le_div_of_nonneg_right _ hε.le
      linarith [(abs_le.mp (hh i)).2]
    have hnn : 0 ≤ (h i + W) / ε := div_nonneg (by linarith [(abs_le.mp (hh i)).1]) hε.le
    exact Nat.cast_lt.mp (lt_of_le_of_lt (le_trans (Nat.floor_le hnn) h0) hK)
  refine ⟨fun i => ⟨⌊(h i + W) / ε⌋₊, hb i⟩, fun i => ?_⟩
  have hnn : 0 ≤ (h i + W) / ε := div_nonneg (by linarith [(abs_le.mp (hh i)).1]) hε.le
  have f1 := Nat.floor_le hnn
  have f2 := Nat.lt_floor_add_one ((h i + W) / ε)
  unfold hv
  simp only
  rw [abs_le]
  have e1 : ε * (⌊(h i + W) / ε⌋₊ : ℝ) ≤ h i + W := by
    have := mul_le_mul_of_nonneg_left f1 hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have e2 : h i + W < ε * ((⌊(h i + W) / ε⌋₊ : ℝ) + 1) := by
    have := mul_lt_mul_of_pos_left f2 hε
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  constructor <;> nlinarith

section Total

lemma logLoss_eq (q : ℝ) (ω : Bool) (h : 0 < likF q ω) :
    logLoss q ω = ENNReal.ofReal (-Real.log (likF q ω)) := by
  cases ω <;> simp only [logLoss, likF, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · rw [if_neg (by linarith)]
  · rw [if_neg (not_le.mpr h)]

lemma likF_mem {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) (ω : Bool) : 0 ≤ likF q ω ∧ likF q ω ≤ 1 := by
  obtain ⟨h0, h1⟩ := hq
  cases ω <;> simp only [likF, Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith

lemma likF_pos {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (ω : Bool) : 0 < likF q ω := by
  cases ω <;> simp only [likF, Bool.false_eq_true, ↓reduceIte] <;> linarith

lemma neg_log_likF_nonneg {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) (ω : Bool) :
    0 ≤ -Real.log (likF q ω) := by
  have := likF_mem hq ω
  linarith [Real.log_nonpos this.1 this.2]

lemma sum_fin_ite {M : Type*} [AddCommMonoid M] (T : ℕ) (N : ℕ → Prop) [DecidablePred N]
    (f : ℕ → M) :
    ∑ t : Fin T, (if N t then f t else 0) = ∑ t ∈ (Finset.range T).filter N, f t := by
  rw [Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun t => if N t then f t else 0) T

/-- Expert forecasts of period `t` as a total function of `t`. -/
noncomputable def Fgx {n m T : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℕ → ℝ) (P : ℕ → (j : Fin m) → Bool → Measure (S j)) (Aset : Fin n → Finset (Fin m))
    (x : Fin T → Bool × (∀ j, S j)) (t : ℕ) : Fin n → ℝ :=
  if h : t < T then Fv (μ t) (P t) Aset (x ⟨t, h⟩).2 else fun _ => 0

/-- State of period `t` as a total function of `t`. -/
def ωgx {m T : ℕ} {S : Fin m → Type*} (x : Fin T → Bool × (∀ j, S j)) (t : ℕ) : Bool :=
  if h : t < T then (x ⟨t, h⟩).1 else false

lemma Fgx_fin {n m T : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℕ → ℝ) (P : ℕ → (j : Fin m) → Bool → Measure (S j)) (Aset : Fin n → Finset (Fin m))
    (x : Fin T → Bool × (∀ j, S j)) (t : Fin T) :
    Fgx μ P Aset x t = Fv (μ t) (P t) Aset (x t).2 := by
  simp only [Fgx, dif_pos t.2]

lemma ωgx_fin {m T : ℕ} {S : Fin m → Type*} (x : Fin T → Bool × (∀ j, S j)) (t : Fin T) :
    ωgx x t = (x t).1 := by
  simp only [ωgx, dif_pos t.2]

lemma forecast_eq {n m T K : ℕ} (τ δ W ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (Aset : Fin n → Finset (Fin m)) {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℕ → ℝ) (P : ℕ → (j : Fin m) → Bool → Measure (S j))
    (x : Fin T → Bool × (∀ j, S j)) (t : Fin T) :
    (mainAgg n T K τ δ W ε hδ0 hδ).forecast t (fun u => μ u.val)
        (fun u i => post (μ u.val) (P u.val) (Aset i) (x ⟨u.val, by omega⟩).2)
        (fun u => (x ⟨u.val, by omega⟩).1) =
      fcast K τ δ W ε t (fun u => μ u) (fun u => Fgx μ P Aset x u) (fun u => ωgx x u) := by
  simp only [mainAgg]
  congr 1
  · funext u
    have hu : u.val < T := by omega
    simp only [Fgx, dif_pos hu]
    rfl
  · funext u
    have hu : u.val < T := by omega
    simp only [ωgx, dif_pos hu]

lemma term_le {n m T K : ℕ} [Nonempty (Fin n → Fin K)] (τ δ W ε : ℝ)
    (Aset : Fin n → Finset (Fin m)) {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℕ → ℝ) (P : ℕ → (j : Fin m) → Bool → Measure (S j))
    (g : ℕ → Bool × (∀ j, S j) → ENNReal)
    (hg : ∀ t y, (if loP τ (μ t) (Fv (μ t) (P t) Aset y.2) ∨ hiP τ (μ t) (Fv (μ t) (P t) Aset y.2)
      then logLoss (extF δ (loP τ (μ t) (Fv (μ t) (P t) Aset y.2))
        (hiP τ (μ t) (Fv (μ t) (P t) Aset y.2))) y.1 else 0) ≤ g t y)
    (x : Fin T → Bool × (∀ j, S j)) (t : Fin T) :
    logLoss (fcast K τ δ W ε t (fun u => μ u) (fun u => Fgx μ P Aset x u) (fun u => ωgx x u))
        (x t).1 ≤
      g t (x t) + (if Np τ (μ t) (Fgx μ P Aset x t) then ENNReal.ofReal (-Real.log
        (likF (mixF (K := K) τ W ε t (fun u => μ u) (fun u => Fgx μ P Aset x u)
          (fun u => ωgx x u)) (ωgx x t))) else 0) := by
  have hF := Fgx_fin μ P Aset x t
  have hω := ωgx_fin x t
  by_cases hN : Np τ (μ t) (Fgx μ P Aset x t)
  · rw [if_pos hN]
    unfold fcast
    split_ifs with hc
    · exact absurd hc hN
    · rw [← hω]
      refine le_trans (le_of_eq (logLoss_eq _ _ ?_)) le_add_self
      rw [likF_mixF]
      exact div_pos (Finset.sum_pos (fun k _ => mul_pos
          (Wt_pos _ (fun k u => lk_pos W ε k _ _ _) _ k _)
          (lk_pos W ε k (μ t) (Fgx μ P Aset x t) (ωgx x t))) Finset.univ_nonempty)
        (Finset.sum_pos (fun k _ => Wt_pos _ (fun k u => lk_pos W ε k _ _ _) _ k _)
          Finset.univ_nonempty)
  · rw [if_neg hN, add_zero]
    unfold fcast
    split_ifs with hc
    · have := hg t (x t)
      rw [← hF] at this
      have hc' : loP τ (μ t) (Fgx μ P Aset x t) ∨ hiP τ (μ t) (Fgx μ P Aset x t) := hc
      rw [if_pos hc'] at this
      exact this
    · exact absurd hc hN

lemma normal_chain {n m T K : ℕ} [Nonempty (Fin n → Fin K)] (τ W ε : ℝ) (hτ : 0 < τ)
    (hε : 0 ≤ ε) (hL : 0 ≤ Real.log (1 / τ))
    (Aset : Fin n → Finset (Fin m)) {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℕ → ℝ) (P : ℕ → (j : Fin m) → Bool → Measure (S j))
    (h : Fin n → ℝ) (k' : Fin n → Fin K) (hk : ∀ i, |hv W ε k' i - h i| ≤ ε)
    (x : Fin T → Bool × (∀ j, S j)) :
    ∑ t ∈ (Finset.range T).filter (fun u => Np τ (μ u) (Fgx μ P Aset x u)),
        -Real.log (likF (mixF (K := K) τ W ε t (fun u => μ u) (fun u => Fgx μ P Aset x u)
          (fun u => ωgx x u)) (ωgx x t)) ≤
      Real.log (Fintype.card (Fin n → Fin K)) + T * (n * ε * (2 * Real.log (1 / τ))) +
        ∑ t ∈ (Finset.range T).filter (fun u => Np τ (μ u) (Fgx μ P Aset x u)),
          -Real.log (likF (sig (logit (μ t) + ∑ i, h i * (logit (Fgx μ P Aset x t i) - logit (μ t))))
            (ωgx x t)) := by
  have h1 := normal_regret (K := K) τ W ε μ (Fgx μ P Aset x) (ωgx x) T k'
  have h3 := Finset.sum_le_sum (s := (Finset.range T).filter (fun u => Np τ (μ u) (Fgx μ P Aset x u)))
    (fun t ht => grid_step W ε τ hτ hε k' h hk (μ t)
    (Fgx μ P Aset x t) (Finset.mem_filter.mp ht).2 (ωgx x t))
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h3
  have hcard : (((Finset.range T).filter (fun u => Np τ (μ u) (Fgx μ P Aset x u))).card : ℝ) ≤ T := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range T).le
  have hc0 : 0 ≤ (n : ℝ) * ε * (2 * Real.log (1 / τ)) := by positivity
  have := mul_le_mul_of_nonneg_right hcard hc0
  linarith

lemma bench_eq {n m T : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (Aset : Fin n → Finset (Fin m)) {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℕ → ℝ) (P : ℕ → (j : Fin m) → Bool → Measure (S j))
    (h : Fin n → ℝ) (hh : ∀ j, ∑ i, h i * evidenceMatrix Aset i j = 1)
    (x : Fin T → Bool × (∀ j, S j)) (t : Fin T) (hN : Np τ (μ t) (Fgx μ P Aset x t)) :
    ENNReal.ofReal (-Real.log (likF (sig (logit (μ t) + ∑ i, h i *
        (logit (Fgx μ P Aset x t i) - logit (μ t)))) (ωgx x t))) =
      logLoss (post (μ t) (P t) Finset.univ (x t).2) (x t).1 := by
  obtain ⟨hμ1, hμ2, hFb⟩ := Np_bounds hN
  rw [Fgx_fin] at hFb ⊢
  rw [ωgx_fin]
  have hF : ∀ i, 0 < post (μ t) (P t) (Aset i) (x t).2 ∧ post (μ t) (P t) (Aset i) (x t).2 < 1 :=
    fun i => ⟨by have := (hFb i).1; simp only [Fv] at this; linarith,
      by have := (hFb i).2; simp only [Fv] at this; linarith⟩
  rw [post_univ_eq_sig (μ t) (P t) Aset (x t).2 h hh (by linarith) (by linarith) hF,
    logLoss_eq _ _ (likF_pos (sig_pos _) (sig_lt_one _) _)]
  rfl

/-- C6c: pointwise total bound for the main aggregator. -/
theorem pointwise_total {n m T K : ℕ} [Nonempty (Fin n → Fin K)] (τ δ W ε : ℝ) (hτ : 0 < τ)
    (hε : 0 ≤ ε) (hL : 0 ≤ Real.log (1 / τ)) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (Aset : Fin n → Finset (Fin m)) {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℕ → ℝ) (P : ℕ → (j : Fin m) → Bool → Measure (S j))
    (h : Fin n → ℝ) (hh : ∀ j, ∑ i, h i * evidenceMatrix Aset i j = 1)
    (k' : Fin n → Fin K) (hk : ∀ i, |hv W ε k' i - h i| ≤ ε)
    (g : ℕ → Bool × (∀ j, S j) → ENNReal)
    (hg : ∀ t y, (if loP τ (μ t) (Fv (μ t) (P t) Aset y.2) ∨ hiP τ (μ t) (Fv (μ t) (P t) Aset y.2)
      then logLoss (extF δ (loP τ (μ t) (Fv (μ t) (P t) Aset y.2))
        (hiP τ (μ t) (Fv (μ t) (P t) Aset y.2))) y.1 else 0) ≤ g t y)
    (x : Fin T → Bool × (∀ j, S j)) :
    ∑ t : Fin T, logLoss ((mainAgg n T K τ δ W ε hδ0 hδ).forecast t (fun u => μ u.val)
        (fun u i => post (μ u.val) (P u.val) (Aset i) (x ⟨u.val, by omega⟩).2)
        (fun u => (x ⟨u.val, by omega⟩).1)) (x t).1 ≤
      (∑ t : Fin T, g t (x t) + ENNReal.ofReal (Real.log (Fintype.card (Fin n → Fin K)) +
        T * (n * ε * (2 * Real.log (1 / τ))))) +
        ∑ t : Fin T, logLoss (post (μ t) (P t) Finset.univ (x t).2) (x t).1 := by
  simp_rw [forecast_eq τ δ W ε hδ0 hδ Aset μ P x]
  refine le_trans (Finset.sum_le_sum (fun t _ => term_le τ δ W ε Aset μ P g hg x t)) ?_
  rw [Finset.sum_add_distrib, add_assoc]
  refine add_le_add le_rfl ?_
  have hmm : ∀ t : ℕ, 0 ≤ -Real.log (likF (mixF (K := K) τ W ε t (fun u => μ u)
      (fun u => Fgx μ P Aset x u) (fun u => ωgx x u)) (ωgx x t)) :=
    fun t => neg_log_likF_nonneg (mixF_mem _ _ _ _ _ _ _) _
  have hrr : ∀ t : ℕ, 0 ≤ -Real.log (likF (sig (logit (μ t) + ∑ i, h i *
      (logit (Fgx μ P Aset x t i) - logit (μ t)))) (ωgx x t)) :=
    fun t => neg_log_likF_nonneg ⟨(sig_pos _).le, (sig_lt_one _).le⟩ _
  rw [sum_fin_ite T (fun u => Np τ (μ u) (Fgx μ P Aset x u)) (fun t => ENNReal.ofReal
    (-Real.log (likF (mixF (K := K) τ W ε t (fun u => μ u) (fun u => Fgx μ P Aset x u)
      (fun u => ωgx x u)) (ωgx x t)))), ← ENNReal.ofReal_sum_of_nonneg (fun t _ => hmm t)]
  refine le_trans (ENNReal.ofReal_le_ofReal (normal_chain τ W ε hτ hε hL Aset μ P h k' hk x)) ?_
  refine le_trans ENNReal.ofReal_add_le ?_
  gcongr
  rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => hrr t), ← sum_fin_ite]
  refine Finset.sum_le_sum (fun t _ => ?_)
  split_ifs with hN
  · exact le_of_eq (bench_eq τ hτ Aset μ P h hh x t hN)
  · exact bot_le

end Total

section Assemble

/-- C6d: integrated bound for the main aggregator. -/
theorem main_bound {n m T K : ℕ} [Nonempty (Fin n → Fin K)] (τ δ W ε : ℝ) (hτ : 0 < τ)
    (hε : 0 ≤ ε) (hL : 0 ≤ Real.log (1 / τ)) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hnτ : (n + 1) * τ ≤ δ)
    (Aset : Fin n → Finset (Fin m)) {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℕ → ℝ) (P : ℕ → (j : Fin m) → Bool → Measure (S j)) (hμ : ∀ t, μ t ∈ Set.Icc (0:ℝ) 1)
    [hP : ∀ t j b, IsProbabilityMeasure (P t j b)]
    (h : Fin n → ℝ) (hh : ∀ j, ∑ i, h i * evidenceMatrix Aset i j = 1)
    (k' : Fin n → Fin K) (hk : ∀ i, |hv W ε k' i - h i| ≤ ε) :
    aggregatorLoss (mainAgg n T K τ δ W ε hδ0 hδ) Aset μ P ≤ benchmarkLoss T μ P +
      ENNReal.ofReal (T * (2 * δ + 2 * δ * Real.log (1 / δ)) +
        (Real.log (Fintype.card (Fin n → Fin K)) + T * (n * ε * (2 * Real.log (1 / τ))))) := by
  choose g hgm hgle hgint using fun t : ℕ => ext_major (μ t) (hμ t) (P t) Aset τ δ hτ hδ0 hδ hnτ
  haveI : ∀ t : Fin T, IsProbabilityMeasure (jointLaw (μ t) (P t)) := fun t =>
    ⟨jointLaw_univ (μ t) (hμ t) (P t)⟩
  have hR0 : 0 ≤ Real.log (Fintype.card (Fin n → Fin K)) + T * (n * ε * (2 * Real.log (1 / τ))) := by
    have h1 : (1:ℝ) ≤ Fintype.card (Fin n → Fin K) := by exact_mod_cast Fintype.card_pos
    exact add_nonneg (Real.log_nonneg h1) (by positivity)
  have hB0 : 0 ≤ 2 * δ + 2 * δ * Real.log (1 / δ) := by
    have : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
    positivity
  unfold aggregatorLoss benchmarkLoss dynamicLaw
  have hsum : Measurable (fun x : Fin T → Bool × (∀ j, S j) => ∑ t : Fin T, g t (x t)) := by
    refine Finset.measurable_sum _ (fun (t : Fin T) _ => ?_)
    exact (hgm t).comp (measurable_pi_apply t)
  have hmeas : Measurable (fun x : Fin T → Bool × (∀ j, S j) => ∑ t : Fin T, g t (x t) +
      ENNReal.ofReal (Real.log (Fintype.card (Fin n → Fin K)) +
        T * (n * ε * (2 * Real.log (1 / τ))))) := by
    exact hsum.add measurable_const
  calc _ ≤ ∫⁻ x, (∑ t : Fin T, g t (x t) + ENNReal.ofReal (Real.log (Fintype.card (Fin n → Fin K)) +
        T * (n * ε * (2 * Real.log (1 / τ))))) +
        ∑ t : Fin T, logLoss (post (μ t) (P t) Finset.univ (x t).2) (x t).1
        ∂(Measure.pi fun t : Fin T => jointLaw (μ t) (P t)) :=
        lintegral_mono (fun x => pointwise_total τ δ W ε hτ hε hL hδ0 hδ Aset μ P h hh k' hk g hgle x)
    _ = (∑ t : Fin T, ∫⁻ y, g t y ∂(jointLaw (μ t) (P t))) +
        ENNReal.ofReal (Real.log (Fintype.card (Fin n → Fin K)) +
          T * (n * ε * (2 * Real.log (1 / τ)))) +
        ∫⁻ x, ∑ t : Fin T, logLoss (post (μ t) (P t) Finset.univ (x t).2) (x t).1
          ∂(Measure.pi fun t : Fin T => jointLaw (μ t) (P t)) := by
        have hfs : ∫⁻ x, ∑ t : Fin T, g t (x t) ∂(Measure.pi fun t : Fin T => jointLaw (μ t) (P t)) =
            ∑ t : Fin T, ∫⁻ x, g t (x t) ∂(Measure.pi fun t : Fin T => jointLaw (μ t) (P t)) :=
          lintegral_finset_sum _ (fun (t : Fin T) _ => (hgm t).comp (measurable_pi_apply t))
        rw [lintegral_add_left hmeas, lintegral_add_left hsum, hfs,
          lintegral_const, measure_univ, mul_one]
        congr 2
        refine Finset.sum_congr rfl (fun t _ => ?_)
        exact (measurePreserving_eval (fun t : Fin T => jointLaw (μ t) (P t)) t).lintegral_comp (hgm t)
    _ ≤ ENNReal.ofReal (T * (2 * δ + 2 * δ * Real.log (1 / δ))) +
        ENNReal.ofReal (Real.log (Fintype.card (Fin n → Fin K)) +
          T * (n * ε * (2 * Real.log (1 / τ)))) +
        ∫⁻ x, ∑ t : Fin T, logLoss (post (μ t) (P t) Finset.univ (x t).2) (x t).1
          ∂(Measure.pi fun t : Fin T => jointLaw (μ t) (P t)) := by
        gcongr
        calc ∑ t : Fin T, ∫⁻ y, g t y ∂(jointLaw (μ t) (P t)) ≤
            ∑ _t : Fin T, ENNReal.ofReal (2 * δ + 2 * δ * Real.log (1 / δ)) :=
              Finset.sum_le_sum (fun t _ => hgint t)
          _ = ENNReal.ofReal (T * (2 * δ + 2 * δ * Real.log (1 / δ))) := by
              rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hB0), Finset.sum_const,
                Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by
        rw [← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hB0) hR0, add_comm]

/-- Branch A aggregator: forecast the (clamped) prior. -/
noncomputable def clampAgg (n T : ℕ) : PriorAwareAggregator n T where
  forecast t μs _ _ := max 0 (min 1 (μs (Fin.last t)))
  measurable_forecast t := measurable_const.max (measurable_const.min
    ((measurable_pi_apply (Fin.last t.val)).comp measurable_fst))
  forecast_mem_Icc t μs _ _ := ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- Branch B aggregator: always forecast `1/2`. -/
noncomputable def halfAgg (n T : ℕ) : PriorAwareAggregator n T where
  forecast _ _ _ _ := 1 / 2
  measurable_forecast _ := measurable_const
  forecast_mem_Icc _ _ _ _ := ⟨by norm_num, by norm_num⟩

theorem clamp_bound {n m T : ℕ} (Aset : Fin n → Finset (Fin m)) {S : Fin m → Type*}
    [∀ j, MeasurableSpace (S j)] (hm : m = 0) (μ : ℕ → ℝ)
    (P : ℕ → (j : Fin m) → Bool → Measure (S j)) (hμ : ∀ t, μ t ∈ Set.Icc (0:ℝ) 1) :
    aggregatorLoss (clampAgg n T) Aset μ P ≤ benchmarkLoss T μ P := by
  subst hm
  unfold aggregatorLoss benchmarkLoss
  refine lintegral_mono (fun x => Finset.sum_le_sum (fun t _ => le_of_eq ?_))
  simp only [clampAgg, Fin.val_last]
  rw [Finset.univ_eq_empty, post_empty _ (hμ t), min_eq_right (hμ t).2, max_eq_right (hμ t).1]

lemma logLoss_half (ω : Bool) : logLoss (1 / 2) ω = ENNReal.ofReal (Real.log 2) := by
  have e : -Real.log (1 / 2) = Real.log 2 := by rw [one_div, Real.log_inv, neg_neg]
  cases ω <;> simp only [logLoss, Bool.false_eq_true, ↓reduceIte]
  · rw [if_neg (by norm_num), show (1:ℝ) - 1 / 2 = 1 / 2 by norm_num, e]
  · rw [if_neg (by norm_num), e]

theorem half_bound {n m T : ℕ} (Aset : Fin n → Finset (Fin m)) {S : Fin m → Type*}
    [∀ j, MeasurableSpace (S j)] (μ : ℕ → ℝ)
    (P : ℕ → (j : Fin m) → Bool → Measure (S j)) (hμ : ∀ t, μ t ∈ Set.Icc (0:ℝ) 1)
    [hP : ∀ t j b, IsProbabilityMeasure (P t j b)] :
    aggregatorLoss (halfAgg n T) Aset μ P ≤ ENNReal.ofReal (T * Real.log 2) := by
  haveI : ∀ t : Fin T, IsProbabilityMeasure (jointLaw (μ t) (P t)) := fun t =>
    ⟨jointLaw_univ (μ t) (hμ t) (P t)⟩
  unfold aggregatorLoss dynamicLaw
  calc _ ≤ ∫⁻ _x, ∑ _t : Fin T, ENNReal.ofReal (Real.log 2)
        ∂(Measure.pi fun t : Fin T => jointLaw (μ t) (P t)) :=
        lintegral_mono (fun x => Finset.sum_le_sum (fun t _ => le_of_eq (logLoss_half _)))
    _ = _ := by
        rw [lintegral_const, measure_univ, mul_one,
          ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.log_nonneg (by norm_num)),
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Assemble

section Final

lemma euc_norm {k : ℕ} (v : Fin k → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin k))‖ = Real.sqrt (v ⬝ᵥ v) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, sq]

lemma dot_self_nonneg {k : ℕ} (v : Fin k → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma inj_of_bound {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hA : ∀ y : EuclideanSpace ℝ (Fin m), σ * ‖y‖ ≤
      ‖(WithLp.toLp 2 (A.mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖) :
    Function.Injective A.mulVec := by
  intro y1 y2 h12
  have h := hA (WithLp.toLp 2 (y1 - y2))
  rw [WithLp.ofLp_toLp, Matrix.mulVec_sub, h12, sub_self, euc_norm, euc_norm, dotProduct_zero,
    Real.sqrt_zero] at h
  have h5 : Real.sqrt ((y1 - y2) ⬝ᵥ (y1 - y2)) = 0 := by
    refine le_antisymm ?_ (Real.sqrt_nonneg _)
    by_contra hc
    have := mul_pos hσ (lt_of_not_ge hc)
    linarith
  have h6 := (Real.sqrt_eq_zero (dot_self_nonneg _)).mp h5
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h6)

lemma m_le_n {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (hinj : Function.Injective A.mulVec) :
    m ≤ n := by
  have := LinearMap.finrank_le_finrank_of_injective (f := Matrix.mulVecLin A) hinj
  simpa using this

lemma m_zero_of_large {n m : ℕ} (Aset : Fin n → Finset (Fin m)) {σ : ℝ} (hσ : Real.sqrt n < σ)
    (hA : ∀ y : EuclideanSpace ℝ (Fin m), σ * ‖y‖ ≤
      ‖(WithLp.toLp 2 ((evidenceMatrix Aset).mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖) :
    m = 0 := by
  classical
  by_contra hm
  let j : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  have h := hA (WithLp.toLp 2 (Pi.single j 1))
  rw [WithLp.ofLp_toLp, euc_norm, euc_norm] at h
  have e1 : (Pi.single j (1:ℝ) : Fin m → ℝ) ⬝ᵥ Pi.single j 1 = 1 := by simp
  have e3 : (evidenceMatrix Aset) *ᵥ Pi.single j 1 = fun i => evidenceMatrix Aset i j := by
    ext i; simp [Matrix.mulVec, dotProduct_single]
  rw [e1, Real.sqrt_one, mul_one, e3] at h
  have e2 : (fun i => evidenceMatrix Aset i j) ⬝ᵥ (fun i => evidenceMatrix Aset i j) ≤ n := by
    simp only [dotProduct]
    calc ∑ i, evidenceMatrix Aset i j * evidenceMatrix Aset i j ≤ ∑ _i : Fin n, (1:ℝ) :=
          Finset.sum_le_sum (fun i _ => by unfold evidenceMatrix; split_ifs <;> norm_num)
      _ = n := by simp
  linarith [Real.sqrt_le_sqrt e2]

lemma sigma_of_inj {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (hinj : Function.Injective A.mulVec) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ y : EuclideanSpace ℝ (Fin m), σ * ‖y‖ ≤
      ‖(WithLp.toLp 2 (A.mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖ := by
  have hf : Function.Injective (Matrix.toEuclideanLin A) := by
    intro y1 y2 h
    rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply] at h
    have h' : A *ᵥ y1.ofLp = A *ᵥ y2.ofLp := by simpa using congrArg WithLp.ofLp h
    have h'' := hinj h'
    simpa using congrArg (WithLp.toLp 2) h''
  obtain ⟨K, hK, hKf⟩ := (LinearMap.injective_iff_antilipschitz _).mp hf
  have hK' : (0:ℝ) < K := NNReal.coe_pos.mpr hK
  refine ⟨1 / K, one_div_pos.mpr hK', fun y => ?_⟩
  have := hKf.le_mul_dist y 0
  rw [map_zero, dist_zero_right, dist_zero_right, Matrix.toEuclideanLin_apply] at this
  rw [one_div, inv_mul_le_iff₀ hK']
  exact this

lemma exists_sigma (n : ℕ) : ∃ σ : ℝ, 0 < σ ∧ ∀ (m : ℕ) (Aset : Fin n → Finset (Fin m)),
    Function.Injective (evidenceMatrix Aset).mulVec → ∀ y : EuclideanSpace ℝ (Fin m), σ * ‖y‖ ≤
      ‖(WithLp.toLp 2 ((evidenceMatrix Aset).mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖ := by
  classical
  let σe : (Σ m : Fin (n + 1), (Fin n → Finset (Fin m.val))) → ℝ := fun e =>
    if hinj : Function.Injective (evidenceMatrix e.2).mulVec then
      Classical.choose (sigma_of_inj _ hinj) else 1
  have hσe : ∀ e, 0 < σe e := by
    intro e
    simp only [σe]
    split_ifs with hinj
    · exact (Classical.choose_spec (sigma_of_inj _ hinj)).1
    · exact one_pos
  have hne : (Finset.univ : Finset (Σ m : Fin (n + 1), (Fin n → Finset (Fin m.val)))).Nonempty :=
    ⟨⟨0, fun _ => ∅⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne σe, (Finset.lt_inf'_iff hne).mpr (fun e _ => hσe e), ?_⟩
  intro m Aset hinj y
  have hmn : m < n + 1 := Nat.lt_succ_of_le (m_le_n _ hinj)
  let e : (Σ m : Fin (n + 1), (Fin n → Finset (Fin m.val))) := ⟨⟨m, hmn⟩, Aset⟩
  have hle : Finset.univ.inf' hne σe ≤ σe e := Finset.inf'_le _ (Finset.mem_univ e)
  have he : σe e = Classical.choose (sigma_of_inj (evidenceMatrix Aset) hinj) := by
    simp only [σe, e, dif_pos hinj]
  have hspec := (Classical.choose_spec (sigma_of_inj (evidenceMatrix Aset) hinj)).2 y
  rw [← he] at hspec
  exact le_trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _)) hspec

lemma half_real (n T : ℕ) (σ : ℝ) (hσ : 0 < σ) (hT : 1 ≤ T) (hB : σ * Real.sqrt T ≤ 4 * n) :
    T * Real.log 2 ≤ 10 * n / σ * Real.sqrt T * (1 + Real.log T) ^ 1 := by
  set r := Real.sqrt T with hr
  have hT0 : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hr2 : r ^ 2 = T := Real.sq_sqrt (by linarith)
  have hr1 : 1 ≤ r := by have := Real.sqrt_le_sqrt hT0; rwa [Real.sqrt_one] at this
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT0
  have hrle : r ≤ 4 * n / σ := by rw [le_div_iff₀ hσ]; linarith
  have hQ : 0 ≤ (n:ℝ) / σ * r := by positivity
  calc (T:ℝ) * Real.log 2 ≤ T := by nlinarith
    _ = r * r := by rw [← hr2]; ring
    _ ≤ r * (4 * n / σ) := by gcongr
    _ = 4 * ((n:ℝ) / σ * r) := by ring
    _ ≤ 10 * ((n:ℝ) / σ * r) * (1 + Real.log T) := by nlinarith
    _ = _ := by ring

lemma main_real (n T K : ℕ) (σ s δ τ L ε W : ℝ) (hσ : 0 < σ) (hT : 1 ≤ T)
    (hσn : σ ≤ Real.sqrt n) (hB : 4 * n < σ * Real.sqrt T)
    (hs : s = σ * Real.sqrt T) (hδ : δ = 2 * n / s) (hτ : τ = 1 / s) (hL : L = Real.log s)
    (hε : ε = 1 / (n * L * T)) (hW : W = Real.sqrt n / σ) (hK : (K : ℝ) ≤ 2 * W / ε + 1)
    (hK1 : (1:ℝ) ≤ K) :
    T * (2 * δ + 2 * δ * Real.log (1 / δ)) +
        (Real.log (Fintype.card (Fin n → Fin K)) + T * (n * ε * (2 * Real.log (1 / τ)))) ≤
      10 * n / σ * Real.sqrt T * (1 + Real.log T) ^ 1 := by
  set q := Real.sqrt n with hq
  set r := Real.sqrt T with hr
  have hT0 : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hr2 : r ^ 2 = T := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hr1 : 1 ≤ r := by have := Real.sqrt_le_sqrt hT0; rwa [Real.sqrt_one] at this
  have hr0 : r ≠ 0 := by positivity
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqpos : 0 < q := lt_of_lt_of_le hσ hσn
  have hnpos : (0:ℝ) < n := by rw [← hq2]; positivity
  have hn1 : (1:ℝ) ≤ n := by
    have : 0 < n := by exact_mod_cast hnpos
    exact_mod_cast this
  have hrq : 4 * q < r := by
    have h0 : σ * r ≤ q * r := mul_le_mul_of_nonneg_right hσn (by linarith)
    have h1 : 4 * q ^ 2 < q * r := by rw [hq2]; linarith
    nlinarith
  have hs_pos : 0 < s := by rw [hs]; positivity
  have hs4 : 4 * (n:ℝ) < s := by rw [hs]; exact hB
  have hs1 : 1 < s := by linarith
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos hs1
  have hLs : L < s := by rw [hL]; linarith [Real.log_le_sub_one_of_pos hs_pos]
  have hQn : (n:ℝ) ≤ n * r / σ := by
    rw [le_div_iff₀ hσ]; nlinarith
  have hTδ : (T:ℝ) * δ = 2 * (n * r / σ) := by
    rw [hδ, hs, ← hr2]; field_simp; try ring
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT0
  have hX : Real.log (1 / δ) ≤ Real.log T := by
    have hd : 0 < δ := by rw [hδ]; positivity
    apply Real.log_le_log (by positivity)
    rw [hδ, one_div_div, div_le_iff₀ (by positivity), hs, ← hr2]
    nlinarith
  have hQ0 : 0 ≤ (n:ℝ) * r / σ := by positivity
  have hp1 : T * (2 * δ + 2 * δ * Real.log (1 / δ)) ≤ 4 * (n * r / σ) * (1 + Real.log T) := by
    have e : (T:ℝ) * (2 * δ + 2 * δ * Real.log (1 / δ)) = 2 * (T * δ) * (1 + Real.log (1 / δ)) := by
      ring
    rw [e, hTδ]
    nlinarith
  have hp2 : (T:ℝ) * (n * ε * (2 * Real.log (1 / τ))) = 2 := by
    rw [hτ, one_div_one_div, ← hL, hε]
    have : (T:ℝ) ≠ 0 := by positivity
    have : (n:ℝ) ≠ 0 := by positivity
    have : L ≠ 0 := hL0.ne'
    field_simp
  have hcard : Real.log (Fintype.card (Fin n → Fin K)) = n * Real.log K := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  have hK3 : (K:ℝ) ≤ 3 * T ^ 3 := by
    have h2W : 2 * W / ε = 2 * q * n * L * T / σ := by
      rw [hW, hε]
      have : (T:ℝ) ≠ 0 := by positivity
      have : (n:ℝ) ≠ 0 := by positivity
      have : L ≠ 0 := hL0.ne'
      field_simp
    have h3 : 2 * W / ε ≤ 2 * q * n * r * T := by
      rw [h2W, div_le_iff₀ hσ]
      have hLr : L ≤ σ * r := by rw [← hs]; exact hLs.le
      have hpos : 0 ≤ 2 * q * n * T := by positivity
      have := mul_le_mul_of_nonneg_left hLr hpos
      linarith
    have h4 : q * n * r * T ≤ T ^ 3 := by
      rw [← hq2, ← hr2]
      have hqr : q ≤ r := by linarith
      have hr0' : 0 ≤ r := by linarith
      calc q * q ^ 2 * r * r ^ 2 = q ^ 3 * r ^ 3 := by ring
        _ ≤ r ^ 3 * r ^ 3 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hqr 3) (pow_nonneg hr0' 3)
        _ = (r ^ 2) ^ 3 := by ring
    have hT3 : 1 ≤ (T:ℝ) ^ 3 := one_le_pow₀ hT0
    linarith
  have hlogK : Real.log K ≤ 2 + 3 * Real.log T := by
    have h1 : Real.log K ≤ Real.log (3 * T ^ 3) := Real.log_le_log (by linarith) hK3
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    have h3 : Real.log 3 ≤ 2 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)]
    push_cast at h1
    linarith
  have hp3 : (n:ℝ) * Real.log K ≤ 3 * (n * r / σ) * (1 + Real.log T) := by
    have : (n:ℝ) * Real.log K ≤ n * (3 * (1 + Real.log T)) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
    have h2 := mul_le_mul_of_nonneg_right hQn (by linarith : (0:ℝ) ≤ 1 + Real.log T)
    linarith
  have hQ1 : 1 ≤ (n:ℝ) * r / σ := le_trans hn1 hQn
  have hQL : 1 ≤ ((n:ℝ) * r / σ) * (1 + Real.log T) :=
    one_le_mul_of_one_le_of_one_le hQ1 (by linarith)
  rw [hcard, hp2, pow_one]
  have e : 10 * (n:ℝ) / σ * r * (1 + Real.log T) = 10 * ((n:ℝ) * r / σ) * (1 + Real.log T) := by
    ring
  rw [e]
  linarith

theorem part2_explicit (n : ℕ) (σ : ℝ) (hσ : 0 < σ) (T : ℕ) (hT : 1 ≤ T) :
    ∃ alg : PriorAwareAggregator n T,
      ∀ (m : ℕ) (Aset : Fin n → Finset (Fin m)),
        (∀ y : EuclideanSpace ℝ (Fin m), σ * ‖y‖ ≤
          ‖(WithLp.toLp 2 ((evidenceMatrix Aset).mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖) →
        ∀ (S : Fin m → Type u) [∀ j, MeasurableSpace (S j)] (μ : ℕ → ℝ)
          (P : ℕ → (j : Fin m) → Bool → Measure (S j)),
          (∀ t, μ t ∈ Set.Icc (0 : ℝ) 1) → (∀ t j b, IsProbabilityMeasure (P t j b)) →
          aggregatorLoss alg Aset μ P ≤ benchmarkLoss T μ P +
            ENNReal.ofReal (10 * n / σ * Real.sqrt T * (1 + Real.log T) ^ 1) := by
  by_cases hA : Real.sqrt n < σ
  · refine ⟨clampAgg n T, fun m Aset hAs S _ μ P hμ hP => ?_⟩
    exact le_trans (clamp_bound Aset (m_zero_of_large Aset hA hAs) μ P hμ) le_self_add
  by_cases hB : σ * Real.sqrt T ≤ 4 * n
  · refine ⟨halfAgg n T, fun m Aset hAs S _ μ P hμ hP => ?_⟩
    exact le_trans (half_bound Aset μ P hμ) (le_trans (ENNReal.ofReal_le_ofReal
      (half_real n T σ hσ hT hB)) le_add_self)
  push_neg at hA hB
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = σ * Real.sqrt T := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log s := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = Real.sqrt n / σ := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (n * L * T) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊2 * W / ε⌋₊ + 1 := ⟨_, rfl⟩
  have hT0 : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hn0 : (0:ℝ) < n := Real.sqrt_pos.mp (lt_of_lt_of_le hσ hA)
  have hs4 : 4 * (n:ℝ) < s := by rw [hs]; exact hB
  have hs0 : 0 < s := by linarith
  have hn1 : (1:ℝ) ≤ n := by
    have : 0 < n := by exact_mod_cast hn0
    exact_mod_cast this
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hτ0 : 0 < 1 / s := by positivity
  have hδ0 : 0 < 2 * (n:ℝ) / s := by positivity
  have hδ2 : 2 * (n:ℝ) / s ≤ 1 / 2 := by rw [div_le_iff₀ hs0]; linarith
  have hnτ : ((n:ℝ) + 1) * (1 / s) ≤ 2 * n / s := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right (by linarith) hs0.le
  have hLτ : 0 ≤ Real.log (1 / (1 / s)) := by
    rw [one_div_one_div]; exact Real.log_nonneg (by linarith)
  have hfl : 0 ≤ 2 * W / ε := by positivity
  have hKlt : 2 * W / ε < K := by rw [hK]; push_cast; exact Nat.lt_floor_add_one _
  have hKle : (K:ℝ) ≤ 2 * W / ε + 1 := by
    rw [hK]; push_cast; linarith [Nat.floor_le hfl]
  have hK1 : (1:ℝ) ≤ K := by
    rw [hK]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌊2 * W / ε⌋₊]
  haveI : Nonempty (Fin K) := ⟨⟨0, by rw [hK]; omega⟩⟩
  refine ⟨mainAgg n T K (1 / s) (2 * n / s) W ε hδ0 hδ2, fun m Aset hAs S _ μ P hμ hP => ?_⟩
  obtain ⟨h, hh, hhb⟩ := exists_dual_weights (evidenceMatrix Aset) hσ hAs
  have hmn : m ≤ n := m_le_n _ (inj_of_bound _ hσ hAs)
  have hhW : ∀ i, |h i| ≤ W := fun i => (hhb i).trans (by
    rw [hW]; exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast hmn)) hσ.le)
  obtain ⟨k', hk'⟩ := grid_near W ε hW0 hε0 hKlt h hhW
  refine le_trans (main_bound (1 / s) (2 * n / s) W ε hτ0 hε0.le hLτ hδ0 hδ2 hnτ Aset μ P hμ
    h hh k' hk') (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  exact main_real n T K σ s (2 * n / s) (1 / s) L ε W hσ hT hA hB hs rfl rfl hL hε hW hKle hK1

lemma tendsto_R (C : ℝ) :
    Tendsto (fun T : ℕ => C * Real.sqrt T * (1 + Real.log T) ^ 1 / T) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => (x ^ (1 / 2 : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (by norm_num))
  have h3 : Tendsto (fun x : ℝ => C * ((x ^ (1 / 2 : ℝ))⁻¹ + Real.log x / x ^ (1 / 2 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (h2.add h1).const_mul C
  have h4 := h3.comp tendsto_natCast_atTop_atTop
  refine h4.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with T hT
  have hT0 : (0:ℝ) < T := by exact_mod_cast hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hss : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  simp only [Function.comp, pow_one]
  rw [← Real.sqrt_eq_rpow]
  have key : ∀ u : ℝ, 0 < u → ∀ a x : ℝ, x = u * u →
      C * (u⁻¹ + a / u) = C * u * (1 + a) / x := by
    intro u hu a x hx
    rw [hx]
    field_simp
  exact key _ hs _ _ hss.symm

theorem part1 (n : ℕ) : ∃ R : ℕ → ℝ, Tendsto (fun T : ℕ => R T / T) atTop (𝓝 0) ∧
      ∀ T : ℕ, ∃ alg : PriorAwareAggregator n T,
        ∀ (m : ℕ) (Aset : Fin n → Finset (Fin m)),
          Function.Injective (evidenceMatrix Aset).mulVec →
          ∀ (S : Fin m → Type u) [∀ j, MeasurableSpace (S j)] (μ : ℕ → ℝ)
            (P : ℕ → (j : Fin m) → Bool → Measure (S j)),
            (∀ t, μ t ∈ Set.Icc (0 : ℝ) 1) → (∀ t j b, IsProbabilityMeasure (P t j b)) →
            aggregatorLoss alg Aset μ P ≤ benchmarkLoss T μ P + ENNReal.ofReal (R T) := by
  obtain ⟨σ, hσ, hσA⟩ := exists_sigma n
  refine ⟨fun T => 10 * n / σ * Real.sqrt T * (1 + Real.log T) ^ 1, tendsto_R _, fun T => ?_⟩
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    refine ⟨halfAgg n 0, fun m Aset _ S _ μ P _ _ => ?_⟩
    simp [aggregatorLoss]
  · obtain ⟨alg, halg⟩ := part2_explicit n σ hσ T hT
    exact ⟨alg, fun m Aset hinj S _ μ P hμ hP => halg m Aset (hσA m Aset hinj) S μ P hμ hP⟩

end Final

end FAL77

open ForecastAggLearn MeasureTheory Filter Topology in
theorem solution :
    (∀ n : ℕ, ∃ R : ℕ → ℝ, Tendsto (fun T : ℕ => R T / T) atTop (𝓝 0) ∧
      ∀ T : ℕ, ∃ alg : PriorAwareAggregator n T,
        ∀ (m : ℕ) (Aset : Fin n → Finset (Fin m)),
          Function.Injective (evidenceMatrix Aset).mulVec →
          ∀ (S : Fin m → Type u) [∀ j, MeasurableSpace (S j)] (μ : ℕ → ℝ)
            (P : ℕ → (j : Fin m) → Bool → Measure (S j)),
            (∀ t, μ t ∈ Set.Icc (0 : ℝ) 1) → (∀ t j b, IsProbabilityMeasure (P t j b)) →
            aggregatorLoss alg Aset μ P ≤ benchmarkLoss T μ P + ENNReal.ofReal (R T)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ k : ℕ, ∀ n : ℕ, ∀ σ : ℝ, 0 < σ → ∀ T : ℕ, 1 ≤ T →
      ∃ alg : PriorAwareAggregator n T,
        ∀ (m : ℕ) (Aset : Fin n → Finset (Fin m)),
          (∀ y : EuclideanSpace ℝ (Fin m), σ * ‖y‖ ≤
            ‖(WithLp.toLp 2 ((evidenceMatrix Aset).mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖) →
          ∀ (S : Fin m → Type u) [∀ j, MeasurableSpace (S j)] (μ : ℕ → ℝ)
            (P : ℕ → (j : Fin m) → Bool → Measure (S j)),
            (∀ t, μ t ∈ Set.Icc (0 : ℝ) 1) → (∀ t j b, IsProbabilityMeasure (P t j b)) →
            aggregatorLoss alg Aset μ P ≤ benchmarkLoss T μ P +
              ENNReal.ofReal (c * n / σ * Real.sqrt T * (1 + Real.log T) ^ k)) := by
  exact ⟨fun n => FAL77.part1 n, ⟨10, by norm_num, 1, fun n σ hσ T hT => FAL77.part2_explicit n σ hσ T hT⟩⟩
