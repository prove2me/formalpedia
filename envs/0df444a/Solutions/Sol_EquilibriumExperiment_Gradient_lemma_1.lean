-- Prove2me | solution 1 for EquilibriumExperiment.Gradient.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T13:10:48.160009+00:00
-- url     : https://prove2.me/submissions/8ae696f2-1c2a-4ebb-8d9c-86b7d026ddfd

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EqExpL1Aux

/-- Bernstein sum `∑_{k ≤ n} C(n,k) μ^k (1-μ)^(n-k) a_k`. -/
noncomputable def bern (n : ℕ) (a : ℕ → ℝ) (μ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k) * a k

lemma bern_zero (a : ℕ → ℝ) (μ : ℝ) : bern 0 a μ = a 0 := by
  simp [bern]

lemma bern_succ (n : ℕ) (a : ℕ → ℝ) (μ : ℝ) :
    bern (n + 1) a μ = (1 - μ) * bern n a μ + μ * bern n (fun k => a (k + 1)) μ := by
  unfold bern
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  have h1 : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * μ ^ (k + 1) * (1 - μ) ^ (n + 1 - (k + 1))
      * a (k + 1) = μ * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k)
      * a (k + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [show n + 1 - (k + 1) = n - k by omega]
    ring
  have h2 : ∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ) * μ ^ (k + 1) *
      (1 - μ) ^ (n + 1 - (k + 1)) * a (k + 1) + (n + 1).choose 0 * μ ^ 0 * (1 - μ) ^ (n + 1 - 0)
      * a 0 = (1 - μ) * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k)
      * a k := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul, zero_mul,
      add_zero]
    conv_rhs => rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < n := Finset.mem_range.mp hk
      rw [show n + 1 - (k + 1) = (n - (k + 1)) + 1 by omega, pow_succ]
      ring
    · simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero, pow_succ]
      ring
  linarith

lemma bern_mono_seq (n : ℕ) {a b : ℕ → ℝ} (h : ∀ k, a k ≤ b k) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) : bern n a μ ≤ bern n b μ := by
  unfold bern
  refine Finset.sum_le_sum fun k _ => ?_
  have : 0 ≤ (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k) := by
    have h1 : 0 ≤ 1 - μ := by linarith [hμ.2]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hμ.1 _)) (pow_nonneg h1 _)
  exact mul_le_mul_of_nonneg_left (h k) this

lemma bern_nonneg (n : ℕ) {a : ℕ → ℝ} (h : ∀ k, 0 ≤ a k) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ bern n a μ := by
  have := bern_mono_seq n (a := fun _ => 0) (b := a) h hμ
  simpa [bern] using this

lemma bern_antitone (n : ℕ) : ∀ a : ℕ → ℝ, Antitone a → AntitoneOn (bern n a) (Set.Icc 0 1) := by
  induction n with
  | zero =>
    intro a _ x _ y _ _
    simp [bern_zero]
  | succ n ih =>
    intro a ha x hx y hy hxy
    have hS : Antitone (fun k => a (k + 1)) := fun i j hij => ha (by omega)
    rw [bern_succ, bern_succ]
    have e1 := ih a ha hx hy hxy
    have e2 := ih _ hS hx hy hxy
    have e3 : bern n (fun k => a (k + 1)) x ≤ bern n a x :=
      bern_mono_seq n (fun k => ha (Nat.le_succ k)) hx
    have hy1 : 0 ≤ 1 - y := by linarith [hy.2]
    have hy0 : 0 ≤ y := hy.1
    nlinarith [mul_le_mul_of_nonneg_left e1 hy1, mul_le_mul_of_nonneg_left e2 hy0]

lemma bern_continuous (n : ℕ) (a : ℕ → ℝ) : Continuous (bern n a) := by
  unfold bern
  fun_prop


section Psi
variable {B : Type} [MeasurableSpace B]

lemma ae_nonneg_of_Iio (π : Measure ℝ) (hπ : π (Set.Iio 0) = 0) : ∀ᵐ P ∂π, 0 ≤ P := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp [not_le]
  rw [this]; exact hπ

variable (β : Measure B) [IsProbabilityMeasure β] (π : Measure ℝ) [IsProbabilityMeasure π]
  (f : B → ℝ → ℝ) (hπ : π (Set.Iio 0) = 0) (hf01 : ∀ b x, 0 ≤ x → f b x ∈ Set.Icc (0 : ℝ) 1)
  (hfmeas : Measurable (Function.uncurry f))

include hfmeas in
lemma inner_meas (y : B) (t : ℝ) : Measurable (fun P : ℝ => f y (P * t)) := by
  have : Measurable (fun P : ℝ => (y, P * t)) :=
    measurable_const.prodMk (measurable_id.mul_const t)
  exact hfmeas.comp this

include hfmeas in
lemma outer_meas (t : ℝ) : Measurable (fun y : B => ∫ P, f y (P * t) ∂π) := by
  have hF : StronglyMeasurable (fun z : B × ℝ => f z.1 (z.2 * t)) := by
    apply Measurable.stronglyMeasurable
    have : Measurable (fun z : B × ℝ => (z.1, z.2 * t)) :=
      measurable_fst.prodMk (measurable_snd.mul_const t)
    exact hfmeas.comp this
  exact (hF.integral_prod_right' (ν := π)).measurable

include hπ hf01 hfmeas in
lemma inner_bound (y : B) {t : ℝ} (ht : 0 ≤ t) :
    (∀ᵐ P ∂π, f y (P * t) ∈ Set.Icc (0 : ℝ) 1) ∧ Integrable (fun P => f y (P * t)) π ∧
    ∫ P, f y (P * t) ∂π ∈ Set.Icc (0 : ℝ) 1 := by
  have hae : ∀ᵐ P ∂π, f y (P * t) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [ae_nonneg_of_Iio π hπ] with P hP
    exact hf01 y _ (mul_nonneg hP ht)
  have hint : Integrable (fun P => f y (P * t)) π := by
    refine (integrable_const (1 : ℝ)).mono' (inner_meas f hfmeas y t).aestronglyMeasurable ?_
    filter_upwards [hae] with P hP
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hP.1, hP.2]
  refine ⟨hae, hint, ?_, ?_⟩
  · exact integral_nonneg_of_ae (hae.mono fun P hP => hP.1)
  · have : ∫ P, f y (P * t) ∂π ≤ ∫ _P, (1 : ℝ) ∂π :=
      integral_mono_ae hint (integrable_const _) (hae.mono fun P hP => hP.2)
    simpa using this

include hπ hf01 hfmeas in
lemma outer_bound {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun y => ∫ P, f y (P * t) ∂π) β ∧
    ∫ y, ∫ P, f y (P * t) ∂π ∂β ∈ Set.Icc (0 : ℝ) 1 := by
  have hb : ∀ y, ∫ P, f y (P * t) ∂π ∈ Set.Icc (0 : ℝ) 1 :=
    fun y => (inner_bound π f hπ hf01 hfmeas y ht).2.2
  have hint : Integrable (fun y => ∫ P, f y (P * t) ∂π) β := by
    refine (integrable_const (1 : ℝ)).mono' (outer_meas π f hfmeas t).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hb y).1, (hb y).2]
  refine ⟨hint, ?_, ?_⟩
  · exact integral_nonneg fun y => (hb y).1
  · have : ∫ y, ∫ P, f y (P * t) ∂π ∂β ≤ ∫ _y, (1 : ℝ) ∂β :=
      integral_mono hint (integrable_const _) fun y => (hb y).2
    simpa using this

include hπ hf01 hfmeas in
lemma psi_antitone (hfmono : ∀ b, MonotoneOn (f b) (Set.Ici 0)) (c : ℝ → ℝ)
    (hc0 : ∀ μ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ c μ) (hcanti : AntitoneOn c (Set.Icc 0 1)) :
    AntitoneOn (fun μ => ∫ y, ∫ P, f y (P * c μ) ∂π ∂β) (Set.Icc 0 1) := by
  intro x hx z hz hxz
  have hcz := hc0 z hz
  have hcx := hc0 x hx
  have hle : c z ≤ c x := hcanti hx hz hxz
  apply integral_mono (outer_bound β π f hπ hf01 hfmeas hcz).1
    (outer_bound β π f hπ hf01 hfmeas hcx).1
  intro y
  apply integral_mono_ae (inner_bound π f hπ hf01 hfmeas y hcz).2.1
    (inner_bound π f hπ hf01 hfmeas y hcx).2.1
  filter_upwards [ae_nonneg_of_Iio π hπ] with P hP
  exact hfmono y (Set.mem_Ici.mpr (mul_nonneg hP hcz)) (Set.mem_Ici.mpr (mul_nonneg hP hcx))
    (mul_le_mul_of_nonneg_left hle hP)

include hπ hf01 hfmeas in
lemma psi_continuousOn (hfcont : ∀ b, ContinuousOn (f b) (Set.Ici 0)) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Set.Icc 0 1))
    (hc0 : ∀ μ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ c μ) :
    ContinuousOn (fun μ => ∫ y, ∫ P, f y (P * c μ) ∂π ∂β) (Set.Icc 0 1) := by
  have hinner : ∀ y, ContinuousOn (fun μ => ∫ P, f y (P * c μ) ∂π) (Set.Icc 0 1) := by
    intro y
    apply continuousOn_of_dominated (bound := fun _ => 1)
    · intro μ _
      exact (inner_meas f hfmeas y (c μ)).aestronglyMeasurable
    · intro μ hμ
      filter_upwards [(inner_bound π f hπ hf01 hfmeas y (hc0 μ hμ)).1] with P hP
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hP.1, hP.2]
    · exact integrable_const _
    · filter_upwards [ae_nonneg_of_Iio π hπ] with P hP
      refine (hfcont y).comp (continuousOn_const.mul hc) ?_
      intro μ hμ
      exact Set.mem_Ici.mpr (mul_nonneg hP (hc0 μ hμ))
  apply continuousOn_of_dominated (bound := fun _ => 1)
  · intro μ _
    exact (outer_meas π f hfmeas (c μ)).aestronglyMeasurable
  · intro μ hμ
    refine Filter.Eventually.of_forall fun y => ?_
    have := (inner_bound π f hπ hf01 hfmeas y (hc0 μ hμ)).2.2
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  · exact integrable_const _
  · exact Filter.Eventually.of_forall hinner

include hπ hf01 hfmeas in
lemma nu_A {t : ℝ} (ht : 0 ≤ t) :
    (β.prod (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))))
      {e : B × ℝ × ℝ | e.2.2 ≤ f e.1 (e.2.1 * t)} =
      ENNReal.ofReal (∫ y, ∫ P, f y (P * t) ∂π ∂β) := by
  have hA : MeasurableSet {e : B × ℝ × ℝ | e.2.2 ≤ f e.1 (e.2.1 * t)} := by
    apply measurableSet_le measurable_snd.snd
    have : Measurable (fun e : B × ℝ × ℝ => (e.1, e.2.1 * t)) :=
      measurable_fst.prodMk (measurable_snd.fst.mul_const t)
    exact hfmeas.comp this
  rw [Measure.prod_apply hA]
  have inner : ∀ y : B, (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
      (Prod.mk y ⁻¹' {e : B × ℝ × ℝ | e.2.2 ≤ f e.1 (e.2.1 * t)}) =
      ENNReal.ofReal (∫ P, f y (P * t) ∂π) := by
    intro y
    rw [Measure.prod_apply (measurable_prodMk_left hA)]
    have hib := inner_bound π f hπ hf01 hfmeas y ht
    have hae : ∀ᵐ P ∂π, (volume.restrict (Set.Icc (0 : ℝ) 1))
        (Prod.mk P ⁻¹' (Prod.mk y ⁻¹' {e : B × ℝ × ℝ | e.2.2 ≤ f e.1 (e.2.1 * t)})) =
        ENNReal.ofReal (f y (P * t)) := by
      filter_upwards [hib.1] with P hP
      have h1 : Prod.mk P ⁻¹' (Prod.mk y ⁻¹' {e : B × ℝ × ℝ | e.2.2 ≤ f e.1 (e.2.1 * t)}) =
          Set.Iic (f y (P * t)) := by
        ext u; simp
      rw [h1, Measure.restrict_apply measurableSet_Iic]
      have h2 : Set.Iic (f y (P * t)) ∩ Set.Icc 0 1 = Set.Icc 0 (f y (P * t)) := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2 hP.2⟩
      rw [h2, Real.volume_Icc, sub_zero]
    rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal hib.2.1
      (hib.1.mono fun P hP => hP.1)]
  simp_rw [inner]
  have hob := outer_bound β π f hπ hf01 hfmeas ht
  rw [← ofReal_integral_eq_lintegral_ofReal hob.1
    (Filter.Eventually.of_forall fun y => (inner_bound π f hπ hf01 hfmeas y ht).2.2.1)]

end Psi

section Count

lemma prod_ite_const {n : ℕ} (S : Finset (Fin n)) (a b : ENNReal) :
    ∏ i, (if i ∈ S then a else b) = a ^ S.card * b ^ (n - S.card) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 2
  · congr 1
    ext i; simp
  · rw [Finset.filter_not, Finset.card_sdiff]
    simp only [Finset.card_univ, Fintype.card_fin]
    congr 2
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.inter_univ]

lemma pi_count {E : Type} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (A : Set E) (hA : MeasurableSet A) (z : E → ℝ) (hz1 : ∀ e ∈ A, z e = 1)
    (hz0 : ∀ e ∉ A, z e = 0) (n k : ℕ) :
    Measure.pi (fun _ : Fin n => ν) {y | ∑ i, z (y i) = (k : ℝ)} =
      (n.choose k : ENNReal) * ν A ^ k * ν Aᶜ ^ (n - k) := by
  classical
  have hsum : ∀ (y : Fin n → E) (S : Finset (Fin n)), (∀ i, (y i ∈ A ↔ i ∈ S)) →
      ∑ i, z (y i) = (S.card : ℝ) := by
    intro y S hS
    have : ∀ i, z (y i) = if i ∈ S then 1 else 0 := by
      intro i
      by_cases hi : i ∈ S
      · rw [if_pos hi]; exact hz1 _ ((hS i).mpr hi)
      · rw [if_neg hi]; exact hz0 _ (fun h => hi ((hS i).mp h))
    simp only [this]
    rw [Finset.sum_boole]
    simp
  have hset : {y : Fin n → E | ∑ i, z (y i) = (k : ℝ)} =
      ⋃ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        Set.pi Set.univ (fun i => if i ∈ S then A else Aᶜ) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_powersetCard, Set.mem_pi,
      Set.mem_univ, true_implies, exists_prop]
    constructor
    · intro h
      refine ⟨Finset.univ.filter (fun i => y i ∈ A), ⟨Finset.subset_univ _, ?_⟩, ?_⟩
      · have := hsum y (Finset.univ.filter (fun i => y i ∈ A)) (fun i => by simp)
        rw [this] at h
        exact_mod_cast h
      · intro i
        by_cases hi : y i ∈ A
        · simp [hi]
        · simp [hi]
    · rintro ⟨S, ⟨-, hS⟩, hy⟩
      have hiff : ∀ i, (y i ∈ A ↔ i ∈ S) := by
        intro i
        have := hy i
        by_cases hi : i ∈ S
        · simp only [hi, if_true] at this; simp [hi, this]
        · simp only [hi, if_false, Set.mem_compl_iff] at this; simp [hi, this]
      rw [hsum y S hiff, hS]
  rw [hset, measure_biUnion_finset]
  · have : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        Measure.pi (fun _ : Fin n => ν) (Set.pi Set.univ (fun i => if i ∈ S then A else Aᶜ)) =
          ν A ^ k * ν Aᶜ ^ (n - k) := by
      intro S hS
      rw [Measure.pi_pi]
      have h2 : ∀ i, ν (if i ∈ S then A else Aᶜ) = if i ∈ S then ν A else ν Aᶜ := by
        intro i; split_ifs <;> rfl
      simp only [h2]
      rw [prod_ite_const, (Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  · intro S _ T _ hST
    rw [Function.onFun, Set.disjoint_left]
    intro y hyS hyT
    simp only [Set.mem_pi, Set.mem_univ, true_implies] at hyS hyT
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra h
      push Not at h
      exact hST (Finset.ext h)
    have h1 := hyS i
    have h2 := hyT i
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp_all
  · intro S _
    refine MeasurableSet.univ_pi fun i => ?_
    split_ifs
    · exact hA
    · exact hA.compl

end Count

end EqExpL1Aux

open EqExpL1Aux EquilibriumExperiment.Gradient

theorem solution {B : Type} [MeasurableSpace B] (M : EquilibriumExperiment.Gradient.Market B)
    (hM : M.Standing)
    (π : Measure ℝ) [IsProbabilityMeasure π] (hπ : π (Set.Iio 0) = 0) {n : ℕ} (hn : 1 ≤ n) :
    (∃! μ : ℝ, μ ∈ Set.Icc (0 : ℝ) 1 ∧ M.psi n π μ = μ) ∧
    ∀ k : ℕ, k ≤ n →
      M.sample n π {x | ∑ i, M.Z n π x i = (k : ℝ)} =
        ENNReal.ofReal ((n.choose k : ℝ) * M.muN n π ^ k * (1 - M.muN n π) ^ (n - k)) := by
  obtain ⟨-, hF, -, -, -, hβ, hω, -, hΩt, hl, -, hΩeq, hΩmeas, hf01, hfmono, hfderiv, -, hfmeas,
    -, -, -, -⟩ := hM
  haveI := (hF n).1
  haveI := hβ
  obtain ⟨K, hK⟩ := hl
  set a : ℕ → ℝ := fun k => ∫ D, M.Ω D k ∂(M.F n) with ha
  have hqa : ∀ μ, M.q n μ = bern n a μ := fun μ => rfl
  have hDae : ∀ᵐ D ∂(M.F n), 0 ≤ D := ae_nonneg_of_Iio _ (hF n).2
  have hΩb : ∀ D, 0 ≤ D → ∀ k : ℕ, 0 ≤ M.Ω D k ∧ M.Ω D k ≤ 1 + K := by
    intro D hD k
    rw [hΩeq D k hD (Nat.cast_nonneg k)]
    have h1 := hω.1 (D / k) (div_nonneg hD (Nat.cast_nonneg k))
    have h2 := hK D k hD (Nat.cast_nonneg k)
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hintk : ∀ k : ℕ, Integrable (fun D => M.Ω D k) (M.F n) := by
    intro k
    refine (integrable_const (1 + K)).mono' (hΩmeas k).aestronglyMeasurable ?_
    filter_upwards [hDae] with D hD
    have := hΩb D hD k
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  have ha0 : ∀ k, 0 ≤ a k := fun k =>
    integral_nonneg_of_ae (hDae.mono fun D hD => (hΩb D hD k).1)
  have hanti : Antitone a := by
    apply antitone_nat_of_succ_le
    intro k
    apply integral_mono_ae (hintk (k + 1)) (hintk k)
    filter_upwards [hDae] with D hD
    have h := hΩt D (k : ℝ) ((k : ℝ) + 1) hD (Nat.cast_nonneg k) (by linarith)
    rw [Nat.cast_succ]; exact h
  have hq0 : ∀ μ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.q n μ := fun μ hμ => by
    rw [hqa]; exact bern_nonneg n ha0 hμ
  have hqanti : AntitoneOn (M.q n) (Set.Icc 0 1) := by
    intro x hx y hy hxy
    rw [hqa, hqa]; exact bern_antitone n a hanti hx hy hxy
  have hqcont : ContinuousOn (M.q n) (Set.Icc 0 1) := by
    have : M.q n = bern n a := funext hqa
    rw [this]; exact (bern_continuous n a).continuousOn
  have hfcont : ∀ b, ContinuousOn (M.f b) (Set.Ici 0) := by
    intro b x hx
    exact (hfderiv b x hx).1.continuousWithinAt
  have hpsi : ∀ μ, M.psi n π μ = ∫ y, ∫ P, M.f y (P * M.q n μ) ∂π ∂M.β := fun μ => rfl
  have hψ01 : ∀ μ ∈ Set.Icc (0 : ℝ) 1, M.psi n π μ ∈ Set.Icc (0 : ℝ) 1 := by
    intro μ hμ
    rw [hpsi]
    exact (outer_bound M.β π M.f hπ hf01 hfmeas (hq0 μ hμ)).2
  have hψcont : ContinuousOn (M.psi n π) (Set.Icc 0 1) :=
    psi_continuousOn M.β π M.f hπ hf01 hfmeas hfcont (M.q n) hqcont hq0
  have hψanti : AntitoneOn (M.psi n π) (Set.Icc 0 1) :=
    psi_antitone M.β π M.f hπ hf01 hfmeas hfmono (M.q n) hq0 hqanti
  -- existence
  have hex : ∃ μ ∈ Set.Icc (0 : ℝ) 1, M.psi n π μ = μ := by
    have hivt := intermediate_value_Icc' (zero_le_one' ℝ)
      (hψcont.sub (continuousOn_id (s := Set.Icc (0 : ℝ) 1)))
    have h0 : (0 : ℝ) ∈ Set.Icc (M.psi n π 1 - id 1) (M.psi n π 0 - id 0) := by
      have e1 := hψ01 1 ⟨zero_le_one, le_refl _⟩
      have e0 := hψ01 0 ⟨le_refl _, zero_le_one⟩
      simp only [id]
      constructor <;> linarith [e1.2, e0.1]
    obtain ⟨μ, hμ, hμeq⟩ := hivt h0
    refine ⟨μ, hμ, ?_⟩
    simp only [Pi.sub_apply, id] at hμeq
    linarith
  have huniq : ∀ μ₁ ∈ Set.Icc (0 : ℝ) 1, ∀ μ₂ ∈ Set.Icc (0 : ℝ) 1,
      M.psi n π μ₁ = μ₁ → M.psi n π μ₂ = μ₂ → μ₁ ≤ μ₂ := by
    intro μ₁ h₁ μ₂ h₂ e₁ e₂
    by_contra hlt
    push Not at hlt
    have := hψanti h₂ h₁ hlt.le
    linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨μ, hμ, hμeq⟩ := hex
    refine ⟨μ, ⟨hμ, hμeq⟩, ?_⟩
    rintro μ' ⟨hμ', hμ'eq⟩
    exact le_antisymm (huniq μ' hμ' μ hμ hμ'eq hμeq) (huniq μ hμ μ' hμ' hμeq hμ'eq)
  · intro k _
    have hmuN : M.muN n π ∈ Set.Icc (0 : ℝ) 1 ∧ M.psi n π (M.muN n π) = M.muN n π := by
      unfold Market.muN
      rw [dif_pos hex]
      exact hex.choose_spec
    set m := M.muN n π with hm
    set c := M.q n m with hc
    have hc0 : 0 ≤ c := hq0 m hmuN.1
    haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      ⟨by simp [Measure.restrict_apply MeasurableSet.univ, Real.volume_Icc]⟩
    set ν := M.β.prod (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) with hν
    set A : Set (B × ℝ × ℝ) := {e | e.2.2 ≤ M.f e.1 (e.2.1 * c)} with hAdef
    have hA : MeasurableSet A := by
      apply measurableSet_le measurable_snd.snd
      have : Measurable (fun e : B × ℝ × ℝ => (e.1, e.2.1 * c)) :=
        measurable_fst.prodMk (measurable_snd.fst.mul_const c)
      exact hfmeas.comp this
    let z : B × ℝ × ℝ → ℝ := fun e => M.Z n π ((0 : ℝ), fun _ => e) ⟨0, by omega⟩
    have hz1 : ∀ e ∈ A, z e = 1 := by
      intro e he
      simp only [z, Market.Z]
      exact if_pos he
    have hz0 : ∀ e ∉ A, z e = 0 := by
      intro e he
      simp only [z, Market.Z]
      exact if_neg he
    have hset : {x : Outcome B n | ∑ i, M.Z n π x i = (k : ℝ)} =
        Set.univ ×ˢ {y : Fin n → B × ℝ × ℝ | ∑ i, z (y i) = (k : ℝ)} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
      rfl
    have hνA : ν A = ENNReal.ofReal m := by
      rw [hν, hAdef, nu_A M.β π M.f hπ hf01 hfmeas hc0]
      congr 1
      exact hmuN.2
    have hνAc : ν Aᶜ = ENNReal.ofReal (1 - m) := by
      rw [prob_compl_eq_one_sub hA, hνA, ENNReal.ofReal_sub _ hmuN.1.1, ENNReal.ofReal_one]
    unfold Market.sample
    rw [hset, Measure.prod_prod, measure_univ, one_mul, pi_count ν A hA z hz1 hz0 n k, hνA, hνAc]
    have h1m : 0 ≤ 1 - m := by linarith [hmuN.1.2]
    rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hmuN.1.1 _)),
      ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_pow hmuN.1.1, ENNReal.ofReal_pow h1m, ENNReal.ofReal_natCast]
