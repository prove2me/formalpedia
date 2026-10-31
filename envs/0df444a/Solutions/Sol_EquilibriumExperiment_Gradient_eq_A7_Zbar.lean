-- Prove2me | solution 1 for EquilibriumExperiment.Gradient.eq_A7_Zbar
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T13:33:27.185177+00:00
-- url     : https://prove2.me/submissions/ce8994ca-585a-47ce-9760-cb5f8246ee28

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model
import Theorems.Thm_EquilibriumExperiment_Gradient_lemma_2

open MeasureTheory ProbabilityTheory Filter Topology

namespace EqExpA7ZAux

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

section FInt
variable {B : Type} [MeasurableSpace B] (β : Measure B) [IsProbabilityMeasure β]
  (f : B → ℝ → ℝ) (hf01 : ∀ b x, 0 ≤ x → f b x ∈ Set.Icc (0 : ℝ) 1)
  (hfmeas : Measurable (Function.uncurry f))

include hfmeas in
lemma fmeas (x : ℝ) : Measurable (fun b => f b x) :=
  hfmeas.comp (measurable_id.prodMk measurable_const)

include hf01 hfmeas in
lemma fint {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun b => f b x) β ∧ ∫ b, f b x ∂β ∈ Set.Icc (0 : ℝ) 1 := by
  have hint : Integrable (fun b => f b x) β := by
    refine (integrable_const (1 : ℝ)).mono' (fmeas f hfmeas x).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun b => ?_
    have := hf01 b x hx
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  refine ⟨hint, integral_nonneg fun b => (hf01 b x hx).1, ?_⟩
  have : ∫ b, f b x ∂β ≤ ∫ _b, (1 : ℝ) ∂β :=
    integral_mono hint (integrable_const _) fun b => (hf01 b x hx).2
  simpa using this

include hf01 hfmeas in
lemma fint_mono (hfmono : ∀ b, MonotoneOn (f b) (Set.Ici 0)) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : ∫ b, f b x ∂β ≤ ∫ b, f b y ∂β :=
  integral_mono (fint β f hf01 hfmeas hx).1 (fint β f hf01 hfmeas (le_trans hx hxy)).1
    fun b => hfmono b (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (le_trans hx hxy)) hxy

include hf01 hfmeas in
lemma fint_continuousOn (hfcont : ∀ b, ContinuousOn (f b) (Set.Ici 0)) (c : ℝ → ℝ) (s : Set ℝ)
    (hc : ContinuousOn c s) (hc0 : ∀ μ ∈ s, 0 ≤ c μ) :
    ContinuousOn (fun μ => ∫ b, f b (c μ) ∂β) s := by
  apply continuousOn_of_dominated (bound := fun _ => 1)
  · intro μ _
    exact (fmeas f hfmeas (c μ)).aestronglyMeasurable
  · intro μ hμ
    refine Filter.Eventually.of_forall fun b => ?_
    have := hf01 b _ (hc0 μ hμ)
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun b => ?_
    exact (hfcont b).comp hc (fun μ hμ => Set.mem_Ici.mpr (hc0 μ hμ))

include hf01 hfmeas in
lemma fint_tendsto (hfcont : ∀ b, ContinuousOn (f b) (Set.Ici 0)) {ι : Type} {l : Filter ι}
    [l.IsCountablyGenerated] (u : ι → ℝ) {x : ℝ} (hx : 0 ≤ x) (hu : Tendsto u l (𝓝 x))
    (hu0 : ∀ᶠ i in l, 0 ≤ u i) :
    Tendsto (fun i => ∫ b, f b (u i) ∂β) l (𝓝 (∫ b, f b x ∂β)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => 1)
  · exact Filter.Eventually.of_forall fun i => (fmeas f hfmeas (u i)).aestronglyMeasurable
  · filter_upwards [hu0] with i hi
    refine Filter.Eventually.of_forall fun b => ?_
    have := hf01 b _ hi
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun b => ?_
    have h1 : Tendsto u l (𝓝[Set.Ici 0] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hu, hu0⟩
    exact ((hfcont b) x (Set.mem_Ici.mpr hx)).tendsto.comp h1

end FInt

lemma pi_L2 {E : Type} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (z : E → ℝ) (hz : Measurable z) (hz01 : ∀ e, z e ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (hn : 1 ≤ n)
    (c : ℝ) :
    eLpNorm (fun y : Fin n → E => (1 / (n : ℝ)) * ∑ i, z (y i) - c) 2
      (Measure.pi fun _ => ν) ≤
      ENNReal.ofReal ((1 / (n : ℝ)) ^ (1 / (2 : ℝ))) + ENNReal.ofReal |(∫ e, z e ∂ν) - c| := by
  set P := Measure.pi fun _ : Fin n => ν
  set g : (Fin n → E) → ℝ := fun y => (1 / (n : ℝ)) * ∑ i, z (y i) with hg
  have hgm : Measurable g := (Finset.measurable_sum _ fun i _ =>
    hz.comp (measurable_pi_apply i)).const_mul _
  have hzint : Integrable z ν := by
    refine (integrable_const (1 : ℝ)).mono' hz.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hz01 e).1, (hz01 e).2]
  have hzL : MemLp z 2 ν := by
    refine MemLp.of_bound hz.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun e => ?_)
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hz01 e).1, (hz01 e).2]
  set m := ∫ e, z e ∂ν with hm
  have hcoord : ∀ i : Fin n, ∫ y, z (y i) ∂P = m := by
    intro i
    have hmp : MeasurePreserving (fun y : Fin n → E => y i) P ν :=
      measurePreserving_eval (fun _ => ν) i
    rw [hm, ← hmp.map_eq, integral_map (measurable_pi_apply i).aemeasurable
      hz.aestronglyMeasurable]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hEg : ∫ y, g y ∂P = m := by
    simp only [g]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => ?_)]
    · simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · have hmp : MeasurePreserving (fun y : Fin n → E => y i) P ν :=
        measurePreserving_eval (fun _ => ν) i
      exact (integrable_map_measure hz.aestronglyMeasurable
        (measurable_pi_apply i).aemeasurable).mp (by rw [hmp.map_eq]; exact hzint)
  have hgL : MemLp g 2 P := by
    refine MemLp.of_bound hgm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ ∑ i, z (y i) := Finset.sum_nonneg fun i _ => (hz01 _).1
    have h1 : ∑ i, z (y i) ≤ n := by
      have := Finset.sum_le_sum (s := Finset.univ) fun i _ => (hz01 (y i)).2
      simpa using this
    rw [Real.norm_eq_abs, abs_le]
    simp only [g]
    constructor
    · have : 0 ≤ 1 / (n : ℝ) * ∑ i, z (y i) := by positivity
      linarith
    · rw [div_mul_eq_mul_div, one_mul, div_le_one hnpos]; exact h1
  have hvar : Var[g; P] ≤ 1 / n := by
    have h1 : Var[g; P] = (1 / (n : ℝ)) ^ 2 * Var[fun y : Fin n → E => ∑ i, z (y i); P] :=
      variance_const_mul _ _ _
    have h2 : Var[fun y : Fin n → E => ∑ i, z (y i); P] = ∑ _i : Fin n, Var[z; ν] := by
      have := variance_sum_pi (μ := fun _ : Fin n => ν) (X := fun _ => z) (fun _ => hzL)
      rw [← this]
      congr 1
      funext y
      simp [Finset.sum_apply]
    have h3 : Var[z; ν] ≤ 1 := by
      have := variance_le_sq_of_bounded (μ := ν) (a := 0) (b := 1)
        (Filter.Eventually.of_forall hz01) hz.aemeasurable
      nlinarith
    rw [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h4 : (n : ℝ) * Var[z; ν] ≤ n := by nlinarith [variance_nonneg z ν]
    calc (1 / (n : ℝ)) ^ 2 * (n * Var[z; ν]) ≤ (1 / (n : ℝ)) ^ 2 * n :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 1 / n := by field_simp
  have hcen : eLpNorm (fun y => g y - m) 2 P ≤ ENNReal.ofReal ((1 / (n : ℝ)) ^ (1 / (2 : ℝ))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have he : ∫⁻ y, ‖g y - m‖ₑ ^ (2 : ENNReal).toReal ∂P = evariance g P := by
      rw [evariance, hEg]
      refine lintegral_congr fun y => ?_
      rw [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [he, ← ofReal_variance hgL, ENNReal.toReal_ofNat,
      ENNReal.ofReal_rpow_of_nonneg (variance_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow (variance_nonneg _ _) hvar (by norm_num)
  have hsplit : (fun y : Fin n → E => (1 / (n : ℝ)) * ∑ i, z (y i) - c) =
      (fun y => g y - m) + (fun _ => m - c) := by
    funext y; simp only [Pi.add_apply, g]; ring
  rw [hsplit]
  refine le_trans (eLpNorm_add_le (hgm.sub_const _).aestronglyMeasurable
    aestronglyMeasurable_const (by norm_num)) ?_
  gcongr
  rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero P), measure_univ,
    ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]


open EquilibriumExperiment.Gradient in
lemma integral_perturbLaw (p ζ : ℝ) (g : ℝ → ℝ) :
    ∫ x, g x ∂(perturbLaw p ζ) = (g (p + ζ) + g (p - ζ)) / 2 := by
  unfold perturbLaw
  rw [integral_smul_measure, integral_add_measure (integrable_dirac enorm_lt_top)
    (integrable_dirac enorm_lt_top), integral_dirac, integral_dirac]
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

open EquilibriumExperiment.Gradient in
lemma perturbLaw_prob (p ζ : ℝ) : IsProbabilityMeasure (perturbLaw p ζ) := by
  constructor
  simp only [perturbLaw, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, one_div, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

open EquilibriumExperiment.Gradient in
lemma perturbLaw_Iio (p ζ : ℝ) (h1 : 0 ≤ p + ζ) (h2 : 0 ≤ p - ζ) :
    perturbLaw p ζ (Set.Iio 0) = 0 := by
  simp only [perturbLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ measurableSet_Iio, Measure.dirac_apply' _ measurableSet_Iio,
    Set.indicator_of_notMem (by simp; linarith), Set.indicator_of_notMem (by simp; linarith),
    add_zero, mul_zero]

end EqExpA7ZAux

open EqExpA7ZAux EquilibriumExperiment.Gradient

theorem solution {B : Type} [MeasurableSpace B] (M : EquilibriumExperiment.Gradient.Market B)
    (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β)
    {ζ α : ℝ} (hζ : 0 < ζ) (hα : 0 < α) (hα' : α < 1 / 2) :
    Tendsto (fun n : ℕ => eLpNorm (fun x : Outcome B n =>
        M.Zbar n p (ζ * (n : ℝ) ^ (-α)) x - M.muLim p) 2
      (M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α))))) atTop (𝓝 0) := by
  have hL2 := lemma_2 M hM
  obtain ⟨hd, hF, -, -, -, hβ, hω, -, hΩt, hl, -, hΩeq, hΩmeas, hf01, hfmono, hfderiv,
    -, hfmeas, -, -, -, -⟩ := hM
  haveI := hβ
  have hqlim := hL2.2
  have hexL : ∃ μ ∈ Set.Ioc (0 : ℝ) 1, μ = ∫ b, M.f b (p * M.ω (M.d / μ)) ∂M.β := by
    obtain ⟨μ, ⟨h1, h2⟩, -⟩ := (hL2.1 p hp hpos).1
    exact ⟨μ, h1, h2⟩
  have hfcont : ∀ b, ContinuousOn (M.f b) (Set.Ici 0) := by
    intro b x hx
    exact (hfderiv b x hx).1.continuousWithinAt
  obtain ⟨K, hK⟩ := hl
  -- facts about `q_n`
  have hqfacts : ∀ n : ℕ, (∀ μ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.q n μ) ∧
      AntitoneOn (M.q n) (Set.Icc 0 1) ∧ Continuous (M.q n) := by
    intro n
    haveI := (hF n).1
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
    refine ⟨fun μ hμ => ?_, fun x hx y hy hxy => ?_, ?_⟩
    · rw [hqa]; exact bern_nonneg n ha0 hμ
    · rw [hqa, hqa]; exact bern_antitone n a hanti hx hy hxy
    · have : M.q n = bern n a := funext hqa
      rw [this]; exact bern_continuous n a
  -- the perturbation size `ζ_n → 0`
  set ζn : ℕ → ℝ := fun n => ζ * (n : ℝ) ^ (-α) with hζn
  have hζlim : Tendsto ζn atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop).const_mul ζ
    rw [mul_zero] at this
    exact this
  have hζ0 : ∀ n, 0 ≤ ζn n := fun n => mul_nonneg hζ.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hevp : ∀ᶠ n in atTop, ζn n ≤ p := hζlim.eventually (ge_mem_nhds hp)
  haveI hπprob : ∀ n, IsProbabilityMeasure (perturbLaw p (ζn n)) := fun n => perturbLaw_prob _ _
  set π : ℕ → Measure ℝ := fun n => perturbLaw p (ζn n) with hπ
  have hπIio : ∀ n, ζn n ≤ p → π n (Set.Iio 0) = 0 := fun n hn =>
    perturbLaw_Iio p (ζn n) (by linarith [hζ0 n]) (by linarith)
  -- the balance maps `ψ_n`
  set ψ : ℕ → ℝ → ℝ := fun n μ => M.psi n (π n) μ with hψdef
  have hψeq : ∀ n μ, ψ n μ = ∫ y, ∫ P, M.f y (P * M.q n μ) ∂(π n) ∂M.β := fun n μ => rfl
  have hψ01 : ∀ n, ζn n ≤ p → ∀ μ ∈ Set.Icc (0 : ℝ) 1, ψ n μ ∈ Set.Icc (0 : ℝ) 1 :=
    fun n hn μ hμ => (outer_bound M.β (π n) M.f (hπIio n hn) hf01 hfmeas
      ((hqfacts n).1 μ hμ)).2
  have hψanti : ∀ n, ζn n ≤ p → AntitoneOn (ψ n) (Set.Icc 0 1) := fun n hn =>
    psi_antitone M.β (π n) M.f (hπIio n hn) hf01 hfmeas hfmono (M.q n) (hqfacts n).1
      (hqfacts n).2.1
  have hψcont : ∀ n, ζn n ≤ p → ContinuousOn (ψ n) (Set.Icc 0 1) := fun n hn =>
    psi_continuousOn M.β (π n) M.f (hπIio n hn) hf01 hfmeas hfcont (M.q n)
      (hqfacts n).2.2.continuousOn (hqfacts n).1
  have hmuN : ∀ n, ζn n ≤ p → M.muN n (π n) ∈ Set.Icc (0 : ℝ) 1 ∧
      ψ n (M.muN n (π n)) = M.muN n (π n) := by
    intro n hn
    have hex : ∃ μ ∈ Set.Icc (0 : ℝ) 1, M.psi n (π n) μ = μ := by
      have hivt := intermediate_value_Icc' (zero_le_one' ℝ)
        ((hψcont n hn).sub (continuousOn_id (s := Set.Icc (0 : ℝ) 1)))
      have h0 : (0 : ℝ) ∈ Set.Icc (ψ n 1 - id 1) (ψ n 0 - id 0) := by
        have e1 := hψ01 n hn 1 ⟨zero_le_one, le_refl _⟩
        have e0 := hψ01 n hn 0 ⟨le_refl _, zero_le_one⟩
        simp only [id]
        constructor <;> linarith [e1.2, e0.1]
      obtain ⟨μ, hμ, hμeq⟩ := hivt h0
      refine ⟨μ, hμ, ?_⟩
      simp only [Pi.sub_apply, id] at hμeq
      show ψ n μ = μ
      linarith
    unfold Market.muN
    rw [dif_pos hex]
    exact hex.choose_spec
  -- the mean-field map `Ψ`
  set Ψ : ℝ → ℝ := fun μ => ∫ b, M.f b (p * M.ω (M.d / μ)) ∂M.β with hΨdef
  have hωd0 : ∀ μ, 0 < μ → 0 ≤ M.ω (M.d / μ) := fun μ hμ =>
    (hω.1 _ (div_nonneg hd.le hμ.le)).1
  have hΨanti : AntitoneOn Ψ (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx' : (0 : ℝ) < x := hx
    have hy' : (0 : ℝ) < y := hy
    apply fint_mono M.β M.f hf01 hfmeas hfmono (mul_nonneg hp.le (hωd0 y hy'))
    apply mul_le_mul_of_nonneg_left _ hp.le
    exact hω.2.2.2.1 (Set.mem_Ici.mpr (div_nonneg hd.le hy'.le))
      (Set.mem_Ici.mpr (div_nonneg hd.le hx'.le)) (div_le_div_of_nonneg_left hd.le hx' hxy)
  have hmuL : M.muLim p ∈ Set.Ioc (0 : ℝ) 1 ∧ M.muLim p = Ψ (M.muLim p) := by
    unfold Market.muLim
    rw [dif_pos hexL]
    exact hexL.choose_spec
  set μs := M.muLim p with hμs
  -- pointwise convergence `ψ_n → Ψ`
  have hψlim : ∀ μ ∈ Set.Ioc (0 : ℝ) 1, Tendsto (fun n => ψ n μ) atTop (𝓝 (Ψ μ)) := by
    intro μ hμ
    have hq0 : ∀ n, 0 ≤ M.q n μ := fun n => (hqfacts n).1 μ ⟨hμ.1.le, hμ.2⟩
    have hx0 : 0 ≤ p * M.ω (M.d / μ) := mul_nonneg hp.le (hωd0 μ hμ.1)
    have hplus : Tendsto (fun n => ∫ b, M.f b ((p + ζn n) * M.q n μ) ∂M.β) atTop
        (𝓝 (Ψ μ)) := by
      apply fint_tendsto M.β M.f hf01 hfmeas hfcont _ hx0
      · have := ((tendsto_const_nhds (x := p)).add hζlim).mul (hqlim μ hμ)
        rwa [add_zero] at this
      · exact Filter.Eventually.of_forall fun n =>
          mul_nonneg (by linarith [hζ0 n]) (hq0 n)
    have hminus : Tendsto (fun n => ∫ b, M.f b ((p - ζn n) * M.q n μ) ∂M.β) atTop
        (𝓝 (Ψ μ)) := by
      apply fint_tendsto M.β M.f hf01 hfmeas hfcont _ hx0
      · have := ((tendsto_const_nhds (x := p)).sub hζlim).mul (hqlim μ hμ)
        rwa [sub_zero] at this
      · filter_upwards [hevp] with n hn
        exact mul_nonneg (by linarith) (hq0 n)
    have hsum := (hplus.add hminus).div_const 2
    rw [add_self_div_two] at hsum
    refine hsum.congr' ?_
    filter_upwards [hevp] with n hn
    rw [hψeq]
    have hin : ∀ y, ∫ P, M.f y (P * M.q n μ) ∂(π n) =
        (M.f y ((p + ζn n) * M.q n μ) + M.f y ((p - ζn n) * M.q n μ)) / 2 := fun y =>
      integral_perturbLaw p (ζn n) _
    simp_rw [hin]
    rw [integral_div, integral_add (fint M.β M.f hf01 hfmeas
        (mul_nonneg (by linarith [hζ0 n]) (hq0 n))).1
      (fint M.β M.f hf01 hfmeas (mul_nonneg (by linarith) (hq0 n))).1]
  -- `μ_n(p, ζ_n) → μ_a(p)`
  have hmlim : Tendsto (fun n => M.muN n (π n)) atTop (𝓝 μs) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      set s := max a (μs / 2) with hs
      have hs0 : 0 < s := lt_of_lt_of_le (by linarith [hmuL.1.1]) (le_max_right _ _)
      have hsμ : s < μs := max_lt ha (by linarith [hmuL.1.1])
      have hs1 : s ≤ 1 := le_trans hsμ.le hmuL.1.2
      have hΨs : s < Ψ s := by
        have := hΨanti (show (0 : ℝ) < s from hs0) (show (0 : ℝ) < μs from hmuL.1.1) hsμ.le
        linarith [hmuL.2]
      have hev := (hψlim s ⟨hs0, hs1⟩).eventually (lt_mem_nhds hΨs)
      filter_upwards [hev, hevp] with n hn hnp
      refine lt_of_le_of_lt (le_max_left a (μs / 2)) ?_
      by_contra hcon
      push Not at hcon
      have h1 := hψanti n hnp (hmuN n hnp).1 ⟨hs0.le, hs1⟩ hcon
      rw [(hmuN n hnp).2] at h1
      linarith
    · intro b hb
      by_cases hμ1 : μs = 1
      · filter_upwards [hevp] with n hnp
        exact lt_of_le_of_lt (hmuN n hnp).1.2 (by linarith)
      · have hμlt : μs < 1 := lt_of_le_of_ne hmuL.1.2 hμ1
        set t := min b 1 with ht
        have htμ : μs < t := lt_min hb hμlt
        have ht0 : 0 < t := lt_trans hmuL.1.1 htμ
        have ht1 : t ≤ 1 := min_le_right _ _
        have hΨt : Ψ t < t := by
          have := hΨanti (show (0 : ℝ) < μs from hmuL.1.1) (show (0 : ℝ) < t from ht0) htμ.le
          linarith [hmuL.2]
        have hev := (hψlim t ⟨ht0, ht1⟩).eventually (gt_mem_nhds hΨt)
        filter_upwards [hev, hevp] with n hn hnp
        refine lt_of_lt_of_le ?_ (min_le_left b 1)
        by_contra hcon
        push Not at hcon
        have h1 := hψanti n hnp ⟨ht0.le, ht1⟩ (hmuN n hnp).1 hcon
        rw [(hmuN n hnp).2] at h1
        linarith
  -- the `L²` bound
  haveI hU : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Measure.restrict_apply MeasurableSet.univ, Real.volume_Icc]⟩
  have hbound : ∀ᶠ n in atTop, eLpNorm (fun x : Outcome B n =>
      M.Zbar n p (ζn n) x - μs) 2 (M.sample n (π n)) ≤
      ENNReal.ofReal ((1 / (n : ℝ)) ^ (1 / (2 : ℝ))) +
        ENNReal.ofReal |M.muN n (π n) - μs| := by
    filter_upwards [hevp, eventually_ge_atTop 1] with n hnp hn1
    haveI := (hF n).1
    set m := M.muN n (π n) with hm
    set c := M.q n m with hc
    have hc0 : 0 ≤ c := (hqfacts n).1 m (hmuN n hnp).1
    set ν := M.β.prod ((π n).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) with hν
    set A : Set (B × ℝ × ℝ) := {e | e.2.2 ≤ M.f e.1 (e.2.1 * c)} with hAdef
    have hA : MeasurableSet A := by
      apply measurableSet_le measurable_snd.snd
      have : Measurable (fun e : B × ℝ × ℝ => (e.1, e.2.1 * c)) :=
        measurable_fst.prodMk (measurable_snd.fst.mul_const c)
      exact hfmeas.comp this
    let z : B × ℝ × ℝ → ℝ := fun e => M.Z n (π n) ((0 : ℝ), fun _ => e) ⟨0, by omega⟩
    have hzA : ∀ e, z e = A.indicator (fun _ => (1 : ℝ)) e := by
      intro e
      by_cases he : e ∈ A
      · rw [Set.indicator_of_mem he]
        simp only [z, Market.Z]
        exact if_pos he
      · rw [Set.indicator_of_notMem he]
        simp only [z, Market.Z]
        exact if_neg he
    have hzfun : z = A.indicator (fun _ => (1 : ℝ)) := funext hzA
    have hzm : Measurable z := by
      rw [hzfun]; exact measurable_const.indicator hA
    have hz01 : ∀ e, z e ∈ Set.Icc (0 : ℝ) 1 := by
      intro e
      rw [hzA]
      by_cases he : e ∈ A
      · rw [Set.indicator_of_mem he]; exact ⟨zero_le_one, le_rfl⟩
      · rw [Set.indicator_of_notMem he]; exact ⟨le_rfl, zero_le_one⟩
    have hνA : ν A = ENNReal.ofReal m := by
      rw [hν, hAdef, nu_A M.β (π n) M.f (hπIio n hnp) hf01 hfmeas hc0]
      congr 1
      exact (hmuN n hnp).2
    have hzint : ∫ e, z e ∂ν = m := by
      rw [hzfun, integral_indicator_const _ hA, smul_eq_mul, mul_one, Measure.real, hνA,
        ENNReal.toReal_ofReal (hmuN n hnp).1.1]
    have hmp : MeasurePreserving (Prod.snd : Outcome B n → (Fin n → B × ℝ × ℝ))
        (M.sample n (π n)) (Measure.pi fun _ => ν) := measurePreserving_snd
    have hcomp : (fun x : Outcome B n => M.Zbar n p (ζn n) x - μs) =
        (fun y : Fin n → B × ℝ × ℝ => (1 / (n : ℝ)) * ∑ i, z (y i) - μs) ∘ Prod.snd := rfl
    rw [hcomp, eLpNorm_comp_measurePreserving _ hmp]
    · have := pi_L2 ν z hzm hz01 n hn1 μs
      rwa [hzint] at this
    · exact (((Finset.measurable_sum _ fun i _ => hzm.comp (measurable_pi_apply i)).const_mul
        _).sub_const _).aestronglyMeasurable
  have hupper : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / (n : ℝ)) ^ (1 / (2 : ℝ))) +
      ENNReal.ofReal |M.muN n (π n) - μs|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 / (n : ℝ)) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
      have := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).tendsto 0).comp
        tendsto_one_div_atTop_nhds_zero_nat
      rwa [Real.zero_rpow (by norm_num)] at this
    have h2 : Tendsto (fun n : ℕ => |M.muN n (π n) - μs|) atTop (𝓝 0) := by
      have := (hmlim.sub_const μs).abs
      rwa [sub_self, abs_zero] at this
    have := (ENNReal.tendsto_ofReal h1).add (ENNReal.tendsto_ofReal h2)
    rwa [ENNReal.ofReal_zero, add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun n => bot_le) hbound
