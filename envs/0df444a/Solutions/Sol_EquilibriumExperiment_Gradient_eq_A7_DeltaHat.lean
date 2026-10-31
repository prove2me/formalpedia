-- Prove2me | solution 1 for EquilibriumExperiment.Gradient.eq_A7_DeltaHat
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T13:58:32.98276+00:00
-- url     : https://prove2.me/submissions/3d4cdaee-b5bf-4221-850e-942be21e2280

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


namespace EqExpDHAux
open Real EqExpA7ZAux

variable {E : Type} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]

lemma pi_coord_integral (n : ℕ) (X : E → ℝ) (hX : AEStronglyMeasurable X ν) (i : Fin n) :
    ∫ y, X (y i) ∂(Measure.pi fun _ : Fin n => ν) = ∫ e, X e ∂ν := by
  have hmp : MeasurePreserving (fun y : Fin n → E => y i) (Measure.pi fun _ => ν) ν :=
    measurePreserving_eval (fun _ => ν) i
  calc ∫ y, X (y i) ∂(Measure.pi fun _ : Fin n => ν)
      = ∫ e, X e ∂((Measure.pi fun _ : Fin n => ν).map (fun y => y i)) :=
        (integral_map (measurable_pi_apply i).aemeasurable (by rw [hmp.map_eq]; exact hX)).symm
    _ = ∫ e, X e ∂ν := by rw [hmp.map_eq]

/-- one-sided Hoeffding for i.i.d. coordinates with values in `[-1, 1]` and mean zero -/
lemma hoeffding_pi (n : ℕ) (X : E → ℝ) (hX : Measurable X)
    (hb : ∀ᵐ e ∂ν, X e ∈ Set.Icc (-1 : ℝ) 1) (hm : ∫ e, X e ∂ν = 0) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => ν).real {y | t ≤ ∑ i, X (y i)} ≤ exp (-t ^ 2 / (2 * n)) := by
  set P := Measure.pi fun _ : Fin n => ν
  have hind : iIndepFun (fun (i : Fin n) (y : Fin n → E) => X (y i)) P :=
    iIndepFun_pi (μ := fun _ => ν) (X := fun _ => X) fun _ => hX.aemeasurable
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (fun y : Fin n → E => X (y i)) ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2) P := by
    intro i _
    have hmp : MeasurePreserving (fun y : Fin n → E => y i) P ν :=
      measurePreserving_eval (fun _ => ν) i
    apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    · exact (hX.comp (measurable_pi_apply i)).aemeasurable
    · exact hmp.quasiMeasurePreserving.ae (p := fun e => X e ∈ Set.Icc (-1 : ℝ) 1) hb
    · rw [pi_coord_integral ν n X hX.aestronglyMeasurable i, hm]
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub ht
  have hc : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal) = 1 := by
    have : ‖(1 : ℝ) - (-1)‖₊ = 2 := by
      rw [show (1 : ℝ) - (-1) = 2 by norm_num]; simp
    rw [this]; norm_num
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, NNReal.coe_natCast] at h
  convert h using 3

/-- second moment of a sum of i.i.d. centred bounded coordinates -/
lemma sq_sum_pi (n : ℕ) (X : E → ℝ) (hX : Measurable X) {M : ℝ}
    (hb : ∀ᵐ e ∂ν, X e ∈ Set.Icc (-M) M) (hm : ∫ e, X e ∂ν = 0) :
    ∫ y, (∑ i, X (y i)) ^ 2 ∂(Measure.pi fun _ : Fin n => ν) ≤ n * M ^ 2 := by
  set P := Measure.pi fun _ : Fin n => ν
  have hXL : MemLp X 2 ν := by
    refine MemLp.of_bound hX.aestronglyMeasurable M (hb.mono fun e he => ?_)
    rw [Real.norm_eq_abs, abs_le]; exact he
  have hsum_meas : Measurable (fun y : Fin n → E => ∑ i, X (y i)) :=
    Finset.measurable_sum _ fun i _ => hX.comp (measurable_pi_apply i)
  have hXint : Integrable X ν := hXL.integrable one_le_two
  have hmean : ∫ y, (∑ i, X (y i)) ∂P = 0 := by
    rw [integral_finsetSum _ (fun i _ => ?_)]
    · rw [Finset.sum_eq_zero]
      intro i _
      rw [pi_coord_integral ν n X hX.aestronglyMeasurable, hm]
    · have hmp : MeasurePreserving (fun y : Fin n → E => y i) P ν :=
        measurePreserving_eval (fun _ => ν) i
      exact (integrable_map_measure hX.aestronglyMeasurable
        (measurable_pi_apply i).aemeasurable).mp (by rw [hmp.map_eq]; exact hXint)
  have hvar := variance_sum_pi (μ := fun _ : Fin n => ν) (X := fun _ => X) (fun _ => hXL)
  have hfun : (∑ i : Fin n, fun ω : Fin n → E => X (ω i)) = fun y => ∑ i, X (y i) := by
    funext y; simp [Finset.sum_apply]
  rw [hfun, variance_eq_integral hsum_meas.aemeasurable, hmean] at hvar
  simp only [sub_zero] at hvar
  rw [hvar]
  have hv : Var[X; ν] ≤ M ^ 2 := by
    have h := variance_le_sq_of_bounded hb hX.aemeasurable
    have : ((M - -M) / 2) ^ 2 = M ^ 2 := by ring
    linarith
  calc ∑ _i : Fin n, Var[X; ν] ≤ ∑ _i : Fin n, M ^ 2 := Finset.sum_le_sum fun _ _ => hv
    _ = n * M ^ 2 := by simp


/-- the regression estimate (4.1) as a function of the coordinates -/
noncomputable def Dhat (n : ℕ) (ζ : ℝ) (zv εv : Fin n → ℝ) : ℝ :=
  ζ⁻¹ * (∑ i, (zv i - (1 / (n : ℝ)) * ∑ j, zv j) * (εv i - (1 / (n : ℝ)) * ∑ j, εv j)) /
    ∑ i, (εv i - (1 / (n : ℝ)) * ∑ j, εv j) ^ 2

lemma S_zero_or_ge_one (n : ℕ) (hn : 1 ≤ n) (εv : Fin n → ℝ) (hpm : ∀ i, εv i = 1 ∨ εv i = -1) :
    ∑ i, (εv i - (1 / (n : ℝ)) * ∑ j, εv j) ^ 2 = 0 ∨
      1 ≤ ∑ i, (εv i - (1 / (n : ℝ)) * ∑ j, εv j) ^ 2 := by
  set eb := (1 / (n : ℝ)) * ∑ j, εv j with heb
  by_cases h : ∃ i j, εv i = 1 ∧ εv j = -1
  · right
    obtain ⟨i, j, hi, hj⟩ := h
    have hij : i ≠ j := by intro h; rw [h] at hi; linarith
    have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun k => (εv k - eb) ^ 2) (fun k _ _ => sq_nonneg _)
    rw [Finset.sum_pair hij, hi, hj] at this
    nlinarith [sq_nonneg eb]
  · left
    push Not at h
    have i0 : Fin n := ⟨0, by omega⟩
    have hall : ∀ i, εv i = εv i0 := by
      intro i
      rcases hpm i with h1 | h1 <;> rcases hpm i0 with h2 | h2
      · rw [h1, h2]
      · exact absurd h2 (h i i0 h1)
      · exact absurd h1 (h i0 i h2)
      · rw [h1, h2]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have heb' : eb = εv i0 := by
      rw [heb, Finset.sum_congr rfl (fun i _ => hall i), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
    apply Finset.sum_eq_zero
    intro i _
    rw [hall i, heb', sub_self]; ring

lemma aux_sq (R t H : ℝ) (ht : t ^ 2 ≤ 1 / 4) : (R - t * H) ^ 2 ≤ 2 * (R ^ 2 + H ^ 2) := by
  nlinarith [sq_nonneg (R + t * H), mul_le_mul_of_nonneg_right ht (sq_nonneg H)]

lemma aux_good (c X n S : ℝ) (hc : 0 ≤ c) (hX : 0 ≤ X) (hn : 0 < n) (hS : 3 * n / 4 ≤ S) :
    c * X * n ^ 2 ≤ 2 * c * X * S ^ 2 := by
  have h1 : 0 ≤ 3 * n / 4 := by positivity
  have h2 : (3 * n / 4) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ h1 hS 2
  have h3 : n ^ 2 ≤ 2 * S ^ 2 := by nlinarith
  have h4 : 0 ≤ c * X := mul_nonneg hc hX
  nlinarith [mul_le_mul_of_nonneg_left h3 h4]

lemma aux_crude (c N n S : ℝ) (hc : 0 ≤ c) (hn : 0 ≤ n) (hS : 1 ≤ S) (hN : N ^ 2 ≤ n * S) :
    c * N ^ 2 ≤ c * n * S ^ 2 := by
  have h1 : n * S ≤ n * S ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hn
  nlinarith [mul_le_mul_of_nonneg_left (le_trans hN h1) hc]

lemma pointwise_bound (n : ℕ) (hn : 2 ≤ n) (zv εv : Fin n → ℝ)
    (hz : ∀ i, zv i ∈ Set.Icc (0 : ℝ) 1) (hpm : ∀ i, εv i = 1 ∨ εv i = -1)
    (m a ζ : ℝ) (hζ : 0 < ζ) :
    (Dhat n ζ zv εv - ζ⁻¹ * a) ^ 2 ≤
      4 * (ζ⁻¹) ^ 2 * ((∑ i, (zv i - m - a * εv i) * εv i) ^ 2 +
        (∑ i, (zv i - m - a * εv i)) ^ 2) / (n : ℝ) ^ 2 +
      (2 * (ζ⁻¹) ^ 2 * n + 2 * (ζ⁻¹ * a) ^ 2) *
        (if (n : ℝ) / 2 < |∑ i, εv i| then 1 else 0) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set s := ∑ i, εv i with hs
  set Z := ∑ i, zv i with hZ
  set W := ∑ i, zv i * εv i with hW
  set R := ∑ i, (zv i - m - a * εv i) * εv i with hR
  set H := ∑ i, (zv i - m - a * εv i) with hH
  set N := ∑ i, (zv i - (1 / (n : ℝ)) * Z) * (εv i - (1 / (n : ℝ)) * s) with hNdef
  set S := ∑ i, (εv i - (1 / (n : ℝ)) * s) ^ 2 with hSdef
  have hsq : ∀ i, εv i ^ 2 = 1 := fun i => by rcases hpm i with h | h <;> rw [h] <;> norm_num
  have hq : ∑ i, εv i ^ 2 = n := by simp [hsq]
  have hN : N = W - Z * s / n := by
    rw [hNdef]
    have : ∀ i, (zv i - (1 / (n : ℝ)) * Z) * (εv i - (1 / (n : ℝ)) * s) =
        zv i * εv i - (1 / (n : ℝ)) * s * zv i - (1 / (n : ℝ)) * Z * εv i +
          (1 / (n : ℝ)) ^ 2 * Z * s := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hW, ← hZ, ← hs]
    field_simp
    ring
  have hS : S = n - s ^ 2 / n := by
    rw [hSdef]
    have : ∀ i, (εv i - (1 / (n : ℝ)) * s) ^ 2 =
        εv i ^ 2 - 2 * (1 / (n : ℝ)) * s * εv i + (1 / (n : ℝ)) ^ 2 * s ^ 2 := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hq, ← hs]
    field_simp
    ring
  have hRe : R = W - m * s - a * n := by
    rw [hR]
    have : ∀ i, (zv i - m - a * εv i) * εv i = zv i * εv i - m * εv i - a * εv i ^ 2 :=
      fun i => by ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hq, ← hW, ← hs]
  have hHe : H = Z - n * m - a * s := by
    rw [hH]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rfl
  have hT : N - a * S = R - (s / n) * H := by
    rw [hN, hS, hRe, hHe]; field_simp; ring
  have hD : Dhat n ζ zv εv = ζ⁻¹ * N / S := rfl
  have hfirst0 : 0 ≤ 4 * (ζ⁻¹) ^ 2 * (R ^ 2 + H ^ 2) / (n : ℝ) ^ 2 := by positivity
  by_cases hG : (n : ℝ) / 2 < |s|
  · rw [if_pos hG, mul_one]
    -- crude bound `D² ≤ ζ⁻² n`
    have hD2 : (Dhat n ζ zv εv) ^ 2 ≤ (ζ⁻¹) ^ 2 * n := by
      rcases S_zero_or_ge_one n hn1 εv hpm with h0 | h1
      · rw [hD, show S = 0 from h0, div_zero]
        have : 0 ≤ (ζ⁻¹) ^ 2 * (n : ℝ) := by positivity
        simpa using this
      · have hS1 : 1 ≤ S := h1
        have hCS : N ^ 2 ≤ (∑ i, (zv i - (1 / (n : ℝ)) * Z) ^ 2) * S :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        have hzb : (1 / (n : ℝ)) * Z ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (hz i).1)
          · have : Z ≤ n := by
              have := Finset.sum_le_sum (s := Finset.univ) fun i _ => (hz i).2
              simpa [hZ] using this
            rw [div_mul_eq_mul_div, one_mul, div_le_one hnpos]; exact this
        have hzz : ∑ i, (zv i - (1 / (n : ℝ)) * Z) ^ 2 ≤ (n : ℝ) := by
          have : ∀ i, (zv i - (1 / (n : ℝ)) * Z) ^ 2 ≤ 1 := by
            intro i
            have h1 := hz i
            nlinarith [hzb.1, hzb.2, h1.1, h1.2]
          have := Finset.sum_le_sum (s := Finset.univ) fun i _ => this i
          simpa using this
        have hN2 : N ^ 2 ≤ n * S := le_trans hCS (mul_le_mul_of_nonneg_right hzz (by linarith))
        rw [hD, div_pow, mul_pow]
        rw [div_le_iff₀ (by positivity)]
        exact aux_crude _ _ _ _ (by positivity) hnpos.le hS1 hN2
    have : (Dhat n ζ zv εv - ζ⁻¹ * a) ^ 2 ≤ 2 * (Dhat n ζ zv εv) ^ 2 + 2 * (ζ⁻¹ * a) ^ 2 := by
      nlinarith [sq_nonneg (Dhat n ζ zv εv + ζ⁻¹ * a)]
    linarith
  · rw [if_neg hG, mul_zero, add_zero]
    push Not at hG
    have hs2 : s ^ 2 ≤ (n : ℝ) ^ 2 / 4 := by
      have := abs_le.mp hG
      have h := sq_le_sq' this.1 this.2
      have e : ((n : ℝ) / 2) ^ 2 = (n : ℝ) ^ 2 / 4 := by ring
      linarith
    have hS34 : 3 * n / 4 ≤ S := by
      rw [hS]
      have : s ^ 2 / n ≤ n / 4 := by
        rw [div_le_iff₀ hnpos]
        have e : (n : ℝ) / 4 * n = (n : ℝ) ^ 2 / 4 := by ring
        linarith
      linarith
    have hSpos : 0 < S := by linarith
    have hdiff : Dhat n ζ zv εv - ζ⁻¹ * a = ζ⁻¹ * (N - a * S) / S := by
      rw [hD]; field_simp
    rw [hdiff, hT, div_pow, mul_pow]
    have hsn : (s / n) ^ 2 ≤ 1 / 4 := by
      rw [div_pow, div_le_iff₀ (by positivity)]; linarith
    have hT2 : (R - s / n * H) ^ 2 ≤ 2 * (R ^ 2 + H ^ 2) := aux_sq R (s / n) H hsn
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hz2 : 0 ≤ (ζ⁻¹) ^ 2 := by positivity
    have e1 : (ζ⁻¹) ^ 2 * (R - s / n * H) ^ 2 * (n : ℝ) ^ 2 ≤
        (ζ⁻¹) ^ 2 * (2 * (R ^ 2 + H ^ 2)) * (n : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hT2 hz2
    have e2 := aux_good ((ζ⁻¹) ^ 2) (2 * (R ^ 2 + H ^ 2)) n S hz2 (by positivity) hnpos hS34
    have e3 : 2 * (ζ⁻¹) ^ 2 * (2 * (R ^ 2 + H ^ 2)) * S ^ 2 =
        4 * (ζ⁻¹) ^ 2 * (R ^ 2 + H ^ 2) * S ^ 2 := by ring
    linarith


lemma deltahat_int (z ε : E → ℝ) (hz : Measurable z) (hε : Measurable ε)
    (hz01 : ∀ e, z e ∈ Set.Icc (0 : ℝ) 1) (hpm : ∀ᵐ e ∂ν, ε e = 1 ∨ ε e = -1)
    (hε0 : ∫ e, ε e ∂ν = 0) {ζ : ℝ} (hζ : 0 < ζ) (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun y : Fin n → E => (Dhat n ζ (fun i => z (y i)) (fun i => ε (y i)) -
        ζ⁻¹ * ∫ e, z e * ε e ∂ν) ^ 2) (Measure.pi fun _ : Fin n => ν) ∧
    ∫ y, (Dhat n ζ (fun i => z (y i)) (fun i => ε (y i)) - ζ⁻¹ * ∫ e, z e * ε e ∂ν) ^ 2
        ∂(Measure.pi fun _ : Fin n => ν) ≤
      72 * (ζ⁻¹) ^ 2 / n +
        (2 * (ζ⁻¹) ^ 2 * n + 2 * (ζ⁻¹ * ∫ e, z e * ε e ∂ν) ^ 2) * (2 * exp (-(n : ℝ) / 8)) := by
  set P := Measure.pi fun _ : Fin n => ν with hP
  set a := ∫ e, z e * ε e ∂ν with ha
  set m := ∫ e, z e ∂ν with hm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hεb : ∀ᵐ e ∂ν, ε e ∈ Set.Icc (-1 : ℝ) 1 := hpm.mono fun e he => by
    rcases he with h | h <;> rw [h] <;> norm_num
  have hε2 : ∀ᵐ e ∂ν, ε e ^ 2 = 1 := hpm.mono fun e he => by
    rcases he with h | h <;> rw [h] <;> norm_num
  have bdd_int : ∀ (X : E → ℝ) (C : ℝ), Measurable X → (∀ᵐ e ∂ν, |X e| ≤ C) → Integrable X ν :=
    fun X C hX hb => (integrable_const C).mono' hX.aestronglyMeasurable
      (hb.mono fun e he => by rw [Real.norm_eq_abs]; exact he)
  have hzint : Integrable z ν := bdd_int z 1 hz (Filter.Eventually.of_forall fun e => by
    rw [abs_le]; constructor <;> linarith [(hz01 e).1, (hz01 e).2])
  have hεint : Integrable ε ν := bdd_int ε 1 hε (hεb.mono fun e he => abs_le.mpr he)
  have hzεint : Integrable (fun e => z e * ε e) ν := bdd_int _ 1 (hz.mul hε)
    (hεb.mono fun e he => by
      rw [abs_mul]
      have h1 : |z e| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hz01 e).1, (hz01 e).2]
      have h2 : |ε e| ≤ 1 := abs_le.mpr he
      nlinarith [abs_nonneg (z e), abs_nonneg (ε e)])
  have hε2int : ∫ e, ε e ^ 2 ∂ν = 1 := by
    rw [integral_congr_ae hε2]; simp
  have ha1 : |a| ≤ 1 := by
    have : ‖∫ e, z e * ε e ∂ν‖ ≤ 1 * (ν Set.univ).toReal := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [hεb] with e he
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |z e| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hz01 e).1, (hz01 e).2]
      have h2 : |ε e| ≤ 1 := abs_le.mpr he
      nlinarith [abs_nonneg (z e), abs_nonneg (ε e)]
    simpa using this
  have hm01 : m ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact integral_nonneg fun e => (hz01 e).1
    · have : ∫ e, z e ∂ν ≤ ∫ _e, (1 : ℝ) ∂ν :=
        integral_mono hzint (integrable_const _) fun e => (hz01 e).2
      simpa using this
  -- the centred residuals
  set X1 : E → ℝ := fun e => (z e - m - a * ε e) * ε e with hX1
  set X2 : E → ℝ := fun e => z e - m - a * ε e with hX2
  have hX2m : Measurable X2 := (hz.sub_const _).sub (hε.const_mul _)
  have hX1m : Measurable X1 := hX2m.mul hε
  have hX2b : ∀ᵐ e ∂ν, X2 e ∈ Set.Icc (-3 : ℝ) 3 := hεb.mono fun e he => by
    have h1 := hz01 e
    have h2 : |a * ε e| ≤ 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg (ε e), abs_le.mpr he]
    have := abs_le.mp h2
    constructor <;> simp only [X2] <;> linarith [h1.1, h1.2, hm01.1, hm01.2]
  have hX1b : ∀ᵐ e ∂ν, X1 e ∈ Set.Icc (-3 : ℝ) 3 := (hX2b.and hεb).mono fun e ⟨h1, h2⟩ => by
    have k1 : |X2 e| ≤ 3 := abs_le.mpr h1
    have k2 : |ε e| ≤ 1 := abs_le.mpr h2
    have : |X1 e| ≤ 3 := by
      simp only [X1]; rw [abs_mul]
      nlinarith [abs_nonneg (X2 e), abs_nonneg (ε e)]
    exact abs_le.mp this
  have hX2int : ∫ e, X2 e ∂ν = 0 := by
    simp only [X2]
    have i1 : Integrable (fun e => z e - m) ν := hzint.sub (integrable_const m)
    have i2 : Integrable (fun e => a * ε e) ν := hεint.const_mul a
    rw [integral_sub i1 i2, integral_sub hzint (integrable_const _), integral_const_mul, hε0]
    simp [hm]
  have hX1int : ∫ e, X1 e ∂ν = 0 := by
    have hexp : X1 = fun e => z e * ε e - m * ε e - a * ε e ^ 2 := by
      funext e; simp only [X1]; ring
    have i1 : Integrable (fun e => z e * ε e - m * ε e) ν := hzεint.sub (hεint.const_mul m)
    have i0 : Integrable (fun e => m * ε e) ν := hεint.const_mul m
    have i2 : Integrable (fun e => a * ε e ^ 2) ν :=
      (bdd_int _ 1 (hε.pow_const 2) (hε2.mono fun e he => by rw [he]; norm_num)).const_mul _
    rw [hexp]
    show ∫ e, (z e * ε e - m * ε e - a * ε e ^ 2) ∂ν = 0
    rw [integral_sub i1 i2, integral_sub hzεint i0, integral_const_mul, integral_const_mul, hε0,
      hε2int, ← ha]
    ring
  have hR := sq_sum_pi ν n X1 hX1m hX1b hX1int
  have hH := sq_sum_pi ν n X2 hX2m hX2b hX2int
  -- Hoeffding
  set G := {y : Fin n → E | (n : ℝ) / 2 < |∑ i, ε (y i)|} with hGdef
  have hGm : MeasurableSet G :=
    measurableSet_lt measurable_const
      ((Finset.measurable_sum _ fun i _ => hε.comp (measurable_pi_apply i)).abs)
  have hPG : P.real G ≤ 2 * exp (-(n : ℝ) / 8) := by
    have h1 := hoeffding_pi ν n ε hε hεb hε0 (t := (n : ℝ) / 2) (by positivity)
    have h2 := hoeffding_pi ν n (fun e => -ε e) hε.neg
      (hεb.mono fun e he => ⟨by linarith [he.2], by linarith [he.1]⟩)
      (by rw [integral_neg, hε0, neg_zero]) (t := (n : ℝ) / 2) (by positivity)
    have hsub : G ⊆ {y | (n : ℝ) / 2 ≤ ∑ i, ε (y i)} ∪
        {y | (n : ℝ) / 2 ≤ ∑ i, (fun e => -ε e) (y i)} := by
      intro y hy
      simp only [hGdef, Set.mem_ofPred_eq] at hy
      simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.sum_neg_distrib]
      rcases le_or_gt 0 (∑ i, ε (y i)) with h | h
      · left; rw [abs_of_nonneg h] at hy; linarith
      · right; rw [abs_of_neg h] at hy; linarith
    have e : -((n : ℝ) / 2) ^ 2 / (2 * n) = -(n : ℝ) / 8 := by field_simp; ring
    rw [e] at h1 h2
    calc P.real G ≤ P.real ({y | (n : ℝ) / 2 ≤ ∑ i, ε (y i)} ∪
          {y | (n : ℝ) / 2 ≤ ∑ i, (fun e => -ε e) (y i)}) := measureReal_mono hsub
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = 2 * exp (-(n : ℝ) / 8) := by ring
  -- the dominating function
  set C := 2 * (ζ⁻¹) ^ 2 * n + 2 * (ζ⁻¹ * a) ^ 2 with hC
  set g : (Fin n → E) → ℝ := fun y => 4 * (ζ⁻¹) ^ 2 * ((∑ i, X1 (y i)) ^ 2 +
      (∑ i, X2 (y i)) ^ 2) / (n : ℝ) ^ 2 + G.indicator (fun _ => C) y with hg
  have hsumint : ∀ X : E → ℝ, Measurable X → (∀ᵐ e ∂ν, X e ∈ Set.Icc (-3 : ℝ) 3) →
      Integrable (fun y : Fin n → E => (∑ i, X (y i)) ^ 2) P := by
    intro X hXm hXb
    have hall : ∀ᵐ y ∂P, ∀ i, X (y i) ∈ Set.Icc (-3 : ℝ) 3 := ae_all_iff.mpr fun i =>
      (measurePreserving_eval (fun _ => ν) i).quasiMeasurePreserving.ae
        (p := fun e => X e ∈ Set.Icc (-3 : ℝ) 3) hXb
    refine (integrable_const ((3 * n) ^ 2 : ℝ)).mono'
      ((Finset.measurable_sum _ fun i _ => hXm.comp (measurable_pi_apply i)).pow_const
        2).aestronglyMeasurable (hall.mono fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : |∑ i, X (y i)| ≤ 3 * n := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have := Finset.sum_le_sum (s := Finset.univ) fun i _ => abs_le.mpr (hy i)
      simp at this; linarith
    have h0 := abs_nonneg (∑ i, X (y i))
    rw [← sq_abs]
    exact pow_le_pow_left₀ h0 this 2
  have hgint : Integrable g P := by
    apply Integrable.add
    · exact (((hsumint X1 hX1m hX1b).add (hsumint X2 hX2m hX2b)).const_mul
        (4 * (ζ⁻¹) ^ 2)).div_const _
    · exact (integrable_const C).indicator hGm
  have hpmP : ∀ᵐ y ∂P, ∀ i, ε (y i) = 1 ∨ ε (y i) = -1 := ae_all_iff.mpr fun i =>
    (measurePreserving_eval (fun _ => ν) i).quasiMeasurePreserving.ae
      (p := fun e => ε e = 1 ∨ ε e = -1) hpm
  have hle : ∀ᵐ y ∂P, (Dhat n ζ (fun i => z (y i)) (fun i => ε (y i)) - ζ⁻¹ * a) ^ 2 ≤ g y := by
    filter_upwards [hpmP] with y hy
    have := pointwise_bound n hn (fun i => z (y i)) (fun i => ε (y i)) (fun i => hz01 _) hy m a
      ζ hζ
    refine le_trans this (le_of_eq ?_)
    simp only [hg, X1, X2]
    congr 1
    by_cases hy' : y ∈ G
    · rw [Set.indicator_of_mem hy', if_pos (by simpa [hGdef] using hy'), mul_one]
    · rw [Set.indicator_of_notMem hy', if_neg (by simpa [hGdef] using hy'), mul_zero]
  have hDmeas : Measurable (fun y : Fin n → E =>
      (Dhat n ζ (fun i => z (y i)) (fun i => ε (y i)) - ζ⁻¹ * a) ^ 2) := by
    unfold Dhat
    have hzi : ∀ i : Fin n, Measurable (fun y : Fin n → E => z (y i)) := fun i =>
      hz.comp (measurable_pi_apply i)
    have hεi : ∀ i : Fin n, Measurable (fun y : Fin n → E => ε (y i)) := fun i =>
      hε.comp (measurable_pi_apply i)
    have hzs : Measurable (fun y : Fin n → E => ∑ j, z (y j)) :=
      Finset.measurable_sum _ fun j _ => hzi j
    have hεs : Measurable (fun y : Fin n → E => ∑ j, ε (y j)) :=
      Finset.measurable_sum _ fun j _ => hεi j
    refine ((Measurable.div ?_ ?_).sub_const _).pow_const 2
    · exact (Finset.measurable_sum _ fun i _ => ((hzi i).sub (hzs.const_mul _)).mul
        ((hεi i).sub (hεs.const_mul _))).const_mul _
    · exact Finset.measurable_sum _ fun i _ => ((hεi i).sub (hεs.const_mul _)).pow_const 2
  have hDint : Integrable (fun y : Fin n → E =>
      (Dhat n ζ (fun i => z (y i)) (fun i => ε (y i)) - ζ⁻¹ * a) ^ 2) P :=
    hgint.mono' hDmeas.aestronglyMeasurable (hle.mono fun y hy => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hy)
  refine ⟨hDint, le_trans (integral_mono_ae hDint hgint hle) ?_⟩
  -- evaluate the bound
  have hgi : ∫ y, g y ∂P = 4 * (ζ⁻¹) ^ 2 * (∫ y, (∑ i, X1 (y i)) ^ 2 ∂P +
      ∫ y, (∑ i, X2 (y i)) ^ 2 ∂P) / (n : ℝ) ^ 2 + C * P.real G := by
    simp only [hg]
    have j1 : Integrable (fun y : Fin n → E => (∑ i, X1 (y i)) ^ 2 + (∑ i, X2 (y i)) ^ 2) P :=
      (hsumint X1 hX1m hX1b).add (hsumint X2 hX2m hX2b)
    have j2 : Integrable (fun y : Fin n → E => 4 * (ζ⁻¹) ^ 2 * ((∑ i, X1 (y i)) ^ 2 +
        (∑ i, X2 (y i)) ^ 2) / (n : ℝ) ^ 2) P := (j1.const_mul (4 * (ζ⁻¹) ^ 2)).div_const _
    have j3 : Integrable (fun y => G.indicator (fun _ => C) y) P :=
      (integrable_const C).indicator hGm
    rw [integral_add j2 j3, integral_div, integral_const_mul, integral_add (hsumint X1 hX1m hX1b)
        (hsumint X2 hX2m hX2b), integral_indicator_const _ hGm, smul_eq_mul, mul_comm C]
  rw [hgi]
  have hC0 : 0 ≤ C := by positivity
  have e1 : 4 * (ζ⁻¹) ^ 2 * (∫ y, (∑ i, X1 (y i)) ^ 2 ∂P + ∫ y, (∑ i, X2 (y i)) ^ 2 ∂P) /
      (n : ℝ) ^ 2 ≤ 72 * (ζ⁻¹) ^ 2 / n := by
    rw [div_le_div_iff₀ (by positivity) hnpos]
    have hz2 : 0 ≤ 4 * (ζ⁻¹) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add hR hH) hz2
    have e : 4 * (ζ⁻¹) ^ 2 * (↑n * 3 ^ 2 + ↑n * 3 ^ 2) * n = 72 * (ζ⁻¹) ^ 2 * (n : ℝ) ^ 2 := by
      ring
    nlinarith [mul_le_mul_of_nonneg_right this hnpos.le]
  have e2 : C * P.real G ≤ C * (2 * exp (-(n : ℝ) / 8)) := mul_le_mul_of_nonneg_left hPG hC0
  linarith

lemma accPt_Ici {x : ℝ} (hx : 0 ≤ x) : AccPt x (𝓟 (Set.Ici 0)) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨x + ε / 2, ⟨hball ?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]; linarith
  · simp only [Set.mem_Ici]; linarith
  · intro h; linarith


lemma fprime_bounds (g g' g'' : ℝ → ℝ) (h01 : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hmono : MonotoneOn g (Set.Ici 0))
    (hder : ∀ x, 0 ≤ x → HasDerivWithinAt g (g' x) (Set.Ici 0) x ∧
      HasDerivWithinAt g' (g'' x) (Set.Ici 0) x)
    (K : ℝ) (hK : ∀ x, 0 ≤ x → |g'' x| ≤ K) :
    ∀ x, 0 ≤ x → 0 ≤ g' x ∧ g' x ≤ 1 + K := by
  intro x hx
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 le_rfl)
  refine ⟨(hder x hx).1.nonneg_of_monotoneOn (accPt_Ici hx) hmono, ?_⟩
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope g g' (lt_add_one x)
    (fun t ht => ((hder t (le_trans hx ht.1)).1.continuousWithinAt).mono
      (fun y hy => Set.mem_Ici.mpr (le_trans hx hy.1)))
    (fun t ht => (hder t (by linarith [ht.1])).1.hasDerivAt (Ici_mem_nhds (by linarith [ht.1])))
  have hgc : g' c ≤ 1 := by
    rw [hcs, add_sub_cancel_left, div_one]
    have h1 := h01 (x + 1) (by linarith)
    have h2 := h01 x hx
    linarith [h1.2, h2.1]
  have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g') (f' := g'')
    (s := Set.Icc x c) (x := x) (y := c) (C := K)
    (fun y hy => ((hder y (le_trans hx hy.1)).2).mono
      (fun z hz => Set.mem_Ici.mpr (le_trans hx hz.1)))
    (fun y hy => by rw [Real.norm_eq_abs]; exact hK y (le_trans hx hy.1))
    (convex_Icc x c) ⟨le_rfl, hc.1.le⟩ ⟨hc.1.le, le_rfl⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hlip
  have hcx : |c - x| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hc.1, hc.2]
  have : K * |c - x| ≤ K := by nlinarith [abs_nonneg (c - x)]
  have := (abs_le.mp hlip).1
  linarith


lemma fprime_lip (g g' g'' : ℝ → ℝ)
    (hder : ∀ x, 0 ≤ x → HasDerivWithinAt g (g' x) (Set.Ici 0) x ∧
      HasDerivWithinAt g' (g'' x) (Set.Ici 0) x)
    (K : ℝ) (hK : ∀ x, 0 ≤ x → |g'' x| ≤ K) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |g' x - g' y| ≤ K * |x - y| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g') (f' := g'')
    (s := Set.Ici 0) (x := y) (y := x) (C := K)
    (fun t ht => (hder t ht).2) (fun t ht => by rw [Real.norm_eq_abs]; exact hK t ht)
    (convex_Ici 0) hy hx
  simpa [Real.norm_eq_abs] using this

lemma quotient_bound (g g' g'' : ℝ → ℝ) (h01 : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hmono : MonotoneOn g (Set.Ici 0))
    (hder : ∀ x, 0 ≤ x → HasDerivWithinAt g (g' x) (Set.Ici 0) x ∧
      HasDerivWithinAt g' (g'' x) (Set.Ici 0) x)
    (K : ℝ) (hK : ∀ x, 0 ≤ x → |g'' x| ≤ K) {p ζ c c₀ : ℝ} (hp : 0 < p) (hζ : 0 < ζ)
    (hζp : ζ ≤ p) (hc : 0 ≤ c) (hc₀ : 0 ≤ c₀) :
    |(g ((p + ζ) * c) - g ((p - ζ) * c)) / (2 * ζ) - c₀ * g' (p * c₀)| ≤
      K * (ζ * c + p * |c - c₀|) * c + (1 + K) * |c - c₀| := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 le_rfl)
  have hb := fprime_bounds g g' g'' h01 hmono hder K hK (p * c₀) (by positivity)
  have hg'abs : |g' (p * c₀)| ≤ 1 + K := by rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
  rcases eq_or_lt_of_le hc with h0 | hcpos
  · rw [← h0]
    simp only [mul_zero, sub_self, zero_div, zero_sub, abs_neg, zero_add, add_zero]
    rw [abs_mul, abs_of_nonneg hc₀]
    nlinarith [mul_le_mul_of_nonneg_left hg'abs hc₀, abs_nonneg (g' (p * c₀))]
  · have hlt : (p - ζ) * c < (p + ζ) * c := by nlinarith
    have hlo : 0 ≤ (p - ζ) * c := mul_nonneg (by linarith) hc
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' hlt
      (fun t ht => ((hder t (le_trans hlo ht.1)).1.continuousWithinAt).mono
        (fun y hy => Set.mem_Ici.mpr (le_trans hlo hy.1)))
      (fun t ht => (hder t (by linarith [ht.1])).1.hasDerivAt
        (Ici_mem_nhds (by linarith [ht.1])))
    have hq : (g ((p + ζ) * c) - g ((p - ζ) * c)) / (2 * ζ) = c * g' ξ := by
      have hden : (p + ζ) * c - (p - ζ) * c = 2 * ζ * c := by ring
      rw [hξeq, hden]; field_simp
    rw [hq]
    have hξ0 : 0 ≤ ξ := by linarith [hξ.1]
    have hlip := fprime_lip g g' g'' hder K hK hξ0 (show 0 ≤ p * c₀ by positivity)
    have hdist : |ξ - p * c₀| ≤ ζ * c + p * |c - c₀| := by
      have h1 : |ξ - p * c| ≤ ζ * c := by
        rw [abs_le]; constructor <;> nlinarith [hξ.1, hξ.2]
      have h2 : |p * c - p * c₀| = p * |c - c₀| := by
        rw [← mul_sub, abs_mul, abs_of_pos hp]
      calc |ξ - p * c₀| = |(ξ - p * c) + (p * c - p * c₀)| := by ring_nf
        _ ≤ |ξ - p * c| + |p * c - p * c₀| := abs_add_le _ _
        _ ≤ _ := by rw [h2]; linarith
    have e : c * g' ξ - c₀ * g' (p * c₀) = c * (g' ξ - g' (p * c₀)) + (c - c₀) * g' (p * c₀) := by
      ring
    rw [e]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hc]
    have k1 : c * |g' ξ - g' (p * c₀)| ≤ c * (K * (ζ * c + p * |c - c₀|)) :=
      mul_le_mul_of_nonneg_left (le_trans hlip (mul_le_mul_of_nonneg_left hdist hK0)) hc
    have k2 : |c - c₀| * |g' (p * c₀)| ≤ |c - c₀| * (1 + K) :=
      mul_le_mul_of_nonneg_left hg'abs (abs_nonneg _)
    nlinarith

section Theta
open EquilibriumExperiment.Gradient
variable {B : Type} [MeasurableSpace B] (β : Measure B) [IsProbabilityMeasure β]

lemma pm_ae (p ζ : ℝ) [IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1))] :
    ∀ᵐ e ∂(β.prod ((perturbLaw p ζ).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))),
      e.2.1 = p + ζ ∨ e.2.1 = p - ζ := by
  rw [ae_iff]
  set T : Set ℝ := ({p + ζ} ∪ {p - ζ})ᶜ with hT
  have hTm : MeasurableSet T :=
    ((measurableSet_singleton _).union (measurableSet_singleton _)).compl
  have hset : {e : B × ℝ × ℝ | ¬(e.2.1 = p + ζ ∨ e.2.1 = p - ζ)} =
      Set.univ ×ˢ (T ×ˢ Set.univ) := by
    ext e; simp [hT]; tauto
  haveI := perturbLaw_prob p ζ
  rw [hset, Measure.prod_prod, Measure.prod_prod]
  have : perturbLaw p ζ T = 0 := by
    simp only [perturbLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ hTm, Measure.dirac_apply' _ hTm,
      Set.indicator_of_notMem (by simp [hT]), Set.indicator_of_notMem (by simp [hT]),
      add_zero, mul_zero]
  rw [this]; simp

lemma theta_formula (f : B → ℝ → ℝ) (hf01 : ∀ b x, 0 ≤ x → f b x ∈ Set.Icc (0 : ℝ) 1)
    (hfmeas : Measurable (Function.uncurry f)) {p ζ c : ℝ} (hζ : 0 < ζ) (hζp : ζ ≤ p)
    (hc : 0 ≤ c) [IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1))] :
    ∫ e, ({e : B × ℝ × ℝ | e.2.2 ≤ f e.1 (e.2.1 * c)}.indicator (fun _ => (1 : ℝ)) e) *
        ((e.2.1 - p) / ζ) ∂(β.prod ((perturbLaw p ζ).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1)))) =
      ∫ b, (f b ((p + ζ) * c) - f b ((p - ζ) * c)) / 2 ∂β := by
  haveI := perturbLaw_prob p ζ
  set U := volume.restrict (Set.Icc (0 : ℝ) 1) with hU
  set A := {e : B × ℝ × ℝ | e.2.2 ≤ f e.1 (e.2.1 * c)} with hA
  have hAm : MeasurableSet A := by
    apply measurableSet_le measurable_snd.snd
    have : Measurable (fun e : B × ℝ × ℝ => (e.1, e.2.1 * c)) :=
      measurable_fst.prodMk (measurable_snd.fst.mul_const c)
    exact hfmeas.comp this
  set F : B × ℝ × ℝ → ℝ := fun e => A.indicator (fun _ => (1 : ℝ)) e * ((e.2.1 - p) / ζ)
    with hF
  have hFm : Measurable F :=
    (measurable_const.indicator hAm).mul ((measurable_snd.fst.sub_const _).div_const _)
  have hFb : ∀ e : B × ℝ × ℝ, (e.2.1 = p + ζ ∨ e.2.1 = p - ζ) → |F e| ≤ 1 := by
    intro e he
    simp only [hF]
    have h1 : |A.indicator (fun _ => (1 : ℝ)) e| ≤ 1 := by
      by_cases h : e ∈ A
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
    have h2 : |(e.2.1 - p) / ζ| = 1 := by
      rcases he with h | h
      · rw [h, add_sub_cancel_left, div_self hζ.ne', abs_one]
      · rw [h, show p - ζ - p = -ζ by ring, neg_div, div_self hζ.ne', abs_neg, abs_one]
    rw [abs_mul, h2, mul_one]; exact h1
  have hFint : Integrable F (β.prod ((perturbLaw p ζ).prod U)) :=
    (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
      ((pm_ae β p ζ).mono fun e he => by rw [Real.norm_eq_abs]; exact hFb e he)
  rw [integral_prod F hFint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only
  -- inner integral over `(P, U)`
  have hpmQ : ∀ᵐ q ∂((perturbLaw p ζ).prod U), q.1 = p + ζ ∨ q.1 = p - ζ := by
    rw [ae_iff]
    have hset : {q : ℝ × ℝ | ¬(q.1 = p + ζ ∨ q.1 = p - ζ)} =
        ({p + ζ} ∪ {p - ζ})ᶜ ×ˢ Set.univ := by ext q; simp; tauto
    have hTm : MeasurableSet (({p + ζ} ∪ {p - ζ})ᶜ : Set ℝ) :=
      ((measurableSet_singleton _).union (measurableSet_singleton _)).compl
    rw [hset, Measure.prod_prod]
    have : perturbLaw p ζ (({p + ζ} ∪ {p - ζ})ᶜ) = 0 := by
      simp only [perturbLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
      rw [Measure.dirac_apply' _ hTm, Measure.dirac_apply' _ hTm,
        Set.indicator_of_notMem (by simp), Set.indicator_of_notMem (by simp), add_zero,
        mul_zero]
    rw [this, zero_mul]
  have hFq : Measurable (fun q : ℝ × ℝ => F (b, q)) := hFm.comp measurable_prodMk_left
  have hFqint : Integrable (fun q : ℝ × ℝ => F (b, q)) ((perturbLaw p ζ).prod U) :=
    (integrable_const (1 : ℝ)).mono' hFq.aestronglyMeasurable
      (hpmQ.mono fun q hq => by rw [Real.norm_eq_abs]; exact hFb (b, q) hq)
  rw [integral_prod _ hFqint, integral_perturbLaw]
  have hinner : ∀ P : ℝ, 0 ≤ P * c → ∫ u, F (b, (P, u)) ∂U = (P - p) / ζ * f b (P * c) := by
    intro P hP
    have hfun : (fun u => F (b, (P, u))) = (Set.Iic (f b (P * c))).indicator
        (fun _ => (P - p) / ζ) := by
      funext u
      simp only [hF]
      by_cases hu : u ≤ f b (P * c)
      · rw [Set.indicator_of_mem (show (b, (P, u)) ∈ A from hu),
          Set.indicator_of_mem (show u ∈ Set.Iic (f b (P * c)) from hu), one_mul]
      · rw [Set.indicator_of_notMem (show (b, (P, u)) ∉ A from hu),
          Set.indicator_of_notMem (show u ∉ Set.Iic (f b (P * c)) from hu), zero_mul]
    rw [hfun, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, Measure.real,
      hU, Measure.restrict_apply measurableSet_Iic]
    have h01 := hf01 b _ hP
    have h2 : Set.Iic (f b (P * c)) ∩ Set.Icc 0 1 = Set.Icc 0 (f b (P * c)) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2 h01.2⟩
    rw [h2, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal h01.1]
    ring
  rw [hinner (p + ζ) (mul_nonneg (by linarith) hc), hinner (p - ζ) (mul_nonneg (by linarith) hc)]
  field_simp
  ring

end Theta

end EqExpDHAux

open EqExpA7ZAux EqExpDHAux EquilibriumExperiment.Gradient

theorem solution {B : Type} [MeasurableSpace B] (M : EquilibriumExperiment.Gradient.Market B)
    (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β)
    {ζ α : ℝ} (hζ : 0 < ζ) (hα : 0 < α) (hα' : α < 1 / 2) :
    Tendsto (fun n : ℕ => eLpNorm (fun x : Outcome B n =>
        M.DeltaHat n p (ζ * (n : ℝ) ^ (-α)) x - M.DeltaLim p) 2
      (M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α))))) atTop (𝓝 0) := by
  have hL2 := lemma_2 M hM
  obtain ⟨hd, hF, -, -, -, hβ, hω, -, hΩt, hl, -, hΩeq, hΩmeas, hf01, hfmono, hfderiv,
    hf'', hfmeas, hf'meas, -, -, -⟩ := hM
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
  -- `c_n = q_n(μ_n(p, ζ_n)) → c₀ = ω(d_a/μ_a(p))`
  haveI hU : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Measure.restrict_apply MeasurableSet.univ, Real.volume_Icc]⟩
  obtain ⟨K₂, hK₂⟩ := hf''
  have hK₂0 : 0 ≤ K₂ := by
    obtain ⟨b⟩ : Nonempty B := by
      by_contra h
      rw [not_nonempty_iff] at h
      have : M.β Set.univ = 0 := by simp [Set.univ_eq_empty_iff.mpr h]
      simp at this
    exact le_trans (abs_nonneg _) (hK₂ b 0 le_rfl)
  set c₀ := M.ω (M.d / μs) with hc₀
  have hc₀0 : 0 ≤ c₀ := hωd0 μs hmuL.1.1
  set cn : ℕ → ℝ := fun n => M.q n (M.muN n (π n)) with hcn
  have hωcont : ContinuousAt (fun μ => M.ω (M.d / μ)) μs := by
    have hw : 0 < M.d / μs := div_pos hd hmuL.1.1
    exact (hω.2.1.continuousOn.continuousAt (Ioi_mem_nhds hw)).comp
      (continuousAt_const.div continuousAt_id hmuL.1.1.ne')
  have hcnlim : Tendsto cn atTop (𝓝 c₀) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      -- choose `t ≥ μ*` with `ω(d/t) > a`
      obtain ⟨t, ht0, ht1, htμ, hta, hev⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ μs ≤ t ∧
          a < M.ω (M.d / t) ∧ ∀ᶠ n in atTop, M.muN n (π n) ≤ t := by
        by_cases h1 : μs = 1
        · refine ⟨1, one_pos, le_rfl, h1.le, ?_, ?_⟩
          · rw [← h1]; exact ha
          · filter_upwards [hevp] with n hn; exact (hmuN n hn).1.2
        · have hlt : μs < 1 := lt_of_le_of_ne hmuL.1.2 h1
          have hev1 := hωcont.eventually (lt_mem_nhds ha)
          obtain ⟨t, htgt, htp⟩ := (hev1.and (gt_mem_nhds hlt)).exists_gt
          refine ⟨t, lt_trans hmuL.1.1 htgt, htp.2.le, htgt.le, htp.1, ?_⟩
          exact (hmlim.eventually (gt_mem_nhds htgt)).mono fun n hn => hn.le
      have hqt := (hqlim t ⟨ht0, ht1⟩).eventually (lt_mem_nhds hta)
      filter_upwards [hqt, hev, hevp] with n hn1 hn2 hnp
      have := (hqfacts n).2.1 (hmuN n hnp).1 ⟨ht0.le, ht1⟩ hn2
      exact lt_of_lt_of_le hn1 this
    · intro a ha
      have hev1 := hωcont.eventually (gt_mem_nhds ha)
      obtain ⟨s, hslt, hsp⟩ := (hev1.and (lt_mem_nhds hmuL.1.1)).exists_lt
      have hs1 : s ≤ 1 := le_trans hslt.le hmuL.1.2
      have hqs := (hqlim s ⟨hsp.2, hs1⟩).eventually (gt_mem_nhds hsp.1)
      filter_upwards [hqs, hmlim.eventually (lt_mem_nhds hslt), hevp] with n hn1 hn2 hnp
      have := (hqfacts n).2.1 ⟨hsp.2.le, hs1⟩ (hmuN n hnp).1 hn2.le
      exact lt_of_le_of_lt this hn1
  -- the population slope `θ_n → Δ_a(p)`
  set Δ := M.DeltaLim p with hΔ
  have hΔeq : Δ = c₀ * ∫ b, M.f' b (p * c₀) ∂M.β := rfl
  set θ : ℕ → ℝ := fun n => (ζn n)⁻¹ *
    ∫ b, (M.f b ((p + ζn n) * cn n) - M.f b ((p - ζn n) * cn n)) / 2 ∂M.β with hθ
  have hζpos : ∀ n, 1 ≤ n → 0 < ζn n := fun n hn =>
    mul_pos hζ (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _)
  have hcn0 : ∀ n, ζn n ≤ p → 0 ≤ cn n := fun n hn => (hqfacts n).1 _ (hmuN n hn).1
  have hθbound : ∀ n, 1 ≤ n → ζn n ≤ p → |θ n - Δ| ≤
      K₂ * (ζn n * cn n + p * |cn n - c₀|) * cn n + (1 + K₂) * |cn n - c₀| := by
    intro n hn hnp
    have hz := hζpos n hn
    have hc := hcn0 n hnp
    have hint1 : Integrable (fun b => (M.f b ((p + ζn n) * cn n) -
        M.f b ((p - ζn n) * cn n)) / (2 * ζn n)) M.β := by
      have i1 := (fint M.β M.f hf01 hfmeas (x := (p + ζn n) * cn n)
        (mul_nonneg (by linarith) hc)).1
      have i2 := (fint M.β M.f hf01 hfmeas (x := (p - ζn n) * cn n)
        (mul_nonneg (by linarith) hc)).1
      have i3 : Integrable (fun b => M.f b ((p + ζn n) * cn n) - M.f b ((p - ζn n) * cn n))
        M.β := i1.sub i2
      exact i3.div_const _
    have hint2 : Integrable (fun b => c₀ * M.f' b (p * c₀)) M.β := by
      refine ((integrable_const (1 + K₂)).mono'
        (hf'meas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun b => ?_)).const_mul _
      have := fprime_bounds (M.f b) (M.f' b) (M.f'' b) (hf01 b) (hfmono b) (hfderiv b) K₂
        (hK₂ b) (p * c₀) (by positivity)
      show ‖M.f' b (p * c₀)‖ ≤ 1 + K₂
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
    have heq : θ n - Δ = ∫ b, ((M.f b ((p + ζn n) * cn n) - M.f b ((p - ζn n) * cn n)) /
        (2 * ζn n) - c₀ * M.f' b (p * c₀)) ∂M.β := by
      rw [integral_sub hint1 hint2, integral_const_mul, ← hΔeq]
      simp only [hθ]
      rw [← integral_const_mul]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      field_simp
    rw [heq]
    have := norm_integral_le_of_norm_le_const (μ := M.β)
      (C := K₂ * (ζn n * cn n + p * |cn n - c₀|) * cn n + (1 + K₂) * |cn n - c₀|)
      (f := fun b => (M.f b ((p + ζn n) * cn n) - M.f b ((p - ζn n) * cn n)) /
        (2 * ζn n) - c₀ * M.f' b (p * c₀))
      (Filter.Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs]
        exact quotient_bound (M.f b) (M.f' b) (M.f'' b) (hf01 b) (hfmono b) (hfderiv b) K₂
          (hK₂ b) hp hz hnp hc hc₀0)
    simpa using this
  have hθlim : Tendsto θ atTop (𝓝 Δ) := by
    have hb : Tendsto (fun n => K₂ * (ζn n * cn n + p * |cn n - c₀|) * cn n +
        (1 + K₂) * |cn n - c₀|) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => |cn n - c₀|) atTop (𝓝 0) := by
        have := (hcnlim.sub_const c₀).abs; rwa [sub_self, abs_zero] at this
      have := (((tendsto_const_nhds (x := K₂)).mul ((hζlim.mul hcnlim).add
        ((tendsto_const_nhds (x := p)).mul h1))).mul hcnlim).add
        ((tendsto_const_nhds (x := 1 + K₂)).mul h1)
      simpa using this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hb
    filter_upwards [hevp, eventually_ge_atTop 1] with n hnp hn
    rw [Real.norm_eq_abs]; exact hθbound n hn hnp
  -- the `L²` bound for each large `n`
  set Bn : ℕ → ℝ := fun n => 72 * ((ζn n)⁻¹) ^ 2 / n +
    (2 * ((ζn n)⁻¹) ^ 2 * n + 2 * (θ n) ^ 2) * (2 * Real.exp (-(n : ℝ) / 8)) with hBn
  have hbound : ∀ᶠ n in atTop, eLpNorm (fun x : Outcome B n =>
      M.DeltaHat n p (ζn n) x - Δ) 2 (M.sample n (π n)) ≤
      ENNReal.ofReal (Bn n ^ (1 / (2 : ℝ))) + ENNReal.ofReal |θ n - Δ| := by
    filter_upwards [hevp, eventually_ge_atTop 2] with n hnp hn2
    have hn1 : 1 ≤ n := by omega
    have hz := hζpos n hn1
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
    set εf : B × ℝ × ℝ → ℝ := fun e => (e.2.1 - p) / ζn n with hεf
    have hεm : Measurable εf := (measurable_snd.fst.sub_const _).div_const _
    have hpm : ∀ᵐ e ∂ν, εf e = 1 ∨ εf e = -1 := by
      filter_upwards [pm_ae M.β p (ζn n)] with e he
      simp only [εf]
      rcases he with h | h
      · left; rw [h, add_sub_cancel_left, div_self hz.ne']
      · right; rw [h, show p - ζn n - p = -ζn n by ring, neg_div, div_self hz.ne']
    have hε0 : ∫ e, εf e ∂ν = 0 := by
      have hmp1 : MeasurePreserving (Prod.snd : B × ℝ × ℝ → ℝ × ℝ) ν
          ((π n).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := measurePreserving_snd
      have hmp2 : MeasurePreserving (Prod.fst : ℝ × ℝ → ℝ)
          ((π n).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) (π n) := measurePreserving_fst
      have hmp := hmp2.comp hmp1
      have hg : Measurable (fun P : ℝ => (P - p) / ζn n) := (measurable_id.sub_const _).div_const _
      calc ∫ e, εf e ∂ν = ∫ P, (P - p) / ζn n ∂(ν.map (Prod.fst ∘ Prod.snd)) :=
            (integral_map (f := fun P : ℝ => (P - p) / ζn n) hmp.measurable.aemeasurable
              (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable)).symm
        _ = ∫ P, (P - p) / ζn n ∂(π n) := by rw [hmp.map_eq]
        _ = 0 := by
          rw [integral_perturbLaw]
          field_simp; ring
    obtain ⟨hDint, hDle⟩ := deltahat_int ν z εf hzm hεm hz01 hpm hε0 hz n hn2
    have hθeq : (ζn n)⁻¹ * ∫ e, z e * εf e ∂ν = θ n := by
      simp only [hθ]
      congr 1
      rw [hzfun]
      exact theta_formula M.β M.f hf01 hfmeas hz hnp hc0
    rw [hθeq] at hDint hDle
    have hmp : MeasurePreserving (Prod.snd : Outcome B n → (Fin n → B × ℝ × ℝ))
        (M.sample n (π n)) (Measure.pi fun _ => ν) := measurePreserving_snd
    have hcomp : (fun x : Outcome B n => M.DeltaHat n p (ζn n) x - Δ) =
        (fun y : Fin n → B × ℝ × ℝ => Dhat n (ζn n) (fun i => z (y i))
          (fun i => εf (y i)) - Δ) ∘ Prod.snd := rfl
    have hDm : Measurable (fun y : Fin n → B × ℝ × ℝ =>
        Dhat n (ζn n) (fun i => z (y i)) (fun i => εf (y i))) := by
      unfold Dhat
      have hzi : ∀ i : Fin n, Measurable (fun y : Fin n → B × ℝ × ℝ => z (y i)) := fun i =>
        hzm.comp (measurable_pi_apply i)
      have hεi : ∀ i : Fin n, Measurable (fun y : Fin n → B × ℝ × ℝ => εf (y i)) := fun i =>
        hεm.comp (measurable_pi_apply i)
      have hzs : Measurable (fun y : Fin n → B × ℝ × ℝ => ∑ j, z (y j)) :=
        Finset.measurable_sum _ fun j _ => hzi j
      have hεs : Measurable (fun y : Fin n → B × ℝ × ℝ => ∑ j, εf (y j)) :=
        Finset.measurable_sum _ fun j _ => hεi j
      refine Measurable.div ?_ ?_
      · exact (Finset.measurable_sum _ fun i _ => ((hzi i).sub (hzs.const_mul _)).mul
          ((hεi i).sub (hεs.const_mul _))).const_mul _
      · exact Finset.measurable_sum _ fun i _ => ((hεi i).sub (hεs.const_mul _)).pow_const 2
    rw [hcomp, eLpNorm_comp_measurePreserving ((hDm.sub_const _).aestronglyMeasurable) hmp]
    set P := Measure.pi fun _ : Fin n => ν
    have hsplit : (fun y : Fin n → B × ℝ × ℝ => Dhat n (ζn n) (fun i => z (y i))
        (fun i => εf (y i)) - Δ) = (fun y => Dhat n (ζn n) (fun i => z (y i))
        (fun i => εf (y i)) - θ n) + (fun _ => θ n - Δ) := by
      funext y; simp only [Pi.add_apply]; ring
    rw [hsplit]
    refine le_trans (eLpNorm_add_le ((hDm.sub_const _).aestronglyMeasurable)
      aestronglyMeasurable_const (by norm_num)) ?_
    gcongr
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      have hlin : ∫⁻ y, ‖Dhat n (ζn n) (fun i => z (y i)) (fun i => εf (y i)) - θ n‖ₑ ^
          (2 : ENNReal).toReal ∂P = ENNReal.ofReal (∫ y, (Dhat n (ζn n) (fun i => z (y i))
            (fun i => εf (y i)) - θ n) ^ 2 ∂P) := by
        rw [ofReal_integral_eq_lintegral_ofReal hDint
          (Filter.Eventually.of_forall fun y => sq_nonneg _)]
        refine lintegral_congr fun y => ?_
        rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofNat,
          ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
        congr 1
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
      rw [hlin, ENNReal.toReal_ofNat,
        ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun y => sq_nonneg _)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow (integral_nonneg fun y => sq_nonneg _) hDle (by norm_num)
    · rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero P), measure_univ,
        ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]
  -- the bounds vanish
  have hBn : Tendsto Bn atTop (𝓝 0) := by
    have hpow : ∀ n : ℕ, 1 ≤ n → ((ζn n)⁻¹) ^ 2 = ζ⁻¹ ^ 2 * (n : ℝ) ^ (2 * α) := by
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      simp only [ζn]
      rw [Real.rpow_neg hnpos.le, mul_inv, inv_inv, mul_pow,
        ← Real.rpow_natCast ((n : ℝ) ^ α) 2, ← Real.rpow_mul hnpos.le]
      congr 2
      push_cast; ring
    have t1 : Tendsto (fun n : ℕ => ζ⁻¹ ^ 2 * (n : ℝ) ^ (-(1 - 2 * α))) atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 - 2 * α)).comp
        tendsto_natCast_atTop_atTop).const_mul (ζ⁻¹ ^ 2)
      rwa [mul_zero] at this
    have t2 : Tendsto (fun n : ℕ => ζ⁻¹ ^ 2 * ((n : ℝ) ^ (2 * α + 1) *
        Real.exp (-(1 / 8) * n))) atTop (𝓝 0) := by
      have := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * α + 1) (1 / 8)
        (by norm_num)).comp tendsto_natCast_atTop_atTop).const_mul (ζ⁻¹ ^ 2)
      rwa [mul_zero] at this
    have t3 : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) / 8)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num : (0 : ℝ) < 8))
      refine this.congr fun n => ?_
      simp [Function.comp, neg_div]
    have hsum := ((tendsto_const_nhds (x := (72 : ℝ))).mul t1).add
      (((tendsto_const_nhds (x := (4 : ℝ))).mul t2).add
        (((tendsto_const_nhds (x := (4 : ℝ))).mul ((hθlim.pow 2))).mul t3))
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simp only [hBn]
    rw [hpow n hn]
    have e1 : (n : ℝ) ^ (-(1 - 2 * α)) = (n : ℝ) ^ (2 * α) / n := by
      rw [show -(1 - 2 * α) = 2 * α - 1 by ring, Real.rpow_sub_one hnpos.ne']
    have e2 : (n : ℝ) ^ (2 * α + 1) = (n : ℝ) ^ (2 * α) * n := by
      rw [Real.rpow_add_one hnpos.ne']
    rw [e1, e2, show -(1 / 8 : ℝ) * n = -(n : ℝ) / 8 by ring]
    ring
  have hupper : Tendsto (fun n : ℕ => ENNReal.ofReal (Bn n ^ (1 / (2 : ℝ))) +
      ENNReal.ofReal |θ n - Δ|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Bn n ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
      have := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).tendsto 0).comp hBn
      rwa [Real.zero_rpow (by norm_num)] at this
    have h2 : Tendsto (fun n : ℕ => |θ n - Δ|) atTop (𝓝 0) := by
      have := (hθlim.sub_const Δ).abs
      rwa [sub_self, abs_zero] at this
    have := (ENNReal.tendsto_ofReal h1).add (ENNReal.tendsto_ofReal h2)
    rwa [ENNReal.ofReal_zero, add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun n => bot_le) hbound
