-- Prove2me | solution 1 for EthierKurtz.kmt_mixture_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T02:10:29.481728+00:00
-- url     : https://prove2.me/submissions/d84d0804-2233-4b49-8751-b3cf8cc83ae6

import Mathlib
import Definitions.Def_EthierKurtz_kmtDiscreteApproximation

open MeasureTheory ProbabilityTheory

namespace P99bcb804
def devSet (n : ℕ) (c : ℝ) : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
    c < |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|}

lemma measurableSet_devSet (n : ℕ) (c : ℝ) : MeasurableSet (devSet n c) := by
  have : devSet n c = ⋃ k : ℕ, ⋃ (_ : 1 ≤ k ∧ k ≤ n),
      {z : (ℕ → ℝ) × (ℕ → ℝ) |
        c < |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} := by
    ext z; simp [devSet, and_assoc]
  rw [this]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_lt measurable_const (by fun_prop)

/-- A KMT-type coupling of an iid `F`-sequence with an iid `G`-sequence. -/
def KPair (F G : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G] : Prop :=
  ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
    Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => F) ∧
    Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ => G) ∧
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
      ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
        Q (devSet n (C * Real.log (n : ℝ) + x)) < ENNReal.ofReal (K * Real.exp (-lam * x))

/-- The triangle step: a deviation of `a - c` splits into one of `a - b` or of `b - c`. -/
lemma devSet_split (n : ℕ) (c1 c2 : ℝ) (a b c : ℕ → ℝ) (h : (a, c) ∈ devSet n (c1 + c2)) :
    (a, b) ∈ devSet n c1 ∨ (b, c) ∈ devSet n c2 := by
  obtain ⟨k, hk1, hkn, hk⟩ := h
  simp only at hk
  by_contra hcon
  simp only [devSet, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hcon
  have h1 := hcon.1 k hk1 hkn
  have h2 := hcon.2 k hk1 hkn
  have := abs_sub_le (∑ i ∈ Finset.range k, a i) (∑ i ∈ Finset.range k, b i)
    (∑ i ∈ Finset.range k, c i)
  linarith

/-- R2 (gluing; KMT 1976 p.37, "standard measure theoretic arguments"): KMT couplings
`(F, G)` and `(G, H)` compose to a KMT coupling `(F, H)`. -/
theorem kpair_trans (F G H : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] (h1 : KPair F G) (h2 : KPair G H) : KPair F H := by
  obtain ⟨Q1, hQ1, f1, s1, C1, K1, l1, hC1, hK1, hl1, b1⟩ := h1
  obtain ⟨Q2, hQ2, f2, s2, C2, K2, l2, hC2, hK2, hl2, b2⟩ := h2
  set κ : Kernel (ℕ → ℝ) (ℕ → ℝ) := Q2.condKernel with hκ
  set κ' : Kernel ((ℕ → ℝ) × (ℕ → ℝ)) (ℕ → ℝ) := κ.comap Prod.snd measurable_snd with hκ'
  set R : Measure (((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) := Q1 ⊗ₘ κ' with hR
  have hRp : IsProbabilityMeasure R := by rw [hR]; infer_instance
  -- the (a,b) marginal of R is Q1
  have L13 : ∀ E, MeasurableSet E → R ((fun p => p.1) ⁻¹' E) = Q1 E := by
    intro E hE
    rw [← Measure.map_apply measurable_fst hE]
    have : R.map Prod.fst = Q1 := by
      rw [hR]; exact Measure.fst_compProd Q1 κ'
    rw [this]
  -- the (b,c) marginal of R is Q2
  have L23 : ∀ E, MeasurableSet E → R ((fun p => (p.1.2, p.2)) ⁻¹' E) = Q2 E := by
    intro E hE
    have hmeas : Measurable (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) => (p.1.2, p.2)) := by
      fun_prop
    rw [hR, Measure.compProd_apply (hmeas hE)]
    have hfun : ∀ ab : (ℕ → ℝ) × (ℕ → ℝ),
        κ' ab
          (Prod.mk ab ⁻¹' ((fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) => (p.1.2, p.2)) ⁻¹' E)) =
        (fun b => κ b (Prod.mk b ⁻¹' E)) ab.2 := by
      intro ab; rfl
    simp_rw [hfun]
    have hm : Measurable (fun b => κ b (Prod.mk b ⁻¹' E)) :=
      Kernel.measurable_kernel_prodMk_left hE
    rw [← lintegral_map (f := fun b => κ b (Prod.mk b ⁻¹' E)) hm measurable_snd, s1, ← f2]
    rw [← Measure.compProd_apply hE]
    exact congrArg (fun m : Measure _ => m E) (Measure.disintegrate Q2 Q2.condKernel)
  set Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := R.map (fun p => (p.1.1, p.2)) with hQ
  have hQm : Measurable (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) => (p.1.1, p.2)) := by fun_prop
  have hQp : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hQm.aemeasurable
  refine ⟨Q, hQp, ?_, ?_, C1 + C2, K1 + K2, min l1 l2 / 2, by linarith, by linarith,
    by positivity, ?_⟩
  · ext s hs
    rw [Measure.map_apply measurable_fst hs, hQ, Measure.map_apply hQm (measurable_fst hs),
      ← f1, Measure.map_apply measurable_fst hs]
    rw [← L13 _ (measurable_fst hs)]
    rfl
  · ext s hs
    rw [Measure.map_apply measurable_snd hs, hQ, Measure.map_apply hQm (measurable_snd hs),
      ← s2, Measure.map_apply measurable_snd hs]
    rw [← L23 _ (measurable_snd hs)]
    rfl
  · intro n hn x hx
    rw [hQ, Measure.map_apply hQm (measurableSet_devSet _ _)]
    have hsub : (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) => (p.1.1, p.2)) ⁻¹'
        devSet n ((C1 + C2) * Real.log n + x) ⊆
        (fun p => p.1) ⁻¹' devSet n (C1 * Real.log n + x / 2) ∪
        (fun p => (p.1.2, p.2)) ⁻¹' devSet n (C2 * Real.log n + x / 2) := by
      intro p hp
      have hp' : (p.1.1, p.2) ∈ devSet n ((C1 * Real.log n + x / 2) +
          (C2 * Real.log n + x / 2)) := by
        have : (C1 * Real.log n + x / 2) + (C2 * Real.log n + x / 2) =
            (C1 + C2) * Real.log n + x := by ring
        rw [this]; exact hp
      rcases devSet_split n _ _ p.1.1 p.1.2 p.2 hp' with h | h
      · left; exact h
      · right; exact h
    have hx2 : 0 < x / 2 := by linarith
    have e1 := b1 n hn (x / 2) hx2
    have e2 := b2 n hn (x / 2) hx2
    rw [← L13 _ (measurableSet_devSet _ _)] at e1
    rw [← L23 _ (measurableSet_devSet _ _)] at e2
    calc R _ ≤ R ((fun p => p.1) ⁻¹' devSet n (C1 * Real.log n + x / 2) ∪
          (fun p => (p.1.2, p.2)) ⁻¹' devSet n (C2 * Real.log n + x / 2)) := measure_mono hsub
      _ ≤ R ((fun p => p.1) ⁻¹' devSet n (C1 * Real.log n + x / 2)) +
          R ((fun p => (p.1.2, p.2)) ⁻¹' devSet n (C2 * Real.log n + x / 2)) :=
          measure_union_le _ _
      _ < ENNReal.ofReal (K1 * Real.exp (-l1 * (x / 2))) +
          ENNReal.ofReal (K2 * Real.exp (-l2 * (x / 2))) := ENNReal.add_lt_add e1 e2
      _ = ENNReal.ofReal (K1 * Real.exp (-l1 * (x / 2)) + K2 * Real.exp (-l2 * (x / 2))) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal ((K1 + K2) * Real.exp (-(min l1 l2 / 2) * x)) := by
          apply ENNReal.ofReal_le_ofReal
          have m1 : Real.exp (-l1 * (x / 2)) ≤ Real.exp (-(min l1 l2 / 2) * x) := by
            apply Real.exp_le_exp.2
            have := min_le_left l1 l2
            nlinarith
          have m2 : Real.exp (-l2 * (x / 2)) ≤ Real.exp (-(min l1 l2 / 2) * x) := by
            apply Real.exp_le_exp.2
            have := min_le_right l1 l2
            nlinarith
          rw [add_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left m1 hK1.le)
            (mul_le_mul_of_nonneg_left m2 hK2.le)

/-- A `KPair μ N(0,1)` is exactly the leaf's KMT coupling. -/
theorem kmt_of_kpair (μ : ProbabilityMeasure ℝ) (h : KPair (μ : Measure ℝ) (gaussianReal 0 1)) :
    EthierKurtz.kmtDiscreteApproximation μ := by
  obtain ⟨Q, hQ, hf, hs, C, K, lam, hC, hK, hl, hb⟩ := h
  have := hQ
  have m1 : ∀ i, Measurable (fun z : (ℕ → ℝ) × (ℕ → ℝ) => z.1 i) :=
    fun i => (measurable_pi_apply i).comp measurable_fst
  have m2 : ∀ i, Measurable (fun z : (ℕ → ℝ) × (ℕ → ℝ) => z.2 i) :=
    fun i => (measurable_pi_apply i).comp measurable_snd
  have law1 : ∀ i, Q.map (fun z : (ℕ → ℝ) × (ℕ → ℝ) => z.1 i) = (μ : Measure ℝ) := by
    intro i
    have : (fun z : (ℕ → ℝ) × (ℕ → ℝ) => z.1 i) = (fun ω : ℕ → ℝ => ω i) ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply i) measurable_fst, hf,
      Measure.infinitePi_map_eval]
  have law2 : ∀ i, Q.map (fun z : (ℕ → ℝ) × (ℕ → ℝ) => z.2 i) = gaussianReal 0 1 := by
    intro i
    have : (fun z : (ℕ → ℝ) × (ℕ → ℝ) => z.2 i) = (fun ω : ℕ → ℝ => ω i) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply i) measurable_snd, hs,
      Measure.infinitePi_map_eval]
  refine ⟨⟨Q, hQ⟩, ?_, fun i => ⟨(m1 i).aemeasurable, law1 i⟩, ?_,
    fun i => ⟨(m2 i).aemeasurable, law2 i⟩, C, K, lam, hC, hK, hl, ?_⟩
  · change iIndepFun (fun (i : ℕ) (z : (ℕ → ℝ) × (ℕ → ℝ)) => z.1 i) Q
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀ (measurable_pi_iff.2 m1).aemeasurable]
    simp_rw [law1]
    exact hf
  · change iIndepFun (fun (i : ℕ) (z : (ℕ → ℝ) × (ℕ → ℝ)) => z.2 i) Q
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀ (measurable_pi_iff.2 m2).aemeasurable]
    simp_rw [law2]
    exact hs
  · intro n hn x hx
    exact hb n hn x hx

/-- Identity coupling: every law is KMT-coupled with itself (zero error). -/
theorem kpair_refl (F : Measure ℝ) [IsProbabilityMeasure F] : KPair F F := by
  have hm : Measurable (fun ω : ℕ → ℝ => (ω, ω)) := measurable_id.prodMk measurable_id
  refine ⟨(Measure.infinitePi fun _ : ℕ => F).map (fun ω => (ω, ω)),
    Measure.isProbabilityMeasure_map hm.aemeasurable, ?_, ?_, 1, 1, 1, one_pos, one_pos, one_pos, ?_⟩
  · rw [Measure.map_map measurable_fst hm]; exact Measure.map_id
  · rw [Measure.map_map measurable_snd hm]; exact Measure.map_id
  · intro n hn x hx
    rw [Measure.map_apply hm (measurableSet_devSet _ _)]
    have : (fun ω : ℕ → ℝ => (ω, ω)) ⁻¹' devSet n (1 * Real.log n + x) = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨k, -, -, hk⟩
      simp only [sub_self, abs_zero] at hk
      have : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      linarith
    rw [this, measure_empty]
    exact ENNReal.ofReal_pos.2 (by positivity)

/-- Mixture of two laws with weight `p` on the first. -/
noncomputable def mixM (p : ℝ) (F1 F2 : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal p • F1 + ENNReal.ofReal (1 - p) • F2

lemma isProb_mixM (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F1 F2 : Measure ℝ)
    [IsProbabilityMeasure F1] [IsProbabilityMeasure F2] : IsProbabilityMeasure (mixM p F1 F2) := by
  constructor
  simp only [mixM, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  simp

/-- Child R1 (KMT 1976 Part II, Lemma 1, p.37): mixtures of KMT couplings are KMT couplings. -/
def MixProp : Prop :=
  ∀ (F1 G1 F2 G2 : Measure ℝ) [IsProbabilityMeasure F1] [IsProbabilityMeasure G1]
    [IsProbabilityMeasure F2] [IsProbabilityMeasure G2] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1),
    KPair F1 G1 → KPair F2 G2 →
      @KPair (mixM p F1 F2) (mixM p G1 G2) (isProb_mixM p hp0 hp1 F1 F2)
        (isProb_mixM p hp0 hp1 G1 G2)

/-- Child R3 (KMT 1976 Part II, Theorem 1B, §4): bounded non-degenerate laws have a KMT
coupling with Gaussian increments of the same mean and variance. -/
def BddProp : Prop :=
  ∀ (F : Measure ℝ) [IsProbabilityMeasure F], (∃ K : ℝ, F (Set.Icc (-K) K) = 1) →
    0 < variance (fun x : ℝ => x) F →
    KPair F (gaussianReal (∫ x, x ∂F) (variance (fun x : ℝ => x) F).toNNReal)

/-- Child R4 (KMT 1976 Part II, Theorem 1A, §3) in the case of a Gaussian component:
a law `G = p N(m,v) + (1-p) F2` (p > 0, v > 0) with mean 0, variance 1 and exponential
moments has a KMT coupling with standard Gaussian increments. -/
def GaussCompProp : Prop :=
  ∀ (F2 : Measure ℝ) [IsProbabilityMeasure F2] (p m : ℝ) (v : NNReal) (hp0 : 0 < p) (hp1 : p ≤ 1),
    v ≠ 0 →
    (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ →
      Integrable (fun x : ℝ => Real.exp (a * x)) (mixM p (gaussianReal m v) F2)) →
    ∫ x, x ∂(mixM p (gaussianReal m v) F2) = 0 →
    variance (fun x : ℝ => x) (mixM p (gaussianReal m v) F2) = 1 →
    @KPair (mixM p (gaussianReal m v) F2) (gaussianReal 0 1)
      (isProb_mixM p hp0.le hp1 _ _) inferInstance

/-- The splitting step (KMT 1976 Part II, p.37): `μ = p F1 + (1-p) F2` with `F1` bounded and
non-degenerate, such that replacing `F1` by the Gaussian with its mean and variance keeps
mean 0, variance 1 and the exponential moments. -/
def SplitProp : Prop :=
  ∀ μ : ProbabilityMeasure ℝ,
    (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ →
      Integrable (fun x : ℝ => Real.exp (a * x)) (μ : Measure ℝ)) →
    ∫ x : ℝ, x ∂(μ : Measure ℝ) = 0 →
    variance (fun x : ℝ => x) (μ : Measure ℝ) = 1 →
    ∃ (p : ℝ) (F1 F2 : Measure ℝ) (_ : IsProbabilityMeasure F1) (_ : IsProbabilityMeasure F2),
      0 < p ∧ p < 1 ∧ (∃ K : ℝ, F1 (Set.Icc (-K) K) = 1) ∧
      0 < variance (fun x : ℝ => x) F1 ∧ (μ : Measure ℝ) = mixM p F1 F2 ∧
      (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ → Integrable (fun x : ℝ => Real.exp (a * x))
        (mixM p (gaussianReal (∫ x, x ∂F1) (variance (fun x : ℝ => x) F1).toNNReal) F2)) ∧
      ∫ x, x ∂(mixM p (gaussianReal (∫ x, x ∂F1) (variance (fun x : ℝ => x) F1).toNNReal) F2)
        = 0 ∧
      variance (fun x : ℝ => x)
        (mixM p (gaussianReal (∫ x, x ∂F1) (variance (fun x : ℝ => x) F1).toNNReal) F2) = 1


lemma integrable_mixM {p : ℝ} {F1 F2 : Measure ℝ} {f : ℝ → ℝ} (h1 : Integrable f F1)
    (h2 : Integrable f F2) : Integrable f (mixM p F1 F2) :=
  (h1.smul_measure ENNReal.ofReal_ne_top).add_measure (h2.smul_measure ENNReal.ofReal_ne_top)

lemma integral_mixM {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {F1 F2 : Measure ℝ} {f : ℝ → ℝ}
    (h1 : Integrable f F1) (h2 : Integrable f F2) :
    ∫ x, f x ∂(mixM p F1 F2) = p * ∫ x, f x ∂F1 + (1 - p) * ∫ x, f x ∂F2 := by
  rw [mixM, integral_add_measure (h1.smul_measure ENNReal.ofReal_ne_top)
    (h2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith)]
  simp [smul_eq_mul]

lemma abs_le_exp_add (a x : ℝ) (ha : 0 < a) :
    |x| ≤ 1 / a * (Real.exp (a * x) + Real.exp (-a * x)) := by
  have h1 : a * |x| + 1 ≤ Real.exp (a * |x|) := by
    have := Real.add_one_le_exp (a * |x|); linarith
  have h2 : Real.exp (a * |x|) ≤ Real.exp (a * x) + Real.exp (-a * x) := by
    rcases abs_cases x with ⟨hx, -⟩ | ⟨hx, -⟩
    · rw [hx]; have := Real.exp_pos (-a * x); linarith
    · rw [hx]; have := Real.exp_pos (a * x); rw [show a * -x = -a * x by ring]; linarith
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha]
  have := abs_nonneg x
  nlinarith

lemma sq_le_exp_add (a x : ℝ) (ha : 0 < a) :
    x ^ 2 ≤ 2 / a ^ 2 * (Real.exp (a * x) + Real.exp (-a * x)) := by
  have h1 : (a * |x|) ^ 2 / 2 ≤ Real.exp (a * |x|) := by
    have hb : 0 ≤ a * |x| := by positivity
    have := Real.quadratic_le_exp_of_nonneg hb
    nlinarith [sq_nonneg (a * |x|)]
  have h2 : Real.exp (a * |x|) ≤ Real.exp (a * x) + Real.exp (-a * x) := by
    rcases abs_cases x with ⟨hx, -⟩ | ⟨hx, -⟩
    · rw [hx]; have := Real.exp_pos (-a * x); linarith
    · rw [hx]; have := Real.exp_pos (a * x); rw [show a * -x = -a * x by ring]; linarith
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rw [hx2, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : (a * |x|) ^ 2 = a ^ 2 * |x| ^ 2 := by ring
  nlinarith

lemma integrable_id_of_exp {ν : Measure ℝ} {a : ℝ} (ha : 0 < a)
    (h1 : Integrable (fun x : ℝ => Real.exp (a * x)) ν)
    (h2 : Integrable (fun x : ℝ => Real.exp (-a * x)) ν) : Integrable (fun x : ℝ => x) ν := by
  refine Integrable.mono' ((h1.add h2).const_mul (1 / a)) (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using abs_le_exp_add a x ha

lemma integrable_sq_of_exp {ν : Measure ℝ} {a : ℝ} (ha : 0 < a)
    (h1 : Integrable (fun x : ℝ => Real.exp (a * x)) ν)
    (h2 : Integrable (fun x : ℝ => Real.exp (-a * x)) ν) :
    Integrable (fun x : ℝ => x ^ 2) ν := by
  refine Integrable.mono' ((h1.add h2).const_mul (2 / a ^ 2)) (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
    exact sq_le_exp_add a x ha

/-- A mean-zero law with nonzero variance charges both half-lines. -/
lemma two_sided (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (hmean : ∫ x, x ∂μ = 0)
    (hvar : variance (fun x : ℝ => x) μ ≠ 0) : 0 < μ (Set.Iio 0) ∧ 0 < μ (Set.Ioi 0) := by
  have hzero : ∀ (f : ℝ → ℝ), (0 ≤ᵐ[μ] f) → ∫ x, f x ∂μ = 0 → Integrable f μ →
      f =ᵐ[μ] 0 := fun f hf hi hint => (integral_eq_zero_iff_of_nonneg_ae hf hint).1 hi
  have hv0 : (fun x : ℝ => x) =ᵐ[μ] 0 → False := by
    intro h
    apply hvar
    rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop), hmean]
    have : (fun x : ℝ => (x - 0) ^ 2) =ᵐ[μ] 0 := by
      filter_upwards [h] with x hx
      simp only [Pi.zero_apply] at hx
      simp [hx]
    rw [integral_congr_ae this]
    simp
  constructor
  · rw [pos_iff_ne_zero]
    intro h0
    apply hv0
    have hnn : 0 ≤ᵐ[μ] (fun x : ℝ => x) := by
      rw [Filter.EventuallyLE, ae_iff]
      have : {a : ℝ | ¬ (0 : ℝ → ℝ) a ≤ a} = Set.Iio 0 := by
        ext a; simp
      rw [this]; exact h0
    exact hzero _ hnn hmean hint
  · rw [pos_iff_ne_zero]
    intro h0
    apply hv0
    have hnn : 0 ≤ᵐ[μ] (fun x : ℝ => -x) := by
      rw [Filter.EventuallyLE, ae_iff]
      have : {a : ℝ | ¬ (0 : ℝ → ℝ) a ≤ -a} = Set.Ioi 0 := by
        ext a; simp
      rw [this]; exact h0
    have := hzero _ hnn (by rw [integral_neg, hmean, neg_zero]) hint.neg
    filter_upwards [this] with x hx
    simpa using hx

/-- Some bounded window `[-K, K]` charges both sides of 0. -/
lemma exists_window (μ : Measure ℝ) (hl : 0 < μ (Set.Iio 0)) (hr : 0 < μ (Set.Ioi 0)) :
    ∃ K : ℝ, 0 < K ∧ 0 < μ (Set.Ico (-K) 0) ∧ 0 < μ (Set.Ioc 0 K) := by
  have hL : ∃ n : ℕ, 0 < μ (Set.Ico (-(n : ℝ)) 0) := by
    by_contra hc
    push Not at hc
    have : Set.Iio (0 : ℝ) = ⋃ n : ℕ, Set.Ico (-(n : ℝ)) 0 := by
      ext x
      simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Ico]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt (-x)
        exact ⟨n, by linarith, hx⟩
      · rintro ⟨n, -, hx⟩; exact hx
    rw [this, measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc n)] at hl
    exact lt_irrefl _ hl
  have hR : ∃ n : ℕ, 0 < μ (Set.Ioc 0 (n : ℝ)) := by
    by_contra hc
    push Not at hc
    have : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ioc 0 (n : ℝ) := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt x
        exact ⟨n, hx, hn.le⟩
      · rintro ⟨n, hx, -⟩; exact hx
    rw [this, measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc n)] at hr
    exact lt_irrefl _ hr
  obtain ⟨n1, h1⟩ := hL
  obtain ⟨n2, h2⟩ := hR
  refine ⟨max (max n1 n2) 1, by positivity, ?_, ?_⟩
  · refine lt_of_lt_of_le h1 (measure_mono ?_)
    intro x hx
    simp only [Set.mem_Ico] at hx ⊢
    refine ⟨?_, hx.2⟩
    have : (n1 : ℝ) ≤ max (max (n1 : ℝ) n2) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith [hx.1]
  · refine lt_of_lt_of_le h2 (measure_mono ?_)
    intro x hx
    simp only [Set.mem_Ioc] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have : (n2 : ℝ) ≤ max (max (n1 : ℝ) n2) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith [hx.2]

section Pieces
variable (μ : Measure ℝ) (K : ℝ)

/-- Bounded piece: `μ` restricted to `[-K, K]`, normalised. -/
noncomputable def piece1 : Measure ℝ :=
  ENNReal.ofReal (1 / (μ (Set.Icc (-K) K)).toReal) • μ.restrict (Set.Icc (-K) K)

/-- Remainder piece, so that `μ = p piece1 + (1-p) piece2` with `p = μ[-K,K]/2`. -/
noncomputable def piece2 : Measure ℝ :=
  ENNReal.ofReal (1 / (1 - (μ (Set.Icc (-K) K)).toReal / 2)) •
    (μ.restrict (Set.Icc (-K) K)ᶜ + ENNReal.ofReal (1 / 2) • μ.restrict (Set.Icc (-K) K))

variable [IsProbabilityMeasure μ]

lemma piece1_apply_I (hq : 0 < μ (Set.Icc (-K) K)) : piece1 μ K (Set.Icc (-K) K) = 1 := by
  have hne : μ (Set.Icc (-K) K) ≠ ⊤ := measure_ne_top _ _
  have hq' : 0 < (μ (Set.Icc (-K) K)).toReal := ENNReal.toReal_pos hq.ne' hne
  rw [piece1, Measure.smul_apply, Measure.restrict_apply_self, smul_eq_mul,
    ← ENNReal.ofReal_toReal hne, ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal hq'.le,
    one_div, inv_mul_cancel₀ hq'.ne', ENNReal.ofReal_one]

lemma piece1_isProb (hq : 0 < μ (Set.Icc (-K) K)) : IsProbabilityMeasure (piece1 μ K) := by
  constructor
  have h := piece1_apply_I μ K hq
  rw [piece1, Measure.smul_apply, Measure.restrict_apply_self] at h
  rw [piece1, Measure.smul_apply, Measure.restrict_apply_univ]
  exact h

lemma piece2_isProb (hq : 0 < μ (Set.Icc (-K) K)) : IsProbabilityMeasure (piece2 μ K) := by
  constructor
  have hne : μ (Set.Icc (-K) K) ≠ ⊤ := measure_ne_top _ _
  set q := (μ (Set.Icc (-K) K)).toReal with hqdef
  have hq' : 0 < q := ENNReal.toReal_pos hq.ne' hne
  have hq1 : q ≤ 1 := by
    rw [hqdef]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hp2 : 0 < 1 - q / 2 := by linarith
  have hI : μ (Set.Icc (-K) K) = ENNReal.ofReal q := (ENNReal.ofReal_toReal hne).symm
  have hIc : μ (Set.Icc (-K) K)ᶜ = ENNReal.ofReal (1 - q) := by
    rw [prob_compl_eq_one_sub measurableSet_Icc, hI, ENNReal.ofReal_sub _ hq'.le, ENNReal.ofReal_one]
  rw [piece2, ← hqdef, Measure.smul_apply, Measure.add_apply, Measure.smul_apply,
    Measure.restrict_apply_univ, Measure.restrict_apply_univ, hIc, hI, smul_eq_mul, smul_eq_mul,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by linarith) (by positivity),
    ← ENNReal.ofReal_mul (div_nonneg zero_le_one hp2.le)]
  have : 1 / (1 - q / 2) * (1 - q + 1 / 2 * q) = 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_eq_one_iff_eq hp2.ne']
    ring
  rw [this, ENNReal.ofReal_one]

lemma split_eq (hq : 0 < μ (Set.Icc (-K) K)) :
    μ = mixM ((μ (Set.Icc (-K) K)).toReal / 2) (piece1 μ K) (piece2 μ K) := by
  have hne : μ (Set.Icc (-K) K) ≠ ⊤ := measure_ne_top _ _
  set q := (μ (Set.Icc (-K) K)).toReal with hqdef
  have hq' : 0 < q := ENNReal.toReal_pos hq.ne' hne
  have hq1 : q ≤ 1 := by
    rw [hqdef]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hp2 : 0 < 1 - q / 2 := by linarith
  rw [mixM, piece1, piece2, smul_smul, smul_smul, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hp2.le]
  have e1 : q / 2 * (1 / q) = 1 / 2 := by field_simp
  have e2 : (1 - q / 2) * (1 / (1 - q / 2)) = 1 := by rw [mul_one_div, div_self hp2.ne']
  rw [e1, e2, ENNReal.ofReal_one, one_smul]
  calc μ = μ.restrict (Set.Icc (-K) K)ᶜ + μ.restrict (Set.Icc (-K) K) := by
        rw [add_comm]; exact (Measure.restrict_add_restrict_compl measurableSet_Icc).symm
    _ = μ.restrict (Set.Icc (-K) K)ᶜ +
        (ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2)) • μ.restrict (Set.Icc (-K) K) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
    _ = _ := by rw [add_smul]; abel

lemma piece1_pos_of_sub (hq : 0 < μ (Set.Icc (-K) K)) {S : Set ℝ} (hS : MeasurableSet S)
    (hsub : S ⊆ Set.Icc (-K) K) (hpos : 0 < μ S) : 0 < piece1 μ K S := by
  have hne : μ (Set.Icc (-K) K) ≠ ⊤ := measure_ne_top _ _
  have hq' : 0 < (μ (Set.Icc (-K) K)).toReal := ENNReal.toReal_pos hq.ne' hne
  rw [piece1, Measure.smul_apply, Measure.restrict_apply hS, Set.inter_eq_left.2 hsub, smul_eq_mul]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' hpos.ne'

lemma piece1_var_pos (hl : 0 < μ (Set.Ico (-K) 0)) (hr : 0 < μ (Set.Ioc 0 K))
    (hint2 : Integrable (fun x : ℝ => x ^ 2) μ) : 0 < variance (fun x : ℝ => x) (piece1 μ K) := by
  have hK : 0 < K := by
    by_contra hc; push Not at hc
    have : Set.Ioc 0 K = ∅ := by
      ext y; simp only [Set.mem_Ioc, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro hy; linarith
    rw [this, measure_empty] at hr; exact lt_irrefl _ hr
  have hsubL : Set.Ico (-K) 0 ⊆ Set.Icc (-K) K := by
    intro x hx; simp only [Set.mem_Ico, Set.mem_Icc] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hsubR : Set.Ioc 0 K ⊆ Set.Icc (-K) K := by
    intro x hx; simp only [Set.mem_Ioc, Set.mem_Icc] at hx ⊢
    exact ⟨by linarith [hx.1], hx.2⟩
  have hq : 0 < μ (Set.Icc (-K) K) := lt_of_lt_of_le hl (measure_mono hsubL)
  have := piece1_isProb μ K hq
  rcases (variance_nonneg (fun x : ℝ => x) (piece1 μ K)).lt_or_eq with h | h
  · exact h
  exfalso
  set m := ∫ x, x ∂(piece1 μ K) with hm
  have h0 := h.symm
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at h0
  have hintμ : Integrable (fun x : ℝ => (x - m) ^ 2) μ := by
    refine Integrable.mono' ((hint2.const_mul 2).add (integrable_const (2 * m ^ 2)))
      (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    show (x - m) ^ 2 ≤ 2 * x ^ 2 + 2 * m ^ 2
    nlinarith [sq_nonneg (x + m)]
  have hint : Integrable (fun x : ℝ => (x - m) ^ 2) (piece1 μ K) :=
    (hintμ.restrict).smul_measure ENNReal.ofReal_ne_top
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => sq_nonneg (x - m)) hint).1 h0
  rw [Filter.EventuallyEq, ae_iff] at hae
  rcases le_or_gt 0 m with hm0 | hm0
  · have hp := piece1_pos_of_sub μ K hq measurableSet_Ico hsubL hl
    refine absurd (measure_mono_null ?_ hae) hp.ne'
    intro x hx
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_ofPred_eq, Pi.zero_apply]
    have : x - m < 0 := by linarith [hx.2]
    exact pow_ne_zero 2 this.ne
  · have hp := piece1_pos_of_sub μ K hq measurableSet_Ioc hsubR hr
    refine absurd (measure_mono_null ?_ hae) hp.ne'
    intro x hx
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_ofPred_eq, Pi.zero_apply]
    have : 0 < x - m := by linarith [hx.1]
    exact pow_ne_zero 2 this.ne'

end Pieces

lemma integrable_piece1 (μ : Measure ℝ) (K : ℝ) {f : ℝ → ℝ} (h : Integrable f μ) :
    Integrable f (piece1 μ K) :=
  h.restrict.smul_measure ENNReal.ofReal_ne_top

lemma integrable_piece2 (μ : Measure ℝ) (K : ℝ) {f : ℝ → ℝ} (h : Integrable f μ) :
    Integrable f (piece2 μ K) :=
  (h.restrict.add_measure (h.restrict.smul_measure ENNReal.ofReal_ne_top)).smul_measure
    ENNReal.ofReal_ne_top

lemma var_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : Integrable (fun x : ℝ => x ^ 2) ν) :
    variance (fun x : ℝ => x) ν = ∫ x, x ^ 2 ∂ν - (∫ x, x ∂ν) ^ 2 := by
  have hm : MemLp (fun x : ℝ => x) 2 ν := (memLp_two_iff_integrable_sq (by fun_prop)).2 h
  rw [variance_eq_sub hm]
  simp only [Pi.pow_apply]

lemma gauss_int (m : ℝ) (v : NNReal) : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
  integrable_id_of_exp one_pos (integrable_exp_mul_gaussianReal 1)
    (integrable_exp_mul_gaussianReal (-1))

lemma gauss_int2 (m : ℝ) (v : NNReal) : Integrable (fun x : ℝ => x ^ 2) (gaussianReal m v) :=
  integrable_sq_of_exp one_pos (integrable_exp_mul_gaussianReal 1)
    (integrable_exp_mul_gaussianReal (-1))

theorem splitProp : SplitProp := by
  intro μ hexp hmean hvar
  obtain ⟨a₀, ha₀, hexpa⟩ := hexp
  have e1 := hexpa a₀ (by rw [abs_of_pos ha₀])
  have e2 := hexpa (-a₀) (by rw [abs_neg, abs_of_pos ha₀])
  have hint : Integrable (fun x : ℝ => x) (μ : Measure ℝ) := integrable_id_of_exp ha₀ e1 e2
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ) := integrable_sq_of_exp ha₀ e1 e2
  obtain ⟨hl, hr⟩ := two_sided (μ : Measure ℝ) hint hmean (by rw [hvar]; norm_num)
  obtain ⟨K, hK, hlK, hrK⟩ := exists_window (μ : Measure ℝ) hl hr
  have hsubL : Set.Ico (-K) 0 ⊆ Set.Icc (-K) K := by
    intro x hx; simp only [Set.mem_Ico, Set.mem_Icc] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hq : 0 < (μ : Measure ℝ) (Set.Icc (-K) K) := lt_of_lt_of_le hlK (measure_mono hsubL)
  have hne : (μ : Measure ℝ) (Set.Icc (-K) K) ≠ ⊤ := measure_ne_top _ _
  have hq' : 0 < ((μ : Measure ℝ) (Set.Icc (-K) K)).toReal := ENNReal.toReal_pos hq.ne' hne
  have hq1 : ((μ : Measure ℝ) (Set.Icc (-K) K)).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  haveI i1 := piece1_isProb (μ : Measure ℝ) K hq
  haveI i2 := piece2_isProb (μ : Measure ℝ) K hq
  have hsplit := split_eq (μ : Measure ℝ) K hq
  have hv1 := piece1_var_pos (μ : Measure ℝ) K hlK hrK hint2
  set F1 := piece1 (μ : Measure ℝ) K with hF1
  set F2 := piece2 (μ : Measure ℝ) K with hF2
  set p := ((μ : Measure ℝ) (Set.Icc (-K) K)).toReal / 2 with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by linarith
  set m1 := ∫ x, x ∂F1 with hm1
  set v1 := variance (fun x : ℝ => x) F1 with hv1def
  have f1int : Integrable (fun x : ℝ => x) F1 := integrable_piece1 _ K hint
  have f2int : Integrable (fun x : ℝ => x) F2 := integrable_piece2 _ K hint
  have f1int2 : Integrable (fun x : ℝ => x ^ 2) F1 := integrable_piece1 _ K hint2
  have f2int2 : Integrable (fun x : ℝ => x ^ 2) F2 := integrable_piece2 _ K hint2
  have Gm : ∫ x, x ∂(mixM p (gaussianReal m1 v1.toNNReal) F2) = 0 := by
    have hμm := hmean
    rw [hsplit, integral_mixM hp0 hp1 f1int f2int] at hμm
    rw [integral_mixM hp0 hp1 (gauss_int _ _) f2int, integral_id_gaussianReal]
    exact hμm
  refine ⟨p, F1, F2, i1, i2, by positivity, by linarith, ⟨K, piece1_apply_I _ K hq⟩, hv1, hsplit,
    ⟨a₀, ha₀, fun a ha => integrable_mixM (integrable_exp_mul_gaussianReal a)
      (integrable_piece2 _ K (hexpa a ha))⟩, Gm, ?_⟩
  haveI iG := isProb_mixM p hp0 hp1 (gaussianReal m1 v1.toNNReal) F2
  have hμv := hvar
  rw [var_eq _ hint2, hmean, hsplit, integral_mixM hp0 hp1 f1int2 f2int2] at hμv
  have hF1v := var_eq F1 f1int2
  have hgv := var_eq (gaussianReal m1 v1.toNNReal) (gauss_int2 _ _)
  rw [variance_fun_id_gaussianReal, integral_id_gaussianReal, Real.coe_toNNReal _ hv1.le] at hgv
  rw [var_eq _ (integrable_mixM (gauss_int2 _ _) f2int2), Gm,
    integral_mixM hp0 hp1 (gauss_int2 _ _) f2int2]
  have : ∫ x, x ^ 2 ∂(gaussianReal m1 v1.toNNReal) = v1 + m1 ^ 2 := by linarith
  rw [this]
  have : ∫ x, x ^ 2 ∂F1 = v1 + m1 ^ 2 := by rw [← hm1, ← hv1def] at hF1v; linarith
  rw [this] at hμv
  linarith


/-- Bernoulli(p) selector law on `Bool`. -/
noncomputable def bern (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

lemma isProb_bern (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsProbabilityMeasure (bern p) := by
  constructor
  simp only [bern, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  simp

/-- Number of indices `i < n` with selector value `b` (the random time change). -/
def cnt (ε : ℕ → Bool) (b : Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if ε i = b then 1 else 0

lemma cnt_succ (ε : ℕ → Bool) (b : Bool) (n : ℕ) :
    cnt ε b (n + 1) = cnt ε b n + if ε n = b then 1 else 0 :=
  Finset.sum_range_succ _ _

lemma cnt_mono (ε : ℕ → Bool) (b : Bool) {m n : ℕ} (h : m ≤ n) : cnt ε b m ≤ cnt ε b n :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

lemma cnt_inj (ε : ℕ → Bool) (b : Bool) {i j : ℕ} (hi : ε i = b) (hj : ε j = b)
    (h : cnt ε b i = cnt ε b j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := cnt_mono ε b (Nat.succ_le_of_lt hlt)
    rw [cnt_succ, if_pos hi] at this; omega
  · have := cnt_mono ε b (Nat.succ_le_of_lt hlt)
    rw [cnt_succ, if_pos hj] at this; omega

lemma cnt_add (ε : ℕ → Bool) (n : ℕ) : cnt ε true n + cnt ε false n = n := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    rw [cnt_succ, cnt_succ]
    cases h : ε n <;> simp <;> omega

/-- The time-changed merge of two sequences along the selectors. -/
def zf (ε : ℕ → Bool) (x1 x2 : ℕ → ℝ) (n : ℕ) : ℝ :=
  if ε n = true then x1 (cnt ε true n) else x2 (cnt ε false n)

lemma sum_zf (ε : ℕ → Bool) (x1 x2 : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range k, zf ε x1 x2 i =
      ∑ j ∈ Finset.range (cnt ε true k), x1 j + ∑ j ∈ Finset.range (cnt ε false k), x2 j := by
  induction k with
  | zero => simp [cnt]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, cnt_succ, cnt_succ]
    cases h : ε k <;> simp [zf, h, Finset.sum_range_succ] <;> ring

lemma measurable_cnt (b : Bool) (n : ℕ) : Measurable (fun ε : ℕ → Bool => cnt ε b n) := by
  unfold cnt
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (Measurable.of_discrete (f := fun c : Bool => if c = b then 1 else 0)).comp
    (measurable_pi_apply i)

lemma measurable_evalAt {α : Type*} [MeasurableSpace α] {c : α → ℕ} (hc : Measurable c)
    {x : α → ℕ → ℝ} (hx : Measurable x) : Measurable (fun a => x a (c a)) := by
  have : Measurable (fun z : ℕ × (ℕ → ℝ) => z.2 z.1) :=
    measurable_from_prod_countable_right (fun k => measurable_pi_apply k)
  exact this.comp (hc.prodMk hx)

lemma measurable_Zfun :
    Measurable (fun ω : (ℕ → Bool) × ((ℕ → ℝ) × (ℕ → ℝ)) => zf ω.1 ω.2.1 ω.2.2) := by
  rw [measurable_pi_iff]; intro n
  unfold zf
  refine Measurable.ite ?_
    (measurable_evalAt ((measurable_cnt true n).comp measurable_fst) measurable_snd.fst)
    (measurable_evalAt ((measurable_cnt false n).comp measurable_fst) measurable_snd.snd)
  exact (measurableSet_singleton true).preimage ((measurable_pi_apply n).comp measurable_fst)

lemma side (ε : ℕ → Bool) (b : Bool) (F : Measure ℝ) [IsProbabilityMeasure F] (s : Finset ℕ)
    (t : ℕ → Set ℝ) (ht : ∀ i, MeasurableSet (t i)) :
    Measure.infinitePi (fun _ : ℕ => F)
        {x : ℕ → ℝ | ∀ i ∈ s, ε i = b → x (cnt ε b i) ∈ t i} =
      ∏ i ∈ s.filter (fun i => ε i = b), F (t i) := by
  classical
  set T := s.filter (fun i => ε i = b)
  let f : T → ℕ := fun j => cnt ε b j.1
  have hf : Function.Injective f := by
    intro j k h
    exact Subtype.ext (cnt_inj ε b (Finset.mem_filter.1 j.2).2 (Finset.mem_filter.1 k.2).2 h)
  have hset : {x : ℕ → ℝ | ∀ i ∈ s, ε i = b → x (cnt ε b i) ∈ t i} =
      (fun x (j : T) => x (f j)) ⁻¹' (Set.univ.pi (fun j : T => t j.1)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h j; exact h j.1 (Finset.mem_filter.1 j.2).1 (Finset.mem_filter.1 j.2).2
    · intro h i hi he; exact h ⟨i, Finset.mem_filter.2 ⟨hi, he⟩⟩
  have hm : Measurable (fun (x : ℕ → ℝ) (j : T) => x (f j)) := by fun_prop
  rw [hset, ← Measure.map_apply hm (MeasurableSet.univ_pi fun j => ht j.1),
    Measure.map_infinitePi_infinitePi_of_inj hf, Measure.infinitePi_eq_pi, Measure.pi_pi]
  exact Finset.prod_coe_sort T (fun i => F (t i))

/-- Law of the time-changed merge: iid mixture (KMT 1976 Part II, Lemma 1, p.37). -/
lemma law_zf (p : ℝ) (F1 F2 : Measure ℝ) [IsProbabilityMeasure F1] [IsProbabilityMeasure F2]
    [IsProbabilityMeasure (bern p)] [IsProbabilityMeasure (mixM p F1 F2)] :
    ((Measure.infinitePi (fun _ : ℕ => bern p)).prod
      ((Measure.infinitePi (fun _ : ℕ => F1)).prod (Measure.infinitePi (fun _ : ℕ => F2)))).map
        (fun ω => zf ω.1 ω.2.1 ω.2.2) =
      Measure.infinitePi (fun _ : ℕ => mixM p F1 F2) := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hS : MeasurableSet (Set.pi (s : Set ℕ) t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  rw [Measure.map_apply measurable_Zfun hS, Measure.prod_apply (measurable_Zfun hS)]
  have key : ∀ ε : ℕ → Bool,
      ((Measure.infinitePi (fun _ : ℕ => F1)).prod (Measure.infinitePi (fun _ : ℕ => F2)))
        (Prod.mk ε ⁻¹' ((fun ω : (ℕ → Bool) × ((ℕ → ℝ) × (ℕ → ℝ)) => zf ω.1 ω.2.1 ω.2.2) ⁻¹'
          Set.pi (s : Set ℕ) t)) =
        ∏ i ∈ s, (if ε i = true then F1 (t i) else F2 (t i)) := by
    intro ε
    have hsec : Prod.mk ε ⁻¹' ((fun ω : (ℕ → Bool) × ((ℕ → ℝ) × (ℕ → ℝ)) =>
        zf ω.1 ω.2.1 ω.2.2) ⁻¹' Set.pi (s : Set ℕ) t) =
        {x1 : ℕ → ℝ | ∀ i ∈ s, ε i = true → x1 (cnt ε true i) ∈ t i} ×ˢ
        {x2 : ℕ → ℝ | ∀ i ∈ s, ε i = false → x2 (cnt ε false i) ∈ t i} := by
      ext ⟨x1, x2⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_ofPred_eq, zf]
      constructor
      · intro h
        refine ⟨fun i hi he => ?_, fun i hi he => ?_⟩
        · have := h i hi; simpa [he] using this
        · have := h i hi; simpa [he] using this
      · rintro ⟨h1, h2⟩ i hi
        cases he : ε i
        · simpa [he] using h2 i hi he
        · simpa [he] using h1 i hi he
    rw [hsec, Measure.prod_prod, side ε true F1 s t ht, side ε false F2 s t ht, Finset.prod_ite]
    congr 2
    ext i; simp
  simp_rw [key]
  refine (lintegral_prod_eq_prod_lintegral_of_indepFun s
    (fun i (ε : ℕ → Bool) => if ε i = true then F1 (t i) else F2 (t i))
    (iIndepFun_infinitePi (X := fun i (c : Bool) => if c = true then F1 (t i) else F2 (t i))
      (fun i => Measurable.of_discrete))
    (fun i => (Measurable.of_discrete (f := fun c : Bool =>
      if c = true then F1 (t i) else F2 (t i))).comp (measurable_pi_apply i))).trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  have hmap : ∫⁻ ε : ℕ → Bool, (if ε i = true then F1 (t i) else F2 (t i))
      ∂(Measure.infinitePi (fun _ : ℕ => bern p)) =
      ∫⁻ c : Bool, (if c = true then F1 (t i) else F2 (t i)) ∂(bern p) := by
    have h := lintegral_map (μ := Measure.infinitePi (fun _ : ℕ => bern p))
      (f := fun c : Bool => if c = true then F1 (t i) else F2 (t i)) Measurable.of_discrete
      (measurable_pi_apply i)
    rw [Measure.infinitePi_map_eval] at h
    exact h.symm
  rw [hmap, bern, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, mixM]
  simp

lemma dev_mix (ε : ℕ → Bool) (x1 y1 x2 y2 : ℕ → ℝ) (n : ℕ) (c1 c2 : ℝ) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (h : (zf ε x1 x2, zf ε y1 y2) ∈ devSet n (c1 + c2)) :
    (x1, y1) ∈ devSet n c1 ∨ (x2, y2) ∈ devSet n c2 := by
  obtain ⟨k, hk1, hkn, hk⟩ := h
  simp only [sum_zf] at hk
  have hab := cnt_add ε k
  have key : c1 < |∑ j ∈ Finset.range (cnt ε true k), x1 j - ∑ j ∈ Finset.range (cnt ε true k), y1 j| ∨
      c2 < |∑ j ∈ Finset.range (cnt ε false k), x2 j -
        ∑ j ∈ Finset.range (cnt ε false k), y2 j| := by
    by_contra hc
    push Not at hc
    have := abs_add_le (∑ j ∈ Finset.range (cnt ε true k), x1 j -
      ∑ j ∈ Finset.range (cnt ε true k), y1 j) (∑ j ∈ Finset.range (cnt ε false k), x2 j -
        ∑ j ∈ Finset.range (cnt ε false k), y2 j)
    rw [show ∀ A1 A2 B1 B2 : ℝ, A1 + A2 - (B1 + B2) = (A1 - B1) + (A2 - B2) from
      fun _ _ _ _ => by ring] at hk
    linarith [hc.1, hc.2]
  rcases key with h1 | h1
  · left
    rcases Nat.eq_zero_or_pos (cnt ε true k) with h0 | h0
    · rw [h0] at h1; simp at h1; linarith
    · exact ⟨cnt ε true k, h0, by omega, h1⟩
  · right
    rcases Nat.eq_zero_or_pos (cnt ε false k) with h0 | h0
    · rw [h0] at h1; simp at h1; linarith
    · exact ⟨cnt ε false k, h0, by omega, h1⟩

/-- The merged coupling map. -/
def phiM (ω : (ℕ → Bool) × (((ℕ → ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)))) :
    (ℕ → ℝ) × (ℕ → ℝ) :=
  (zf ω.1 ω.2.1.1 ω.2.2.1, zf ω.1 ω.2.1.2 ω.2.2.2)

lemma measurable_phiM : Measurable phiM := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_Zfun.comp
      (measurable_fst.prodMk (measurable_snd.fst.fst.prodMk measurable_snd.snd.fst))
  · exact measurable_Zfun.comp
      (measurable_fst.prodMk (measurable_snd.fst.snd.prodMk measurable_snd.snd.snd))

lemma marg_side (p : ℝ) [IsProbabilityMeasure (bern p)] (Q1 Q2 : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure Q1] [IsProbabilityMeasure Q2] (side : Bool) :
    ((Measure.infinitePi (fun _ : ℕ => bern p)).prod (Q1.prod Q2)).map
      (fun ω => if side then ω.2.1 else ω.2.2) = if side then Q1 else Q2 := by
  cases side
  · simp only [Bool.false_eq_true, if_false]
    rw [show (fun ω : (ℕ → Bool) × (((ℕ → ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ))) => ω.2.2) =
      Prod.snd ∘ Prod.snd from rfl, ← Measure.map_map measurable_snd measurable_snd]
    simp [Measure.map_snd_prod]
  · simp only [if_true]
    rw [show (fun ω : (ℕ → Bool) × (((ℕ → ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ))) => ω.2.1) =
      Prod.fst ∘ Prod.snd from rfl, ← Measure.map_map measurable_fst measurable_snd]
    simp [Measure.map_snd_prod, Measure.map_fst_prod]

lemma marg_merge (p : ℝ) [IsProbabilityMeasure (bern p)] (Q1 Q2 : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure Q1] [IsProbabilityMeasure Q2] (F1 F2 : Measure ℝ)
    [IsProbabilityMeasure F1] [IsProbabilityMeasure F2] [IsProbabilityMeasure (mixM p F1 F2)]
    (π : (ℕ → ℝ) × (ℕ → ℝ) → (ℕ → ℝ)) (hπ : Measurable π)
    (h1 : Q1.map π = Measure.infinitePi (fun _ : ℕ => F1))
    (h2 : Q2.map π = Measure.infinitePi (fun _ : ℕ => F2)) :
    ((Measure.infinitePi (fun _ : ℕ => bern p)).prod (Q1.prod Q2)).map
      (fun ω => zf ω.1 (π ω.2.1) (π ω.2.2)) = Measure.infinitePi (fun _ : ℕ => mixM p F1 F2) := by
  have e1 : (Q1.prod Q2).map (Prod.map π π) =
      (Measure.infinitePi (fun _ : ℕ => F1)).prod (Measure.infinitePi (fun _ : ℕ => F2)) := by
    rw [← Measure.map_prod_map Q1 Q2 hπ hπ, h1, h2]
  have e2 : ((Measure.infinitePi (fun _ : ℕ => bern p)).prod (Q1.prod Q2)).map
      (Prod.map id (Prod.map π π)) = (Measure.infinitePi (fun _ : ℕ => bern p)).prod
        ((Measure.infinitePi (fun _ : ℕ => F1)).prod (Measure.infinitePi (fun _ : ℕ => F2))) := by
    rw [← e1, ← Measure.map_prod_map _ _ measurable_id (hπ.prodMap hπ), Measure.map_id]
  rw [show (fun ω : (ℕ → Bool) × (((ℕ → ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ))) =>
      zf ω.1 (π ω.2.1) (π ω.2.2)) =
      (fun ω : (ℕ → Bool) × ((ℕ → ℝ) × (ℕ → ℝ)) => zf ω.1 ω.2.1 ω.2.2) ∘
        Prod.map id (Prod.map π π) from rfl,
    ← Measure.map_map measurable_Zfun (measurable_id.prodMap (hπ.prodMap hπ)), e2]
  exact law_zf p F1 F2

/-- Child R1 (KMT 1976 Part II, Lemma 1, p.37). -/
theorem mixProp : MixProp := by
  intro F1 G1 F2 G2 _ _ _ _ p hp0 hp1 k1 k2
  obtain ⟨Q1, iQ1, hQ1f, hQ1s, C1, K1, l1, hC1, hK1, hl1, hb1⟩ := k1
  obtain ⟨Q2, iQ2, hQ2f, hQ2s, C2, K2, l2, hC2, hK2, hl2, hb2⟩ := k2
  have := isProb_bern p hp0 hp1
  have := isProb_mixM p hp0 hp1 F1 F2
  have := isProb_mixM p hp0 hp1 G1 G2
  refine ⟨((Measure.infinitePi (fun _ : ℕ => bern p)).prod (Q1.prod Q2)).map phiM,
    Measure.isProbabilityMeasure_map measurable_phiM.aemeasurable, ?_, ?_,
    C1 + C2, K1 + K2, min l1 l2 / 2, by positivity, by positivity, by positivity, ?_⟩
  · rw [Measure.map_map measurable_fst measurable_phiM]
    exact marg_merge p Q1 Q2 F1 F2 Prod.fst measurable_fst hQ1f hQ2f
  · rw [Measure.map_map measurable_snd measurable_phiM]
    exact marg_merge p Q1 Q2 G1 G2 Prod.snd measurable_snd hQ1s hQ2s
  intro n hn x hx
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  rw [Measure.map_apply measurable_phiM (measurableSet_devSet _ _)]
  have hsub : phiM ⁻¹' devSet n ((C1 + C2) * Real.log (n : ℝ) + x) ⊆
      (fun ω => if true then ω.2.1 else ω.2.2) ⁻¹' devSet n (C1 * Real.log (n : ℝ) + x / 2) ∪
      (fun ω => if false then ω.2.1 else ω.2.2) ⁻¹' devSet n (C2 * Real.log (n : ℝ) + x / 2) := by
    intro ω hω
    have e : (C1 + C2) * Real.log (n : ℝ) + x =
        (C1 * Real.log (n : ℝ) + x / 2) + (C2 * Real.log (n : ℝ) + x / 2) := by ring
    rw [Set.mem_preimage, e] at hω
    exact dev_mix ω.1 _ _ _ _ n _ _ (by positivity) (by positivity) hω
  have hm : ∀ (b : Bool) (S : Set ((ℕ → ℝ) × (ℕ → ℝ))), MeasurableSet S →
      ((Measure.infinitePi (fun _ : ℕ => bern p)).prod (Q1.prod Q2))
        ((fun ω => if b then ω.2.1 else ω.2.2) ⁻¹' S) = (if b then Q1 else Q2) S := by
    intro b S hS
    rw [← Measure.map_apply (by cases b <;> simp <;> fun_prop) hS, marg_side]
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
  rw [hm true _ (measurableSet_devSet _ _), hm false _ (measurableSet_devSet _ _), if_pos rfl,
    if_neg Bool.false_ne_true]
  refine lt_of_lt_of_le (ENNReal.add_lt_add (hb1 n hn (x / 2) (by positivity))
    (hb2 n hn (x / 2) (by positivity))) ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have e1 : Real.exp (-l1 * (x / 2)) ≤ Real.exp (-(min l1 l2 / 2) * x) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left l1 l2])
  have e2 : Real.exp (-l2 * (x / 2)) ≤ Real.exp (-(min l1 l2 / 2) * x) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right l1 l2])
  nlinarith [mul_le_mul_of_nonneg_left e1 hK1.le, mul_le_mul_of_nonneg_left e2 hK2.le]
end P99bcb804

open MeasureTheory ProbabilityTheory in
theorem solution (F1 G1 F2 G2 M1 M2 : Measure ℝ) [IsProbabilityMeasure F1]
    [IsProbabilityMeasure G1] [IsProbabilityMeasure F2] [IsProbabilityMeasure G2]
    [IsProbabilityMeasure M1] [IsProbabilityMeasure M2] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hM1 : M1 = ENNReal.ofReal p • F1 + ENNReal.ofReal (1 - p) • F2)
    (hM2 : M2 = ENNReal.ofReal p • G1 + ENNReal.ofReal (1 - p) • G2)
    (h1 : ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => F1) ∧
        Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ => G1) ∧
        ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
          ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
            Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
              ENNReal.ofReal (K * Real.exp (-lam * x)))
    (h2 : ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => F2) ∧
        Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ => G2) ∧
        ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
          ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
            Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
              ENNReal.ofReal (K * Real.exp (-lam * x))) :
    ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => M1) ∧
      Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ => M2) ∧
      ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ C * Real.log (n : ℝ) + x <
            |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by
  subst hM1 hM2
  exact P99bcb804.mixProp F1 G1 F2 G2 p hp0 hp1 h1 h2
