-- Prove2me | solution 1 for EthierKurtz.kmt_discrete_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T01:50:12.703861+00:00
-- url     : https://prove2.me/submissions/5edb81bd-73c0-4a2d-b431-7ef14c70bcf1

import Mathlib
import Definitions.Def_EthierKurtz_kmtDiscreteApproximation
import Theorems.Thm_EthierKurtz_kmt_mixture_coupling
import Theorems.Thm_EthierKurtz_kmt_bounded_mixture_split
import Theorems.Thm_EthierKurtz_kmt_dyadic_blocks_glue
import Theorems.Thm_EthierKurtz_kmt_bounded_dyadic_coupling
import Theorems.Thm_EthierKurtz_kmt_gaussian_component_dyadic_coupling

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

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

end P99bcb804

namespace P99bcb804

/-- Dyadic finite-horizon KMT bound (KMT I, (1.1) at n = 2^N), coupling with iid N(0,1). -/
def DyKMT (F : Measure ℝ) [IsProbabilityMeasure F] : Prop :=
  ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
    ∃ Q : Measure ((Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = Measure.pi (fun _ : Fin (2 ^ N) => F) ∧
      Q.map Prod.snd = Measure.pi (fun _ : Fin (2 ^ N) => gaussianReal 0 1) ∧
      ∀ x : ℝ, 0 < x →
        Q {q | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C * Real.log ((2 ^ N : ℕ) : ℝ) + x <
          |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
            (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} <
          ENNReal.ofReal (K * Real.exp (-lam * x))

def GlueS : Prop := ∀ (F : Measure ℝ) [IsProbabilityMeasure F], DyKMT F →
    ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => F) ∧
      Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1) ∧
      ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ C * Real.log (n : ℝ) + x <
            |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x))

def BddBlockS : Prop := ∀ (F : Measure ℝ) [IsProbabilityMeasure F] (K : ℝ), 0 < K →
    (∀ᵐ x ∂F, |x| ≤ K) → ∫ x, x ∂F = 0 → ∫ x, x ^ 2 ∂F = 1 → DyKMT F

def GaussBlockS : Prop := ∀ (F2 : Measure ℝ) [IsProbabilityMeasure F2] (p m : ℝ) (v : NNReal),
    0 < p → p ≤ 1 → v ≠ 0 → ∀ (G : Measure ℝ) [IsProbabilityMeasure G],
    G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2 →
    (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ → Integrable (fun x : ℝ => Real.exp (a * x)) G) →
    ∫ x, x ∂G = 0 → variance (fun x : ℝ => x) G = 1 → DyKMT G

def MixS : Prop := ∀ (F1 G1 F2 G2 M1 M2 : Measure ℝ) [IsProbabilityMeasure F1] [IsProbabilityMeasure G1]
    [IsProbabilityMeasure F2] [IsProbabilityMeasure G2] [IsProbabilityMeasure M1]
    [IsProbabilityMeasure M2] (p : ℝ), 0 ≤ p → p ≤ 1 →
    M1 = ENNReal.ofReal p • F1 + ENNReal.ofReal (1 - p) • F2 →
    M2 = ENNReal.ofReal p • G1 + ENNReal.ofReal (1 - p) • G2 →
    KPair F1 G1 → KPair F2 G2 → KPair M1 M2

def SplitS : Prop := SplitProp

end P99bcb804

namespace P99bcb804

lemma measurableSet_dev (n : ℕ) (c : ℝ) : MeasurableSet {z : (ℕ → ℝ) × (ℕ → ℝ) |
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ c < |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} := by
  have : {z : (ℕ → ℝ) × (ℕ → ℝ) | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      c < |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} =
      ⋃ k : ℕ, ⋃ (_ : 1 ≤ k ∧ k ≤ n), {z : (ℕ → ℝ) × (ℕ → ℝ) |
        c < |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} := by
    ext z; simp [and_assoc]
  rw [this]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
    measurableSet_lt measurable_const (by fun_prop)

theorem bdd_unf (hGl : GlueS) (hBd : BddBlockS) (F : Measure ℝ) [IsProbabilityMeasure F] (hb : ∃ K : ℝ, F (Set.Icc (-K) K) = 1)
    (hvar : 0 < variance (fun x : ℝ => x) F) :
    ∃ Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = Measure.infinitePi (fun _ : ℕ => F) ∧
      Q.map Prod.snd = Measure.infinitePi (fun _ : ℕ =>
        gaussianReal (∫ x, x ∂F) (variance (fun x : ℝ => x) F).toNNReal) ∧
      ∃ C K' lam : ℝ, 0 < C ∧ 0 < K' ∧ 0 < lam ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          Q {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ C * Real.log (n : ℝ) + x <
            |(∑ i ∈ Finset.range k, z.1 i) - (∑ i ∈ Finset.range k, z.2 i)|} <
            ENNReal.ofReal (K' * Real.exp (-lam * x)) := by
  obtain ⟨K, hK⟩ := hb
  set m := ∫ x, x ∂F with hm
  set V := variance (fun x : ℝ => x) F with hV
  set σ := √V with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hvar
  have hσ2 : σ ^ 2 = V := Real.sq_sqrt hvar.le
  have hae : ∀ᵐ x ∂F, x ∈ Set.Icc (-K) K := by
    have h0 : F (Set.Icc (-K) K)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Icc).2 hK
    exact measure_eq_zero_iff_ae_notMem.1 h0 |>.mono fun x hx => by simpa using hx
  have hbd : ∀ᵐ x ∂F, |x| ≤ |K| := hae.mono fun x hx =>
    abs_le.2 ⟨by linarith [hx.1, le_abs_self K], by linarith [hx.2, le_abs_self K]⟩
  have hint : Integrable (fun x : ℝ => x) F :=
    Integrable.of_bound (by fun_prop) |K| (hbd.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  have hA : Measurable fun x : ℝ => (x - m) / σ := by fun_prop
  set K' := (|K| + |m|) / σ + 1 with hK'
  have hK'0 : 0 < K' := by positivity
  have hsupp' : ∀ᵐ y ∂(F.map fun x : ℝ => (x - m) / σ), |y| ≤ K' := by
    refine (ae_map_iff hA.aemeasurable (measurableSet_le (by fun_prop) measurable_const)).2 ?_
    refine hbd.mono fun x hx => ?_
    have h1 : |x - m| ≤ |x| + |m| := abs_sub x m
    have h2 : (|K| + |m|) / σ * σ = |K| + |m| := div_mul_cancel₀ _ hσ0.ne'
    rw [abs_div, abs_of_pos hσ0, div_le_iff₀ hσ0, hK', add_mul, h2]
    nlinarith
  have hm' : ∫ y, y ∂(F.map fun x : ℝ => (x - m) / σ) = 0 := by
    rw [integral_map hA.aemeasurable (by fun_prop : Measurable fun y : ℝ => y).aestronglyMeasurable,
      integral_div,
      integral_sub hint (integrable_const m)]
    simp [← hm]
  have hVeq : V = ∫ x, (x - m) ^ 2 ∂F := variance_eq_integral measurable_id'.aemeasurable
  have hv' : ∫ y, y ^ 2 ∂(F.map fun x : ℝ => (x - m) / σ) = 1 := by
    rw [integral_map hA.aemeasurable
      (by fun_prop : Measurable fun y : ℝ => y ^ 2).aestronglyMeasurable]
    simp only [div_pow]
    rw [integral_div, ← hVeq, hσ2, div_self hvar.ne']
  have hP' : IsProbabilityMeasure (F.map fun x : ℝ => (x - m) / σ) :=
    Measure.isProbabilityMeasure_map hA.aemeasurable
  have hint2' : Integrable (fun y : ℝ => y ^ 2) (F.map fun x : ℝ => (x - m) / σ) := by
    refine Integrable.of_bound (by fun_prop) (K' ^ 2) (hsupp'.mono fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg y), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  obtain ⟨Q, hQp, hQ1, hQ2, C, K2, lam, hC, hK2, hlam, H⟩ :=
    hGl (F.map fun x : ℝ => (x - m) / σ) (hBd _ K' hK'0 hsupp' hm' hv')
  set B : (ℕ → ℝ) → (ℕ → ℝ) := fun z k => m + σ * z k with hBdef
  have hB : Measurable B := by rw [hBdef]; fun_prop
  have hBB : Measurable (Prod.map B B) := (hB.comp measurable_fst).prodMk (hB.comp measurable_snd)
  have hinv : (F.map fun x : ℝ => (x - m) / σ).map (fun y => m + σ * y) = F := by
    rw [Measure.map_map (by fun_prop) hA]
    have : ((fun y => m + σ * y) ∘ fun x : ℝ => (x - m) / σ) = id := by
      funext x; simp only [Function.comp, id]; field_simp; ring
    rw [this, Measure.map_id]
  have hgau : (gaussianReal 0 1).map (fun y => m + σ * y) = gaussianReal m V.toNNReal := by
    rw [show (fun y => m + σ * y) = (fun y => m + y) ∘ (fun y => σ * y) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    congr 1
    · simp
    · ext; simp [hσ2, Real.coe_toNNReal _ hvar.le]
  haveI := hQp
  refine ⟨Q.map (Prod.map B B), Measure.isProbabilityMeasure_map hBB.aemeasurable, ?_, ?_,
    σ * C, K2, lam / σ, by positivity, hK2, by positivity, ?_⟩
  · rw [Measure.map_map measurable_fst hBB]
    rw [show Prod.fst ∘ Prod.map B B = B ∘ Prod.fst from rfl, ← Measure.map_map hB measurable_fst,
      hQ1, Measure.infinitePi_map_pi _ (f := fun _ y => m + σ * y) (fun _ => by fun_prop)]
    simp only [hinv]
  · rw [Measure.map_map measurable_snd hBB]
    rw [show Prod.snd ∘ Prod.map B B = B ∘ Prod.snd from rfl, ← Measure.map_map hB measurable_snd,
      hQ2, Measure.infinitePi_map_pi _ (f := fun _ y => m + σ * y) (fun _ => by fun_prop)]
    simp only [hgau]
  intro n hn x hx
  rw [Measure.map_apply hBB (measurableSet_dev n _)]
  have H' := H n hn (x / σ) (by positivity)
  rw [show -lam * (x / σ) = -(lam / σ) * x by ring] at H'
  refine lt_of_le_of_lt (measure_mono fun z hz => ?_) H'
  obtain ⟨k, hk1, hkn, hk⟩ := hz
  refine ⟨k, hk1, hkn, ?_⟩
  have hk' : σ * C * Real.log n + x <
      |∑ i ∈ Finset.range k, (m + σ * z.1 i) - ∑ i ∈ Finset.range k, (m + σ * z.2 i)| := hk
  have hd : ∑ i ∈ Finset.range k, (m + σ * z.1 i) - ∑ i ∈ Finset.range k, (m + σ * z.2 i) =
      σ * ((∑ i ∈ Finset.range k, z.1 i) - ∑ i ∈ Finset.range k, z.2 i) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
  rw [hd, abs_mul, abs_of_pos hσ0] at hk'
  have e : σ * (C * Real.log n + x / σ) = σ * C * Real.log n + x := by field_simp
  exact lt_of_mul_lt_mul_left (by rw [e]; exact hk') hσ0.le




theorem mixProp_of (h : MixS) : MixProp :=
  fun F1 G1 F2 G2 _ _ _ _ p hp0 hp1 k1 k2 =>
    @h F1 G1 F2 G2 (mixM p F1 F2) (mixM p G1 G2) _ _ _ _ (isProb_mixM p hp0 hp1 F1 F2)
      (isProb_mixM p hp0 hp1 G1 G2) p hp0 hp1 rfl rfl k1 k2

theorem gaussComp_of (hGl : GlueS) (hGB : GaussBlockS) : GaussCompProp :=
  fun F2 _ p m v hp0 hp1 hv hexp hm hvar =>
    @hGl (mixM p (gaussianReal m v) F2) (isProb_mixM p hp0.le hp1 _ _)
      (@hGB F2 _ p m v hp0 hp1 hv (mixM p (gaussianReal m v) F2) (isProb_mixM p hp0.le hp1 _ _) rfl
        hexp hm hvar)

/-- The parent from its parts: R1 + R3 + R4 + split, glued by R2. -/
theorem leaf_of_parts (h1 : MixProp) (h3 : BddProp) (h4 : GaussCompProp) (hs : SplitProp)
    (μ : ProbabilityMeasure ℝ)
    (hexp : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ →
      Integrable (fun x : ℝ => Real.exp (a * x)) (μ : Measure ℝ))
    (hmean : ∫ x : ℝ, x ∂(μ : Measure ℝ) = 0)
    (hvariance : variance (fun x : ℝ => x) (μ : Measure ℝ) = 1) :
    EthierKurtz.kmtDiscreteApproximation μ := by
  obtain ⟨p, F1, F2, i1, i2, hp0, hp1, hK, hv, hμ, gexp, gmean, gvar⟩ := hs μ hexp hmean hvariance
  set v : NNReal := (variance (fun x : ℝ => x) F1).toNNReal with hvdef
  have hv0 : v ≠ 0 := by
    rw [hvdef]; exact (Real.toNNReal_pos.2 hv).ne'
  have k3 := h3 F1 hK hv
  have k1 := h1 F1 (gaussianReal (∫ x, x ∂F1) v) F2 F2 p hp0.le hp1.le k3 (kpair_refl F2)
  have k4 := h4 F2 p (∫ x, x ∂F1) v hp0 hp1.le hv0 gexp gmean gvar
  have k := @kpair_trans (mixM p F1 F2) (mixM p (gaussianReal (∫ x, x ∂F1) v) F2)
    (gaussianReal 0 1) (isProb_mixM p hp0.le hp1.le _ _) (isProb_mixM p hp0.le hp1.le _ _)
    inferInstance k1 k4
  apply kmt_of_kpair
  convert k



theorem leaf_red (h1 : MixS) (h2 : SplitS) (h3 : GlueS) (h4 : BddBlockS) (h5 : GaussBlockS)
    (μ : ProbabilityMeasure ℝ)
    (hexp : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ →
      Integrable (fun x : ℝ => Real.exp (a * x)) (μ : Measure ℝ))
    (hmean : ∫ x : ℝ, x ∂(μ : Measure ℝ) = 0)
    (hvariance : variance (fun x : ℝ => x) (μ : Measure ℝ) = 1) :
    EthierKurtz.kmtDiscreteApproximation μ :=
  leaf_of_parts (mixProp_of h1) (fun F _ hb hv => bdd_unf h3 h4 F hb hv) (gaussComp_of h3 h5) h2
    μ hexp hmean hvariance

end P99bcb804

open MeasureTheory ProbabilityTheory EthierKurtz in
theorem solution
    (μ : ProbabilityMeasure ℝ)
    (hexp : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ →
      Integrable (fun x : ℝ => Real.exp (a * x)) (μ : Measure ℝ))
    (hmean : ∫ x : ℝ, x ∂(μ : Measure ℝ) = 0)
    (hvariance : variance (fun x : ℝ => x) (μ : Measure ℝ) = 1) :
    kmtDiscreteApproximation μ := by
  exact P99bcb804.leaf_red (by exact EthierKurtz.kmt_mixture_coupling)
    (fun μ => by exact EthierKurtz.kmt_bounded_mixture_split (μ : Measure ℝ)) (by exact EthierKurtz.kmt_dyadic_blocks_glue)
    (by exact EthierKurtz.kmt_bounded_dyadic_coupling)
    (by exact EthierKurtz.kmt_gaussian_component_dyadic_coupling) μ hexp hmean hvariance
