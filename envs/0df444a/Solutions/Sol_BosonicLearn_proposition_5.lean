-- Prove2me | solution 1 for BosonicLearn.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T03:41:19.016201+00:00
-- url     : https://prove2.me/submissions/6a5e7464-3dd0-4318-a0be-39e57daab6b7

/-
Locally verified proof-sketch for BosonicLearn.proposition_5.
NOT POSTED. The only open theorem dependencies are the mission's existing
BosonicLearn.proposition_1 and BosonicLearn.proposition_2.
All new helper theorems in this file are proved; no new child is assumed.
Other imported platform theorems have status Proved, checked against the API.
Lean v4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Definitions.Def_WHMultiplicativity_schattenNorm
import Definitions.Def_BosonicLearn_Herm0
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_Gsupp
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Theorems.Thm_BosonicLearn_adaptive_scheme_product_povm
import Theorems.Thm_BosonicLearn_fugacityFamily_promiseClass
import Theorems.Thm_BosonicLearn_isDensity_prod
import Theorems.Thm_BosonicLearn_isDensity_reindex
import Theorems.Thm_BosonicLearn_isDensity_of_posSemidef
import Theorems.Thm_BosonicLearn_proposition_1
import Theorems.Thm_BosonicLearn_proposition_2
import Definitions.Def_BosonicLearn_FockPOVM
import Theorems.Thm_BosonicLearn_effect_entry_born
import Theorems.Thm_BosonicLearn_fockPOVM_of_effect
import Definitions.Def_BosonicLearn_sequentialLaw
import Theorems.Thm_BosonicLearn_gammaFock_basic
import Theorems.Thm_BosonicLearn_gammaFock_mul
import Theorems.Thm_BosonicLearn_gammaFock_posSemidef
import Theorems.Thm_BosonicLearn_born_truncation
import Theorems.Thm_BosonicLearn_fugacityCoeff_isDensity
import Theorems.Thm_BosonicLearn_effect_matrix_operator
import Theorems.Thm_BosonicLearn_effect_trace_pairing
import Definitions.Def_BosonicLearn_AdaptiveScheme
import Theorems.Thm_BosonicLearn_kronecker_integral_posSemidef
import Theorems.Thm_BosonicLearn_fockPOVM_postprocess
import Definitions.Def_BosonicLearn_PhiMap
import Definitions.Def_BosonicLearn_Ggood
import Definitions.Def_BosonicLearn_herm0Ball
import Theorems.Thm_BosonicLearn_priorMu_prob
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Definitions.Def_BosonicLearn_priorMu
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_HighDimProb_RandomProcesses_ProcessESup
import Theorems.Thm_HighDimProb_RandomProcesses_sudakov_fernique
import Theorems.Thm_GaussianMatrix_gaussian_concentration_vector
import Theorems.Thm_GaussianMatrix_sudakov_fernique

set_option autoImplicit false

/- Local helper source: Solutions.Prop5Bayes -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Cauchy--Schwarz on a probability space, in nonnegative extended reals. -/
theorem lintegral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ≥0∞}
    (hf : Measurable f) : (∫⁻ ω, f ω ∂μ) ^ 2 ≤ ∫⁻ ω, f ω ^ 2 ∂μ := by
  have hc : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc hf.aemeasurable
    (measurable_const.aemeasurable : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) μ)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ, mul_one, one_div] at h
  have h' := (ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2)).mp h
  simpa only [ENNReal.rpow_ofNat] using h'

/-- Two independent draws in one small ball must form a close pair. -/
theorem ball_mass_sq_le_collision {Θ : Type*} [MeasurableSpace Θ]
    (P : Measure Θ) [SFinite P] (R Q : Θ → Θ → Prop)
    (hQ : MeasurableSet {p : Θ × Θ | Q p.1 p.2})
    (htriangle : ∀ y u v, R y u → R y v → Q u v) (y : Θ) :
    P {u | R y u} ^ 2 ≤ ∫⁻ u, P {v | Q u v} ∂P := by
  calc
    P {u | R y u} ^ 2 = (P.prod P) ({u | R y u} ×ˢ {u | R y u}) := by
      rw [Measure.prod_prod, pow_two]
    _ ≤ (P.prod P) {p : Θ × Θ | Q p.1 p.2} :=
      measure_mono (fun p hp => htriangle y p.1 p.2 hp.1 hp.2)
    _ = ∫⁻ u, P {v | Q u v} ∂P := Measure.prod_apply hQ

/-- The probability of success of any randomized estimator, squared, is at most
    the posterior probability that two independent parameters form a close pair. -/
theorem randomized_success_sq_le_collision {T Θ : Type*}
    [MeasurableSpace T] [MeasurableSpace Θ]
    (ρ : Measure T) [IsProbabilityMeasure ρ]
    (P A : Kernel T Θ) [IsMarkovKernel P] [IsMarkovKernel A]
    (R Q : Θ → Θ → Prop)
    (hR : MeasurableSet {p : Θ × Θ | R p.1 p.2})
    (hQ : MeasurableSet {p : Θ × Θ | Q p.1 p.2})
    (htriangle : ∀ y u v, R y u → R y v → Q u v) :
    (∫⁻ x, ∫⁻ y, P x {u | R y u} ∂A x ∂ρ) ^ 2 ≤
      ∫⁻ x, ∫⁻ u, P x {v | Q u v} ∂P x ∂ρ := by
  let f : T × Θ → ℝ≥0∞ := fun p => P p.1 {u | R p.2 u}
  have hf : Measurable f := by
    exact Kernel.measurable_kernel_prodMk_left
      (κ := P.comap Prod.fst measurable_fst)
      (hR.preimage (measurable_fst.snd.prodMk measurable_snd))
  have hcomp : ∫⁻ p, f p ∂(ρ ⊗ₘ A) = ∫⁻ x, ∫⁻ y, P x {u | R y u} ∂A x ∂ρ :=
    Measure.lintegral_compProd hf
  rw [← hcomp]
  calc
    (∫⁻ p, f p ∂(ρ ⊗ₘ A)) ^ 2 ≤ ∫⁻ p, f p ^ 2 ∂(ρ ⊗ₘ A) :=
      lintegral_sq_le (ρ ⊗ₘ A) hf
    _ = ∫⁻ x, ∫⁻ y, P x {u | R y u} ^ 2 ∂A x ∂ρ :=
      Measure.lintegral_compProd (hf.pow_const 2)
    _ ≤ ∫⁻ x, ∫⁻ y, (∫⁻ u, P x {v | Q u v} ∂P x) ∂A x ∂ρ := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      exact ball_mass_sq_le_collision (P x) R Q hQ htriangle y
    _ = ∫⁻ x, ∫⁻ u, P x {v | Q u v} ∂P x ∂ρ := by simp


/-- Bayes' rule for the success event, including the estimator's randomization.
The assumption is equality of the two factorizations of the joint law. -/
theorem bayes_success_eq {T Θ : Type*}
    [MeasurableSpace T] [MeasurableSpace Θ]
    (μ : Measure Θ) [SFinite μ] (K : Kernel Θ T) [IsSFiniteKernel K]
    (ρ : Measure T) [SFinite ρ]
    (P A : Kernel T Θ) [IsSFiniteKernel P] [IsSFiniteKernel A]
    (hbayes : Measure.map Prod.swap (μ ⊗ₘ K) = ρ ⊗ₘ P)
    (R : Θ → Θ → Prop)
    (hR : MeasurableSet {p : Θ × Θ | R p.1 p.2}) :
    (∫⁻ u, ∫⁻ x, A x {y | R y u} ∂K u ∂μ) =
      ∫⁻ x, ∫⁻ y, P x {u | R y u} ∂A x ∂ρ := by
  let f : T × Θ → ℝ≥0∞ := fun p => A p.1 {y | R y p.2}
  have hf : Measurable f := by
    exact Kernel.measurable_kernel_prodMk_left
      (κ := A.comap Prod.fst measurable_fst)
      (hR.preimage (measurable_snd.prodMk measurable_fst.snd))
  calc
    (∫⁻ u, ∫⁻ x, A x {y | R y u} ∂K u ∂μ) =
        ∫⁻ p, f p.swap ∂(μ ⊗ₘ K) :=
      (Measure.lintegral_compProd (hf.comp measurable_swap)).symm
    _ = ∫⁻ p, f p ∂(Measure.map Prod.swap (μ ⊗ₘ K)) :=
      (lintegral_map hf measurable_swap).symm
    _ = ∫⁻ p, f p ∂(ρ ⊗ₘ P) := by rw [hbayes]
    _ = ∫⁻ x, ∫⁻ u, A x {y | R y u} ∂P x ∂ρ :=
      Measure.lintegral_compProd hf
    _ = ∫⁻ x, ∫⁻ y, P x {u | R y u} ∂A x ∂ρ := by
      apply lintegral_congr
      intro x
      have hs : MeasurableSet {p : Θ × Θ | R p.2 p.1} :=
        hR.preimage measurable_swap
      exact (Measure.prod_apply (μ := P x) (ν := A x) hs).symm.trans
        (Measure.prod_apply_symm hs)

/-- Generic Bayesian lower-bound reduction for arbitrary randomized estimators. -/
theorem bayes_success_sq_le_collision {T Θ : Type*}
    [MeasurableSpace T] [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (K : Kernel Θ T) [IsMarkovKernel K]
    (ρ : Measure T) [IsProbabilityMeasure ρ]
    (P A : Kernel T Θ) [IsMarkovKernel P] [IsMarkovKernel A]
    (hbayes : Measure.map Prod.swap (μ ⊗ₘ K) = ρ ⊗ₘ P)
    (R Q : Θ → Θ → Prop)
    (hR : MeasurableSet {p : Θ × Θ | R p.1 p.2})
    (hQ : MeasurableSet {p : Θ × Θ | Q p.1 p.2})
    (htriangle : ∀ y u v, R y u → R y v → Q u v) :
    (∫⁻ u, ∫⁻ x, A x {y | R y u} ∂K u ∂μ) ^ 2 ≤
      ∫⁻ x, ∫⁻ u, P x {v | Q u v} ∂P x ∂ρ := by
  rw [bayes_success_eq μ K ρ P A hbayes R hR]
  exact randomized_success_sq_le_collision ρ P A R Q hR hQ htriangle

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5Tail -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- A random variable bounded by one is controlled by any of its upper tails. -/
theorem lintegral_le_threshold_add_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ≥0∞)
    (hf : Measurable f) (hbound : ∀ x, f x ≤ 1) (ε : ℝ≥0∞) :
    (∫⁻ x, f x ∂μ) ≤ ε + μ {x | ε < f x} := by
  have hs : MeasurableSet {x | ε < f x} := measurableSet_lt measurable_const hf
  calc
    (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, ε + {x | ε < f x}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : ε < f x
      · simpa [hx] using (hbound x).trans (le_add_left le_rfl)
      · simpa [hx] using le_of_not_gt hx
    _ = ε + μ {x | ε < f x} := by
      rw [lintegral_add_left measurable_const, lintegral_const,
        lintegral_indicator hs, lintegral_const, Measure.restrict_apply_univ]
      simp

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5IntegratedTail -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- A high-probability estimate on a good set of parameters controls the full
prior/transcript expectation, paying the prior mass of the excluded set. -/
theorem integrated_tail_to_mean {Θ T : Type*}
    [MeasurableSpace Θ] [MeasurableSpace T]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (K : Kernel Θ T) [IsMarkovKernel K]
    (G : Set Θ) (hG : MeasurableSet G)
    (f : Θ × T → ℝ≥0∞) (hf : Measurable f)
    (hbound : ∀ p, f p ≤ 1) (e δ : ℝ≥0∞)
    (htail : (∫⁻ θ in G, K θ {x | e < f (θ, x)} ∂μ) ≤ δ) :
    (∫⁻ θ, ∫⁻ x, f (θ, x) ∂K θ ∂μ) ≤ e + μ Gᶜ + δ := by
  let B : Set (Θ × T) := {p | e < f p}
  let H : Set (Θ × T) := {p | p.1 ∈ G ∧ e < f p}
  have hB : MeasurableSet B := measurableSet_lt measurable_const hf
  have hH : MeasurableSet H := (hG.preimage measurable_fst).inter hB
  have hHmass : (μ ⊗ₘ K) H = ∫⁻ θ in G, K θ {x | e < f (θ, x)} ∂μ := by
    rw [Measure.compProd_apply hH, ← lintegral_indicator hG]
    apply lintegral_congr
    intro θ
    by_cases hθ : θ ∈ G
    · simp [H, hθ]
    · simp [H, hθ]
  have hbad : (μ ⊗ₘ K) B ≤ μ Gᶜ + δ := by
    calc
      (μ ⊗ₘ K) B ≤ (μ ⊗ₘ K) ((Gᶜ ×ˢ Set.univ) ∪ H) := by
        apply measure_mono
        intro p hp
        by_cases h : p.1 ∈ G
        · exact Or.inr ⟨h, hp⟩
        · exact Or.inl ⟨h, Set.mem_univ _⟩
      _ ≤ (μ ⊗ₘ K) (Gᶜ ×ˢ Set.univ) + (μ ⊗ₘ K) H := measure_union_le _ _
      _ ≤ μ Gᶜ + δ := by
        rw [Measure.compProd_apply_prod hG.compl MeasurableSet.univ, hHmass]
        simpa using add_le_add_left htail (μ Gᶜ)
  rw [← Measure.lintegral_compProd hf]
  exact (lintegral_le_threshold_add_tail (μ ⊗ₘ K) f hf hbound e).trans
    ((add_le_add le_rfl hbad).trans_eq (add_assoc e (μ Gᶜ) δ).symm)

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5BayesTail -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- A measurable nonnegative quantity has the same expectation in the
prior/transcript and marginal/posterior factorizations of a joint law. -/
theorem bayes_lintegral_eq {T Θ : Type*}
    [MeasurableSpace T] [MeasurableSpace Θ]
    (μ : Measure Θ) [SFinite μ] (K : Kernel Θ T) [IsSFiniteKernel K]
    (ρ : Measure T) [SFinite ρ] (P : Kernel T Θ) [IsSFiniteKernel P]
    (hbayes : Measure.map Prod.swap (μ ⊗ₘ K) = ρ ⊗ₘ P)
    (f : Θ × T → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u, ∫⁻ x, f (u, x) ∂K u ∂μ) =
      ∫⁻ x, ∫⁻ u, f (u, x) ∂P x ∂ρ := by
  calc
    (∫⁻ u, ∫⁻ x, f (u, x) ∂K u ∂μ) = ∫⁻ p, f p ∂(μ ⊗ₘ K) :=
      (Measure.lintegral_compProd hf).symm
    _ = ∫⁻ p, f p.swap ∂(Measure.map Prod.swap (μ ⊗ₘ K)) := by
      simpa only [Function.comp_apply, Prod.swap_swap] using
        (lintegral_map (μ := μ ⊗ₘ K) (hf.comp measurable_swap) measurable_swap).symm
    _ = ∫⁻ p, f p.swap ∂(ρ ⊗ₘ P) := by rw [hbayes]
    _ = ∫⁻ x, ∫⁻ u, f (u, x) ∂P x ∂ρ :=
      Measure.lintegral_compProd (hf.comp measurable_swap)

/-- Posterior anti-concentration on a good prior set bounds the squared
success probability of every randomized estimator. -/
theorem bayes_success_sq_le_of_tail {T Θ : Type*}
    [MeasurableSpace T] [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (K : Kernel Θ T) [IsMarkovKernel K]
    (ρ : Measure T) [IsProbabilityMeasure ρ]
    (P A : Kernel T Θ) [IsMarkovKernel P] [IsMarkovKernel A]
    (hbayes : Measure.map Prod.swap (μ ⊗ₘ K) = ρ ⊗ₘ P)
    (R Q : Θ → Θ → Prop)
    (hR : MeasurableSet {p : Θ × Θ | R p.1 p.2})
    (hQ : MeasurableSet {p : Θ × Θ | Q p.1 p.2})
    (htriangle : ∀ y u v, R y u → R y v → Q u v)
    (G : Set Θ) (hG : MeasurableSet G) (e δ : ℝ≥0∞)
    (htail : (∫⁻ u in G, K u {x | e < P x {v | Q u v}} ∂μ) ≤ δ) :
    (∫⁻ u, ∫⁻ x, A x {y | R y u} ∂K u ∂μ) ^ 2 ≤ e + μ Gᶜ + δ := by
  let f : Θ × T → ℝ≥0∞ := fun p => P p.2 {v | Q p.1 v}
  have hf : Measurable f := by
    exact Kernel.measurable_kernel_prodMk_left
      (κ := P.comap Prod.snd measurable_snd)
      (hQ.preimage (measurable_fst.fst.prodMk measurable_snd))
  have hbound : ∀ p, f p ≤ 1 := fun p => (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
  calc
    (∫⁻ u, ∫⁻ x, A x {y | R y u} ∂K u ∂μ) ^ 2 ≤
        ∫⁻ x, ∫⁻ u, P x {v | Q u v} ∂P x ∂ρ :=
      bayes_success_sq_le_collision μ K ρ P A hbayes R Q hR hQ htriangle
    _ = ∫⁻ u, ∫⁻ x, f (u, x) ∂K u ∂μ :=
      (bayes_lintegral_eq μ K ρ P hbayes f hf).symm
    _ ≤ e + μ Gᶜ + δ := integrated_tail_to_mean μ K G hG f hf hbound e δ htail

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5Geometry -/
section
open scoped ENNReal Matrix ComplexOrder
open BosonicLearn
set_option maxHeartbeats 600000

noncomputable section
namespace Prop5Geometry

/-- The trace norm of a Hermitian matrix is attained on a unitary: `‖H‖₁ = Tr(H W)`. -/
private lemma schatten_one_herm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ∃ W : Matrix (Fin n) (Fin n) ℂ, Wᴴ * W = 1 ∧
      WHMultiplicativity.schattenNorm 1 H = (H * W).trace.re := by
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ,
      V = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hV1 : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_star_mul_self _
  have hV2 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_mul_star_self _
  set x : Fin n → ℝ := hH.eigenvalues with hx
  have hspec : H = V * Matrix.diagonal (fun i => ((x i : ℝ) : ℂ)) * Vᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact h
  have hcfc : cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H) =
      V * Matrix.diagonal (fun i => ((|x i| : ℝ) : ℂ)) * Vᴴ := by
    rw [hH.eq]
    have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
    have h1 : H * H = cfc (fun t : ℝ => t ^ 2) H := by
      rw [cfc_pow_id H 2, pow_two]
    have hc : Continuous (fun t : ℝ => t ^ ((1 : ℝ) / 2)) :=
      Real.continuous_rpow_const (by norm_num)
    rw [h1, ← cfc_comp' (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (fun t : ℝ => t ^ 2) H hc.continuousOn,
      hH.cfc_eq]
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, ← hVdef, Matrix.star_eq_conjTranspose]
    have hd : (RCLike.ofReal ∘ (fun t : ℝ => (t ^ 2) ^ ((1 : ℝ) / 2)) ∘ hH.eigenvalues :
        Fin n → ℂ) = fun i => ((|x i| : ℝ) : ℂ) := by
      funext i
      simp only [Function.comp_apply]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
      rfl
    rw [hd]
  have hnorm : WHMultiplicativity.schattenNorm 1 H =
      (cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H)).trace.re := by
    unfold WHMultiplicativity.schattenNorm
    rw [if_neg ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, div_one]
    rw [Real.rpow_one]
  set s : Fin n → ℝ := fun i => if 0 ≤ x i then 1 else -1 with hs
  have hss : ∀ i, s i * s i = 1 := by
    intro i
    simp only [hs]
    split_ifs <;> norm_num
  have hxs : ∀ i, x i * s i = |x i| := by
    intro i
    simp only [hs]
    split_ifs with h
    · rw [abs_of_nonneg h, mul_one]
    · rw [abs_of_neg (not_le.mp h)]; ring
  set W : Matrix (Fin n) (Fin n) ℂ := V * Matrix.diagonal (fun i => ((s i : ℝ) : ℂ)) * Vᴴ with hW
  have hWh : Wᴴ = W := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    funext i
    simp
  have hmul : ∀ d₁ d₂ : Fin n → ℂ, (V * Matrix.diagonal d₁ * Vᴴ) * (V * Matrix.diagonal d₂ * Vᴴ) =
      V * Matrix.diagonal (fun i => d₁ i * d₂ i) * Vᴴ := by
    intro d₁ d₂
    have h : (V * Matrix.diagonal d₁ * Vᴴ) * (V * Matrix.diagonal d₂ * Vᴴ) =
        V * (Matrix.diagonal d₁ * (Vᴴ * V) * Matrix.diagonal d₂) * Vᴴ := by
      simp only [Matrix.mul_assoc]
    rw [h, hV1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  refine ⟨W, ?_, ?_⟩
  · rw [hWh, hW, hmul]
    have h1 : (fun i => ((s i : ℝ) : ℂ) * ((s i : ℝ) : ℂ)) = fun _ : Fin n => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, hss i, Complex.ofReal_one]
    rw [h1, Matrix.diagonal_one, Matrix.mul_one, hV2]
  · rw [hnorm, hcfc]
    have h2 : (fun i => ((x i : ℝ) : ℂ) * ((s i : ℝ) : ℂ)) = fun i => ((|x i| : ℝ) : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, hxs i]
    conv_rhs => rw [hspec, hW, hmul, h2]

/-- Hölder-type bound: `|Tr(diag(e) P Q)| ≤ ∑ |eᵢ|` when `P Pᴴ ⪯ 1` and `Qᴴ Q ⪯ 1`. -/
private lemma holder {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ)
    (hP : (1 - P * Pᴴ).PosSemidef) (hQ : (1 - Qᴴ * Q).PosSemidef) :
    |(Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * (P * Q)).trace.re| ≤ ∑ i, |e i| := by
  have hProw : ∀ i, ∑ j, ‖P i j‖ ^ 2 ≤ 1 := by
    intro i
    have h := hP.diag_nonneg (i := i)
    have h2 : (1 - P * Pᴴ) i i = ((1 - ∑ j, ‖P i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj']
    rw [h2] at h
    have := Complex.zero_le_real.mp h
    linarith
  have hQcol : ∀ i, ∑ j, ‖Q j i‖ ^ 2 ≤ 1 := by
    intro i
    have h := hQ.diag_nonneg (i := i)
    have h2 : (1 - Qᴴ * Q) i i = ((1 - ∑ j, ‖Q j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
    rw [h2] at h
    have := Complex.zero_le_real.mp h
    linarith
  have htr : (Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * (P * Q)).trace.re =
      ∑ i, e i * ∑ j, (P i j * Q j i).re := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.diagonal_mul]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply, Complex.re_ofReal_mul, Complex.re_sum]
  rw [htr]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hone : |∑ j, (P i j * Q j i).re| ≤ 1 := by
    calc |∑ j, (P i j * Q j i).re| ≤ ∑ j, |(P i j * Q j i).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (‖P i j‖ ^ 2 + ‖Q j i‖ ^ 2) / 2 := Finset.sum_le_sum fun j _ => by
          have h1 : |(P i j * Q j i).re| ≤ ‖P i j‖ * ‖Q j i‖ := by
            rw [← norm_mul]
            exact Complex.abs_re_le_norm _
          nlinarith [sq_nonneg (‖P i j‖ - ‖Q j i‖)]
      _ = (∑ j, ‖P i j‖ ^ 2 + ∑ j, ‖Q j i‖ ^ 2) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ 1 := by linarith [hProw i, hQcol i]
  calc |e i| * |∑ j, (P i j * Q j i).re| ≤ |e i| * 1 :=
        mul_le_mul_of_nonneg_left hone (abs_nonneg _)
    _ = |e i| := mul_one _


theorem schatten_one_herm_eq_sum {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    WHMultiplicativity.schattenNorm 1 H = ∑ i, |hH.eigenvalues i| := by
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ,
      V = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hV1 : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_star_mul_self _
  have hV2 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_mul_star_self _
  set x : Fin n → ℝ := hH.eigenvalues with hx
  have hspec : H = V * Matrix.diagonal (fun i => ((x i : ℝ) : ℂ)) * Vᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact h
  have hcfc : cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H) =
      V * Matrix.diagonal (fun i => ((|x i| : ℝ) : ℂ)) * Vᴴ := by
    rw [hH.eq]
    have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
    have h1 : H * H = cfc (fun t : ℝ => t ^ 2) H := by
      rw [cfc_pow_id H 2, pow_two]
    have hc : Continuous (fun t : ℝ => t ^ ((1 : ℝ) / 2)) :=
      Real.continuous_rpow_const (by norm_num)
    rw [h1, ← cfc_comp' (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (fun t : ℝ => t ^ 2) H hc.continuousOn,
      hH.cfc_eq]
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, ← hVdef, Matrix.star_eq_conjTranspose]
    have hd : (RCLike.ofReal ∘ (fun t : ℝ => (t ^ 2) ^ ((1 : ℝ) / 2)) ∘ hH.eigenvalues :
        Fin n → ℂ) = fun i => ((|x i| : ℝ) : ℂ) := by
      funext i
      simp only [Function.comp_apply]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
      rfl
    rw [hd]
  have hnorm : WHMultiplicativity.schattenNorm 1 H =
      (cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H)).trace.re := by
    unfold WHMultiplicativity.schattenNorm
    rw [if_neg ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, div_one]
    rw [Real.rpow_one]
  rw [hnorm, hcfc, Matrix.trace_mul_cycle, hV1, Matrix.one_mul,
    Matrix.trace_diagonal, Complex.re_sum]
  simp [hx]

private lemma trace_mul_unitary_le {n : ℕ}
    (H W : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hW : Wᴴ * W = 1) :
    (H * W).trace.re ≤ WHMultiplicativity.schattenNorm 1 H := by
  let V : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  have hV1 : Vᴴ * V = 1 := by
    exact Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hV2 : V * Vᴴ = 1 := by
    exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hW2 : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have hspec : H = V * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Vᴴ := by
    simpa [V, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using hH.spectral_theorem
  have hp : (1 - (Vᴴ * W) * (Vᴴ * W)ᴴ).PosSemidef := by
    have heq : (Vᴴ * W) * (Vᴴ * W)ᴴ = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc (Vᴴ * W) * (Wᴴ * V) = Vᴴ * (W * Wᴴ) * V := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hW2, Matrix.mul_one, hV1]
    rw [heq, sub_self]; exact Matrix.PosSemidef.zero
  have hq : (1 - Vᴴ * V).PosSemidef := by
    rw [hV1, sub_self]; exact Matrix.PosSemidef.zero
  have hb := holder (Vᴴ * W) V hH.eigenvalues hp hq
  rw [schatten_one_herm_eq_sum H hH]
  calc (H * W).trace.re =
      (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * ((Vᴴ * W) * V)).trace.re := by
        conv_lhs => rw [hspec]
        congr 1
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm V]
        simp only [Matrix.mul_assoc]
    _ ≤ |(Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * ((Vᴴ * W) * V)).trace.re| := le_abs_self _
    _ ≤ ∑ i, |hH.eigenvalues i| := hb

/-- Triangle inequality for the trace norm of Hermitian matrices. -/
theorem schatten_one_add_le {n : ℕ}
    (H K : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    WHMultiplicativity.schattenNorm 1 (H + K) ≤
      WHMultiplicativity.schattenNorm 1 H + WHMultiplicativity.schattenNorm 1 K := by
  obtain ⟨W, hW, hnorm⟩ := schatten_one_herm (H + K) (hH.add hK)
  rw [hnorm, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  exact add_le_add (trace_mul_unitary_le H W hH hW) (trace_mul_unitary_le K W hK hW)

/-- The trace norm is unchanged by negating a matrix. -/
theorem schatten_one_neg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 1 (-H) = WHMultiplicativity.schattenNorm 1 H := by
  simp [WHMultiplicativity.schattenNorm]

open scoped Matrix.Norms.L2Operator in
/-- The finite-dimensional trace norm is continuous. -/
theorem continuous_schatten_one (n : ℕ) :
    Continuous fun H : Matrix (Fin n) (Fin n) ℂ => WHMultiplicativity.schattenNorm 1 H := by
  have hmul : Continuous fun H : Matrix (Fin n) (Fin n) ℂ => Hᴴ * H :=
    continuous_id.matrix_conjTranspose.mul continuous_id
  have hcfc : Continuous fun H : Matrix (Fin n) (Fin n) ℂ =>
      cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H) := by
    exact hmul.cfc_of_mem_nhdsSet (s := Set.univ) (fun t : ℝ => t ^ ((1 : ℝ) / 2))
      (by simp)
      (ha' := fun H => (Matrix.posSemidef_conjTranspose_mul_self H).isHermitian.isSelfAdjoint)
      (hf := (Real.continuous_rpow_const (by norm_num)).continuousOn)
  convert Complex.continuous_re.comp hcfc.matrix_trace using 1
  ext H
  simp [WHMultiplicativity.schattenNorm]

/-- Symmetry of the trace-norm distance on traceless Hermitian matrices. -/
theorem trace_distance_symm {n : ℕ} (X Y : Herm0 n) :
    WHMultiplicativity.schattenNorm 1 ((X - Y : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) =
      WHMultiplicativity.schattenNorm 1 ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) := by
  change WHMultiplicativity.schattenNorm 1 ((X : Matrix (Fin n) (Fin n) ℂ) -
    (Y : Matrix (Fin n) (Fin n) ℂ)) =
      WHMultiplicativity.schattenNorm 1 ((Y : Matrix (Fin n) (Fin n) ℂ) -
        (X : Matrix (Fin n) (Fin n) ℂ))
  rw [← neg_sub (Y : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ),
    schatten_one_neg]

/-- Triangle inequality in exactly the parameter space used by Proposition 5. -/
theorem trace_distance_triangle {n : ℕ} (X Y Z : Herm0 n) :
    WHMultiplicativity.schattenNorm 1 ((X - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤
      WHMultiplicativity.schattenNorm 1 ((X - Y : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) +
      WHMultiplicativity.schattenNorm 1 ((Y - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) := by
  have h := schatten_one_add_le
    ((X - Y : Herm0 n) : Matrix (Fin n) (Fin n) ℂ)
    ((Y - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ)
    (X - Y).property.1 (Y - Z).property.1
  simpa only [Submodule.coe_sub, sub_add_sub_cancel] using h

/-- Two points in a trace ball of radius `r` have mutual distance at most `2r`. -/
theorem trace_ball_pair {n : ℕ} (X Y Z : Herm0 n) (r : ℝ)
    (hX : WHMultiplicativity.schattenNorm 1
      ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r)
    (hZ : WHMultiplicativity.schattenNorm 1
      ((Y - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r) :
    WHMultiplicativity.schattenNorm 1
      ((Z - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ 2 * r := by
  have ht := trace_distance_triangle Z Y X
  rw [trace_distance_symm Z Y] at ht
  linarith

/-- Joint measurability of trace-norm distance. -/
theorem measurable_trace_distance (n : ℕ) :
    Measurable fun XY : Herm0 n × Herm0 n => WHMultiplicativity.schattenNorm 1
      ((XY.1 - XY.2 : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) := by
  have : SecondCountableTopology (Herm0 n) :=
    @TopologicalSpace.Subtype.secondCountableTopology (Fin n → Fin n → ℂ) _
      (fun X => X ∈ Herm0 n) inferInstance
  apply Continuous.measurable
  exact (continuous_schatten_one n).comp
    ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd))

/-- The trace-distance relation at a fixed radius is a Borel set. -/
theorem measurableSet_trace_relation (n : ℕ) (r : ℝ) :
    MeasurableSet {XY : Herm0 n × Herm0 n | WHMultiplicativity.schattenNorm 1
      ((XY.1 - XY.2 : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r} :=
  measurableSet_le (measurable_trace_distance n) measurable_const

/-- Trace balls are measurable, including for an arbitrary real radius. -/
theorem measurableSet_trace_ball {n : ℕ} (X : Herm0 n) (r : ℝ) :
    MeasurableSet {Y : Herm0 n | WHMultiplicativity.schattenNorm 1
      ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r} := by
  have hc : Continuous fun Y : Herm0 n => WHMultiplicativity.schattenNorm 1
      ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) :=
    (continuous_schatten_one n).comp (continuous_subtype_val.sub continuous_const)
  exact (isClosed_le hc continuous_const).measurableSet

end Prop5Geometry

end
end

/- Local helper source: Solutions.Prop5Constants -/
section
namespace BosonicLearn.Prop5

/-- A quantitative exponential tail can be made uniformly small in the dimension. -/
theorem eventually_exp_neg_mul_nat_le (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Real.exp (-(c * n)) ≤ ε := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (-Real.log ε / c)
  refine ⟨n₀, fun n hn => ?_⟩
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hprod : -Real.log ε < c * n₀ := by
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hn₀
  apply (Real.le_log_iff_exp_le hε).mp
  nlinarith

/-- Choosing a fixed sufficiently small sample constant turns all posterior
    error terms into a total collision bound of one percent. -/
theorem posterior_error_constants (c C cg : ℝ) (hc : 0 < c) (hC : 0 < C) (hcg : 0 < cg) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ N : ℕ, ∀ ν ξ : ℝ,
        (N : ℝ) * ν ^ 2 * ξ ^ 2 ≤ κ * n →
        Real.exp (-(cg * n)) + (1 / 400 : ℝ) + Real.exp (-(n : ℝ) ^ 2) +
          Real.exp (-(c * (n : ℝ) ^ 2) + C * N * n * ν ^ 2 * ξ ^ 2 / (1 / 400))
            ≤ 1 / 100 := by
  obtain ⟨ng, hng⟩ := eventually_exp_neg_mul_nat_le cg (1 / 400) hcg (by norm_num)
  obtain ⟨ne, hne⟩ := eventually_exp_neg_mul_nat_le 1 (1 / 400) (by norm_num) (by norm_num)
  obtain ⟨np, hnp⟩ := eventually_exp_neg_mul_nat_le (c / 2) (1 / 400) (by positivity) (by norm_num)
  let κ := c / (800 * C)
  refine ⟨κ, by dsimp [κ]; positivity, max 1 (max ng (max ne np)), le_max_left _ _, ?_⟩
  intro n hn N ν ξ hN
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hng' := hng n ((le_max_left ng _).trans ((le_max_right _ _).trans hn))
  have hne' := hne n ((le_max_left ne _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hnp' := hnp n ((le_max_right ne np).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have he : Real.exp (-(n : ℝ) ^ 2) ≤ (1 / 400 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr (neg_le_neg hsq))
    simpa only [one_mul] using hne'
  have hCN : C * ((N : ℝ) * ν ^ 2 * ξ ^ 2) ≤ c / 800 * n := by
    have h := mul_le_mul_of_nonneg_left hN (le_of_lt hC)
    dsimp [κ] at h
    calc
      C * ((N : ℝ) * ν ^ 2 * ξ ^ 2) ≤ C * (c / (800 * C) * n) := h
      _ = c / 800 * n := by field_simp
  have hCNn := mul_le_mul_of_nonneg_right hCN (show 0 ≤ (n : ℝ) by positivity)
  have hexp : -(c * (n : ℝ) ^ 2) + C * N * n * ν ^ 2 * ξ ^ 2 / (1 / 400) ≤ -(c / 2 * n) := by
    have hcnsq := mul_le_mul_of_nonneg_left hsq (show 0 ≤ c / 2 by positivity)
    nlinarith
  have hp := (Real.exp_le_exp.mpr hexp).trans hnp'
  linarith

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5TranscriptKernel -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 600000

private lemma tensorPow_apply {a : Type} (N : ℕ) (M : Matrix a a ℂ) (x y : Fin N → a) :
    WildeQIT.Schumacher.tensorPow N M x y = ∏ i, M (x i) (y i) := rfl

private lemma isDensity_tensorPow_zero {a : Type} (M : Matrix a a ℂ) :
    IsDensity (WildeQIT.Schumacher.tensorPow 0 M) := by
  have hX : ∀ x y : Fin 0 → a, WildeQIT.Schumacher.tensorPow 0 M x y = 1 := by
    intro x y
    rw [tensorPow_apply]
    simp
  refine isDensity_of_posSemidef _ ?_ ?_ ?_
  · intro s z
    have h : ∑ i ∈ s, ∑ j ∈ s, star (z i) * WildeQIT.Schumacher.tensorPow 0 M i j * z j =
        star (∑ i ∈ s, z i) * ∑ i ∈ s, z i := by
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hX, mul_one]
    rw [h]
    have h2 : star (∑ i ∈ s, z i) * ∑ i ∈ s, z i = ((Complex.normSq (∑ i ∈ s, z i) : ℝ) : ℂ) := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
    rw [h2]
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact Complex.normSq_nonneg _⟩
  · exact (hasSum_fintype _).summable
  · rw [tsum_fintype]
    simp [hX]

private lemma isDensity_tensorPow {a : Type} (M : Matrix a a ℂ) (hM : IsDensity M) (N : ℕ) :
    IsDensity (WildeQIT.Schumacher.tensorPow N M) := by
  induction N with
  | zero => exact isDensity_tensorPow_zero M
  | succ N ih =>
    have h := isDensity_reindex (Fin.consEquiv fun _ : Fin (N + 1) => a) (isDensity_prod hM ih)
    have heq : (fun i j : Fin (N + 1) → a =>
        (fun p q : a × (Fin N → a) => M p.1 q.1 * WildeQIT.Schumacher.tensorPow N M p.2 q.2)
          ((Fin.consEquiv fun _ : Fin (N + 1) => a).symm i)
          ((Fin.consEquiv fun _ : Fin (N + 1) => a).symm j)) =
        WildeQIT.Schumacher.tensorPow (N + 1) M := by
      funext x y
      simp [tensorPow_apply, Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]
    rw [heq] at h
    exact h


/-- A fixed POVM turns any entrywise measurable family of density matrices into a kernel. -/
theorem povm_law_measurable {I Ω T : Type} [DecidableEq I] [Countable I]
    [MeasurableSpace Ω] [MeasurableSpace T] (P : FockPOVM I T)
    (ρ : Ω → Matrix I I ℂ) (hρ : ∀ i j, Measurable fun X => ρ X i j)
    (hd : ∀ X, IsDensity (ρ X)) : Measurable fun X => P.law (ρ X) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  have ht : Measurable fun X => ∑' i, ∑' j, P.effect B i j * ρ X j i :=
    Measurable.tsum fun i => Measurable.tsum fun j => measurable_const.mul (hρ j i)
  have hf := (Complex.measurable_re.comp ht).ennreal_ofReal
  simpa only [P.law_born _ (hd _) B hB, Function.comp_def] using hf

/-- Each Fock coefficient is continuous in the fugacity matrix. -/
theorem continuous_fugacityCoeff_entry (n : ℕ) (u v : Occupation (Fin n)) :
    Continuous fun R : Matrix (Fin n) (Fin n) ℂ => fugacityCoeff R u v := by
  have hgamma : Continuous fun R : Fin n → Fin n → ℂ => gammaFock R u v := by
    unfold gammaFock
    fun_prop
  change Continuous fun R : Matrix (Fin n) (Fin n) ℂ => (1 - R).det * gammaFock R u v
  exact (continuous_const.sub continuous_id).matrix_det.mul hgamma

/-- The family used in the lower bound is entrywise continuous in its parameter. -/
theorem continuous_family_entry {n : ℕ} (ν ξ : ℝ) (u v : Occupation (Fin n)) :
    Continuous fun X : Herm0 n => fugacityCoeff (fugacityFamily ν ξ X) u v := by
  apply (continuous_fugacityCoeff_entry n u v).comp
  unfold fugacityFamily
  fun_prop

/-- The parameter support is measurable. -/
theorem gsupp_measurable (n : ℕ) : MeasurableSet (Gsupp n) := by
  have hc : Continuous fun M : Matrix (Fin n) (Fin n) ℂ =>
      Matrix.toEuclideanCLM (𝕜 := ℂ) M :=
    LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)
  have heq : Gsupp n = {X : Herm0 n |
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 4} := by
    ext X
    simp [Gsupp, WHMultiplicativity.schattenNorm]
  rw [heq]
  exact (isClosed_le (hc.norm.comp continuous_subtype_val) continuous_const).measurableSet

/-- The zero parameter belongs to the support. -/
theorem zero_mem_gsupp (n : ℕ) : (0 : Herm0 n) ∈ Gsupp n := by
  simp [Gsupp, WHMultiplicativity.schattenNorm]

/-- Every adaptive transcript experiment admits a measurable Markov kernel on the prior support. -/
theorem transcript_kernel_exists {n N : ℕ} {O : Type} [MeasurableSpace O]
    (S : AdaptiveScheme n N O) (ν ξ : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32) :
    ∃ K : Kernel (Herm0 n) (Fin N → O), IsMarkovKernel K ∧
      ∀ X ∈ Gsupp n, K X = transcriptLaw S (fugacityCoeff (fugacityFamily ν ξ X)) := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  let q : Herm0 n → Herm0 n := fun X => if X ∈ Gsupp n then X else 0
  have hq : Measurable q := Measurable.ite (gsupp_measurable n) measurable_id measurable_const
  have hqmem : ∀ X, q X ∈ Gsupp n := by
    intro X
    dsimp [q]
    split_ifs with h
    · exact h
    · exact zero_mem_gsupp n
  let ρ : Herm0 n → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ :=
    fun X => fugacityCoeff (fugacityFamily ν ξ (q X))
  have hρd : ∀ X, IsDensity (ρ X) := by
    intro X
    obtain ⟨σ, hσ, _, _⟩ := fugacityFamily_promiseClass n ν ξ hν0 hν1 hξ hξ32 (q X) (hqmem X)
    change IsDensity (fugacityCoeff (fugacityFamily ν ξ (q X)))
    rw [← hσ]
    exact σ.density
  have hρ : ∀ u v, Measurable fun X => ρ X u v := by
    intro u v
    exact (continuous_family_entry ν ξ u v).measurable.comp hq
  obtain ⟨M, hM⟩ := adaptive_scheme_product_povm S
  let K : Kernel (Herm0 n) (Fin N → O) :=
    ⟨fun X => M.law (WildeQIT.Schumacher.tensorPow N (ρ X)),
      povm_law_measurable M _ (fun u v => by
        change Measurable fun X => ∏ t, ρ X (u t) (v t)
        exact Finset.measurable_prod _ fun t _ => hρ (u t) (v t))
        (fun X => isDensity_tensorPow (ρ X) (hρd X) N)⟩
  refine ⟨K, ⟨fun X => M.law_prob _ (isDensity_tensorPow (ρ X) (hρd X) N)⟩, ?_⟩
  intro X hX
  change M.law (WildeQIT.Schumacher.tensorPow N (ρ X)) = _
  have heq : ρ X = fugacityCoeff (fugacityFamily ν ξ X) := by simp [ρ, q, hX]
  have h := hM (fun _ => ρ X) (fun _ => hρd X)
  change M.law (WildeQIT.Schumacher.tensorPow N (ρ X)) = transcriptLaw S (ρ X) at h
  rw [heq] at h ⊢
  exact h

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5Compression -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open scoped ENNReal Matrix ComplexOrder

noncomputable section
namespace BosonicLearn.Prop5

/-- POVM entries are countably additive, by polarization into four
ordinary probability measures. -/
theorem fockPOVM_entry_hasSum {I O : Type} [DecidableEq I] [MeasurableSpace O]
    (M : FockPOVM I O) (i j : I) (B : ℕ → Set O)
    (hB : ∀ k, MeasurableSet (B k)) (hd : Pairwise (Function.onFun Disjoint B)) :
    HasSum (fun k => M.effect (B k) i j) (M.effect (⋃ k, B k) i j) := by
  obtain ⟨τ, c, hτ, _, hentry⟩ := effect_entry_born i j
  simp_rw [hentry O M (⋃ k, B k) (MeasurableSet.iUnion hB), hentry O M _ (hB _)]
  refine hasSum_sum (fun a _ => HasSum.mul_left _ ?_)
  letI := M.law_prob (τ a) (hτ a)
  have hU : M.law (τ a) (⋃ k, B k) = ∑' k, M.law (τ a) (B k) := measure_iUnion hd hB
  have hne : (∑' k, M.law (τ a) (B k)) ≠ ∞ := hU ▸ measure_ne_top _ _
  have hs := ENNReal.hasSum_toReal hne
  rw [← ENNReal.tsum_toReal_eq (fun k => measure_ne_top _ _), ← hU] at hs
  exact Complex.ofRealCLM.hasSum hs

/-- Compression to an embedded basis preserves all effect bounds. -/
theorem compressed_effect_form {I J O : Type} [DecidableEq I] [DecidableEq J]
    [MeasurableSpace O] (M : FockPOVM I O) (a : J ↪ I)
    (B : Set O) (hB : MeasurableSet B) (s : Finset J) (z : J → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * M.effect B (a i) (a j) * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * M.effect B (a i) (a j) * z j).re ∧
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * M.effect B (a i) (a j) * z j).re ≤
      ∑ i ∈ s, ‖z i‖ ^ 2 := by
  have h := M.effect_form B hB (s.image a) (Function.extend a z 0)
  simpa only [Finset.sum_image a.injective.injOn, a.injective.extend_apply] using h

/-- Restricting a POVM to any embedded basis gives another POVM.
The finite case is used for photon-sector products. -/
theorem fockPOVM_compression {I J O : Type} [DecidableEq I] [DecidableEq J]
    [MeasurableSpace O] (M : FockPOVM I O) (a : J ↪ I) :
    ∃ P : FockPOVM J O, P.effect = fun B => (M.effect B).submatrix a a := by
  apply fockPOVM_of_effect
  · exact compressed_effect_form M a
  · rw [M.effect_univ, Matrix.submatrix_one a a.injective]
  · intro i j B hB hd
    exact fockPOVM_entry_hasSum M (a i) (a j) B hB hd

/-- Arrays supported on an embedded finite basis have finite Born
pairings, equal to the trace pairing of their compressed matrices. -/
theorem born_sum_compression {I J : Type} [DecidableEq I] [DecidableEq J] [Fintype J]
    (a : J ↪ I) (E ρ : Matrix I I ℂ)
    (hsupport : ∀ i j, i ∉ Set.range a ∨ j ∉ Set.range a → ρ i j = 0) :
    (∑' i, ∑' j, E i j * ρ j i) =
      ∑ i : J, ∑ j : J, E (a i) (a j) * ρ (a j) (a i) := by
  classical
  let s : Finset I := Finset.univ.image a
  have hmem (i : I) : i ∈ s ↔ i ∈ Set.range a := by simp [s, Set.mem_range]
  have hinner (i : I) : (∑' j, E i j * ρ j i) = ∑ j ∈ s, E i j * ρ j i := by
    apply tsum_eq_sum
    intro j hj
    rw [hsupport j i (Or.inl (by simpa only [hmem] using hj)), mul_zero]
  rw [tsum_congr hinner, tsum_eq_sum (s := s) (fun i hi => by
    apply Finset.sum_eq_zero
    intro j _
    rw [hsupport j i (Or.inr (by simpa only [hmem] using hi)), mul_zero])]
  simp only [s, Finset.sum_image a.injective.injOn]

/-- A density supported on an embedded finite basis remains a density
when regarded as a finite matrix on that basis. -/
theorem compressed_state_isDensity {I J : Type} [DecidableEq I] [DecidableEq J] [Fintype J]
    (a : J ↪ I) (ρ : Matrix I I ℂ) (hρ : IsDensity ρ)
    (hsupport : ∀ i j, i ∉ Set.range a ∨ j ∉ Set.range a → ρ i j = 0) :
    IsDensity (ρ.submatrix a a) := by
  apply isDensity_of_posSemidef
  · intro s z
    have h := hρ.2.1 (s.image a) (Function.extend a z 0)
    simpa only [Finset.sum_image a.injective.injOn, a.injective.extend_apply,
      Matrix.submatrix_apply] using h
  · exact (hasSum_fintype _).summable
  · have he : (∑' i : I, (ρ i i).re) = ∑ j : J, (ρ (a j) (a j)).re := by
      let s : Finset I := Finset.univ.image a
      have hmem (i : I) : i ∈ s ↔ i ∈ Set.range a := by simp [s, Set.mem_range]
      rw [tsum_eq_sum (s := s) (fun i hi => by
        rw [hsupport i i (Or.inl (by simpa only [hmem] using hi)), Complex.zero_re])]
      simp only [s, Finset.sum_image a.injective.injOn]
    simpa only [tsum_fintype, Matrix.submatrix_apply, ← he] using hρ.2.2.2

/-- The finite compressed POVM has exactly the same measurement law
on a state supported on the selected basis. -/
theorem compressed_law_eq {I J O : Type} [DecidableEq I] [DecidableEq J] [Fintype J]
    [MeasurableSpace O] (M : FockPOVM I O) (P : FockPOVM J O) (a : J ↪ I)
    (hP : P.effect = fun B => (M.effect B).submatrix a a)
    (ρ : Matrix I I ℂ) (hρ : IsDensity ρ)
    (hsupport : ∀ i j, i ∉ Set.range a ∨ j ∉ Set.range a → ρ i j = 0) :
    P.law (ρ.submatrix a a) = M.law ρ := by
  ext B hB
  rw [P.law_born _ (compressed_state_isDensity a ρ hρ hsupport) B hB,
    M.law_born ρ hρ B hB, born_sum_compression a (M.effect B) ρ hsupport]
  simp only [hP, tsum_fintype, Matrix.submatrix_apply]

/-- Multiplicativity of the matrix tensor product on dependent finite
basis types, written directly as products of entries. -/
theorem finite_tensor_mul {T : Type} [Fintype T] [DecidableEq T]
    {J : T → Type} [∀ t, Fintype (J t)]
    (A B : ∀ t, Matrix (J t) (J t) ℂ) :
    Matrix.of (fun u v : ∀ t, J t => ∏ t, (A t * B t) (u t) (v t)) =
      Matrix.of (fun u v : ∀ t, J t => ∏ t, A t (u t) (v t)) *
      Matrix.of (fun u v : ∀ t, J t => ∏ t, B t (u t) (v t)) := by
  classical
  ext u v
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact Finset.prod_mul_distrib

theorem finite_tensor_conjTranspose {T : Type} [Fintype T] [DecidableEq T]
    {J : T → Type} [∀ t, Fintype (J t)]
    (A : ∀ t, Matrix (J t) (J t) ℂ) :
    Matrix.of (fun u v : ∀ t, J t => ∏ t, (A t)ᴴ (u t) (v t)) =
      Matrix.of (fun u v : ∀ t, J t => ∏ t, A t (u t) (v t))ᴴ := by
  ext u v
  change (∏ t, star (A t (v t) (u t))) = star (∏ t, A t (v t) (u t))
  exact (star_prod _ _).symm

theorem finite_tensor_one {T : Type} [Fintype T] [DecidableEq T]
    {J : T → Type} [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] :
    Matrix.of (fun u v : ∀ t, J t => ∏ t, (1 : Matrix (J t) (J t) ℂ) (u t) (v t)) = 1 := by
  classical
  ext u v
  by_cases huv : u = v
  · subst v
    simp
  · have hne : ∃ t, u t ≠ v t := by
      by_contra h
      apply huv
      funext t
      exact Classical.not_not.mp (fun ht => h ⟨t, ht⟩)
    obtain ⟨t, ht⟩ := hne
    simp only [Matrix.of_apply, Matrix.one_apply_ne huv]
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    exact Matrix.one_apply_ne ht

open scoped MatrixOrder in
/-- Products of positive local matrices are positive, for varying
finite local dimensions. -/
theorem finite_tensor_posSemidef {T : Type} [Fintype T] [DecidableEq T]
    {J : T → Type} [∀ t, Fintype (J t)]
    (R : ∀ t, Matrix (J t) (J t) ℂ) (hR : ∀ t, (R t).PosSemidef) :
    (Matrix.of (fun u v : ∀ t, J t => ∏ t, R t (u t) (v t))).PosSemidef := by
  classical
  choose B hB using fun t => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hR t).nonneg
  have he : Matrix.of (fun u v : ∀ t, J t => ∏ t, R t (u t) (v t)) =
      Matrix.of (fun u v : ∀ t, J t => ∏ t, B t (u t) (v t))ᴴ *
        Matrix.of (fun u v : ∀ t, J t => ∏ t, B t (u t) (v t)) := by
    rw [← finite_tensor_conjTranspose B, ← finite_tensor_mul (fun t => (B t)ᴴ) B]
    funext u v
    apply Finset.prod_congr rfl
    intro t _
    rw [hB t, Matrix.star_eq_conjTranspose]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem finite_tensor_posDef {T : Type} [Fintype T] [DecidableEq T]
    {J : T → Type} [∀ t, Fintype (J t)]
    (R : ∀ t, Matrix (J t) (J t) ℂ) (hR : ∀ t, (R t).PosDef) :
    (Matrix.of (fun u v : ∀ t, J t => ∏ t, R t (u t) (v t))).PosDef := by
  classical
  apply (finite_tensor_posSemidef R (fun t => (hR t).posSemidef)).posDef_iff_isUnit.mpr
  let A : Matrix (∀ t, J t) (∀ t, J t) ℂ := fun u v => ∏ t, R t (u t) (v t)
  let B : Matrix (∀ t, J t) (∀ t, J t) ℂ := fun u v => ∏ t, (R t)⁻¹ (u t) (v t)
  have hAB : A * B = 1 := by
    change Matrix.of (fun u v : ∀ t, J t => ∏ t, R t (u t) (v t)) *
      Matrix.of (fun u v : ∀ t, J t => ∏ t, (R t)⁻¹ (u t) (v t)) = 1
    rw [← finite_tensor_mul R (fun t => (R t)⁻¹)]
    simp only [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hR _).isUnit)]
    exact finite_tensor_one
  have hBA : B * A = 1 := by
    change Matrix.of (fun u v : ∀ t, J t => ∏ t, (R t)⁻¹ (u t) (v t)) *
      Matrix.of (fun u v : ∀ t, J t => ∏ t, R t (u t) (v t)) = 1
    rw [← finite_tensor_mul (fun t => (R t)⁻¹) R]
    simp only [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (hR _).isUnit)]
    exact finite_tensor_one
  exact ⟨⟨A, B, hAB, hBA⟩, rfl⟩

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5PhotonMixture -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Appending one outcome is measurable even when the outcome space
has an arbitrary sigma algebra. -/
theorem measurable_append_outcome {O : Type*} [MeasurableSpace O] (t : ℕ) :
    Measurable (fun p : (Fin t → O) × O =>
      (Fin.snoc (α := fun _ => O) p.1 p.2 : Fin (t + 1) → O)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · simpa [Function.comp_def] using (measurable_pi_apply j).comp measurable_fst

/-- The same recursion as `sequentialLaw`, with round kernels indexed
by all natural numbers, to make induction on prefix length direct. -/
noncomputable def evolvingLaw {O : Type*} [MeasurableSpace O]
    (K : (t : ℕ) → Kernel (Fin t → O) O) : (t : ℕ) → Measure (Fin t → O)
  | 0 => Measure.dirac (fun i => Fin.elim0 i)
  | t + 1 => ((evolvingLaw K t) ⊗ₘ K t).map
      (fun p => Fin.snoc (α := fun _ => O) p.1 p.2)

/-- The transcript law when each round's component label is fixed. -/
noncomputable def recordLaw {O I : Type*} [MeasurableSpace O]
    (A : (t : ℕ) → I → Kernel (Fin t → O) O) :
    (t : ℕ) → (Fin t → I) → Measure (Fin t → O)
  | 0, _ => Measure.dirac (fun i => Fin.elim0 i)
  | t + 1, k => ((recordLaw A t (Fin.init k)) ⊗ₘ A t (k (Fin.last t))).map
      (fun p => Fin.snoc (α := fun _ => O) p.1 p.2)

instance evolvingLaw_sfinite {O : Type*} [MeasurableSpace O]
    (K : (t : ℕ) → Kernel (Fin t → O) O) [∀ t, IsSFiniteKernel (K t)] (t : ℕ) :
    SFinite (evolvingLaw K t) := by
  induction t with
  | zero => dsimp [evolvingLaw]; infer_instance
  | succ t ih =>
    letI := ih
    dsimp [evolvingLaw]
    infer_instance

instance recordLaw_sfinite {O I : Type*} [MeasurableSpace O]
    (A : (t : ℕ) → I → Kernel (Fin t → O) O)
    [∀ t i, IsSFiniteKernel (A t i)] (t : ℕ) (k : Fin t → I) :
    SFinite (recordLaw A t k) := by
  induction t with
  | zero => dsimp [recordLaw]; infer_instance
  | succ t ih =>
    letI := ih (Fin.init k)
    dsimp [recordLaw]
    infer_instance

theorem evolvingLaw_eq_sequentialLaw {O : Type} [MeasurableSpace O]
    (K : (t : ℕ) → Kernel (Fin t → O) O) (N t : ℕ) (ht : t ≤ N) :
    evolvingLaw K t = sequentialLaw (fun u : Fin N => K u) t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [evolvingLaw, sequentialLaw, ih (Nat.le_of_succ_le ht)]

theorem recordLaw_eq_sequentialLaw {O I : Type} [MeasurableSpace O]
    (A : (t : ℕ) → I → Kernel (Fin t → O) O)
    (N : ℕ) (k : Fin N → I) (t : ℕ) (ht : t ≤ N) :
    recordLaw A t (fun u => k (Fin.castLE ht u)) =
      sequentialLaw (fun u : Fin N => A u (k u)) t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [recordLaw, sequentialLaw]
    congr 2
    exact ih (Nat.le_of_succ_le ht)

/-- Independent countable mixture labels can be exposed through all
rounds of an adaptive scheme. Adaptivity remains in each component
kernel's dependence on the earlier outcomes. -/
theorem evolvingLaw_countable_sum {O I : Type} [MeasurableSpace O] [Countable I]
    (A : (t : ℕ) → I → Kernel (Fin t → O) O)
    [∀ t i, IsSFiniteKernel (A t i)] (t : ℕ) :
    evolvingLaw (fun u => Kernel.sum (A u)) t = Measure.sum (recordLaw A t) := by
  induction t with
  | zero =>
    ext s hs
    simp [evolvingLaw, recordLaw, Measure.sum_apply _ hs]
  | succ t ih =>
    rw [evolvingLaw, ih, Measure.compProd_sum_left]
    simp_rw [Measure.compProd_sum_right]
    rw [Measure.map_sum (measurable_append_outcome t).aemeasurable]
    simp_rw [Measure.map_sum (measurable_append_outcome t).aemeasurable]
    rw [Measure.sum_comm, Measure.sum_sum]
    have he := Measure.sum_comp_equiv (Fin.snocEquiv (fun _ : Fin (t + 1) => I))
      (recordLaw A (t + 1))
    simpa only [Function.comp_def, Fin.snocEquiv, Equiv.coe_fn_mk, recordLaw,
      Fin.init_snoc, Fin.snoc_last] using he

/-- Countable mixtures commute with the finite adaptive transcript
construction, without assumptions on the outcome sigma algebra. -/
theorem sequentialLaw_countable_sum {O I : Type} [MeasurableSpace O] [Countable I]
    (A : (t : ℕ) → I → Kernel (Fin t → O) O)
    [∀ t i, IsSFiniteKernel (A t i)] (N : ℕ) :
    sequentialLaw (fun t : Fin N => Kernel.sum (A t)) N le_rfl =
      Measure.sum (fun k : Fin N → I =>
        sequentialLaw (fun t : Fin N => A t (k t)) N le_rfl) := by
  rw [← evolvingLaw_eq_sequentialLaw (fun u => Kernel.sum (A u)) N N le_rfl,
    evolvingLaw_countable_sum]
  congr 1
  funext k
  simpa using recordLaw_eq_sequentialLaw A N k N le_rfl

/-- The finite-round form: labels need only be defined at the rounds
that actually occur. -/
theorem sequentialLaw_countable_sum_fin {O I : Type} [MeasurableSpace O] [Countable I]
    {N : ℕ} (A : (t : Fin N) → I → Kernel (Fin t → O) O)
    [∀ t i, IsSFiniteKernel (A t i)] :
    sequentialLaw (fun t => Kernel.sum (A t)) N le_rfl =
      Measure.sum (fun k : Fin N → I =>
        sequentialLaw (fun t => A t (k t)) N le_rfl) := by
  classical
  let B : (t : ℕ) → I → Kernel (Fin t → O) O :=
    fun t i => if h : t < N then A ⟨t, h⟩ i else 0
  have hB (t : Fin N) (i : I) : B t i = A t i := by simp [B, t.isLt]
  have hB' (t : Fin N) : B t = A t := funext (hB t)
  letI : ∀ t i, IsSFiniteKernel (B t i) := fun t i => by
    dsimp [B]
    split_ifs <;> infer_instance
  have h := sequentialLaw_countable_sum B N
  simpa only [hB'] using h

/-- Multiplication of all the output measures of a kernel by the
same finite mass. -/
noncomputable def scaledKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (a : ℝ≥0∞) (K : Kernel α β) [IsSFiniteKernel K] : Kernel α β :=
  K.withDensity (fun _ _ => a)

theorem scaledKernel_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (a : ℝ≥0∞) (K : Kernel α β) [IsSFiniteKernel K] (x : α) :
    scaledKernel a K x = a • K x := by
  rw [scaledKernel, Kernel.withDensity_apply K measurable_const, withDensity_const]

theorem scaledKernel_sfinite {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (a : ℝ≥0∞) (ha : a ≠ ∞) (K : Kernel α β) [IsSFiniteKernel K] :
    IsSFiniteKernel (scaledKernel a K) :=
  Kernel.IsSFiniteKernel.withDensity K (fun _ _ => ha)

theorem compProd_scaledKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (K : Kernel α β) [IsSFiniteKernel K]
    (a : ℝ≥0∞) (ha : a ≠ ∞) :
    μ ⊗ₘ scaledKernel a K = a • (μ ⊗ₘ K) := by
  letI := scaledKernel_sfinite a ha K
  ext s hs
  simp only [Measure.compProd_apply hs, scaledKernel_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ha]

theorem sequentialLaw_sfinite {O : Type} [MeasurableSpace O] {N : ℕ}
    (K : (t : Fin N) → Kernel (Fin t → O) O) [∀ t, IsSFiniteKernel (K t)]
    (t : ℕ) (ht : t ≤ N) : SFinite (sequentialLaw K t ht) := by
  induction t with
  | zero => dsimp [sequentialLaw]; infer_instance
  | succ t ih =>
    letI := ih (Nat.le_of_succ_le ht)
    dsimp [sequentialLaw]
    infer_instance

/-- Scalar component masses multiply along an adaptive transcript. -/
theorem sequentialLaw_scaled {O : Type} [MeasurableSpace O] {N : ℕ}
    (K : (t : Fin N) → Kernel (Fin t → O) O) [∀ t, IsSFiniteKernel (K t)]
    (w : Fin N → ℝ≥0∞) (hw : ∀ t, w t ≠ ∞) (t : ℕ) (ht : t ≤ N) :
    sequentialLaw (fun u => scaledKernel (w u) (K u)) t ht =
      (∏ u : Fin t, w (Fin.castLE ht u)) • sequentialLaw K t ht := by
  letI : ∀ u, IsSFiniteKernel (scaledKernel (w u) (K u)) :=
    fun u => scaledKernel_sfinite _ (hw u) _
  induction t with
  | zero => simp [sequentialLaw]
  | succ t ih =>
    letI := sequentialLaw_sfinite K t (Nat.le_of_succ_le ht)
    rw [sequentialLaw, ih (Nat.le_of_succ_le ht), Measure.compProd_smul_left,
      compProd_scaledKernel _ _ _ (hw ⟨t, ht⟩), Measure.map_smul, Measure.map_smul,
      smul_smul, Fin.prod_univ_castSucc]
    rfl

/-- A countable per-round mixture expands into a mixture indexed by
the whole label record, with product weights. -/
theorem sequentialLaw_countable_weighted_mixture
    {O I : Type} [MeasurableSpace O] [Countable I] {N : ℕ}
    (K : (t : Fin N) → I → Kernel (Fin t → O) O)
    [∀ t i, IsSFiniteKernel (K t i)]
    (w : Fin N → I → ℝ≥0∞) (hw : ∀ t i, w t i ≠ ∞) :
    sequentialLaw (fun t => Kernel.sum (fun i => scaledKernel (w t i) (K t i))) N le_rfl =
      Measure.sum (fun k : Fin N → I =>
        (∏ t, w t (k t)) • sequentialLaw (fun t => K t (k t)) N le_rfl) := by
  letI : ∀ t i, IsSFiniteKernel (scaledKernel (w t i) (K t i)) :=
    fun t i => scaledKernel_sfinite _ (hw t i) _
  rw [sequentialLaw_countable_sum_fin]
  congr 1
  funext k
  simpa using sequentialLaw_scaled (fun t => K t (k t))
    (fun t => w t (k t)) (fun t => hw t (k t)) N le_rfl

/-- The product weights of a full countable label record have total
mass one, including for the empty record. -/
theorem record_weights_sum_one {I : Type} (w : I → ℝ≥0∞) (hw : ∑' i, w i = 1) (N : ℕ) :
    (∑' k : Fin N → I, ∏ t, w (k t)) = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (N + 1) => I)).tsum_eq]
    change (∑' p : I × (Fin N → I), ∏ t, w (Fin.snoc (α := fun _ => I) p.2 p.1 t)) = 1
    simp_rw [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_right, ih, one_mul]
    exact hw

/-- The mean additive cost of an independent label record is the
number of rounds times the one-round mean cost. No finiteness of the
cost is needed for this extended-nonnegative identity. -/
theorem record_additive_cost_mean {I : Type} (w c : I → ℝ≥0∞)
    (hw : ∑' i, w i = 1) (N : ℕ) :
    (∑' k : Fin N → I, (∏ t, w (k t)) * (∑ t, c (k t))) =
      N * ∑' i, w i * c i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (N + 1) => I)).tsum_eq]
    change (∑' p : I × (Fin N → I),
      (∏ t, w (Fin.snoc (α := fun _ => I) p.2 p.1 t)) *
        (∑ t, c (Fin.snoc (α := fun _ => I) p.2 p.1 t))) = _
    simp_rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      mul_add]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_add]
    have hfirst : (∑' a : I, ∑' k : Fin N → I,
        ((∏ t, w (k t)) * w a) * (∑ t, c (k t))) = N * ∑' i, w i * c i := by
      simp_rw [show ∀ a : I, ∀ k : Fin N → I,
        ((∏ t, w (k t)) * w a) * (∑ t, c (k t)) =
          w a * ((∏ t, w (k t)) * (∑ t, c (k t))) by intros; ring,
        ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right, hw, one_mul]
    have hsecond : (∑' a : I, ∑' k : Fin N → I,
        ((∏ t, w (k t)) * w a) * c a) = ∑' i, w i * c i := by
      simp_rw [mul_assoc, ENNReal.tsum_mul_right, record_weights_sum_one w hw N, one_mul]
    rw [hfirst, hsecond, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5PhotonMoment -/
section
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder
open BosonicLearn
noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-! ### Sectors, cyclicity and unitary diagonalization (as in `gammaFock_trace_psd`) -/

/-- The photon-number sector `N`: occupation vectors of total `N`. -/
private def sec (n N : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (N + 1)).filter (fun w => ∑ i, w i = N)

private lemma mem_sec {n N : ℕ} (w : Fin n → ℕ) : w ∈ sec n N ↔ ∑ i, w i = N := by
  unfold sec
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun k => ?_, h⟩⟩
  rw [Finset.mem_range, ← h]
  have h2 : w k ≤ ∑ i, w i :=
    Finset.single_le_sum (f := fun i => w i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  omega

private lemma gammaFock_mul_sec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock (A * B) u v = ∑ w ∈ sec n (∑ i, u i), gammaFock A u w * gammaFock B w v :=
  gammaFock_mul A B u v

/-- Cyclicity of the trace of `Γ` on a photon-number sector. -/
private lemma sector_trace_comm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) :
    ∑ u ∈ sec n N, gammaFock (A * B) u u = ∑ u ∈ sec n N, gammaFock (B * A) u u := by
  have h1 : ∀ (A B : Matrix (Fin n) (Fin n) ℂ), ∑ u ∈ sec n N, gammaFock (A * B) u u =
      ∑ u ∈ sec n N, ∑ w ∈ sec n N, gammaFock A u w * gammaFock B w u := by
    intro A B
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [gammaFock_mul_sec, (mem_sec u).mp hu]
  rw [h1 A B, h1 B A, Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => mul_comm _ _

/-- Partial sums of a non-negative family are bounded by the sum of another non-negative family with the same
sector sums. -/
private lemma sum_le_of_sector {n : ℕ} (f g : (Fin n → ℕ) → ℝ) (hf : ∀ u, 0 ≤ f u)
    (hg : ∀ u, 0 ≤ g u) (h : ∀ N, ∑ u ∈ sec n N, f u = ∑ u ∈ sec n N, g u) {a : ℝ}
    (hga : HasSum g a) (s : Finset (Fin n → ℕ)) : ∑ u ∈ s, f u ≤ a := by
  set M := s.sup (fun u => ∑ i, u i) with hM
  have hdisj : ((Finset.range (M + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint (sec n) := by
    intro N _ N' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    exact hne (((mem_sec u).mp hu).symm.trans ((mem_sec u).mp hu'))
  have hsub : s ⊆ (Finset.range (M + 1)).biUnion (sec n) := by
    intro u hu
    rw [Finset.mem_biUnion]
    refine ⟨∑ i, u i, ?_, (mem_sec u).mpr rfl⟩
    rw [Finset.mem_range]
    have : ∑ i, u i ≤ M := Finset.le_sup (f := fun u : Fin n → ℕ => ∑ i, u i) hu
    omega
  calc ∑ u ∈ s, f u ≤ ∑ u ∈ (Finset.range (M + 1)).biUnion (sec n), f u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ => hf u
    _ = ∑ N ∈ Finset.range (M + 1), ∑ u ∈ sec n N, f u := Finset.sum_biUnion hdisj
    _ = ∑ N ∈ Finset.range (M + 1), ∑ u ∈ sec n N, g u := Finset.sum_congr rfl fun N _ => h N
    _ = ∑ u ∈ (Finset.range (M + 1)).biUnion (sec n), g u := (Finset.sum_biUnion hdisj).symm
    _ ≤ a := sum_le_hasSum _ (fun u _ => hg u) hga

/-- Two non-negative families with the same sector sums have the same sum. -/
private lemma hasSum_of_sector {n : ℕ} (f g : (Fin n → ℕ) → ℝ) (hf : ∀ u, 0 ≤ f u)
    (hg : ∀ u, 0 ≤ g u) (h : ∀ N, ∑ u ∈ sec n N, f u = ∑ u ∈ sec n N, g u) {a : ℝ}
    (hga : HasSum g a) : HasSum f a := by
  have hsum : Summable f := summable_of_sum_le hf (sum_le_of_sector f g hf hg h hga)
  have h1 : ∑' u, f u ≤ a := hasSum_le_of_sum_le hsum.hasSum (sum_le_of_sector f g hf hg h hga)
  have h2 : a ≤ ∑' u, f u :=
    hasSum_le_of_sum_le hga (sum_le_of_sector g f hg hf (fun N => (h N).symm) hsum.hasSum)
  have h3 : ∑' u, f u = a := le_antisymm h1 h2
  rw [← h3]
  exact hsum.hasSum

private lemma conj_one_sub {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1) :
    Uᴴ * (1 - U * D * Uᴴ) * U = 1 - D := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU1]
  have h : Uᴴ * (U * D * Uᴴ) * U = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
  rw [h, hU1, Matrix.one_mul, Matrix.mul_one]

private lemma one_sub_conj {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ) (hU2 : U * Uᴴ = 1) :
    1 - U * D * Uᴴ = U * (1 - D) * Uᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]

private lemma one_sub_diagonal {n : ℕ} (d : Fin n → ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal (fun i => (d i : ℂ)) =
      Matrix.diagonal (fun i => ((1 - d i : ℝ) : ℂ)) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext i
  simp

/-- Unitary diagonalization `R = U diag(d) Uᴴ` with `0 ≤ dᵢ < 1`. -/
private lemma spectral_data {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      R = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ ∧ (∀ i, 0 ≤ d i) ∧ (∀ i, d i < 1) := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin n) (Fin n) ℂ,
      U = (hR.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hU1 : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hUdef]
    exact Unitary.coe_star_mul_self _
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hUdef]
    exact Unitary.coe_mul_star_self _
  have hspec : R = U * Matrix.diagonal (fun i => ((hR.1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hR.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact h
  refine ⟨U, hR.1.eigenvalues, hU1, hU2, hspec, hR.eigenvalues_nonneg, ?_⟩
  have hD := conj_one_sub U (Matrix.diagonal (fun i => ((hR.1.eigenvalues i : ℝ) : ℂ))) hU1
  rw [← hspec, one_sub_diagonal] at hD
  have hpd : (Uᴴ * (1 - R) * U).PosDef :=
    hR1.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit
      (IsUnit.of_mul_eq_one _ hU2))
  rw [hD, Matrix.posDef_diagonal_iff] at hpd
  intro i
  have h := hpd i
  rw [Complex.zero_lt_real] at h
  linarith

private lemma gammaFock_diag_real {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (u : Fin n → ℕ) : (gammaFock R u u).im = 0 ∧ 0 ≤ (gammaFock R u u).re := by
  have h := gammaFock_posSemidef R hR {u} (fun _ => 1)
  simpa using h

/-! ### Diagonal entries of `Γ(diag c)` and products of series (as in `gammaFock_trace`) -/

/-- The index set of `gammaFock`: matrices `M ∈ ℕ^{n×n}` with row sums `u` and column sums `v`. -/
private def gS {n : ℕ} (u v : Fin n → ℕ) : Finset (Fin n → Fin n → ℕ) :=
  (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin n => Finset.range (u i + 1)).filter
    (fun M => (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j)

/-- The box constraint is automatic. -/
private lemma mem_gS {n : ℕ} (u v : Fin n → ℕ) (M : Fin n → Fin n → ℕ) :
    M ∈ gS u v ↔ (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j := by
  unfold gS
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i j => ?_, h⟩
    have h1 : M i j ≤ ∑ j, M i j :=
      Finset.single_le_sum (f := fun j => M i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [h.1 i] at h1
    omega

/-- The combinatorial sum in `gammaFock`. -/
private def gSum {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) : ℂ :=
  ∑ M ∈ gS u v, ∏ i, ∏ j, R i j ^ (M i j) / (Nat.factorial (M i j) : ℂ)

private lemma gammaFock_eq {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock R u v =
      (Real.sqrt ((∏ i, (Nat.factorial (u i) : ℝ)) * ∏ j, (Nat.factorial (v j) : ℝ)) : ℂ) *
        gSum R u v := rfl

/-- For diagonal `R`, an off-diagonal nonzero entry of `M` kills the term. -/
private lemma term_diagonal_eq_zero {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (h : M i j ≠ 0) :
    ∏ i, ∏ j, (Matrix.diagonal c) i j ^ (M i j) / (Nat.factorial (M i j) : ℂ) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
  rw [Matrix.diagonal_apply_ne c hij, zero_pow h, zero_div]

/-- A matrix with vanishing off-diagonal entries and row sums `u` is `diag u`. -/
private lemma diag_of_offdiag_zero {n : ℕ} (u : Fin n → ℕ) (M : Fin n → Fin n → ℕ)
    (hrow : ∀ i, ∑ j, M i j = u i) (hoff : ∀ i j, i ≠ j → M i j = 0) (i : Fin n) :
    M i i = u i := by
  rw [← hrow i]
  exact (Finset.sum_eq_single i (fun j _ hji => hoff i j (Ne.symm hji))
    (fun h => absurd (Finset.mem_univ i) h)).symm

private lemma gSum_diagonal_self {n : ℕ} (c : Fin n → ℂ) (u : Fin n → ℕ) :
    gSum (Matrix.diagonal c) u u = ∏ i, (c i ^ u i / (Nat.factorial (u i) : ℂ)) := by
  unfold gSum
  rw [Finset.sum_eq_single (fun i j => if i = j then u i else 0)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro M hM hne
    rw [mem_gS] at hM
    by_cases hoff : ∀ i j, i ≠ j → M i j = 0
    · exfalso
      apply hne
      funext i j
      by_cases hij : i = j
      · subst hij
        simp [diag_of_offdiag_zero u M hM.1 hoff i]
      · simp [hij, hoff i j hij]
    · push Not at hoff
      obtain ⟨i, j, hij, hne'⟩ := hoff
      exact term_diagonal_eq_zero c M i j hij hne'
  · intro h
    exfalso
    apply h
    rw [mem_gS]
    constructor
    · intro i
      simp
    · intro j
      simp

/-- Diagonal entries of `Γ(diag c)`. -/
private lemma gammaFock_diagonal_self {n : ℕ} (c : Fin n → ℂ) (u : Fin n → ℕ) :
    gammaFock (Matrix.diagonal c) u u = ∏ i, c i ^ u i := by
  rw [gammaFock_eq, gSum_diagonal_self]
  have hpos : (0 : ℝ) ≤ ∏ i, (Nat.factorial (u i) : ℝ) :=
    Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  rw [Real.sqrt_mul_self hpos]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : ((Nat.factorial (u i) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- A finite product of nonnegative convergent series is the series over `ℕⁿ` of the products. -/
private lemma hasSum_pi_prod_of_nonneg (n : ℕ) : ∀ (f : Fin n → ℕ → ℝ) (a : Fin n → ℝ),
    (∀ i k, 0 ≤ f i k) → (∀ i, HasSum (f i) (a i)) →
    HasSum (fun u : Fin n → ℕ => ∏ i, f i (u i)) (∏ i, a i) := by
  induction n with
  | zero =>
    intro f a _ _
    simp
  | succ n ih =>
    intro f a hf0 hf
    have ih' := ih (fun i => f i.succ) (fun i => a i.succ)
      (fun i k => hf0 i.succ k) (fun i => hf i.succ)
    have hsum : Summable (fun p : ℕ × (Fin n → ℕ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i)) :=
      Summable.mul_of_nonneg (f := f 0) (g := fun u : Fin n → ℕ => ∏ i : Fin n, f i.succ (u i))
        (hf 0).summable ih'.summable (fun k => hf0 0 k)
        (fun u => Finset.prod_nonneg fun i _ => hf0 i.succ (u i))
    have hmul : HasSum (fun p : ℕ × (Fin n → ℕ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i))
        (a 0 * ∏ i : Fin n, a i.succ) :=
      HasSum.mul (f := f 0) (g := fun u : Fin n → ℕ => ∏ i : Fin n, f i.succ (u i)) (hf 0) ih' hsum
    rw [Fin.prod_univ_succ]
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
    refine hmul.congr_fun fun p => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]

private lemma gammaFock_diagonal_re {n : ℕ} (d : Fin n → ℝ) (u : Fin n → ℕ) :
    (gammaFock (Matrix.diagonal fun i => (d i : ℂ)) u u).re = ∏ i, d i ^ u i := by
  simp only [gammaFock_diagonal_self, ← Complex.ofReal_pow, ← Complex.ofReal_prod,
    Complex.ofReal_re]


/-- The second moment series of an unnormalized geometric distribution. -/
theorem hasSum_sq_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * r ^ k) (r * (1 + r) / (1 - r) ^ 3) := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr0] using hr1
  have hne : 1 - r ≠ 0 := by linarith
  have hc := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr).mul_left 2
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr).mul_left 3
  have h0 := (hasSum_geometric_of_lt_one hr0 hr1).mul_left 2
  have hcval (k : ℕ) : 2 * (((k + 2).choose 2 : ℕ) : ℝ) =
      (k : ℝ) ^ 2 + 3 * k + 2 := by
    have hnat : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
      rw [Nat.choose_two_right]
      have heven := Nat.even_mul_pred_self (k + 2)
      simpa [Nat.add_sub_cancel] using (Nat.mul_div_cancel' heven.two_dvd)
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hnat
    push_cast at hcast
    nlinarith
  have h := (hc.sub h1).sub h0
  have hval : 2 * (1 / (1 - r) ^ (2 + 1)) - 3 * (r / (1 - r) ^ 2) -
      2 * (1 - r)⁻¹ = r * (1 + r) / (1 - r) ^ 3 := by
    field_simp
    ring
  rw [hval] at h
  refine h.congr_fun fun k => ?_
  have hh := hcval k
  linear_combination -r ^ k * hh

/-- Mean and second moment of the geometric law on `0,1,…`. -/
theorem geometric_moments {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => (1 - r) * r ^ k) 1 ∧
    HasSum (fun k : ℕ => (k : ℝ) * ((1 - r) * r ^ k)) (r / (1 - r)) ∧
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * ((1 - r) * r ^ k))
      (r / (1 - r) + 2 * (r / (1 - r)) ^ 2) := by
  have hne : 1 - r ≠ 0 := by linarith
  have hr : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr0] using hr1
  constructor
  · have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 - r)
    rwa [mul_inv_cancel₀ hne] at h
  constructor
  · have h := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr).mul_left (1 - r)
    have hv : (1 - r) * (r / (1 - r) ^ 2) = r / (1 - r) := by field_simp
    rw [hv] at h
    exact h.congr_fun fun k => by ring
  · have h := (hasSum_sq_mul_geometric hr0 hr1).mul_left (1 - r)
    have hv : (1 - r) * (r * (1 + r) / (1 - r) ^ 3) =
        r / (1 - r) + 2 * (r / (1 - r)) ^ 2 := by field_simp; ring
    rw [hv] at h
    exact h.congr_fun fun k => by ring

private lemma hasSum_pair_nonneg {A B : Type} {f : A → ℝ} {g : B → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    HasSum (fun p : A × B => f p.1 * g p.2) (a * b) :=
  hf.mul hg (hf.summable.mul_of_nonneg hg.summable hf0 hg0)

/-- First and second moments add in the usual way for independent discrete coordinates. -/
theorem independent_sum_moments (n : ℕ) :
    ∀ (p : Fin n → ℕ → ℝ) (m v : Fin n → ℝ),
      (∀ i k, 0 ≤ p i k) →
      (∀ i, HasSum (p i) 1) →
      (∀ i, HasSum (fun k : ℕ => (k : ℝ) * p i k) (m i)) →
      (∀ i, HasSum (fun k : ℕ => (k : ℝ) ^ 2 * p i k) (v i + (m i) ^ 2)) →
      HasSum (fun u : Fin n → ℕ => ∏ i, p i (u i)) 1 ∧
      HasSum (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) * ∏ i, p i (u i)) (∑ i, m i) ∧
      HasSum (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 * ∏ i, p i (u i))
        ((∑ i, v i) + (∑ i, m i) ^ 2) := by
  induction n with
  | zero =>
    intro p m v _ _ _ _
    simp
  | succ n ih =>
    intro p m v hp h0 h1 h2
    obtain ⟨hP, hM, hS⟩ := ih (fun i => p i.succ) (fun i => m i.succ) (fun i => v i.succ)
      (fun i k => hp i.succ k) (fun i => h0 i.succ)
      (fun i => h1 i.succ) (fun i => h2 i.succ)
    have hp0 : ∀ u : Fin n → ℕ, 0 ≤ ∏ i, p i.succ (u i) :=
      fun u => Finset.prod_nonneg fun i _ => hp i.succ (u i)
    have hm0 : ∀ u : Fin n → ℕ, 0 ≤ (∑ i, (u i : ℝ)) * ∏ i, p i.succ (u i) :=
      fun u => mul_nonneg (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _) (hp0 u)
    have hs0 : ∀ u : Fin n → ℕ, 0 ≤ (∑ i, (u i : ℝ)) ^ 2 * ∏ i, p i.succ (u i) :=
      fun u => mul_nonneg (sq_nonneg _) (hp0 u)
    have hk1 : ∀ k : ℕ, 0 ≤ (k : ℝ) * p 0 k := fun k => mul_nonneg (Nat.cast_nonneg _) (hp 0 k)
    have hk2 : ∀ k : ℕ, 0 ≤ (k : ℝ) ^ 2 * p 0 k := fun k => mul_nonneg (sq_nonneg _) (hp 0 k)
    constructor
    · have h := hasSum_pair_nonneg (h0 0) hP (hp 0) hp0
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
      convert h using 1
      · ext u
        simp [Fin.consEquiv, Fin.prod_univ_succ]
      · norm_num
    constructor
    · have h := (hasSum_pair_nonneg (h1 0) hP hk1 hp0).add
        (hasSum_pair_nonneg (h0 0) hM (hp 0) hm0)
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
      convert h using 1
      · ext u
        simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.sum_univ_succ]
        ring
      · simp [Fin.sum_univ_succ]
    · have h := ((hasSum_pair_nonneg (h2 0) hP hk2 hp0).add
        ((hasSum_pair_nonneg (h1 0) hM hk1 hm0).mul_left 2)).add
          (hasSum_pair_nonneg (h0 0) hS (hp 0) hs0)
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
      convert h using 1
      · ext u
        simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.sum_univ_succ]
        ring
      · simp only [Fin.sum_univ_succ]
        ring

/-- The second moment of a sum of independent geometric occupations. -/
theorem geometric_sum_second_moment {n : ℕ} (d : Fin n → ℝ)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1) :
    HasSum (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 *
      ∏ i, ((1 - d i) * d i ^ u i))
      ((∑ i, (d i / (1 - d i) + (d i / (1 - d i)) ^ 2)) +
        (∑ i, d i / (1 - d i)) ^ 2) := by
  apply (independent_sum_moments n
    (fun i k => (1 - d i) * d i ^ k)
    (fun i => d i / (1 - d i))
    (fun i => d i / (1 - d i) + (d i / (1 - d i)) ^ 2)
    (fun i k => mul_nonneg (by linarith [hd1 i]) (pow_nonneg (hd0 i) k))
    (fun i => (geometric_moments (hd0 i) (hd1 i)).1)
    (fun i => (geometric_moments (hd0 i) (hd1 i)).2.1)
    (fun i => ?_)).2.2
  convert (geometric_moments (hd0 i) (hd1 i)).2.2 using 1
  ring

/-- The actual diagonal Born weights have the same total photon moments as the eigenmode geometries. -/
theorem hasSum_photon_second_moment {n : ℕ} (R U : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℝ) (hR : R.PosSemidef) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hspec : R = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1) :
    HasSum (fun u : Occupation (Fin n) => (∑ i, (u i : ℝ)) ^ 2 * (fugacityCoeff R u u).re)
      ((∑ i, (d i / (1 - d i) + (d i / (1 - d i)) ^ 2)) +
        (∑ i, d i / (1 - d i)) ^ 2) := by
  have hdet : (1 - R).det = ((∏ i, (1 - d i) : ℝ) : ℂ) := by
    rw [hspec, one_sub_conj U _ hU2, one_sub_diagonal, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, mul_right_comm, ← Matrix.det_mul, hU2, Matrix.det_one, one_mul,
      Complex.ofReal_prod]
  have hpos : 0 < ∏ i, (1 - d i) := Finset.prod_pos fun i _ => by linarith [hd1 i]
  have hx : ∀ u, (fugacityCoeff R u u).re = (∏ i, (1 - d i)) * (gammaFock R u u).re := by
    intro u
    unfold fugacityCoeff
    rw [Matrix.smul_apply, smul_eq_mul, hdet, Complex.re_ofReal_mul]
  have hx0 : ∀ u, 0 ≤ (fugacityCoeff R u u).re := fun u => by
    rw [hx]
    exact mul_nonneg hpos.le (gammaFock_diag_real R hR u).2
  have hsec0 : ∀ N, ∑ u ∈ sec n N, (gammaFock R u u).re =
      ∑ u ∈ sec n N, ∏ i, d i ^ u i := by
    intro N
    have h := sector_trace_comm (U * Matrix.diagonal (fun i => (d i : ℂ))) Uᴴ N
    rw [← hspec, ← Matrix.mul_assoc, hU1, Matrix.one_mul] at h
    rw [← Complex.re_sum, h, Complex.re_sum]
    exact Finset.sum_congr rfl fun u _ => gammaFock_diagonal_re d u
  apply hasSum_of_sector
    (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 * (fugacityCoeff R u u).re)
    (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 * ∏ i, ((1 - d i) * d i ^ u i))
    (fun u => mul_nonneg (sq_nonneg _) (hx0 u))
    (fun u => mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ =>
      mul_nonneg (by linarith [hd1 i]) (pow_nonneg (hd0 i) _)))
    ?_ (geometric_sum_second_moment d hd0 hd1)
  intro N
  have hc : ∀ x : (Fin n → ℕ) → ℝ,
      ∑ u ∈ sec n N, (∑ i, (u i : ℝ)) ^ 2 * ((∏ i, (1 - d i)) * x u) =
        ((N : ℝ) ^ 2 * ∏ i, (1 - d i)) * ∑ u ∈ sec n N, x u := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← Nat.cast_sum, (mem_sec u).mp hu]
    ring
  simp_rw [hx, Finset.prod_mul_distrib]
  rw [hc, hc, hsec0 N]

private lemma diagonal_upper_bound {n : ℕ} (R U : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℝ) (b : ℝ) (hU1 : Uᴴ * U = 1)
    (hspec : R = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)
    (hb : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R).PosSemidef) :
    ∀ i, d i ≤ b := by
  have h := hb.conjTranspose_mul_mul_same U
  have heq : Uᴴ * ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R) * U =
      Matrix.diagonal (fun i => ((b - d i : ℝ) : ℂ)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hU1]
    have heq' : Uᴴ * R * U = Matrix.diagonal (fun i => (d i : ℂ)) := by
      rw [hspec]
      calc Uᴴ * (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) * U =
          (Uᴴ * U) * Matrix.diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
    rw [heq', ← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    congr 1
    ext i
    simp
  rw [heq, Matrix.posSemidef_diagonal_iff] at h
  intro i
  have hi := Complex.zero_le_real.mp (h i)
  linarith

/-- The scalar estimate used in Eq. (92), with room in its numerical constant. -/
theorem occupation_moment_bound {n : ℕ} (ν : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (m : Fin n → ℝ)
    (hm0 : ∀ i, 0 ≤ m i) (hm1 : ∀ i, m i ≤ 2 * ν) :
    (∑ i, (m i + (m i) ^ 2)) + (∑ i, m i) ^ 2 ≤ 12 * ν ^ 2 * n ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  have hnν : 1 ≤ ν * n := (div_le_iff₀ hn0).mp hν
  have hm_sq : ∀ i, (m i) ^ 2 ≤ 4 * ν ^ 2 := by
    intro i
    nlinarith [hm0 i, hm1 i]
  have hv : ∑ i, (m i + (m i) ^ 2) ≤ 6 * ν * n := by
    calc ∑ i, (m i + (m i) ^ 2) ≤ ∑ _i : Fin n, (2 * ν + 4 * ν ^ 2) :=
        Finset.sum_le_sum fun i _ => add_le_add (hm1 i) (hm_sq i)
      _ = (2 * ν + 4 * ν ^ 2) * n := by simp; ring
      _ ≤ 6 * ν * n := by
        apply mul_le_mul_of_nonneg_right _ hn0.le
        nlinarith
  have hsum0 : 0 ≤ ∑ i, m i := Finset.sum_nonneg fun i _ => hm0 i
  have hsum1 : ∑ i, m i ≤ 2 * ν * n := by
    calc ∑ i, m i ≤ ∑ _i : Fin n, 2 * ν := Finset.sum_le_sum fun i _ => hm1 i
      _ = _ := by simp; ring
  have hsquare : (∑ i, m i) ^ 2 ≤ 4 * ν ^ 2 * n ^ 2 := by
    nlinarith
  have hlarge : ν * n ≤ ν ^ 2 * n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnν) (mul_nonneg hν0.le hn0.le)]
  nlinarith [sq_nonneg (ν * n)]

/-- A spectral upper bound implies the required second moment bound for actual photon counting. -/
theorem photon_second_moment_le_of_spectral_bound {n : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef) (hR1 : (1 - R).PosDef)
    (ν : ℝ) (hn : 1 ≤ n) (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1)
    (hupper : (((2 * ν / (1 + 2 * ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R).PosSemidef) :
    ∑' u : Occupation (Fin n), ENNReal.ofReal ((∑ i, (u i : ℝ)) ^ 2) *
      ENNReal.ofReal (fugacityCoeff R u u).re ≤ ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  obtain ⟨U, d, hU1, hU2, hspec, hd0, hd1⟩ := spectral_data R hR hR1
  have hdu := diagonal_upper_bound R U d (2 * ν / (1 + 2 * ν)) hU1 hspec hupper
  have hm0 : ∀ i, 0 ≤ d i / (1 - d i) := fun i => div_nonneg (hd0 i) (by linarith [hd1 i])
  have hmu : ∀ i, d i / (1 - d i) ≤ 2 * ν := by
    intro i
    apply (div_le_iff₀ (by linarith [hd1 i])).mpr
    have h := (le_div_iff₀ (by positivity : 0 < 1 + 2 * ν)).mp (hdu i)
    nlinarith
  have hsum := hasSum_photon_second_moment R U d hR hU1 hU2 hspec hd0 hd1
  have hdet : (1 - R).det = ((∏ i, (1 - d i) : ℝ) : ℂ) := by
    rw [hspec, one_sub_conj U _ hU2, one_sub_diagonal, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, mul_right_comm, ← Matrix.det_mul, hU2, Matrix.det_one, one_mul,
      Complex.ofReal_prod]
  have hx0 : ∀ u, 0 ≤ (fugacityCoeff R u u).re := by
    intro u
    unfold fugacityCoeff
    rw [Matrix.smul_apply, smul_eq_mul, hdet, Complex.re_ofReal_mul]
    exact mul_nonneg (Finset.prod_nonneg fun i _ => by linarith [hd1 i])
      (gammaFock_diag_real R hR u).2
  have htotal : (∑' u : Occupation (Fin n), ENNReal.ofReal ((∑ i, (u i : ℝ)) ^ 2) *
      ENNReal.ofReal (fugacityCoeff R u u).re) =
      ENNReal.ofReal ((∑ i, (d i / (1 - d i) + (d i / (1 - d i)) ^ 2)) +
        (∑ i, d i / (1 - d i)) ^ 2) := by
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
      (fun u => mul_nonneg (sq_nonneg _) (hx0 u)) hsum.summable]
    exact tsum_congr fun u => (ENNReal.ofReal_mul (sq_nonneg _)).symm
  rw [htotal]
  exact ENNReal.ofReal_le_ofReal (occupation_moment_bound ν hn hν hν1 _ hm0 hmu)

theorem opnorm_form {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) (c : ℝ)
    (h : WHMultiplicativity.schattenNorm ⊤ X ≤ c) :
    (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef ∧
      (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef := by
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ ≤ c := by
    simpa [WHMultiplicativity.schattenNorm] using h
  have key : ∀ v : Fin n → ℂ, |(star v ⬝ᵥ (X *ᵥ v)).re| ≤ c * ∑ i, ‖v i‖ ^ 2 := by
    intro v
    set w : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v with hw
    have h1 : inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w) = star v ⬝ᵥ (X *ᵥ v) := by
      rw [hw, Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    have h2 : ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖ ≤ c * ‖w‖ ^ 2 := by
      calc ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖
          ≤ ‖w‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X w‖ := norm_inner_le_norm _ _
        _ ≤ ‖w‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ * ‖w‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ‖w‖ * (c * ‖w‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) (norm_nonneg _)
        _ = c * ‖w‖ ^ 2 := by ring
    have h3 : ‖w‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    rw [h1, h3] at h2
    exact (Complex.abs_re_le_norm _).trans h2
  have hsq : ∀ v : Fin n → ℂ, star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    simp only [dotProduct, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have him : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (X *ᵥ v)).im = 0 := fun v =>
    hX.im_star_dotProduct_mulVec_self v
  have hc1 : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.sub hX) fun v => ?_
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.2]
    · rw [Complex.sub_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, sub_zero]
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.add hX) fun v => ?_
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.1]
    · rw [Complex.add_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, add_zero]


/-- Fugacity matrices in the hard family have eigenvalues at most `2ν/(1+2ν)`. -/
theorem family_spectral_bounds {n : ℕ} (ν ξ : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 32) (X : Herm0 n) (hX : X ∈ Gsupp n) :
    (fugacityFamily ν ξ X).PosSemidef ∧ (1 - fugacityFamily ν ξ X).PosDef ∧
    ((((2 * ν / (1 + 2 * ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) -
      fugacityFamily ν ξ X).PosSemidef := by
  have hXh : (X : Matrix (Fin n) (Fin n) ℂ).IsHermitian := X.2.1
  have hop : WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ 4 := hX
  obtain ⟨hminus, hplus⟩ := opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) hXh 4 hop
  have h14 : 0 < 1 - 4 * ξ := by linarith
  have h14' : 1 - 4 * ξ ≠ 0 := h14.ne'
  have h1ν : 1 + ν ≠ 0 := by positivity
  set r : ℝ := ν / ((1 - 4 * ξ) * (1 + ν)) with hr
  have hrpos : 0 < r := by positivity
  have hrt : r * (1 - 4 * ξ) = ν / (1 + ν) := by
    rw [hr]
    field_simp
  have hRdef : fugacityFamily ν ξ X =
      ((r : ℝ) : ℂ) • (1 + ((ξ : ℝ) : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)) := rfl
  have e1 : fugacityFamily ν ξ X - ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef, ← hrt]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hRν : (fugacityFamily ν ξ X -
      ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    rw [e1]
    exact hplus.smul (Complex.zero_le_real.mpr (by positivity))
  have hRpsd : (fugacityFamily ν ξ X).PosSemidef := by
    have e : fugacityFamily ν ξ X = (fugacityFamily ν ξ X -
        ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
        ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [sub_add_cancel]
    rw [e]
    exact hRν.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by positivity)))
  let b : ℝ := 2 * ν / (1 + 2 * ν)
  have hb1 : b < 1 := by
    dsimp [b]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hr_bound : r * (1 + 4 * ξ) ≤ b := by
    rw [hr, div_mul_eq_mul_div]
    dsimp [b]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hξν : ξ * ν ≤ ξ := by nlinarith
    have hsmall : 0 ≤ 1 - 12 * ξ - 16 * ξ * ν := by nlinarith
    nlinarith [mul_nonneg hν0.le hsmall]
  have heq : (b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - fugacityFamily ν ξ X =
      ((b - r * (1 + 4 * ξ) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
          (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hu : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - fugacityFamily ν ξ X).PosSemidef := by
    rw [heq]
    exact (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hr_bound))).add
      (hminus.smul (Complex.zero_le_real.mpr (by positivity)))
  have hp : (1 - fugacityFamily ν ξ X).PosDef := by
    have he : 1 - fugacityFamily ν ξ X =
        ((1 - b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
          ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - fugacityFamily ν ξ X) := by
      push_cast
      module
    rw [he]
    exact (Matrix.PosDef.one.smul (by exact_mod_cast (sub_pos.mpr hb1))).add_posSemidef hu
  exact ⟨hRpsd, hp, hu⟩

/-- Eq. (92): the actual total photon count in the hard family has second moment at most `12ν²n²`. -/
theorem fugacity_count_second_moment {n : ℕ} (ν ξ : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) :
    ∑' u : Occupation (Fin n), ENNReal.ofReal ((∑ i, (u i : ℝ)) ^ 2) *
      ENNReal.ofReal (fugacityCoeff (fugacityFamily ν ξ X) u u).re ≤
        ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  obtain ⟨hR, hR1, hu⟩ := family_spectral_bounds ν ξ hν0 hν1 hξ hξ32 X hX
  exact photon_second_moment_le_of_spectral_bound _ hR hR1 ν hn hν hν1 hu


/-- Regrouping nonnegative second-moment weights by a count statistic. -/
theorem count_second_moment_regroup {I : Type} (c : I → ℕ) (p : I → ℝ≥0∞) :
    (∑' k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2) *
      ∑' u : I, if c u = k then p u else 0) =
      ∑' u : I, ENNReal.ofReal ((c u : ℝ) ^ 2) * p u := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun u => ?_
  rw [tsum_eq_single (c u)]
  · simp
  · intro k hk
    simp [Ne.symm hk]

/-- Eq. (92) expressed using the distribution of the scalar total photon count. -/
theorem fugacity_count_distribution_second_moment {n : ℕ} (ν ξ : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) :
    ∑' k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2) *
      (∑' u : Occupation (Fin n), if ∑ i, u i = k then
        ENNReal.ofReal (fugacityCoeff (fugacityFamily ν ξ X) u u).re else 0) ≤
          ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) := by
  rw [count_second_moment_regroup]
  simp only [Nat.cast_sum]
  exact fugacity_count_second_moment ν ξ hn hν hν1 hξ hξ32 X hX

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5SectorEffects -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

namespace BosonicLearn.Prop5

/-- Finite sums of lower integrals are bounded by the lower integral
of the sum, even without measurability assumptions. -/
theorem finset_lintegral_le_lintegral_sum
    {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset I) (f : I → Ω → ℝ≥0∞) :
    (∑ i ∈ s, ∫⁻ x, f i x ∂μ) ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- A common likelihood lower bound survives finite nonnegative
mixtures. Cross multiplication avoids zero-denominator edge cases;
lower-integral superadditivity avoids measurable eigenvector choices. -/
theorem finite_mixture_likelihood_bound
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (w b : I → ℝ≥0∞) (f : I → Ω → ℝ≥0∞)
    (ell : ℝ≥0∞) (h : ∀ i, ell * b i ≤ ∫⁻ x, f i x ∂μ) :
    ell * (∑ i, w i * b i) ≤ ∫⁻ x, ∑ i, w i * f i x ∂μ := by
  classical
  calc
    ell * (∑ i, w i * b i) = ∑ i, w i * (ell * b i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ac_rfl
    _ ≤ ∑ i, w i * (∫⁻ x, f i x ∂μ) := by
      gcongr with i
      exact h i
    _ ≤ ∑ i, ∫⁻ x, w i * f i x ∂μ :=
      Finset.sum_le_sum fun i _ => lintegral_const_mul_le (w i) (f i)
    _ ≤ ∫⁻ x, ∑ i, w i * f i x ∂μ :=
      finset_lintegral_le_lintegral_sum μ Finset.univ _

/-- Divide a cross-multiplied likelihood bound by a finite positive
baseline. No measurability of the perturbed likelihood is required. -/
theorem likelihood_ratio_bound_of_cross_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (ell b : ℝ≥0∞) (hb0 : b ≠ 0) (hbfin : b ≠ ⊤)
    (h : ell * b ≤ ∫⁻ x, f x ∂μ) :
    ell ≤ ∫⁻ x, f x / b ∂μ := by
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const' b⁻¹ f (ENNReal.inv_ne_top.mpr hb0)]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbfin)).mpr h

theorem likelihood_cross_bound_of_ratio_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (ell b : ℝ≥0∞) (hb0 : b ≠ 0) (hbfin : b ≠ ⊤)
    (h : ell ≤ ∫⁻ x, f x / b ∂μ) :
    ell * b ≤ ∫⁻ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv] at h
  rw [lintegral_mul_const' b⁻¹ f (ENNReal.inv_ne_top.mpr hb0)] at h
  exact (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbfin)).mp h

/-- Expand a product of finite mixtures into its choice tuples and
apply the same fixed-sector bound to every tuple. This is the algebraic
step extending rank-one product effects to arbitrary positive effects. -/
theorem product_mixture_likelihood_bound
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    {I : J → Type*} [∀ j, Fintype (I j)]
    (μ : Measure Ω) (w b : ∀ j, I j → ℝ≥0∞)
    (f : ∀ j, I j → Ω → ℝ≥0∞) (ell : ℝ≥0∞)
    (h : ∀ choice : ∀ j, I j,
      ell * (∏ j, b j (choice j)) ≤ ∫⁻ x, ∏ j, f j (choice j) x ∂μ) :
    ell * (∏ j, ∑ i, w j i * b j i) ≤
      ∫⁻ x, ∏ j, ∑ i, w j i * f j i x ∂μ := by
  classical
  have hm := finite_mixture_likelihood_bound μ
    (fun choice : ∀ j, I j => ∏ j, w j (choice j))
    (fun choice : ∀ j, I j => ∏ j, b j (choice j))
    (fun choice x => ∏ j, f j (choice j) x) ell h
  have hb : (∑ choice : ∀ j, I j, (∏ j, w j (choice j)) * (∏ j, b j (choice j))) =
      ∏ j, ∑ i, w j i * b j i := by
    simp only [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun j i => w j i * b j i)).symm
  have hf (x : Ω) :
      (∑ choice : ∀ j, I j, (∏ j, w j (choice j)) * (∏ j, f j (choice j) x)) =
        ∏ j, ∑ i, w j i * f j i x := by
    simp only [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun j i => w j i * f j i x)).symm
  simpa only [hb, hf] using hm

/-- Occupation vectors in a fixed total-photon-number sector. -/
abbrev PhotonSector (n k : ℕ) := {u : Occupation (Fin n) // ∑ i, u i = k}

private def sectorFinset (n k : ℕ) : Finset (Occupation (Fin n)) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (k + 1)).filter (fun u => ∑ i, u i = k)

private theorem mem_sectorFinset (n k : ℕ) (u : Occupation (Fin n)) :
    u ∈ sectorFinset n k ↔ ∑ i, u i = k := by
  classical
  unfold sectorFinset
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  rw [Finset.mem_range, ← h]
  have hle : u i ≤ ∑ j, u j :=
    Finset.single_le_sum (f := fun j => u j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

noncomputable instance photonSectorFintype (n k : ℕ) : Fintype (PhotonSector n k) :=
  Fintype.ofFinset (sectorFinset n k) (mem_sectorFinset n k)

/-- Extend a finite-sector vector by zero to the whole Fock basis. -/
noncomputable def extendSector {n k : ℕ} (v : PhotonSector n k → ℂ) : Occupation (Fin n) → ℂ :=
  fun u => if h : ∑ i, u i = k then v ⟨u, h⟩ else 0

theorem extendSector_apply {n k : ℕ} (v : PhotonSector n k → ℂ) (u : PhotonSector n k) :
    extendSector v u = v u := by simp [extendSector, u.property]

theorem extendSector_zero_off_sector {n k : ℕ} (v : PhotonSector n k → ℂ)
    (u : Occupation (Fin n)) (hu : ∑ i, u i ≠ k) : extendSector v u = 0 := by
  simp [extendSector, hu]

theorem extendSector_ne_zero {n k : ℕ} (v : PhotonSector n k → ℂ) (hv : v ≠ 0) :
    extendSector v ≠ 0 := by
  intro hzero
  apply hv
  funext u
  simpa only [extendSector_apply, Pi.zero_apply] using congrFun hzero u

/-- Pointwise spectral decomposition of a positive finite-dimensional
effect into nonnegative weighted rank-one effects. The eigenvectors
are nonzero, including for zero eigenvalues. No measurable dependence
on an external outcome is asserted or needed. -/
theorem positive_effect_rank_one_decomposition
    {I : Type*} [Fintype I] [DecidableEq I]
    (E : Matrix I I ℂ) (hE : E.PosSemidef) :
    ∃ (w : I → ℝ) (v : I → I → ℂ),
      (∀ i, 0 ≤ w i) ∧ (∀ i, v i ≠ 0) ∧
      ∀ a b, E a b = ∑ i, (w i : ℂ) * v i a * star (v i b) := by
  let U : Matrix I I ℂ := hE.isHermitian.eigenvectorUnitary
  let w : I → ℝ := hE.isHermitian.eigenvalues
  have hU : Uᴴ * U = 1 := by
    exact Unitary.coe_star_mul_self hE.isHermitian.eigenvectorUnitary
  have hspec : E = U * Matrix.diagonal (fun i => (w i : ℂ)) * Uᴴ := by
    simpa [U, w, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hE.isHermitian.spectral_theorem
  refine ⟨w, fun i a => U a i, hE.eigenvalues_nonneg, ?_, ?_⟩
  · intro i hzero
    have hdiag := congrFun (congrFun hU i) i
    have hz (a : I) : U a i = 0 := congrFun hzero a
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hz] at hdiag
  · intro a b
    rw [hspec, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    ring

/-- Finite-sector quadratic form, in the ordering used by Proposition 2. -/
def finiteQuadraticForm {I : Type*} [Fintype I]
    (R : Matrix I I ℂ) (v : I → ℂ) : ℝ :=
  (∑ a, ∑ b, star (v a) * R a b * v b).re

/-- The finite matrix block of an occupation-indexed matrix on one
total-photon-number sector. -/
def sectorBlock {n : ℕ} (k : ℕ)
    (R : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) :
    Matrix (PhotonSector n k) (PhotonSector n k) ℂ := fun u v => R u v

/-- Quadratic forms of zero-extended sector vectors involve only a
finite sum, with no convergence assumption on the ambient array. -/
theorem occupation_quadratic_form_eq_sector {n k : ℕ}
    (R : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (v : PhotonSector n k → ℂ) :
    (∑' u, ∑' w, star (extendSector v u) * R u w * extendSector v w).re =
      finiteQuadraticForm (sectorBlock k R) v := by
  have hinner (u : Occupation (Fin n)) :
      (∑' w : PhotonSector n k, star (extendSector v u) * R u w * extendSector v w) =
        ∑' w, star (extendSector v u) * R u w * extendSector v w := by
    apply tsum_subtype_eq_of_support_subset
      (s := {w : Occupation (Fin n) | ∑ i, w i = k})
      (f := fun w => star (extendSector v u) * R u w * extendSector v w)
    intro w hw
    by_contra hnot
    have hz : extendSector v w = 0 := extendSector_zero_off_sector v w hnot
    simpa only [Function.mem_support, hz, mul_zero, ne_eq, not_true_eq_false] using hw
  have houter :
      (∑' u : PhotonSector n k, ∑' w, star (extendSector v u) * R u w * extendSector v w) =
        ∑' u, ∑' w, star (extendSector v u) * R u w * extendSector v w := by
    apply tsum_subtype_eq_of_support_subset
      (s := {u : Occupation (Fin n) | ∑ i, u i = k})
      (f := fun u => ∑' w, star (extendSector v u) * R u w * extendSector v w)
    intro u hu
    by_contra hnot
    have hz : extendSector v u = 0 := extendSector_zero_off_sector v u hnot
    simpa only [Function.mem_support, hz, star_zero, zero_mul, tsum_zero, ne_eq,
      not_true_eq_false] using hu
  rw [← houter, tsum_fintype]
  unfold finiteQuadraticForm
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [← hinner u, tsum_fintype]
  simp only [extendSector_apply, sectorBlock]

/-- Second quantization acts multiplicatively on each finite sector. -/
theorem sector_gammaFock_mul {n : ℕ} (k : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    sectorBlock k (gammaFock (A * B)) =
      sectorBlock k (gammaFock A) * sectorBlock k (gammaFock B) := by
  classical
  ext u v
  simp only [sectorBlock, Matrix.mul_apply, gammaFock_mul, u.property]
  exact Finset.sum_subtype (sectorFinset n k) (mem_sectorFinset n k) _

theorem sector_gammaFock_one {n : ℕ} (k : ℕ) :
    sectorBlock k (gammaFock (1 : Matrix (Fin n) (Fin n) ℂ)) = 1 := by
  classical
  ext u v
  simp only [sectorBlock, (gammaFock_basic (1 : Matrix (Fin n) (Fin n) ℂ) u v).2.2,
    Matrix.one_apply, Subtype.val_inj]

theorem sector_gammaFock_conjTranspose {n : ℕ} (k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    sectorBlock k (gammaFock Aᴴ) = (sectorBlock k (gammaFock A))ᴴ := by
  ext u v
  exact (gammaFock_basic A u v).2.1

open scoped MatrixOrder in
/-- Each sector of the second quantization of a positive matrix is
positive; this follows directly from multiplicativity and adjoints. -/
theorem sector_gammaFock_posSemidef {n : ℕ} (k : ℕ)
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef) :
    (sectorBlock k (gammaFock R)).PosSemidef := by
  obtain ⟨A, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  rw [Matrix.star_eq_conjTranspose, sector_gammaFock_mul, sector_gammaFock_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Strict positivity survives second quantization on every finite
sector. The inverse is the second quantization of the inverse matrix. -/
theorem sector_gammaFock_posDef {n : ℕ} (k : ℕ)
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosDef) :
    (sectorBlock k (gammaFock R)).PosDef := by
  classical
  apply (sector_gammaFock_posSemidef k R hR.posSemidef).posDef_iff_isUnit.mpr
  let A := sectorBlock k (gammaFock R)
  let B := sectorBlock k (gammaFock R⁻¹)
  have hAB : A * B = 1 := by
    rw [← sector_gammaFock_mul, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit), sector_gammaFock_one]
  have hBA : B * A = 1 := by
    rw [← sector_gammaFock_mul, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit), sector_gammaFock_one]
  exact ⟨⟨A, B, hAB, hBA⟩, rfl⟩

/-- Every finite block of a faithful passive Gaussian state is
strictly positive. In particular a nonzero positive sector effect
has a strictly positive probability under this state. -/
theorem sector_fugacityCoeff_posDef {n : ℕ} (k : ℕ)
    (R : Matrix (Fin n) (Fin n) ℂ)
    (hR : R.PosDef) (hIR : (1 - R).PosDef) :
    (sectorBlock k (fugacityCoeff R)).PosDef := by
  have h : sectorBlock k (fugacityCoeff R) =
      (1 - R).det • sectorBlock k (gammaFock R) := rfl
  rw [h]
  exact (sector_gammaFock_posDef k R hR).smul hIR.det_pos

theorem sector_fugacityCoeff_posSemidef {n : ℕ} (k : ℕ)
    (R : Matrix (Fin n) (Fin n) ℂ)
    (hR : R.PosSemidef) (hIR : (1 - R).PosSemidef) :
    (sectorBlock k (fugacityCoeff R)).PosSemidef := by
  have h : sectorBlock k (fugacityCoeff R) =
      (1 - R).det • sectorBlock k (gammaFock R) := rfl
  rw [h]
  exact (sector_gammaFock_posSemidef k R hR).smul hIR.det_nonneg

/-- All fugacity matrices in the hard family are strictly positive,
with the same lower spectral bound `ν/(1+ν)` as the scalar family. -/
theorem family_posDef {n : ℕ} (ν ξ : ℝ) (hν : 0 < ν)
    (hξ : 0 ≤ ξ) (hξlt : ξ < 1 / 4) (X : Herm0 n) (hX : X ∈ Gsupp n) :
    (fugacityFamily ν ξ X).PosDef := by
  have hplus := (opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) X.2.1 4 hX).2
  have h14 : 0 < 1 - 4 * ξ := by linarith
  have h1ν : 0 < 1 + ν := by linarith
  let r : ℝ := ν / ((1 - 4 * ξ) * (1 + ν))
  have hr : 0 < r := div_pos hν (mul_pos h14 h1ν)
  have hrt : r * (1 - 4 * ξ) = ν / (1 + ν) := by
    dsimp [r]
    field_simp
  have he : fugacityFamily ν ξ X =
      ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
      ((r * ξ : ℝ) : ℂ) • ((4 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (X : Matrix (Fin n) (Fin n) ℂ)) := by
    change ((r : ℝ) : ℂ) • (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)) = _
    rw [← hrt]
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [he]
  exact (Matrix.PosDef.one.smul (by exact_mod_cast (div_pos hν h1ν))).add_posSemidef
    (hplus.smul (Complex.zero_le_real.mpr (mul_nonneg hr.le hξ)))

theorem family_sector_posDef {n : ℕ} (ν ξ : ℝ) (hν : 0 < ν) (hνhi : ν ≤ 1)
    (hξ : 0 < ξ) (hξhi : ξ < 1 / 32) (X : Herm0 n) (hX : X ∈ Gsupp n) (k : ℕ) :
    (sectorBlock k (fugacityCoeff (fugacityFamily ν ξ X))).PosDef :=
  sector_fugacityCoeff_posDef k _ (family_posDef ν ξ hν hξ.le (by linarith) X hX)
    (family_spectral_bounds ν ξ hν hνhi hξ hξhi X hX).2.1

theorem finiteQuadraticForm_nonneg {I : Type*} [Fintype I]
    (R : Matrix I I ℂ) (hR : R.PosSemidef) (v : I → ℂ) :
    0 ≤ finiteQuadraticForm R v := by
  simpa [finiteQuadraticForm, dotProduct, Matrix.mulVec, Finset.mul_sum,
    Pi.star_apply, mul_assoc] using hR.re_dotProduct_nonneg v

theorem finiteQuadraticForm_pos {I : Type*} [Fintype I]
    (R : Matrix I I ℂ) (hR : R.PosDef) (v : I → ℂ) (hv : v ≠ 0) :
    0 < finiteQuadraticForm R v := by
  simpa [finiteQuadraticForm, dotProduct, Matrix.mulVec, Finset.mul_sum,
    Pi.star_apply, mul_assoc] using hR.re_dotProduct_pos hv

/-- The Born pairing of a finite effect is the corresponding weighted
sum of its rank-one quadratic forms. -/
theorem effect_pairing_of_rank_one_decomposition
    {I J : Type*} [Fintype I] [Fintype J]
    (E R : Matrix I I ℂ) (w : J → ℝ) (v : J → I → ℂ)
    (hE : ∀ a b, E a b = ∑ j, (w j : ℂ) * v j a * star (v j b)) :
    (E * R).trace.re = ∑ j, w j * finiteQuadraticForm R (v j) := by
  have hc : (E * R).trace =
      ∑ j, (w j : ℂ) * ∑ a, ∑ b, star (v j a) * R a b * v j b := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hE, Finset.sum_mul]
    calc
      (∑ a, ∑ b, ∑ j, (w j : ℂ) * v j a * star (v j b) * R b a) =
          ∑ j, ∑ a, ∑ b, (w j : ℂ) * v j a * star (v j b) * R b a := by
        conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
      _ = ∑ j, (w j : ℂ) * ∑ a, ∑ b, star (v j a) * R a b * v j b := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
  rw [hc]
  simp [finiteQuadraticForm, Complex.mul_re]

/-- A nonzero positive effect has strictly positive probability against
a positive-definite state on the finite sector. -/
theorem positive_effect_pairing_pos {I : Type*} [Fintype I] [DecidableEq I]
    (E R : Matrix I I ℂ) (hE : E.PosSemidef) (hEne : E ≠ 0) (hR : R.PosDef) :
    0 < (E * R).trace.re := by
  obtain ⟨w, v, hw, hv, hdec⟩ := positive_effect_rank_one_decomposition E hE
  rw [effect_pairing_of_rank_one_decomposition E R w v hdec]
  have hweight : ∃ i, 0 < w i := by
    by_contra h
    have hwzero (i : I) : w i = 0 := le_antisymm (not_lt.mp (not_exists.mp h i)) (hw i)
    apply hEne
    ext a b
    rw [hdec]
    simp [hwzero]
  obtain ⟨i, hi⟩ := hweight
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j)
    (finiteQuadraticForm_pos R hR (v j) (hv j)).le)
    ⟨i, Finset.mem_univ i, mul_pos hi (finiteQuadraticForm_pos R hR (v i) (hv i))⟩

theorem positive_effect_pairing_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (E R : Matrix I I ℂ) (hE : E.PosSemidef) (hR : R.PosSemidef) :
    0 ≤ (E * R).trace.re := by
  obtain ⟨w, v, hw, _, hdec⟩ := positive_effect_rank_one_decomposition E hE
  rw [effect_pairing_of_rank_one_decomposition E R w v hdec]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (finiteQuadraticForm_nonneg R hR (v i))

theorem ofReal_effect_pairing_decomposition
    {I J : Type*} [Fintype I] [Fintype J]
    (E R : Matrix I I ℂ) (hR : R.PosSemidef) (w : J → ℝ) (v : J → I → ℂ)
    (hw : ∀ j, 0 ≤ w j)
    (hdec : ∀ a b, E a b = ∑ j, (w j : ℂ) * v j a * star (v j b)) :
    ENNReal.ofReal (E * R).trace.re =
      ∑ j, ENNReal.ofReal (w j) * ENNReal.ofReal (finiteQuadraticForm R (v j)) := by
  rw [effect_pairing_of_rank_one_decomposition E R w v hdec,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hw j)
      (finiteQuadraticForm_nonneg R hR (v j)))]
  exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_mul (hw j)

theorem ofReal_product_ratio {J : Type*} [Fintype J]
    (a b : J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 < b j) :
    ENNReal.ofReal (∏ j, a j / b j) =
      (∏ j, ENNReal.ofReal (a j)) / (∏ j, ENNReal.ofReal (b j)) := by
  rw [Finset.prod_div_distrib,
    ENNReal.ofReal_div_of_pos (Finset.prod_pos fun j _ => hb j),
    ENNReal.ofReal_prod_of_nonneg (fun j _ => ha j),
    ENNReal.ofReal_prod_of_nonneg (fun j _ => (hb j).le)]

/-- The cross-multiplied form needs neither faithful states nor
nonzero effects, and is the form used to compare transcript measures. -/
theorem product_positive_effect_cross_bound
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    {I : J → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (μ : Measure Ω) (R₀ E : ∀ j, Matrix (I j) (I j) ℂ)
    (R : ∀ j, Ω → Matrix (I j) (I j) ℂ)
    (hR₀ : ∀ j, (R₀ j).PosSemidef) (hE : ∀ j, (E j).PosSemidef)
    (hR : ∀ᵐ x ∂μ, ∀ j, (R j x).PosSemidef)
    (ell : ℝ≥0∞)
    (hvector : ∀ v : ∀ j, I j → ℂ, (∀ j, v j ≠ 0) →
      ell * (∏ j, ENNReal.ofReal (finiteQuadraticForm (R₀ j) (v j))) ≤
        ∫⁻ x, ∏ j, ENNReal.ofReal (finiteQuadraticForm (R j x) (v j)) ∂μ) :
    ell * (∏ j, ENNReal.ofReal (E j * R₀ j).trace.re) ≤
      ∫⁻ x, ∏ j, ENNReal.ofReal (E j * R j x).trace.re ∂μ := by
  classical
  choose w v hw hv hdec using fun j => positive_effect_rank_one_decomposition (E j) (hE j)
  have h := product_mixture_likelihood_bound μ
    (fun j i => ENNReal.ofReal (w j i))
    (fun j i => ENNReal.ofReal (finiteQuadraticForm (R₀ j) (v j i)))
    (fun j i x => ENNReal.ofReal (finiteQuadraticForm (R j x) (v j i))) ell
    (fun choice => hvector (fun j => v j (choice j)) (fun j => hv j (choice j)))
  have hbase : (∏ j, ∑ i, ENNReal.ofReal (w j i) *
      ENNReal.ofReal (finiteQuadraticForm (R₀ j) (v j i))) =
      ∏ j, ENNReal.ofReal (E j * R₀ j).trace.re := by
    apply Finset.prod_congr rfl
    intro j _
    exact (ofReal_effect_pairing_decomposition (E j) (R₀ j) (hR₀ j)
      (w j) (v j) (hw j) (hdec j)).symm
  have hpert : (fun x => ∏ j, ∑ i, ENNReal.ofReal (w j i) *
      ENNReal.ofReal (finiteQuadraticForm (R j x) (v j i))) =ᵐ[μ]
      (fun x => ∏ j, ENNReal.ofReal (E j * R j x).trace.re) := by
    filter_upwards [hR] with x hx
    apply Finset.prod_congr rfl
    intro j _
    exact (ofReal_effect_pairing_decomposition (E j) (R j x) (hx j)
      (w j) (v j) (hw j) (hdec j)).symm
  rwa [hbase, lintegral_congr_ae hpert] at h

/-- A product-vector likelihood bound extends to a product of arbitrary
nonzero positive effects on finite sectors. Spectral decompositions are
chosen separately for this fixed transcript, with no measurability
requirement on those choices. The perturbed states need only be positive
almost everywhere under the perturbation measure. -/
theorem product_positive_effect_likelihood_bound
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    {I : J → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (μ : Measure Ω) (R₀ E : ∀ j, Matrix (I j) (I j) ℂ)
    (R : ∀ j, Ω → Matrix (I j) (I j) ℂ)
    (hR₀ : ∀ j, (R₀ j).PosDef) (hE : ∀ j, (E j).PosSemidef)
    (hEne : ∀ j, E j ≠ 0)
    (hR : ∀ᵐ x ∂μ, ∀ j, (R j x).PosSemidef)
    (ell : ℝ≥0∞)
    (hvector : ∀ v : ∀ j, I j → ℂ, (∀ j, v j ≠ 0) →
      ell ≤ ∫⁻ x, ENNReal.ofReal (∏ j,
        finiteQuadraticForm (R j x) (v j) / finiteQuadraticForm (R₀ j) (v j)) ∂μ) :
    ell ≤ ∫⁻ x, ENNReal.ofReal (∏ j,
      (E j * R j x).trace.re / (E j * R₀ j).trace.re) ∂μ := by
  classical
  choose w v hw hv hdec using fun j => positive_effect_rank_one_decomposition (E j) (hE j)
  let w' : ∀ j, I j → ℝ≥0∞ := fun j i => ENNReal.ofReal (w j i)
  let b : ∀ j, I j → ℝ≥0∞ := fun j i =>
    ENNReal.ofReal (finiteQuadraticForm (R₀ j) (v j i))
  let f : ∀ j, I j → Ω → ℝ≥0∞ := fun j i x =>
    ENNReal.ofReal (finiteQuadraticForm (R j x) (v j i))
  have hbase (j : J) (i : I j) : 0 < finiteQuadraticForm (R₀ j) (v j i) :=
    finiteQuadraticForm_pos (R₀ j) (hR₀ j) (v j i) (hv j i)
  have hchoice (choice : ∀ j, I j) :
      ell * (∏ j, b j (choice j)) ≤ ∫⁻ x, ∏ j, f j (choice j) x ∂μ := by
    have hbprod : (∏ j, b j (choice j)) =
        ENNReal.ofReal (∏ j, finiteQuadraticForm (R₀ j) (v j (choice j))) := by
      symm
      exact ENNReal.ofReal_prod_of_nonneg (fun j _ => (hbase j (choice j)).le)
    have hdenpos : 0 < ∏ j, finiteQuadraticForm (R₀ j) (v j (choice j)) :=
      Finset.prod_pos fun j _ => hbase j (choice j)
    apply likelihood_cross_bound_of_ratio_bound μ (fun x => ∏ j, f j (choice j) x) ell
      (∏ j, b j (choice j))
      (by rw [hbprod]; exact ne_of_gt (ENNReal.ofReal_pos.mpr hdenpos))
      (by rw [hbprod]; exact ENNReal.ofReal_ne_top)
    have heq :
        (fun x => ENNReal.ofReal (∏ j,
          finiteQuadraticForm (R j x) (v j (choice j)) /
            finiteQuadraticForm (R₀ j) (v j (choice j)))) =ᵐ[μ]
        (fun x => (∏ j, f j (choice j) x) / (∏ j, b j (choice j))) := by
      filter_upwards [hR] with x hx
      exact ofReal_product_ratio _ _ (fun j =>
        finiteQuadraticForm_nonneg (R j x) (hx j) _) (fun j => hbase j (choice j))
    rw [← lintegral_congr_ae heq]
    exact hvector (fun j => v j (choice j)) (fun j => hv j (choice j))
  have hcross := product_mixture_likelihood_bound μ w' b f ell hchoice
  let B : ℝ≥0∞ := ∏ j, ∑ i, w' j i * b j i
  let F : Ω → ℝ≥0∞ := fun x => ∏ j, ∑ i, w' j i * f j i x
  have hB : B = ENNReal.ofReal (∏ j, (E j * R₀ j).trace.re) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ =>
      (positive_effect_pairing_pos (E j) (R₀ j) (hE j) (hEne j) (hR₀ j)).le)]
    apply Finset.prod_congr rfl
    intro j _
    exact (ofReal_effect_pairing_decomposition (E j) (R₀ j) (hR₀ j).posSemidef
      (w j) (v j) (hw j) (hdec j)).symm
  have hBpos : 0 < ∏ j, (E j * R₀ j).trace.re :=
    Finset.prod_pos fun j _ => positive_effect_pairing_pos (E j) (R₀ j) (hE j) (hEne j) (hR₀ j)
  have hratio : ell ≤ ∫⁻ x, F x / B ∂μ :=
    likelihood_ratio_bound_of_cross_bound μ F ell B
      (by rw [hB]; exact ne_of_gt (ENNReal.ofReal_pos.mpr hBpos))
      (by rw [hB]; exact ENNReal.ofReal_ne_top) hcross
  have heq : (fun x => ENNReal.ofReal (∏ j,
      (E j * R j x).trace.re / (E j * R₀ j).trace.re)) =ᵐ[μ] (fun x => F x / B) := by
    filter_upwards [hR] with x hx
    rw [ofReal_product_ratio _ _
      (fun j => positive_effect_pairing_nonneg (E j) (R j x) (hE j) (hx j))
      (fun j => positive_effect_pairing_pos (E j) (R₀ j) (hE j) (hEne j) (hR₀ j))]
    congr 1
    · apply Finset.prod_congr rfl
      intro j _
      exact ofReal_effect_pairing_decomposition (E j) (R j x) (hx j)
        (w j) (v j) (hw j) (hdec j)
    · symm
      apply Finset.prod_congr rfl
      intro j _
      exact (ofReal_effect_pairing_decomposition (E j) (R₀ j) (hR₀ j).posSemidef
        (w j) (v j) (hw j) (hdec j)).symm
  rwa [← lintegral_congr_ae heq] at hratio

/-- Direct connection to Proposition 2's formulation with infinite
occupation-indexed quadratic forms. A fixed-sector rank-one bound
extends to arbitrary nonzero positive effects in those sectors. -/
theorem occupation_rank_one_bound_to_sector_effects
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n N : ℕ) (k : Fin N → ℕ)
    (R₀ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (R : Ω → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (E : ∀ t, Matrix (PhotonSector n (k t)) (PhotonSector n (k t)) ℂ)
    (hR₀ : ∀ t, (sectorBlock (k t) R₀).PosDef)
    (hE : ∀ t, (E t).PosSemidef) (hEne : ∀ t, E t ≠ 0)
    (hR : ∀ᵐ x ∂μ, ∀ t, (sectorBlock (k t) (R x)).PosSemidef)
    (ell : ℝ≥0∞)
    (hsector : ∀ ϕ : Fin N → Occupation (Fin n) → ℂ,
      (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
      ell ≤ ∫⁻ x, ENNReal.ofReal (∏ t,
        (∑' u, ∑' w, star (ϕ t u) * R x u w * ϕ t w).re /
        (∑' u, ∑' w, star (ϕ t u) * R₀ u w * ϕ t w).re) ∂μ) :
    ell ≤ ∫⁻ x, ENNReal.ofReal (∏ t,
      (E t * sectorBlock (k t) (R x)).trace.re /
      (E t * sectorBlock (k t) R₀).trace.re) ∂μ := by
  apply product_positive_effect_likelihood_bound μ (fun t => sectorBlock (k t) R₀) E
    (fun t x => sectorBlock (k t) (R x)) hR₀ hE hEne hR ell
  intro v hv
  have h := hsector (fun t => extendSector (v t))
    (fun t u hu => extendSector_zero_off_sector (v t) u hu)
    (fun t => extendSector_ne_zero (v t) (hv t))
  simpa only [occupation_quadratic_form_eq_sector] using h

/-- The measure-comparison form of the sector-effect extension.
Zero effects are allowed: their baseline weight is zero, so the
cross-multiplied lower bound remains meaningful. -/
theorem occupation_rank_one_bound_to_sector_effects_cross
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n N : ℕ) (k : Fin N → ℕ)
    (R₀ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (R : Ω → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (E : ∀ t, Matrix (PhotonSector n (k t)) (PhotonSector n (k t)) ℂ)
    (hR₀ : ∀ t, (sectorBlock (k t) R₀).PosDef)
    (hE : ∀ t, (E t).PosSemidef)
    (hR : ∀ᵐ x ∂μ, ∀ t, (sectorBlock (k t) (R x)).PosSemidef)
    (ell : ℝ≥0∞)
    (hsector : ∀ ϕ : Fin N → Occupation (Fin n) → ℂ,
      (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
      ell ≤ ∫⁻ x, ENNReal.ofReal (∏ t,
        (∑' u, ∑' w, star (ϕ t u) * R x u w * ϕ t w).re /
        (∑' u, ∑' w, star (ϕ t u) * R₀ u w * ϕ t w).re) ∂μ) :
    ell * (∏ t, ENNReal.ofReal (E t * sectorBlock (k t) R₀).trace.re) ≤
      ∫⁻ x, ∏ t, ENNReal.ofReal (E t * sectorBlock (k t) (R x)).trace.re ∂μ := by
  apply product_positive_effect_cross_bound μ (fun t => sectorBlock (k t) R₀) E
    (fun t x => sectorBlock (k t) (R x)) (fun t => (hR₀ t).posSemidef) hE hR ell
  intro v hv
  have hbpos (t : Fin N) : 0 < finiteQuadraticForm (sectorBlock (k t) R₀) (v t) :=
    finiteQuadraticForm_pos _ (hR₀ t) _ (hv t)
  have hbne : (∏ t, ENNReal.ofReal (finiteQuadraticForm (sectorBlock (k t) R₀) (v t))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro t _
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (hbpos t))
  have hbfin : (∏ t, ENNReal.ofReal (finiteQuadraticForm (sectorBlock (k t) R₀) (v t))) ≠ ∞ :=
    ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  apply likelihood_cross_bound_of_ratio_bound μ _ ell _ hbne hbfin
  have hs := hsector (fun t => extendSector (v t))
    (fun t u hu => extendSector_zero_off_sector (v t) u hu)
    (fun t => extendSector_ne_zero (v t) (hv t))
  simp only [occupation_quadratic_form_eq_sector] at hs
  have heq : (fun x => ENNReal.ofReal (∏ t,
      finiteQuadraticForm (sectorBlock (k t) (R x)) (v t) /
        finiteQuadraticForm (sectorBlock (k t) R₀) (v t))) =ᵐ[μ]
      (fun x => (∏ t, ENNReal.ofReal (finiteQuadraticForm (sectorBlock (k t) (R x)) (v t))) /
        (∏ t, ENNReal.ofReal (finiteQuadraticForm (sectorBlock (k t) R₀) (v t)))) := by
    filter_upwards [hR] with x hx
    exact ofReal_product_ratio _ _ (fun t => finiteQuadraticForm_nonneg _ (hx t) _) hbpos
  rwa [← lintegral_congr_ae heq]

/-- Proposition 2 for positive finite-sector effects. The two matrix
positivity hypotheses are displayed explicitly so this theorem can be
used independently of the separate fugacity-faithfulness arguments. -/
theorem proposition_2_sector_effects :
    ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 →
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ X₀ ∈ Ggood n,
      ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∀ (N : ℕ) (k : Fin N → ℕ)
        (E : ∀ t, Matrix (PhotonSector n (k t)) (PhotonSector n (k t)) ℂ),
        (∀ t, (E t).PosSemidef) → (∀ t, E t ≠ 0) →
        (∀ t, (sectorBlock (k t) (fugacityCoeff (fugacityFamily ν ξ X₀))).PosDef) →
        (∀ᵐ Z ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b),
          ∀ t, (sectorBlock (k t) (fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)))).PosSemidef) →
        ENNReal.ofReal (Real.exp
          (-(C * ξ ^ 2 * ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)))) ≤
          ∫⁻ Z, ENNReal.ofReal (∏ t,
            (E t * sectorBlock (k t) (fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)))).trace.re /
            (E t * sectorBlock (k t) (fugacityCoeff (fugacityFamily ν ξ X₀))).trace.re)
            ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) := by
  obtain ⟨C, hC, ξ₀, hξ₀, hξ₀lt, hfixed⟩ := proposition_2
  refine ⟨C, hC, ξ₀, hξ₀, hξ₀lt, ?_⟩
  intro n hn ν hνlo hνhi ξ hξlo hξhi X₀ hX₀ b hbpos hbhi N k E hE hEne hR₀ hR
  apply occupation_rank_one_bound_to_sector_effects
    (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) n N k
    (fugacityCoeff (fugacityFamily ν ξ X₀))
    (fun Z => fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z))) E hR₀ hE hEne hR
  exact fun ϕ => hfixed n hn ν hνlo hνhi ξ hξlo hξhi X₀ hX₀ b hbpos hbhi N k ϕ

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5PhotonStates -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

noncomputable section
namespace BosonicLearn.Prop5

/-- Compression to a finite set of Fock basis vectors, retained as an
array on the full Hilbert space. -/
def finiteCut {I : Type} [DecidableEq I] (s : Finset I) (ρ : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => if i ∈ s then if j ∈ s then ρ i j else 0 else 0

/-- The mass of the finite compression. -/
def finiteCutMass {I : Type} (s : Finset I) (ρ : Matrix I I ℂ) : ℝ :=
  ∑ i ∈ s, (ρ i i).re

/-- Normalized finite compression. It is used only when its mass is positive. -/
def normalizedFiniteCut {I : Type} [DecidableEq I] (s : Finset I)
    (ρ : Matrix I I ℂ) : Matrix I I ℂ :=
  ((finiteCutMass s ρ)⁻¹ : ℂ) • finiteCut s ρ

theorem normalizedFiniteCut_isDensity {I : Type} [Countable I] [DecidableEq I]
    (s : Finset I) (ρ : Matrix I I ℂ) (hρ : IsDensity ρ)
    (hmass : 0 < finiteCutMass s ρ) : IsDensity (normalizedFiniteCut s ρ) := by
  apply isDensity_of_posSemidef
  · intro t z
    have he : ∑ i ∈ t, ∑ j ∈ t, star (z i) * normalizedFiniteCut s ρ i j * z j =
        (((finiteCutMass s ρ)⁻¹ : ℝ) : ℂ) *
        (∑ i ∈ t, ∑ j ∈ t,
          star (if i ∈ s then z i else 0) * ρ i j * (if j ∈ s then z j else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;>
        simp [normalizedFiniteCut, finiteCut, hi, hj] <;> ring
    rw [he]
    obtain ⟨him, hre⟩ := hρ.2.1 t (fun i => if i ∈ s then z i else 0)
    constructor
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, him, mul_zero]
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (inv_nonneg.mpr hmass.le) hre
  · apply summable_of_ne_finset_zero (s := s)
    intro i hi
    simp [normalizedFiniteCut, finiteCut, hi]
  · rw [tsum_eq_sum (s := s) (fun i hi => by simp [normalizedFiniteCut, finiteCut, hi])]
    have he : ∑ i ∈ s, (normalizedFiniteCut s ρ i i).re =
        (finiteCutMass s ρ)⁻¹ * finiteCutMass s ρ := by
      calc
        _ = ∑ i ∈ s, (finiteCutMass s ρ)⁻¹ * (ρ i i).re := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [normalizedFiniteCut, finiteCut, hi]
        _ = _ := by rw [← Finset.mul_sum]; rfl
    rw [he, inv_mul_cancel₀ hmass.ne']

/-- The Born pairing with a normalized compression is a finite sum. -/
theorem normalizedFiniteCut_born {I : Type} [DecidableEq I]
    (s : Finset I) (ρ E : Matrix I I ℂ) :
    (∑' i, ∑' j, E i j * normalizedFiniteCut s ρ j i).re =
      (finiteCutMass s ρ)⁻¹ * (∑ i ∈ s, ∑ j ∈ s, E i j * ρ j i).re := by
  have hinner (i : I) : (∑' j, E i j * normalizedFiniteCut s ρ j i) =
      ∑ j ∈ s, E i j * normalizedFiniteCut s ρ j i := by
    apply tsum_eq_sum
    intro j hj
    simp [normalizedFiniteCut, finiteCut, hj]
  rw [tsum_congr hinner, tsum_eq_sum (s := s) (fun i hi => by
    apply Finset.sum_eq_zero
    intro j hj
    simp [normalizedFiniteCut, finiteCut, hi])]
  have he : (∑ i ∈ s, ∑ j ∈ s, E i j * normalizedFiniteCut s ρ j i) =
      (((finiteCutMass s ρ)⁻¹ : ℝ) : ℂ) * (∑ i ∈ s, ∑ j ∈ s, E i j * ρ j i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [normalizedFiniteCut, finiteCut, hi, hj]
    ring
  rw [he]
  simp

/-- A finite set listing exactly the photon-number sector. -/
def photonSectorSet (n k : ℕ) : Finset (Occupation (Fin n)) :=
  (Finset.univ : Finset (PhotonSector n k)).map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_photonSectorSet (n k : ℕ) (u : Occupation (Fin n)) :
    u ∈ photonSectorSet n k ↔ ∑ i, u i = k := by
  simp only [photonSectorSet, Finset.mem_map, Finset.mem_univ, true_and]
  exact ⟨fun ⟨v, hv⟩ => hv ▸ v.property, fun hu => ⟨⟨u, hu⟩, rfl⟩⟩

theorem sum_photonSectorSet {n k : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Occupation (Fin n) → α) :
    ∑ u ∈ photonSectorSet n k, f u = ∑ u : PhotonSector n k, f u := by
  simp [photonSectorSet]

theorem photonSector_nonempty (n : ℕ) (hn : 1 ≤ n) (k : ℕ) : Nonempty (PhotonSector n k) := by
  letI : NeZero n := ⟨by omega⟩
  exact ⟨⟨Pi.single (0 : Fin n) k, by simp⟩⟩

theorem photonSector_mass_pos {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (hρ : (sectorBlock k ρ).PosDef) : 0 < finiteCutMass (photonSectorSet n k) ρ := by
  letI := photonSector_nonempty n hn k
  have h := hρ.trace_pos
  change 0 < (sectorBlock k ρ).trace at h
  have hr := Complex.pos_iff.mp h
  simpa [finiteCutMass, sum_photonSectorSet, Matrix.trace, Matrix.diag, sectorBlock] using hr.1

theorem density_diagonal_nonneg {I : Type} [DecidableEq I]
    (ρ : Matrix I I ℂ) (hρ : IsDensity ρ) (u : I) : 0 ≤ (ρ u u).re := by
  simpa using (hρ.2.1 {u} (fun _ => 1)).2

theorem photon_mass_nonneg {n : ℕ}
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (hρ : IsDensity ρ) (k : ℕ) :
    0 ≤ finiteCutMass (photonSectorSet n k) ρ :=
  Finset.sum_nonneg (fun u _ => density_diagonal_nonneg ρ hρ u)

theorem photon_mass_hasSum {n : ℕ}
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (hρ : IsDensity ρ) :
    HasSum (fun k => finiteCutMass (photonSectorSet n k) ρ) 1 := by
  have hs : HasSum (fun u => (ρ u u).re) 1 := hρ.2.2.2 ▸ hρ.2.2.1.hasSum
  let c : Occupation (Fin n) → ℕ := fun u => ∑ i, u i
  have hσ := (Equiv.sigmaFiberEquiv c).hasSum_iff.mpr hs
  apply hσ.sigma
  intro k
  change HasSum (fun u : PhotonSector n k => (ρ u u).re) _
  rw [finiteCutMass, sum_photonSectorSet]
  exact hasSum_fintype _

theorem photon_weights_sum_one {n : ℕ}
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (hρ : IsDensity ρ) :
    (∑' k, ENNReal.ofReal (finiteCutMass (photonSectorSet n k) ρ)) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (photon_mass_nonneg ρ hρ)
    (photon_mass_hasSum ρ hρ).summable, (photon_mass_hasSum ρ hρ).tsum_eq]
  simp

theorem photon_mass_eq_count_weight {n : ℕ}
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (hρ : IsDensity ρ) (k : ℕ) :
    ENNReal.ofReal (finiteCutMass (photonSectorSet n k) ρ) =
      ∑' u : Occupation (Fin n), if ∑ i, u i = k then ENNReal.ofReal (ρ u u).re else 0 := by
  rw [tsum_eq_sum (s := photonSectorSet n k) (fun u hu => by
    simp only [mem_photonSectorSet] at hu
    simp [hu])]
  rw [finiteCutMass, ENNReal.ofReal_sum_of_nonneg
    (fun u _ => density_diagonal_nonneg ρ hρ u)]
  apply Finset.sum_congr rfl
  intro u hu
  simp [(mem_photonSectorSet n k u).mp hu]

theorem family_sector_mass_second_moment {n : ℕ} (ν ξ : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) :
    ∑' k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2) *
      ENNReal.ofReal (finiteCutMass (photonSectorSet n k) (fugacityCoeff (fugacityFamily ν ξ X))) ≤
        ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  have hR := family_spectral_bounds ν ξ hν0 hν1 hξ hξ32 X hX
  have hρ := fugacityCoeff_isDensity _ hR.1 hR.2.1
  simp_rw [photon_mass_eq_count_weight _ hρ]
  exact fugacity_count_distribution_second_moment ν ξ hn hν hν1 hξ hξ32 X hX

/-- One photon-sector label has expected likelihood cost at most
`13 n ν²`, combining normalization with the physical second moment. -/
theorem family_sector_cost_mean {n : ℕ} (ν ξ : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) :
    ∑' k : ℕ,
      ENNReal.ofReal (finiteCutMass (photonSectorSet n k) (fugacityCoeff (fugacityFamily ν ξ X))) *
        ENNReal.ofReal ((n : ℝ) * ν ^ 2 + (k : ℝ) ^ 2 / n) ≤
          ENNReal.ofReal (13 * n * ν ^ 2) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  have hR := family_spectral_bounds ν ξ hν0 hν1 hξ hξ32 X hX
  have hρ := fugacityCoeff_isDensity _ hR.1 hR.2.1
  let w : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (finiteCutMass (photonSectorSet n k) (fugacityCoeff (fugacityFamily ν ξ X)))
  have hw : ∑' k, w k = 1 := photon_weights_sum_one _ hρ
  have hm : (∑' k, w k * ENNReal.ofReal ((k : ℝ) ^ 2)) ≤
      ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) := by
    simpa only [mul_comm] using family_sector_mass_second_moment ν ξ hn hν hν1 hξ hξ32 X hX
  change (∑' k, w k * ENNReal.ofReal ((n : ℝ) * ν ^ 2 + (k : ℝ) ^ 2 / n)) ≤ _
  have hsplit (k : ℕ) : ENNReal.ofReal ((n : ℝ) * ν ^ 2 + (k : ℝ) ^ 2 / n) =
      ENNReal.ofReal ((n : ℝ) * ν ^ 2) + ENNReal.ofReal ((k : ℝ) ^ 2) / ENNReal.ofReal n := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_div_of_pos hn0]
  simp_rw [hsplit, mul_add, div_eq_mul_inv, ← mul_assoc]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hw, one_mul, ENNReal.tsum_mul_right]
  calc
    _ ≤ ENNReal.ofReal ((n : ℝ) * ν ^ 2) +
        ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) * (ENNReal.ofReal n)⁻¹ := by gcongr
    _ = ENNReal.ofReal (13 * n * ν ^ 2) := by
      rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hn0,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp
      ring

/-- The full hidden photon record has the quantitative mean-cost
certificate needed by likelihood coarsening. -/
theorem family_photon_record_cost_mean {n : ℕ} (N : ℕ) (ν ξ : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) :
    ∑' k : Fin N → ℕ,
      (∏ t, ENNReal.ofReal
        (finiteCutMass (photonSectorSet n (k t)) (fugacityCoeff (fugacityFamily ν ξ X)))) *
      ENNReal.ofReal (∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)) ≤
        ENNReal.ofReal (13 * N * n * ν ^ 2) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  have hR := family_spectral_bounds ν ξ hν0 hν1 hξ hξ32 X hX
  have hρ := fugacityCoeff_isDensity _ hR.1 hR.2.1
  have hsplit (k : Fin N → ℕ) :
      ENNReal.ofReal (∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)) =
      ∑ t, ENNReal.ofReal ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n) :=
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)
  simp_rw [hsplit]
  rw [record_additive_cost_mean _
    (fun k : ℕ => ENNReal.ofReal ((n : ℝ) * ν ^ 2 + (k : ℝ) ^ 2 / n))
    (photon_weights_sum_one _ hρ) N]
  calc
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (13 * n * ν ^ 2) := by
      gcongr
      exact family_sector_cost_mean ν ξ hn hν hν1 hξ hξ32 X hX
    _ = _ := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      congr 1
      ring

/-- Regroup the Born trace into photon-number blocks. Summability
comes from bounded-effect/trace-class duality, and each block is finite. -/
theorem photon_pairing_hasSum {n : ℕ}
    (ρ E : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (hρ : IsDensity ρ)
    (hblock : ∀ u v, ∑ i, u i ≠ ∑ i, v i → ρ u v = 0)
    (hE : ∀ (s : Finset (Occupation (Fin n))) (z : Occupation (Fin n) → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2) :
    HasSum (fun k => ∑ u ∈ photonSectorSet n k, ∑ v ∈ photonSectorSet n k, E u v * ρ v u)
      (∑' u, ∑' v, E u v * ρ v u) := by
  classical
  obtain ⟨F, _, _, hF, _⟩ := effect_matrix_operator E hE
  obtain ⟨e⟩ := hρ.1
  have hs := (effect_trace_pairing E F hF ρ e).2.1.hasSum
  let c : Occupation (Fin n) → ℕ := fun u => ∑ i, u i
  have hσ := (Equiv.sigmaFiberEquiv c).hasSum_iff.mpr hs
  apply hσ.sigma
  intro k
  have hinner (u : PhotonSector n k) : (∑' v, E u v * ρ v u) =
      ∑ v ∈ photonSectorSet n k, E u v * ρ v u := by
    apply tsum_eq_sum
    intro v hv
    have hne : ∑ i, v i ≠ ∑ i, u.val i := by
      simpa only [u.property, mem_photonSectorSet] using hv
    rw [hblock v u hne, mul_zero]
  change HasSum (fun u : PhotonSector n k => ∑' v, E u v * ρ v u) _
  simp only [hinner]
  rw [sum_photonSectorSet]
  exact hasSum_fintype _

/-- Measuring a block-diagonal state is the countable mixture of the
laws of its normalized photon-sector states. No regularity of the
measurement outcome space is required. -/
theorem fockPOVM_law_photon_mixture {n : ℕ} {O : Type} [MeasurableSpace O]
    (M : FockPOVM (Occupation (Fin n)) O)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (hρ : IsDensity ρ)
    (hblock : ∀ u v, ∑ i, u i ≠ ∑ i, v i → ρ u v = 0)
    (hmass : ∀ k, 0 < finiteCutMass (photonSectorSet n k) ρ) :
    M.law ρ = Measure.sum (fun k =>
      ENNReal.ofReal (finiteCutMass (photonSectorSet n k) ρ) •
        M.law (normalizedFiniteCut (photonSectorSet n k) ρ)) := by
  ext B hB
  rw [Measure.sum_apply _ hB, M.law_born ρ hρ B hB]
  have hsum := photon_pairing_hasSum ρ (M.effect B) hρ hblock (M.effect_form B hB)
  have hsumre := hsum.map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous
  change HasSum (fun k => (∑ u ∈ photonSectorSet n k, ∑ v ∈ photonSectorSet n k,
    M.effect B u v * ρ v u).re) (∑' u, ∑' v, M.effect B u v * ρ v u).re at hsumre
  have hnonneg (k : ℕ) :
      0 ≤ (∑ u ∈ photonSectorSet n k, ∑ v ∈ photonSectorSet n k,
        M.effect B u v * ρ v u).re :=
    ((born_truncation ρ hρ).2.1 _ _ (M.effect_form B hB)).2
  rw [← hsumre.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnonneg hsumre.summable]
  apply tsum_congr
  intro k
  rw [Measure.smul_apply, smul_eq_mul,
    M.law_born _ (normalizedFiniteCut_isDensity _ ρ hρ (hmass k)) B hB,
    normalizedFiniteCut_born]
  rw [← ENNReal.ofReal_mul (hmass k).le]
  congr 1
  rw [← mul_assoc, mul_inv_cancel₀ (hmass k).ne', one_mul]

theorem fugacityCoeff_block_diagonal {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ)
    (u v : Occupation (Fin n)) (huv : ∑ i, u i ≠ ∑ i, v i) :
    fugacityCoeff R u v = 0 := by
  simp only [fugacityCoeff, Matrix.smul_apply, smul_eq_mul,
    (gammaFock_basic R u v).1 huv, mul_zero]

/-- The normalized state carried by the `k`-photon component of the
hard Gaussian family is a valid density operator. -/
theorem family_photon_state_isDensity {n : ℕ} (hn : 1 ≤ n)
    (ν ξ : ℝ) (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) (k : ℕ) :
    IsDensity (normalizedFiniteCut (photonSectorSet n k) (fugacityCoeff (fugacityFamily ν ξ X))) := by
  have hR := family_spectral_bounds ν ξ hν hνhi hξ hξhi X hX
  apply normalizedFiniteCut_isDensity
  · exact fugacityCoeff_isDensity _ hR.1 hR.2.1
  · exact photonSector_mass_pos hn k _ (family_sector_posDef ν ξ hν hνhi hξ hξhi X hX k)

theorem fockPOVM_family_photon_mixture {n : ℕ} {O : Type} [MeasurableSpace O]
    (M : FockPOVM (Occupation (Fin n)) O) (hn : 1 ≤ n)
    (ν ξ : ℝ) (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) :
    M.law (fugacityCoeff (fugacityFamily ν ξ X)) = Measure.sum (fun k =>
      ENNReal.ofReal (finiteCutMass (photonSectorSet n k) (fugacityCoeff (fugacityFamily ν ξ X))) •
        M.law (normalizedFiniteCut (photonSectorSet n k) (fugacityCoeff (fugacityFamily ν ξ X)))) := by
  have hR := family_spectral_bounds ν ξ hν hνhi hξ hξhi X hX
  apply fockPOVM_law_photon_mixture
  · exact fugacityCoeff_isDensity _ hR.1 hR.2.1
  · exact fugacityCoeff_block_diagonal _
  · intro k
    exact photonSector_mass_pos hn k _ (family_sector_posDef ν ξ hν hνhi hξ hξhi X hX k)

/-- The photon-mixture identity at the level of each adaptive round.
The component kernels are available from `AdaptiveScheme.round`, so
no disintegration or measurable choice of sector measurements is needed. -/
theorem adaptive_round_photon_mixture {n N : ℕ} {O : Type} [MeasurableSpace O]
    (S : AdaptiveScheme n N O)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (hρ : IsDensity ρ)
    (hblock : ∀ u v, ∑ i, u i ≠ ∑ i, v i → ρ u v = 0)
    (hmass : ∀ k, 0 < finiteCutMass (photonSectorSet n k) ρ) (t : Fin N) :
    S.round ρ t = Kernel.sum (fun k =>
      @scaledKernel _ _ _ _ (ENNReal.ofReal (finiteCutMass (photonSectorSet n k) ρ))
        (S.round (normalizedFiniteCut (photonSectorSet n k) ρ) t)
        (by letI := S.round_markov (normalizedFiniteCut (photonSectorSet n k) ρ) t
            infer_instance)) := by
  letI (σ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (u : Fin N) :
      IsMarkovKernel (S.round σ u) := S.round_markov σ u
  ext x B hB
  rw [S.round_born ρ hρ t x,
    fockPOVM_law_photon_mixture _ ρ hρ hblock hmass,
    Kernel.sum_apply, Measure.sum_apply _ hB, Measure.sum_apply _ hB]
  apply tsum_congr
  intro k
  rw [scaledKernel_apply, S.round_born _ (normalizedFiniteCut_isDensity _ ρ hρ (hmass k)) t x]

/-- An adaptive transcript from a block-diagonal state is a mixture
over its full photon-number record, with independent prior weights.
The individual outcome kernels can still depend on the entire past. -/
theorem adaptive_transcript_photon_mixture {n N : ℕ} {O : Type} [MeasurableSpace O]
    (S : AdaptiveScheme n N O)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (hρ : IsDensity ρ)
    (hblock : ∀ u v, ∑ i, u i ≠ ∑ i, v i → ρ u v = 0)
    (hmass : ∀ k, 0 < finiteCutMass (photonSectorSet n k) ρ) :
    transcriptLaw S ρ = Measure.sum (fun k : Fin N → ℕ =>
      (∏ t, ENNReal.ofReal (finiteCutMass (photonSectorSet n (k t)) ρ)) •
        sequentialLaw (fun t => S.round (normalizedFiniteCut (photonSectorSet n (k t)) ρ) t)
          N le_rfl) := by
  letI (σ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (t : Fin N) :
      IsMarkovKernel (S.round σ t) := S.round_markov σ t
  unfold transcriptLaw
  have hr : S.round ρ = fun t => Kernel.sum (fun k =>
      scaledKernel (ENNReal.ofReal (finiteCutMass (photonSectorSet n k) ρ))
        (S.round (normalizedFiniteCut (photonSectorSet n k) ρ) t)) := by
    funext t
    exact adaptive_round_photon_mixture S ρ hρ hblock hmass t
  rw [hr]
  exact sequentialLaw_countable_weighted_mixture
    (fun t k => S.round (normalizedFiniteCut (photonSectorSet n k) ρ) t)
    (fun _ k => ENNReal.ofReal (finiteCutMass (photonSectorSet n k) ρ))
    (fun _ _ => ENNReal.ofReal_ne_top)

theorem adaptive_family_photon_mixture {n N : ℕ} {O : Type} [MeasurableSpace O]
    (S : AdaptiveScheme n N O) (hn : 1 ≤ n)
    (ν ξ : ℝ) (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) :
    transcriptLaw S (fugacityCoeff (fugacityFamily ν ξ X)) = Measure.sum (fun k : Fin N → ℕ =>
      (∏ t, ENNReal.ofReal
        (finiteCutMass (photonSectorSet n (k t)) (fugacityCoeff (fugacityFamily ν ξ X)))) •
        sequentialLaw (fun t => S.round
          (normalizedFiniteCut (photonSectorSet n (k t)) (fugacityCoeff (fugacityFamily ν ξ X))) t)
          N le_rfl) := by
  have hR := family_spectral_bounds ν ξ hν hνhi hξ hξhi X hX
  apply adaptive_transcript_photon_mixture
  · exact fugacityCoeff_isDensity _ hR.1 hR.2.1
  · exact fugacityCoeff_block_diagonal _
  · intro k
    exact photonSector_mass_pos hn k _ (family_sector_posDef ν ξ hν hνhi hξ hξhi X hX k)

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5BlockPositive -/
section
open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-- Finite positive matrices are finite sums of unnormalized rank-one positive matrices. -/
theorem posSemidef_eq_sum_rankOne {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (hA : A.PosSemidef) :
    ∃ v : J → J → ℂ, A = ∑ k, Matrix.vecMulVec (v k) (star (v k)) := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  refine ⟨fun k i => star (B k i), ?_⟩
  ext i j
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_star]

/-- Contract the first factor against a local effect. This orientation matches `Tr(Aρ)`. -/
def partialContract {J K : Type*} [Fintype J]
    (A : Matrix J J ℂ) (H : Matrix (J × K) (J × K) ℂ) : Matrix K K ℂ :=
  fun a b => ∑ i, ∑ j, A j i * H (i,a) (j,b)

/-- A rank-one contraction equals testing the original operator on the corresponding product vector. -/
lemma partialContract_rankOne_quadratic {J K : Type*} [Fintype J] [Fintype K]
    (H : Matrix (J × K) (J × K) ℂ) (v : J → ℂ) (w : K → ℂ) :
    star w ⬝ᵥ (partialContract (Matrix.vecMulVec v (star v)) H *ᵥ w) =
      star (fun p : J × K => v p.1 * w p.2) ⬝ᵥ
        (H *ᵥ (fun p : J × K => v p.1 * w p.2)) := by
  simp only [partialContract, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply,
    Pi.star_apply, star_mul, Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Positivity against each local product vector extends to an arbitrary positive local effect. -/
theorem partialContract_quadratic_nonneg {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J]
    (H : Matrix (J × K) (J × K) ℂ) (A : Matrix J J ℂ) (hA : A.PosSemidef)
    (w : K → ℂ)
    (hprod : ∀ v : J → ℂ, 0 ≤
      star (fun p : J × K => v p.1 * w p.2) ⬝ᵥ
        (H *ᵥ (fun p : J × K => v p.1 * w p.2))) :
    0 ≤ star w ⬝ᵥ (partialContract A H *ᵥ w) := by
  obtain ⟨v, rfl⟩ := posSemidef_eq_sum_rankOne A hA
  have heq : partialContract (∑ k, Matrix.vecMulVec (v k) (star (v k))) H =
      ∑ k, partialContract (Matrix.vecMulVec (v k) (star (v k))) H := by
    ext a b
    simp only [partialContract, Matrix.sum_apply, Finset.sum_mul]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [heq, Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_nonneg
  intro k hk
  rw [partialContract_rankOne_quadratic]
  exact hprod (v k)

lemma partialContract_isHermitian {J K : Type*} [Fintype J]
    (A : Matrix J J ℂ) (H : Matrix (J × K) (J × K) ℂ)
    (hA : A.IsHermitian) (hH : H.IsHermitian) : (partialContract A H).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  simp only [partialContract, star_sum, star_mul]
  simp_rw [hA.apply, hH.apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The bilinear trace pairing, written entrywise to avoid any analytic assumptions. -/
def matrixPair {J : Type*} [Fintype J] (H A : Matrix J J ℂ) : ℂ :=
  ∑ i, ∑ j, H i j * A j i

lemma matrixPair_kronecker {J K : Type*} [Fintype J] [Fintype K]
    (H : Matrix (J × K) (J × K) ℂ) (A : Matrix J J ℂ) (B : Matrix K K ℂ) :
    matrixPair H (fun p q => A p.1 q.1 * B p.2 q.2) =
      matrixPair (partialContract A H) B := by
  simp only [matrixPair, partialContract, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Testing an integrated adaptive effect is the integral of the tests of its local contractions. -/
theorem matrixPair_integral_tensor {Ω J K : Type*} [MeasurableSpace Ω]
    [Fintype J] [Fintype K] (μ : Measure Ω)
    (H : Matrix (J × K) (J × K) ℂ) (e : Ω → Matrix J J ℂ) (G : Ω → Matrix K K ℂ)
    (he : ∀ i j, Integrable (fun x => e x i j) μ)
    (hGm : ∀ a b, AEStronglyMeasurable (fun x => G x a b) μ)
    (hGb : ∃ C : ℝ, ∀ x a b, ‖G x a b‖ ≤ C) :
    matrixPair H (fun p q => ∫ x, e x p.1 q.1 * G x p.2 q.2 ∂μ) =
      ∫ x, matrixPair (partialContract (e x) H) (G x) ∂μ := by
  obtain ⟨C, hC⟩ := hGb
  have hi : ∀ i j a b, Integrable (fun x => e x i j * G x a b) μ :=
    fun i j a b => (he i j).mul_bdd (hGm a b) (ae_of_all μ (fun x => hC x a b))
  simp_rw [← matrixPair_kronecker H]
  simp only [matrixPair]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      exact (integral_const_mul _ _).symm
    · intro q hq
      exact (hi q.1 p.1 q.2 p.2).const_mul _
  · intro p hp
    exact integrable_finsetSum _ (fun q _ => (hi q.1 p.1 q.2 p.2).const_mul _)

/-- One adaptive measurement step preserves every dual cone defined by product-vector tests.
The downstream test may depend measurably on the first outcome. -/
theorem adaptive_block_positive_step {Ω J K : Type*} [MeasurableSpace Ω]
    [Fintype J] [Fintype K] [DecidableEq J] (μ : Measure Ω)
    (W : Set (K → ℂ)) (H : Matrix (J × K) (J × K) ℂ) (hH : H.IsHermitian)
    (hprod : ∀ v : J → ℂ, ∀ w ∈ W, 0 ≤
      star (fun p : J × K => v p.1 * w p.2) ⬝ᵥ
        (H *ᵥ (fun p : J × K => v p.1 * w p.2)))
    (e : Ω → Matrix J J ℂ) (he : ∀ i j, Integrable (fun x => e x i j) μ)
    (hepos : ∀ᵐ x ∂μ, (e x).PosSemidef)
    (G : Ω → Matrix K K ℂ)
    (hGm : ∀ a b, AEStronglyMeasurable (fun x => G x a b) μ)
    (hGb : ∃ C : ℝ, ∀ x a b, ‖G x a b‖ ≤ C)
    (hTest : ∀ x, ∀ F : Matrix K K ℂ, F.IsHermitian →
      (∀ w ∈ W, 0 ≤ star w ⬝ᵥ (F *ᵥ w)) → 0 ≤ matrixPair F (G x)) :
    0 ≤ matrixPair H (fun p q => ∫ x, e x p.1 q.1 * G x p.2 q.2 ∂μ) := by
  rw [matrixPair_integral_tensor μ H e G he hGm hGb]
  apply integral_nonneg_of_ae
  filter_upwards [hepos] with x hx
  apply hTest x (partialContract (e x) H)
    (partialContract_isHermitian _ _ hx.isHermitian hH)
  intro w hw
  exact partialContract_quadratic_nonneg H (e x) hx w (fun v => hprod v w hw)

lemma matrixPair_rankOne {J : Type*} [Fintype J] (H : Matrix J J ℂ) (v : J → ℂ) :
    matrixPair H (Matrix.vecMulVec v (star v)) = star v ⬝ᵥ (H *ᵥ v) := by
  simp only [matrixPair, Matrix.vecMulVec_apply, Pi.star_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem matrixPair_posSemidef_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (H A : Matrix J J ℂ) (hH : H.PosSemidef) (hA : A.PosSemidef) :
    0 ≤ matrixPair H A := by
  obtain ⟨v, rfl⟩ := posSemidef_eq_sum_rankOne A hA
  have heq : matrixPair H (∑ k, Matrix.vecMulVec (v k) (star (v k))) =
      ∑ k, matrixPair H (Matrix.vecMulVec (v k) (star (v k))) := by
    simp only [matrixPair, Matrix.sum_apply, Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [heq]
  apply Finset.sum_nonneg
  intro k hk
  rw [matrixPair_rankOne]
  exact hH.dotProduct_mulVec_nonneg (v k)

/-- Contract the last tensor factor against one vector. -/
def rightVectorContract {J K : Type*} [Fintype K]
    (H : Matrix (J × K) (J × K) ℂ) (w : K → ℂ) : Matrix J J ℂ :=
  fun i j => ∑ a, ∑ b, star (w a) * H (i,a) (j,b) * w b

lemma rightVectorContract_isHermitian {J K : Type*} [Fintype K]
    (H : Matrix (J × K) (J × K) ℂ) (hH : H.IsHermitian) (w : K → ℂ) :
    (rightVectorContract H w).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [rightVectorContract, star_sum, star_mul, star_star]
  simp_rw [hH.apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma rightVectorContract_quadratic {J K : Type*} [Fintype J] [Fintype K]
    (H : Matrix (J × K) (J × K) ℂ) (v : J → ℂ) (w : K → ℂ) :
    star v ⬝ᵥ (rightVectorContract H w *ᵥ v) =
      star (fun p : J × K => v p.1 * w p.2) ⬝ᵥ
        (H *ᵥ (fun p : J × K => v p.1 * w p.2)) := by
  simp only [rightVectorContract, dotProduct, Matrix.mulVec, Pi.star_apply,
    star_mul, Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma partialContract_quadratic_eq_pair {J K : Type*} [Fintype J] [Fintype K]
    (A : Matrix J J ℂ) (H : Matrix (J × K) (J × K) ℂ) (w : K → ℂ) :
    star w ⬝ᵥ (partialContract A H *ᵥ w) = matrixPair (rightVectorContract H w) A := by
  simp only [partialContract, rightVectorContract, matrixPair, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- A last-round adaptive step: the accumulated effect tests all previous product-positive
matrices nonnegatively, while the new local effect is positive semidefinite. -/
theorem adaptive_block_positive_last_step {Ω J K : Type*} [MeasurableSpace Ω]
    [Fintype J] [Fintype K] [DecidableEq K] (μ : Measure Ω)
    (W : Set (J → ℂ)) (H : Matrix (J × K) (J × K) ℂ) (hH : H.IsHermitian)
    (hprod : ∀ v ∈ W, ∀ w : K → ℂ, 0 ≤
      star (fun p : J × K => v p.1 * w p.2) ⬝ᵥ
        (H *ᵥ (fun p : J × K => v p.1 * w p.2)))
    (e : Ω → Matrix J J ℂ) (he : ∀ i j, Integrable (fun x => e x i j) μ)
    (heH : ∀ᵐ x ∂μ, (e x).IsHermitian)
    (heTest : ∀ᵐ x ∂μ, ∀ F : Matrix J J ℂ, F.IsHermitian →
      (∀ v ∈ W, 0 ≤ star v ⬝ᵥ (F *ᵥ v)) → 0 ≤ matrixPair F (e x))
    (G : Ω → Matrix K K ℂ)
    (hGm : ∀ a b, AEStronglyMeasurable (fun x => G x a b) μ)
    (hGb : ∃ C : ℝ, ∀ x a b, ‖G x a b‖ ≤ C)
    (hGpos : ∀ᵐ x ∂μ, (G x).PosSemidef) :
    0 ≤ matrixPair H (fun p q => ∫ x, e x p.1 q.1 * G x p.2 q.2 ∂μ) := by
  rw [matrixPair_integral_tensor μ H e G he hGm hGb]
  apply integral_nonneg_of_ae
  filter_upwards [heH, heTest, hGpos] with x hxH hxT hxG
  apply matrixPair_posSemidef_nonneg _ _ _ hxG
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (partialContract_isHermitian _ _ hxH hH)
  intro w
  rw [partialContract_quadratic_eq_pair]
  apply hxT _ (rightVectorContract_isHermitian H hH w)
  intro v hv
  rw [rightVectorContract_quadratic]
  exact hprod v hv w

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5ComposeEffect -/
section
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix ComplexOrder
open Filter Topology

open BosonicLearn

noncomputable section

namespace BosonicLearn.Prop5.ComposeEffect

/-- The hypothesis `effect_form` of a `FockPOVM`. -/
private abbrev EffB {I : Type} (E : Matrix I I ℂ) : Prop :=
  ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2

/-! ### Entries of effects from Born probabilities -/

def tS {I : Type} [DecidableEq I] (a b : I) : Fin 4 → Matrix I I ℂ :=
  Classical.choose (effect_entry_born a b)

def cS {I : Type} [DecidableEq I] (a b : I) : Fin 4 → ℂ :=
  Classical.choose (Classical.choose_spec (effect_entry_born a b))

lemma tS_density {I : Type} [DecidableEq I] (a b : I) (c : Fin 4) : IsDensity (tS a b c) :=
  (Classical.choose_spec (Classical.choose_spec (effect_entry_born a b))).1 c

lemma cS_sum {I : Type} [DecidableEq I] (a b : I) :
    ∑ c, cS a b c = (1 : Matrix I I ℂ) a b :=
  (Classical.choose_spec (Classical.choose_spec (effect_entry_born a b))).2.1

lemma entry_eq {I O : Type} [DecidableEq I] [MeasurableSpace O] (P : FockPOVM I O) {B : Set O}
    (hB : MeasurableSet B) (a b : I) :
    P.effect B a b = ∑ c, cS a b c * (((P.law (tS a b c) B).toReal : ℝ) : ℂ) :=
  (Classical.choose_spec (Classical.choose_spec (effect_entry_born a b))).2.2 O P B hB

/-! ### Bounds and symmetry of effect matrices -/

private lemma norm_entry_le {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (i j : I) :
    ‖E i j‖ ≤ 1 := by
  obtain ⟨F, hF1, -, -, hF4⟩ := effect_matrix_operator E hE
  have h1 : ‖(lp.single 2 i (1 : ℂ) : Hilbert I)‖ = 1 := by
    rw [lp.norm_single (by norm_num)]
    simp
  have h2 : ‖(lp.single 2 j (1 : ℂ) : Hilbert I)‖ = 1 := by
    rw [lp.norm_single (by norm_num)]
    simp
  have h3 : ‖F (lp.single 2 j (1 : ℂ))‖ ≤ 1 := by
    have h := F.le_opNorm (lp.single 2 j (1 : ℂ))
    rw [h2, mul_one] at h
    exact h.trans hF1
  rw [← hF4 i j]
  have h := norm_inner_le_norm (𝕜 := ℂ) (lp.single 2 i (1 : ℂ) : Hilbert I) (F (lp.single 2 j (1 : ℂ)))
  rw [h1, one_mul] at h
  exact h.trans h3

private lemma herm_of_form {I : Type} {E : Matrix I I ℂ}
    (h : ∀ (s : Finset I) (z : I → ℂ), (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0)
    (i j : I) : E j i = star (E i j) := by
  classical
  have hd : ∀ k, (E k k).im = 0 := fun k => by simpa using h {k} (Pi.single k 1)
  by_cases hij : i = j
  · subst hij
    exact (Complex.conj_eq_iff_im.mpr (hd i)).symm
  · have hji : j ≠ i := fun h => hij h.symm
    have hii := hd i
    have hjj := hd j
    have h1 := h {i, j} (fun k => if k = i then 1 else if k = j then 1 else 0)
    have h2 := h {i, j} (fun k => if k = i then 1 else if k = j then Complex.I else 0)
    simp [Finset.sum_pair hij, hji] at h1 h2
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith

/-- The block of an effect matrix on a finite set is positive semidefinite. -/
private lemma eff_block_psd {I : Type} {E : Matrix I I ℂ} (hE : EffB E) (s : Finset I) :
    (Matrix.of fun a b : s => E a b).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    exact (herm_of_form (fun s z => (hE s z).1) b a).symm
  · let z : I → ℂ := fun i => if h : i ∈ s then x ⟨i, h⟩ else 0
    have h := hE s z
    have e : star x ⬝ᵥ (Matrix.of fun a b : s => E a b).mulVec x =
        ∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j := by
      rw [← Finset.sum_coe_sort s]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_coe_sort s]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [z, mul_assoc]
    rw [e, Complex.nonneg_iff]
    exact ⟨h.2.1, h.1.symm⟩

/-! ### Sections of a measurable set under a Markov kernel -/

private lemma integrable_kernel_sec {Ω O : Type} [MeasurableSpace Ω] [MeasurableSpace O]
    (m : Measure Ω) [IsFiniteMeasure m] (k : Kernel Ω O) [IsMarkovKernel k] {C : Set (Ω × O)}
    (hC : MeasurableSet C) :
    Integrable (fun x => (((k x (Prod.mk x ⁻¹' C)).toReal : ℝ) : ℂ)) m := by
  refine Integrable.of_bound (Complex.measurable_ofReal.comp
    (Kernel.measurable_kernel_prodMk_left hC).ennreal_toReal).aestronglyMeasurable 1
    (Eventually.of_forall fun x => ?_)
  rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := k x) (s := Prod.mk x ⁻¹' C))

private lemma compProd_toReal {Ω O : Type} [MeasurableSpace Ω] [MeasurableSpace O]
    (m : Measure Ω) [IsFiniteMeasure m] (k : Kernel Ω O) [IsMarkovKernel k] {C : Set (Ω × O)}
    (hC : MeasurableSet C) :
    ((m ⊗ₘ k) C).toReal = ∫ x, (k x (Prod.mk x ⁻¹' C)).toReal ∂m := by
  rw [Measure.compProd_apply hC, integral_toReal
    (Kernel.measurable_kernel_prodMk_left hC).aemeasurable
    (Eventually.of_forall fun x => measure_lt_top _ _)]

section Compose

variable {J I' Ω O : Type} [DecidableEq J] [DecidableEq I'] [MeasurableSpace Ω] [MeasurableSpace O]

/-- The entry `(a, b)` of the effect of `Q_x` on the section `C_x`, as a function of `x`. -/
def gE (Q : Ω → FockPOVM I' O) (C : Set (Ω × O)) (a b : I') (x : Ω) : ℂ :=
  (Q x).effect (Prod.mk x ⁻¹' C) a b

private lemma gE_eq (Q : Ω → FockPOVM I' O) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ) {C : Set (Ω × O)} (hC : MeasurableSet C)
    (a b : I') (x : Ω) :
    gE Q C a b x = ∑ d, cS a b d * (((κ (tS a b d) x (Prod.mk x ⁻¹' C)).toReal : ℝ) : ℂ) := by
  unfold gE
  rw [entry_eq (Q x) (measurable_prodMk_left hC) a b]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hκQ _ (tS_density a b d) x]

lemma gE_measurable (Q : Ω → FockPOVM I' O) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ)
    {C : Set (Ω × O)} (hC : MeasurableSet C) (a b : I') : Measurable (gE Q C a b) := by
  have h : gE Q C a b =
      fun x => ∑ d, cS a b d * (((κ (tS a b d) x (Prod.mk x ⁻¹' C)).toReal : ℝ) : ℂ) :=
    funext fun x => gE_eq Q κ hκQ hC a b x
  rw [h]
  refine Finset.measurable_sum _ fun d _ => ?_
  have := hκ (tS a b d)
  exact measurable_const.mul
    (Complex.measurable_ofReal.comp (Kernel.measurable_kernel_prodMk_left hC).ennreal_toReal)

lemma gE_norm_le (Q : Ω → FockPOVM I' O) {C : Set (Ω × O)} (hC : MeasurableSet C)
    (a b : I') (x : Ω) : ‖gE Q C a b x‖ ≤ 1 :=
  norm_entry_le ((Q x).effect_form _ (measurable_prodMk_left hC)) a b

lemma gE_integrable (Q : Ω → FockPOVM I' O) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ)
    {C : Set (Ω × O)} (hC : MeasurableSet C) (a b : I') (m : Measure Ω) [IsFiniteMeasure m] :
    Integrable (gE Q C a b) m :=
  Integrable.of_bound (gE_measurable Q κ hκ hκQ hC a b).aestronglyMeasurable 1
    (Eventually.of_forall fun x => gE_norm_le Q hC a b x)

/-- The effect of the composed measurement. -/
def cEff (M : FockPOVM J Ω) (κ : Matrix I' I' ℂ → Kernel Ω O) (C : Set (Ω × O)) :
    Matrix (J × I') (J × I') ℂ :=
  fun p q => ∑ c, ∑ d, cS p.1 q.1 c * cS p.2 q.2 d *
    ((((M.law (tS p.1 q.1 c) ⊗ₘ κ (tS p.2 q.2 d)) C).toReal : ℝ) : ℂ)

/-- `E'(C)_{(u,a),(v,b)} = ∫ Q_x(C_x)_{ab} dM_{uv}(x)`. -/
lemma cEff_eq (M : FockPOVM J Ω) (Q : Ω → FockPOVM I' O) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ)
    {C : Set (Ω × O)} (hC : MeasurableSet C) (p q : J × I') :
    cEff M κ C p q = ∑ c, cS p.1 q.1 c * ∫ x, gE Q C p.2 q.2 x ∂(M.law (tS p.1 q.1 c)) := by
  unfold cEff
  refine Finset.sum_congr rfl fun c _ => ?_
  have hprob := M.law_prob _ (tS_density p.1 q.1 c)
  have hint : ∫ x, gE Q C p.2 q.2 x ∂(M.law (tS p.1 q.1 c)) =
      ∑ d, cS p.2 q.2 d *
        ((((M.law (tS p.1 q.1 c) ⊗ₘ κ (tS p.2 q.2 d)) C).toReal : ℝ) : ℂ) := by
    have h : gE Q C p.2 q.2 = fun x => ∑ d, cS p.2 q.2 d *
        (((κ (tS p.2 q.2 d) x (Prod.mk x ⁻¹' C)).toReal : ℝ) : ℂ) :=
      funext fun x => gE_eq Q κ hκQ hC _ _ x
    rw [h, integral_finsetSum _ fun d _ => by
      have := hκ (tS p.2 q.2 d)
      exact (integrable_kernel_sec _ _ hC).const_mul _]
    refine Finset.sum_congr rfl fun d _ => ?_
    have := hκ (tS p.2 q.2 d)
    rw [integral_const_mul, integral_complex_ofReal, compProd_toReal _ _ hC]
  rw [hint, Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

private lemma cEff_univ (M : FockPOVM J Ω) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) : cEff M κ Set.univ = 1 := by
  ext p q
  unfold cEff
  have h : ∀ c d, ((((M.law (tS p.1 q.1 c) ⊗ₘ κ (tS p.2 q.2 d)) Set.univ).toReal : ℝ) : ℂ) = 1 := by
    intro c d
    have := M.law_prob _ (tS_density p.1 q.1 c)
    have := hκ (tS p.2 q.2 d)
    rw [measure_univ]
    simp
  simp only [h, mul_one]
  rw [← Finset.sum_mul_sum, cS_sum, cS_sum]
  simp only [Matrix.one_apply]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [Prod.ext_iff, h1, h2]

private lemma cEff_add_compl (M : FockPOVM J Ω) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) {C : Set (Ω × O)} (hC : MeasurableSet C) (p q : J × I') :
    cEff M κ C p q + cEff M κ Cᶜ p q = cEff M κ Set.univ p q := by
  unfold cEff
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  have := M.law_prob _ (tS_density p.1 q.1 c)
  have := hκ (tS p.2 q.2 d)
  rw [← mul_add, ← Complex.ofReal_add, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    measure_add_measure_compl hC]

private lemma cEff_hasSum (M : FockPOVM J Ω) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) (p q : J × I') (f : ℕ → Set (Ω × O))
    (hf : ∀ n, MeasurableSet (f n)) (hd : Pairwise (Function.onFun Disjoint f)) :
    HasSum (fun n => cEff M κ (f n) p q) (cEff M κ (⋃ n, f n) p q) := by
  unfold cEff
  refine hasSum_sum fun c _ => hasSum_sum fun d _ => HasSum.mul_left _ ?_
  have := M.law_prob _ (tS_density p.1 q.1 c)
  have := hκ (tS p.2 q.2 d)
  set ν : Measure (Ω × O) := M.law (tS p.1 q.1 c) ⊗ₘ κ (tS p.2 q.2 d) with hν
  have h1 : ν (⋃ n, f n) = ∑' n, ν (f n) := measure_iUnion hd hf
  have hne : ∑' n, ν (f n) ≠ ⊤ := h1 ▸ measure_ne_top _ _
  have h2 := ENNReal.hasSum_toReal hne
  rw [← ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _), ← h1] at h2
  exact Complex.ofRealCLM.hasSum h2

/-! ### Positivity on entangled vectors -/

private lemma cEff_form_nonneg (M : FockPOVM J Ω) (Q : Ω → FockPOVM I' O)
    (κ : Matrix I' I' ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ) {C : Set (Ω × O)} (hC : MeasurableSet C)
    (s₁ : Finset J) (s₂ : Finset I') (z : J × I' → ℂ) :
    0 ≤ ∑ p ∈ s₁ ×ˢ s₂, ∑ q ∈ s₁ ×ˢ s₂, star (z p) * cEff M κ C p q * z q := by
  have hK := kronecker_integral_posSemidef (Ω := Ω) (ι₁ := s₁) (ι₂ := s₂) (K := Fin 4)
    (fun u v c => M.law (tS (u : J) (v : J) c))
    (fun u v c => by
      have := M.law_prob _ (tS_density (u : J) (v : J) c)
      infer_instance)
    (fun u v c => cS (u : J) (v : J) c)
    (fun B hB => by
      have h : (Matrix.of fun u v : s₁ => ∑ c, cS (u : J) (v : J) c *
          (((M.law (tS (u : J) (v : J) c) B).toReal : ℝ) : ℂ)) =
          Matrix.of fun u v : s₁ => M.effect B u v := by
        ext u v
        simp only [Matrix.of_apply]
        exact (entry_eq M hB u v).symm
      rw [h]
      exact eff_block_psd (M.effect_form B hB) s₁)
    (fun x => Matrix.of fun a b : s₂ => gE Q C a b x)
    (fun a b => gE_measurable Q κ hκ hκQ hC a b)
    (fun x a b => gE_norm_le Q hC a b x)
    (fun x => eff_block_psd ((Q x).effect_form _ (measurable_prodMk_left hC)) s₂)
  have h := hK.dotProduct_mulVec_nonneg (fun p : s₁ × s₂ => z ((p.1 : J), (p.2 : I')))
  have e : star (fun p : s₁ × s₂ => z ((p.1 : J), (p.2 : I'))) ⬝ᵥ
      (Matrix.of fun (p q : s₁ × s₂) => ∑ k, cS (p.1 : J) (q.1 : J) k *
        ∫ x, (Matrix.of fun a b : s₂ => gE Q C a b x) p.2 q.2
          ∂(M.law (tS (p.1 : J) (q.1 : J) k))).mulVec
        (fun p : s₁ × s₂ => z ((p.1 : J), (p.2 : I'))) =
      ∑ p ∈ s₁ ×ˢ s₂, ∑ q ∈ s₁ ×ˢ s₂, star (z p) * cEff M κ C p q * z q := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Fintype.sum_prod_type,
      Matrix.of_apply, Finset.sum_product]
    rw [← Finset.sum_coe_sort s₁]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_coe_sort s₂]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_coe_sort s₁]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← Finset.sum_coe_sort s₂]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [cEff_eq M Q κ hκ hκQ hC]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rwa [e] at h

private lemma cEff_effB (M : FockPOVM J Ω) (Q : Ω → FockPOVM I' O)
    (κ : Matrix I' I' ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ) {C : Set (Ω × O)} (hC : MeasurableSet C) :
    EffB (cEff M κ C) := by
  have hnn : ∀ {C : Set (Ω × O)}, MeasurableSet C → ∀ (s : Finset (J × I')) (z : J × I' → ℂ),
      0 ≤ ∑ p ∈ s, ∑ q ∈ s, star (z p) * cEff M κ C p q * z q := by
    intro C hC s z
    have h := cEff_form_nonneg M Q κ hκ hκQ hC (s.image Prod.fst) (s.image Prod.snd)
      (fun p => if p ∈ s then z p else 0)
    have hsub : s ⊆ s.image Prod.fst ×ˢ s.image Prod.snd := fun p hp =>
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
    have e : ∑ p ∈ s.image Prod.fst ×ˢ s.image Prod.snd,
        ∑ q ∈ s.image Prod.fst ×ˢ s.image Prod.snd,
          star ((fun p => if p ∈ s then z p else 0) p) * cEff M κ C p q *
            (fun p => if p ∈ s then z p else 0) q =
        ∑ p ∈ s, ∑ q ∈ s, star (z p) * cEff M κ C p q * z q := by
      rw [← Finset.sum_subset hsub (fun p _ hp => by simp [hp])]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← Finset.sum_subset hsub (fun q _ hq => by simp [hq])]
      exact Finset.sum_congr rfl fun q hq => by simp [hp, hq]
    rwa [e] at h
  intro s z
  have h1 := hnn hC s z
  have h2 := hnn hC.compl s z
  have hsum : (∑ p ∈ s, ∑ q ∈ s, star (z p) * cEff M κ C p q * z q) +
      (∑ p ∈ s, ∑ q ∈ s, star (z p) * cEff M κ Cᶜ p q * z q) =
      ((∑ p ∈ s, ‖z p‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.sum_add_distrib]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_add_distrib]
    have hq : ∀ q ∈ s, star (z p) * cEff M κ C p q * z q + star (z p) * cEff M κ Cᶜ p q * z q =
        star (z p) * (if p = q then 1 else 0) * z q := by
      intro q _
      rw [← add_mul, ← mul_add, cEff_add_compl M κ hκ hC, cEff_univ M κ hκ, Matrix.one_apply]
    rw [Finset.sum_congr rfl hq,
      Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (fun h => absurd hp h),
      if_pos rfl, mul_one, Complex.star_def, Complex.conj_mul']
  rw [Complex.nonneg_iff] at h1 h2
  have hre := congrArg Complex.re hsum
  have him := congrArg Complex.im hsum
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  exact ⟨h1.2.symm, h1.1, by linarith [h2.1]⟩

/-! ### The Born law on product states -/

/-- The Born sum of the composed effect on `ρ ⊗ τ` equals the Born sum on `ρ` of the measurement `M`
post-processed by `x ↦ δ_x ⊗ κ_τ(x)`. -/
private lemma born_prod_eq (M : FockPOVM J Ω) (Q : Ω → FockPOVM I' O)
    (κ : Matrix I' I' ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ) {ρ : Matrix J J ℂ} {τ : Matrix I' I' ℂ}
    (hρ : IsDensity ρ) (hτ : IsDensity τ) (P' : FockPOVM J (Ω × O))
    (hP' : ∀ σ : Matrix J J ℂ, IsDensity σ → P'.law σ = M.law σ ⊗ₘ κ τ)
    {C : Set (Ω × O)} (hC : MeasurableSet C) :
    (∑' p : J × I', ∑' q : J × I', cEff M κ C p q * (ρ q.1 p.1 * τ q.2 p.2)) =
      ∑' u, ∑' v, P'.effect C u v * ρ v u := by
  have hX : IsDensity (fun p q : J × I' => ρ p.1 q.1 * τ p.2 q.2) := isDensity_prod hρ hτ
  have hκτ := hκ τ
  refine eq_of_forall_dist_le fun ε hε => ?_
  rw [dist_eq_norm]
  obtain ⟨hX1, -, -⟩ := born_truncation _ hX
  obtain ⟨hρ1, -, -⟩ := born_truncation ρ hρ
  obtain ⟨hτ1, -, hτ3⟩ := born_truncation τ hτ
  obtain ⟨F0, hF0⟩ := hX1 (ε / 3) (by positivity)
  obtain ⟨F10, hF10⟩ := hρ1 (ε / 3) (by positivity)
  set F₁ : Finset J := F10 ∪ F0.image Prod.fst with hF₁def
  set Kρ : ℝ := ∑ u ∈ F₁, ∑ v ∈ F₁, ‖ρ v u‖ * ∑ c, ‖cS u v c‖ with hKdef
  have hKρ : 0 ≤ Kρ := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
    mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun c _ => norm_nonneg _)
  set η : ℝ := ε / 3 / (Kρ + 1) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨F20, hF20⟩ := hτ1 η hη
  set F₂ : Finset I' := F20 ∪ F0.image Prod.snd with hF₂def
  have hsub : F0 ⊆ F₁ ×ˢ F₂ := fun p hp => Finset.mem_product.mpr
    ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
  -- the three approximations
  have ha := hF0 (F₁ ×ˢ F₂) hsub (cEff M κ C) (cEff_effB M Q κ hκ hκQ hC)
  have hb := hF10 F₁ Finset.subset_union_left (P'.effect C) (P'.effect_form C hC)
  -- the functions of `x`
  set g₂ : Ω → ℂ := fun x => ∑ a ∈ F₂, ∑ b ∈ F₂, gE Q C a b x * τ b a with hg₂
  set gτ : Ω → ℂ := fun x => (((κ τ x (Prod.mk x ⁻¹' C)).toReal : ℝ) : ℂ) with hgτ
  have hpt : ∀ x, ‖g₂ x - gτ x‖ ≤ η := by
    intro x
    have hEx := (Q x).effect_form _ (measurable_prodMk_left (x := x) hC)
    have h1 := hF20 F₂ Finset.subset_union_left _ hEx
    have h3 := hτ3 _ hEx
    have hlaw := (Q x).law_born τ hτ _ (measurable_prodMk_left (x := x) hC)
    have hval : gτ x = ∑' a, ∑' b, (Q x).effect (Prod.mk x ⁻¹' C) a b * τ b a := by
      simp only [hgτ]
      rw [hκQ τ hτ x, hlaw, ENNReal.toReal_ofReal h3.2]
      exact Complex.ext (by simp) (by simp [h3.1])
    rw [hval, norm_sub_rev]
    exact h1
  have hg₂int : ∀ (m : Measure Ω) [IsFiniteMeasure m], Integrable g₂ m := fun m _ =>
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (gE_integrable Q κ hκ hκQ hC a b m).mul_const _
  have hD : ∀ u v : J, ‖(∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a) - P'.effect C u v‖ ≤
      (∑ c, ‖cS u v c‖) * η := by
    intro u v
    have hprob : ∀ c, IsProbabilityMeasure (M.law (tS u v c)) := fun c =>
      M.law_prob _ (tS_density u v c)
    have h1 : ∀ c, ∫ x, g₂ x ∂(M.law (tS u v c)) =
        ∑ a ∈ F₂, ∑ b ∈ F₂, (∫ x, gE Q C a b x ∂(M.law (tS u v c))) * τ b a := by
      intro c
      simp only [hg₂]
      rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
        (gE_integrable Q κ hκ hκQ hC a b _).mul_const _]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ fun b _ => (gE_integrable Q κ hκ hκQ hC a b _).mul_const _]
      exact Finset.sum_congr rfl fun b _ => integral_mul_const _ _
    have h2 : ∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a =
        ∑ c, cS u v c * ∫ x, g₂ x ∂(M.law (tS u v c)) := by
      simp only [h1, Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.univ) (t := F₂)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm (s := Finset.univ) (t := F₂)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [cEff_eq M Q κ hκ hκQ hC, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    have h3 : P'.effect C u v = ∑ c, cS u v c * ∫ x, gτ x ∂(M.law (tS u v c)) := by
      rw [entry_eq P' hC u v]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hP' _ (tS_density u v c), compProd_toReal _ _ hC]
      simp only [hgτ]
      rw [integral_complex_ofReal]
    rw [h2, h3, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [← mul_sub, norm_mul, ← integral_sub (hg₂int _) (integrable_kernel_sec _ _ hC)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := norm_integral_le_of_norm_le_const (μ := M.law (tS u v c))
      (Eventually.of_forall fun x => hpt x)
    simpa using h
  -- the truncated sum on the product block
  have hS12 : ∑ p ∈ F₁ ×ˢ F₂, ∑ q ∈ F₁ ×ˢ F₂, cEff M κ C p q * (ρ q.1 p.1 * τ q.2 p.2) =
      ∑ u ∈ F₁, ∑ v ∈ F₁, ρ v u * ∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Finset.sum_product]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hc : ‖(∑ p ∈ F₁ ×ˢ F₂, ∑ q ∈ F₁ ×ˢ F₂, cEff M κ C p q * (ρ q.1 p.1 * τ q.2 p.2)) -
      ∑ u ∈ F₁, ∑ v ∈ F₁, P'.effect C u v * ρ v u‖ ≤ ε / 3 := by
    rw [hS12, ← Finset.sum_sub_distrib]
    have hterm : ∀ u ∈ F₁, ‖(∑ v ∈ F₁, ρ v u * ∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a) -
        ∑ v ∈ F₁, P'.effect C u v * ρ v u‖ ≤ ∑ v ∈ F₁, ‖ρ v u‖ * (∑ c, ‖cS u v c‖) * η := by
      intro u _
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
      have e : ρ v u * (∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a) -
          P'.effect C u v * ρ v u =
          ρ v u * ((∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a) - P'.effect C u v) := by
        ring
      rw [e, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hD u v) (norm_nonneg _)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    have hK : ∑ u ∈ F₁, ∑ v ∈ F₁, ‖ρ v u‖ * (∑ c, ‖cS u v c‖) * η = Kρ * η := by
      rw [hKdef, Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_mul]
    rw [hK, hηdef]
    have h1 : Kρ * (ε / 3 / (Kρ + 1)) = ε / 3 * (Kρ / (Kρ + 1)) := by ring
    have h2 : Kρ / (Kρ + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    rw [h1]
    calc ε / 3 * (Kρ / (Kρ + 1)) ≤ ε / 3 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε / 3 := mul_one _
  -- conclusion
  set T : ℂ := ∑' p : J × I', ∑' q : J × I', cEff M κ C p q * (ρ q.1 p.1 * τ q.2 p.2) with hT
  set T' : ℂ := ∑' u, ∑' v, P'.effect C u v * ρ v u with hT'
  set S12 : ℂ := ∑ p ∈ F₁ ×ˢ F₂, ∑ q ∈ F₁ ×ˢ F₂, cEff M κ C p q * (ρ q.1 p.1 * τ q.2 p.2) with hS12def
  set S1 : ℂ := ∑ u ∈ F₁, ∑ v ∈ F₁, P'.effect C u v * ρ v u with hS1def
  have ha' : ‖T - S12‖ ≤ ε / 3 := ha
  have hb' : ‖T' - S1‖ ≤ ε / 3 := hb
  have hsplit : T - T' = (T - S12) + (S12 - S1) - (T' - S1) := by ring
  rw [hsplit]
  calc ‖(T - S12) + (S12 - S1) - (T' - S1)‖ ≤ ‖(T - S12) + (S12 - S1)‖ + ‖T' - S1‖ := norm_sub_le _ _
    _ ≤ ‖T - S12‖ + ‖S12 - S1‖ + ‖T' - S1‖ := by linarith [norm_add_le (T - S12) (S12 - S1)]
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

end Compose

/-! ### The statement -/

theorem compose_with_effect {J I' Ω O : Type} [DecidableEq J] [DecidableEq I'] [MeasurableSpace Ω]
    [MeasurableSpace O] (M : FockPOVM J Ω) (Q : Ω → FockPOVM I' O)
    (κ : Matrix I' I' ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ) :
    ∃ M' : FockPOVM (J × I') (Ω × O), M'.effect = cEff M κ ∧
      ∀ (ρ : Matrix J J ℂ) (τ : Matrix I' I' ℂ),
      IsDensity ρ → IsDensity τ →
        M'.law (fun p q => ρ p.1 q.1 * τ p.2 q.2) = (M.law ρ) ⊗ₘ (κ τ) := by
  obtain ⟨M', hM'⟩ := fockPOVM_of_effect (cEff M κ) (fun C hC => cEff_effB M Q κ hκ hκQ hC)
    (cEff_univ M κ hκ) (fun p q f hf hd => cEff_hasSum M κ hκ p q f hf hd)
  refine ⟨M', hM', fun ρ τ hρ hτ => ?_⟩
  have hX : IsDensity (fun p q : J × I' => ρ p.1 q.1 * τ p.2 q.2) := isDensity_prod hρ hτ
  have hκτ := hκ τ
  obtain ⟨P', hP'⟩ := fockPOVM_postprocess M (Kernel.id ×ₖ κ τ) inferInstance
  have hP'law : ∀ σ : Matrix J J ℂ, IsDensity σ → P'.law σ = M.law σ ⊗ₘ κ τ := by
    intro σ hσ
    have := M.law_prob σ hσ
    rw [hP' σ, Measure.compProd_eq_comp_prod]
  refine Measure.ext fun C hC => ?_
  have key := born_prod_eq M Q κ hκ hκQ hρ hτ P' hP'law hC
  have key' : (∑' i, ∑' j, cEff M κ C i j * (fun p q : J × I' => ρ p.1 q.1 * τ p.2 q.2) j i) =
      ∑' u, ∑' v, P'.effect C u v * ρ v u := key
  rw [M'.law_born _ hX C hC, hM', key', ← hP'law ρ hρ, P'.law_born ρ hρ C hC]

/-- Every finite principal effect is positive semidefinite. -/
lemma effect_posSemidef {J Ω : Type} [Fintype J] [DecidableEq J] [MeasurableSpace Ω]
    (M : FockPOVM J Ω) (B : Set Ω) (hB : MeasurableSet B) : (M.effect B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.IsHermitian.ext (fun i j =>
      (herm_of_form (fun s z => (M.effect_form B hB s z).1) j i).symm)
  · intro v
    have h := M.effect_form B hB Finset.univ v
    apply Complex.nonneg_iff.mpr
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc] using
      And.intro h.2.1 h.1.symm

lemma effect_posSemidef_full {J Ω : Type} [DecidableEq J] [MeasurableSpace Ω]
    (M : FockPOVM J Ω) (B : Set Ω) (hB : MeasurableSet B) : (M.effect B).PosSemidef := by
  refine ⟨Matrix.IsHermitian.ext (fun i j =>
    (herm_of_form (fun s z => (M.effect_form B hB s z).1) j i).symm), ?_⟩
  intro v
  have h := M.effect_form B hB v.support v
  exact Complex.nonneg_iff.mpr ⟨h.2.1, h.1.symm⟩

end BosonicLearn.Prop5.ComposeEffect

end
end

/- Local helper source: Solutions.Prop5PositiveDensity -/
section
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Matrix ComplexOrder

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-- Positivity of all measurable-set integrals forces positivity of a finite matrix density.
No topological or countable-generation hypothesis is imposed on the outcome space. -/
theorem matrix_density_posSemidef_ae {J O : Type*} [Fintype J] [MeasurableSpace O]
    (μ : Measure O) (E : Set O → Matrix J J ℂ) (e : O → Matrix J J ℂ)
    (hE : ∀ B, MeasurableSet B → (E B).PosSemidef)
    (he : ∀ i j, Integrable (fun x => e x i j) μ)
    (hset : ∀ B, MeasurableSet B → ∀ i j, ∫ x in B, e x i j ∂μ = E B i j) :
    ∀ᵐ x ∂μ, (e x).PosSemidef := by
  classical
  have hHermEntry : ∀ i j, (fun x => star (e x j i)) =ᵐ[μ] (fun x => e x i j) := by
    intro i j
    have hstar : Integrable (fun x => star (e x j i)) μ :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp (he j i)
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hstar (he i j)
    intro B hB hBfin
    simp only [Complex.star_def]
    rw [integral_conj, hset B hB j i, hset B hB i j]
    exact (hE B hB).isHermitian.apply i j
  have hHerm : ∀ᵐ x ∂μ, (e x).IsHermitian := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hHermEntry i))] with x hx
    exact Matrix.IsHermitian.ext hx
  let q : (J → ℂ) → O → ℂ := fun v x => star v ⬝ᵥ ((e x) *ᵥ v)
  have hqi : ∀ v, Integrable (q v) μ := by
    intro v
    unfold q Matrix.mulVec dotProduct
    apply integrable_finsetSum
    intro i hi
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j hj
    exact (he i j).mul_const _
  have hqset : ∀ v B, MeasurableSet B →
      ∫ x in B, q v x ∂μ = star v ⬝ᵥ ((E B) *ᵥ v) := by
    intro v B hB
    unfold q Matrix.mulVec dotProduct
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul, integral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_mul_const, hset B hB i j]
      · intro j hj
        exact ((he i j).mul_const _).integrableOn
    · intro i hi
      apply Integrable.const_mul
      apply integrable_finsetSum
      intro j hj
      exact ((he i j).mul_const _).integrableOn
  have hqnonneg : ∀ v, ∀ᵐ x ∂μ, 0 ≤ (q v x).re := by
    intro v
    apply ae_nonneg_of_forall_setIntegral_nonneg (hqi v).re
    intro B hB hBfin
    rw [integral_re (hqi v).integrableOn, hqset v B hB]
    exact (Complex.nonneg_iff.mp ((hE B hB).dotProduct_mulVec_nonneg v)).1
  let d : ℕ → (J → ℂ) := denseSeq (J → ℂ)
  have hd : DenseRange d := denseRange_denseSeq (J → ℂ)
  filter_upwards [hHerm, ae_all_iff.mpr (fun n => hqnonneg (d n))] with x hxH hxD
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hxH
  intro v
  apply Complex.nonneg_iff.mpr
  constructor
  · have hc : Continuous (fun v : J → ℂ => (star v ⬝ᵥ ((e x) *ᵥ v)).re) := by
      unfold Matrix.mulVec dotProduct
      fun_prop
    exact hd.induction_on (p := fun v => 0 ≤ (star v ⬝ᵥ ((e x) *ᵥ v)).re)
      v (isClosed_le continuous_const hc) hxD
  · exact (hxH.im_star_dotProduct_mulVec_self v).symm

/-- The same positivity result for countably infinite matrices. Their positivity is tested
on finitely supported vectors, so a countable intersection over finite principal submatrices suffices. -/
theorem countable_matrix_density_posSemidef_ae {I O : Type*} [Countable I] [MeasurableSpace O]
    (μ : Measure O) (E : Set O → Matrix I I ℂ) (e : O → Matrix I I ℂ)
    (hE : ∀ B, MeasurableSet B → (E B).PosSemidef)
    (he : ∀ i j, Integrable (fun x => e x i j) μ)
    (hset : ∀ B, MeasurableSet B → ∀ i j, ∫ x in B, e x i j ∂μ = E B i j) :
    ∀ᵐ x ∂μ, (e x).PosSemidef := by
  classical
  have hHermEntry : ∀ i j, (fun x => star (e x j i)) =ᵐ[μ] (fun x => e x i j) := by
    intro i j
    have hstar : Integrable (fun x => star (e x j i)) μ :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp (he j i)
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hstar (he i j)
    intro B hB hBfin
    simp only [Complex.star_def]
    rw [integral_conj, hset B hB j i, hset B hB i j]
    exact (hE B hB).isHermitian.apply i j
  have hHerm : ∀ᵐ x ∂μ, (e x).IsHermitian := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hHermEntry i))] with x hx
    exact Matrix.IsHermitian.ext hx
  have hfinite : ∀ s : Finset I, ∀ᵐ x ∂μ,
      ((e x).submatrix (fun i : s => (i : I)) (fun i : s => (i : I))).PosSemidef := by
    intro s
    apply matrix_density_posSemidef_ae μ
      (fun B => (E B).submatrix (fun i : s => (i : I)) (fun i : s => (i : I)))
      (fun x => (e x).submatrix (fun i : s => (i : I)) (fun i : s => (i : I)))
    · exact fun B hB => (hE B hB).submatrix _
    · exact fun i j => he i j
    · exact fun B hB i j => hset B hB i j
  filter_upwards [hHerm, ae_all_iff.mpr hfinite] with x hxH hxF
  refine ⟨hxH, ?_⟩
  intro v
  have hv := (hxF v.support).dotProduct_mulVec_nonneg (fun i : v.support => v i)
  let A : I → I → ℂ := e x
  change 0 ≤ ∑ i : v.support, star (v i) * (∑ j : v.support, A i j * v j) at hv
  change 0 ≤ ∑ i ∈ v.support, ∑ j ∈ v.support, star (v i) * A i j * v j
  simp_rw [Finset.mul_sum] at hv
  rw [Finset.sum_coe_sort v.support (fun i =>
    ∑ j : v.support, star (v i) * (A i j * v j))] at hv
  have hinner : ∀ i : I, (∑ j : v.support, star (v i) * (A i j * v j)) =
      ∑ j ∈ v.support, star (v i) * (A i j * v j) := fun i =>
    Finset.sum_coe_sort v.support (fun j => star (v i) * (A i j * v j))
  simp_rw [hinner] at hv
  simpa only [mul_assoc] using hv

/-- An almost-everywhere positive matrix density admits an everywhere-positive,
entrywise-measurable version, even on an arbitrary outcome sigma algebra. -/
theorem exists_posSemidef_density_version {I O : Type*} [MeasurableSpace O]
    (μ : Measure O) (e : O → Matrix I I ℂ)
    (hm : ∀ i j, Measurable (fun x => e x i j))
    (hp : ∀ᵐ x ∂μ, (e x).PosSemidef) :
    ∃ e' : O → Matrix I I ℂ,
      (∀ i j, Measurable (fun x => e' x i j)) ∧
      (∀ x, (e' x).PosSemidef) ∧ e' =ᵐ[μ] e := by
  classical
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  let e' : O → Matrix I I ℂ := fun x => if x ∈ N then 0 else e x
  refine ⟨e', ?_, ?_, ?_⟩
  · intro i j
    have heq : (fun x => e' x i j) = (fun x => if x ∈ N then 0 else e x i j) := by
      funext x
      dsimp only [e']
      split <;> rfl
    rw [heq]
    exact Measurable.ite hNm measurable_const (hm i j)
  · intro x
    by_cases hx : x ∈ N
    · simp only [e', if_pos hx]
      exact Matrix.PosSemidef.zero
    · simp only [e', if_neg hx]
      by_contra hbad
      exact hx (hNsub hbad)
  · have hgood : ∀ᵐ x ∂μ, x ∉ N := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_mem_eq] using hNzero
    filter_upwards [hgood] with x hx
    exact if_neg hx

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5Reference -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Every countable family of probability laws has a common probability
reference law, without restrictions on the outcome measurable space. -/
theorem common_probability_reference {ι Ω : Type*} [Countable ι] [Nonempty ι]
    [MeasurableSpace Ω] (μ : ι → Measure Ω) (hμ : ∀ i, IsProbabilityMeasure (μ i)) :
    ∃ ref : Measure Ω, IsProbabilityMeasure ref ∧ ∀ i, μ i ≪ ref := by
  classical
  letI (i : ι) : IsProbabilityMeasure (μ i) := hμ i
  let m : Measure Ω := Measure.sum μ
  obtain ⟨ν, hν, hmν, _⟩ := exists_isFiniteMeasure_absolutelyContinuous m
  letI : IsFiniteMeasure ν := hν
  have hdom : ∀ i, μ i ≪ ν := fun i =>
    (Measure.absolutelyContinuous_sum_right i Measure.AbsolutelyContinuous.rfl).trans hmν
  have hpos : ν Set.univ ≠ 0 := by
    intro hz
    have h := hdom (Classical.arbitrary ι) hz
    simpa using h
  let ref : Measure Ω := (ν Set.univ)⁻¹ • ν
  refine ⟨ref, ⟨?_⟩, ?_⟩
  · simp only [ref, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hpos (measure_ne_top ν Set.univ)
  · intro i
    exact (hdom i).smul_right (ENNReal.inv_ne_zero.mpr (measure_ne_top ν Set.univ))

/-- A POVM on a countable-basis Hilbert space has a single probability
reference dominating its Born laws on every density operator. Four
polarization states for each pair of basis indices form a countable
separating family, so no choice of densities indexed by states is needed. -/
theorem fockPOVM_probability_reference {I O : Type} [Countable I] [Nonempty I]
    [DecidableEq I] [MeasurableSpace O] (M : FockPOVM I O) :
    ∃ ref : Measure O, IsProbabilityMeasure ref ∧
      ∀ σ : Matrix I I ℂ, IsDensity σ → M.law σ ≪ ref := by
  classical
  choose τ coef hτ hcoef hentry using fun i j : I => effect_entry_born i j
  let μ : I × I × Fin 4 → Measure O := fun t => M.law (τ t.1 t.2.1 t.2.2)
  have hμ : ∀ t, IsProbabilityMeasure (μ t) := fun t =>
    M.law_prob _ (hτ t.1 t.2.1 t.2.2)
  obtain ⟨ref, href, hdom⟩ := common_probability_reference μ hμ
  refine ⟨ref, href, ?_⟩
  intro σ hσ
  apply Measure.AbsolutelyContinuous.mk
  intro B hB hzero
  have hE : ∀ i j, M.effect B i j = 0 := by
    intro i j
    rw [hentry i j O M B hB]
    apply Finset.sum_eq_zero
    intro k _
    have hzero' : M.law (τ i j k) B = 0 := hdom (i, j, k) hzero
    simp [hzero']
  rw [M.law_born σ hσ B hB]
  simp [hE]

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5EffectDensity -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open scoped ENNReal

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 600000

/-- Each matrix entry of a POVM has an integrable density against a common
probability reference. The outcome sigma algebra is unrestricted. -/
theorem fockPOVM_effect_density {I O : Type} [Countable I] [Nonempty I]
    [DecidableEq I] [MeasurableSpace O] (M : FockPOVM I O) :
    ∃ ref : Measure O, IsProbabilityMeasure ref ∧
      (∀ σ : Matrix I I ℂ, IsDensity σ → M.law σ ≪ ref) ∧
      ∃ e : O → Matrix I I ℂ,
        (∀ i j, Measurable fun x => e x i j) ∧
        (∀ i j, Integrable (fun x => e x i j) ref) ∧
        (∀ B, MeasurableSet B → ∀ i j, ∫ x in B, e x i j ∂ref = M.effect B i j) := by
  classical
  obtain ⟨ref, href, hdom⟩ := fockPOVM_probability_reference M
  letI : IsProbabilityMeasure ref := href
  choose τ coef hτ hcoef hentry using fun i j : I => effect_entry_born i j
  let μ : I → I → Fin 4 → Measure O := fun i j k => M.law (τ i j k)
  have hμ : ∀ i j k, IsProbabilityMeasure (μ i j k) :=
    fun i j k => M.law_prob _ (hτ i j k)
  letI (i j : I) (k : Fin 4) : IsProbabilityMeasure (μ i j k) := hμ i j k
  let f : I → I → Fin 4 → O → ℂ := fun i j k x => ((μ i j k).rnDeriv ref x).toReal
  have hfm : ∀ i j k, Measurable (f i j k) := by
    intro i j k
    exact Complex.measurable_ofReal.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hfi : ∀ i j k, Integrable (f i j k) ref := by
    intro i j k
    exact Measure.integrable_toReal_rnDeriv.ofReal
  have hfB : ∀ B, MeasurableSet B → ∀ i j k,
      ∫ x in B, f i j k x ∂ref = (((μ i j k) B).toReal : ℂ) := by
    intro B hB i j k
    rw [show (fun x => f i j k x) =
      (fun x => (((μ i j k).rnDeriv ref x).toReal : ℂ)) from rfl,
      integral_complex_ofReal, Measure.setIntegral_toReal_rnDeriv (hdom _ (hτ i j k))]
    rfl
  let e : O → Matrix I I ℂ := fun x i j => ∑ k, coef i j k * f i j k x
  refine ⟨ref, href, hdom, e, ?_, ?_, ?_⟩
  · intro i j
    exact Finset.measurable_sum _ fun k _ => measurable_const.mul (hfm i j k)
  · intro i j
    exact integrable_finset_sum _ fun k _ => (hfi i j k).const_mul _
  · intro B hB i j
    change (∫ x in B, ∑ k, coef i j k * f i j k x ∂ref) = _
    rw [integral_finset_sum _ (fun k _ => ((hfi i j k).const_mul _).integrableOn),
      hentry i j O M B hB]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, hfB B hB]

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5DualDensity -/
section
open MeasureTheory TopologicalSpace
open scoped ComplexOrder

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 800000

/-- If all set integrals lie in a dual cone of matrix tests, the density
lies in that dual cone almost everywhere. The set of tests can be arbitrary;
separability of the finite-dimensional matrix space handles the common null set. -/
theorem matrix_density_dual_positive_ae {J O : Type*} [Fintype J] [MeasurableSpace O]
    (μ : Measure O) (E : Set O → Matrix J J ℂ) (e : O → Matrix J J ℂ)
    (tests : Set (Matrix J J ℂ))
    (hE : ∀ B, MeasurableSet B → ∀ H ∈ tests, 0 ≤ matrixPair H (E B))
    (he : ∀ i j, Integrable (fun x => e x i j) μ)
    (hset : ∀ B, MeasurableSet B → ∀ i j, ∫ x in B, e x i j ∂μ = E B i j) :
    ∀ᵐ x ∂μ, ∀ H ∈ tests, 0 ≤ matrixPair H (e x) := by
  classical
  letI : SecondCountableTopology (Matrix J J ℂ) :=
    inferInstanceAs (SecondCountableTopology (J → J → ℂ))
  have hpairi : ∀ H : Matrix J J ℂ, Integrable (fun x => matrixPair H (e x)) μ := by
    intro H
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (he j i).const_mul _
  have hpairB : ∀ (H : Matrix J J ℂ) B, MeasurableSet B →
      ∫ x in B, matrixPair H (e x) ∂μ = matrixPair H (E B) := by
    intro H B hB
    unfold matrixPair
    have hiB : ∀ i j : J, IntegrableOn (fun x => H i j * e x j i) B μ :=
      fun i j => ((he j i).const_mul (H i j)).integrableOn
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hiB i j)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => hiB i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, hset B hB]
  have htest : ∀ H ∈ tests, ∀ᵐ x ∂μ, 0 ≤ matrixPair H (e x) := by
    intro H hH
    have hr : ∀ᵐ x ∂μ, 0 ≤ (matrixPair H (e x)).re := by
      apply ae_nonneg_of_forall_setIntegral_nonneg (hpairi H).re
      intro B hB _
      rw [integral_re (hpairi H).integrableOn, hpairB H B hB]
      exact (Complex.nonneg_iff.mp (hE B hB H hH)).1
    have hi : (fun x => (matrixPair H (e x)).im) =ᵐ[μ] 0 := by
      apply (hpairi H).im.ae_eq_zero_of_forall_setIntegral_eq_zero
      intro B hB _
      rw [integral_im (hpairi H).integrableOn, hpairB H B hB]
      exact (Complex.nonneg_iff.mp (hE B hB H hH)).2.symm
    filter_upwards [hr, hi] with x hrx hix
    exact Complex.nonneg_iff.mpr ⟨hrx, hix.symm⟩
  by_cases htests : tests.Nonempty
  · letI : Nonempty tests := htests.to_subtype
    let d : ℕ → tests := denseSeq tests
    have hd : DenseRange d := denseRange_denseSeq tests
    filter_upwards [ae_all_iff.mpr fun k => htest (d k) (d k).property] with x hx
    intro H hH
    have hc : Continuous (fun H : tests => matrixPair (H : Matrix J J ℂ) (e x)) := by
      apply continuous_finsetSum
      intro i _
      apply continuous_finsetSum
      intro j _
      apply Continuous.mul
      · exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
      · exact continuous_const
    exact hd.induction_on (p := fun H : tests => 0 ≤ matrixPair (H : Matrix J J ℂ) (e x))
      ⟨H, hH⟩ (isClosed_le continuous_const hc) hx
  · exact Filter.Eventually.of_forall fun x H hH => False.elim (htests ⟨H, hH⟩)

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5AdaptivePositive -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open scoped Matrix ComplexOrder ENNReal

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-- A density identity on measurable sets extends to bounded measurable test functions.
This is the finite polarization-measure form needed for composed POVM effects. -/
theorem integral_density_mul_eq_sum {Ω L : Type*} [MeasurableSpace Ω] [Fintype L]
    (ref : Measure Ω) [IsFiniteMeasure ref] (ν : L → Measure Ω)
    [∀ k, IsFiniteMeasure (ν k)] (hdom : ∀ k, ν k ≪ ref)
    (coef : L → ℂ) (e : Ω → ℂ) (he : Integrable e ref)
    (hset : ∀ B, MeasurableSet B → ∫ x in B, e x ∂ref =
      ∑ k, coef k * ((((ν k) B).toReal : ℝ) : ℂ))
    (g : Ω → ℂ) (hgm : Measurable g) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) :
    (∫ x, e x * g x ∂ref) = ∑ k, coef k * ∫ x, g x ∂ν k := by
  classical
  let f : L → Ω → ℂ := fun k x => ((ν k).rnDeriv ref x).toReal
  have hfi : ∀ k, Integrable (f k) ref := fun k => Measure.integrable_toReal_rnDeriv.ofReal
  have hfB : ∀ B, MeasurableSet B → ∀ k,
      ∫ x in B, f k x ∂ref = ((((ν k) B).toReal : ℝ) : ℂ) := by
    intro B hB k
    rw [show (fun x => f k x) = (fun x => (((ν k).rnDeriv ref x).toReal : ℂ)) from rfl,
      integral_complex_ofReal, Measure.setIntegral_toReal_rnDeriv (hdom k)]
    rfl
  have hef : e =ᵐ[ref] (fun x => ∑ k, coef k * f k x) := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ he
      (integrable_finsetSum _ (fun k _ => (hfi k).const_mul _))
    intro B hB hBfin
    rw [hset B hB, integral_finsetSum _ (fun k _ => ((hfi k).const_mul _).integrableOn)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul, hfB B hB]
  obtain ⟨C, hC⟩ := hgb
  have hfg : ∀ k, Integrable (fun x => f k x * g x) ref :=
    fun k => (hfi k).mul_bdd hgm.aestronglyMeasurable (ae_of_all ref hC)
  calc
    (∫ x, e x * g x ∂ref) = ∫ x, (∑ k, coef k * f k x) * g x ∂ref :=
      integral_congr_ae (hef.mul (ae_eq_refl g))
    _ = ∫ x, ∑ k, coef k * (f k x * g x) ∂ref := by
      congr 1
      funext x
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ k, coef k * ∫ x, f k x * g x ∂ref := by
      rw [integral_finsetSum _ (fun k _ => (hfg k).const_mul _)]
      exact Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)
    _ = ∑ k, coef k * ∫ x, g x ∂ν k := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      simpa only [f, Complex.real_smul] using
        (integral_rnDeriv_smul (hdom k) (f := g))

/-- Sequential composition can be chosen with the concrete integral effect formula
against any common density of the first POVM. -/
theorem compose_with_density_effect {J K Ω O : Type} [DecidableEq J] [DecidableEq K]
    [MeasurableSpace Ω] [MeasurableSpace O]
    (M : FockPOVM J Ω) (Q : Ω → FockPOVM K O)
    (κ : Matrix K K ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ)
    (ref : Measure Ω) [IsFiniteMeasure ref]
    (hdom : ∀ σ, IsDensity σ → M.law σ ≪ ref)
    (e : Ω → Matrix J J ℂ) (he : ∀ i j, Integrable (fun x => e x i j) ref)
    (hset : ∀ B, MeasurableSet B → ∀ i j, ∫ x in B, e x i j ∂ref = M.effect B i j) :
    ∃ M' : FockPOVM (J × K) (Ω × O),
      (∀ (ρ : Matrix J J ℂ) (τ : Matrix K K ℂ), IsDensity ρ → IsDensity τ →
        M'.law (fun p q => ρ p.1 q.1 * τ p.2 q.2) = (M.law ρ) ⊗ₘ (κ τ)) ∧
      ∀ C, MeasurableSet C → ∀ p q,
        M'.effect C p q = ∫ x, e x p.1 q.1 * (Q x).effect (Prod.mk x ⁻¹' C) p.2 q.2 ∂ref := by
  obtain ⟨M', hEff, hLaw⟩ := ComposeEffect.compose_with_effect M Q κ hκ hκQ
  refine ⟨M', hLaw, ?_⟩
  intro C hC p q
  rw [hEff, ComposeEffect.cEff_eq M Q κ hκ hκQ hC]
  let ν : Fin 4 → Measure Ω := fun c => M.law (ComposeEffect.tS p.1 q.1 c)
  letI (c : Fin 4) : IsProbabilityMeasure (ν c) :=
    M.law_prob _ (ComposeEffect.tS_density p.1 q.1 c)
  symm
  apply integral_density_mul_eq_sum ref ν
    (fun c => hdom _ (ComposeEffect.tS_density p.1 q.1 c))
    (ComposeEffect.cS p.1 q.1) (fun x => e x p.1 q.1) (he p.1 q.1)
  · intro B hB
    rw [hset B hB, ComposeEffect.entry_eq M hB]
  · exact ComposeEffect.gE_measurable Q κ hκ hκQ hC p.2 q.2
  · exact ⟨1, fun x => ComposeEffect.gE_norm_le Q hC p.2 q.2 x⟩

/-- Adding an outcome-dependent last local measurement preserves positivity against
all tensors of previous allowed vectors and arbitrary vectors of the last system. -/
theorem compose_preserves_product_tests {J K Ω O : Type} [Fintype J] [Fintype K]
    [Nonempty J] [DecidableEq J] [DecidableEq K] [MeasurableSpace Ω] [MeasurableSpace O]
    (M : FockPOVM J Ω) (Q : Ω → FockPOVM K O)
    (κ : Matrix K K ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ)
    (W : Set (J → ℂ))
    (hM : ∀ B, MeasurableSet B → ∀ F : Matrix J J ℂ, F.IsHermitian →
      (∀ v ∈ W, 0 ≤ star v ⬝ᵥ (F *ᵥ v)) → 0 ≤ matrixPair F (M.effect B)) :
    ∃ M' : FockPOVM (J × K) (Ω × O),
      (∀ (ρ : Matrix J J ℂ) (τ : Matrix K K ℂ), IsDensity ρ → IsDensity τ →
        M'.law (fun p q => ρ p.1 q.1 * τ p.2 q.2) = (M.law ρ) ⊗ₘ (κ τ)) ∧
      ∀ C, MeasurableSet C → ∀ H : Matrix (J × K) (J × K) ℂ, H.IsHermitian →
        (∀ v ∈ W, ∀ w : K → ℂ, 0 ≤
          star (fun p : J × K => v p.1 * w p.2) ⬝ᵥ
            (H *ᵥ (fun p : J × K => v p.1 * w p.2))) →
        0 ≤ matrixPair H (M'.effect C) := by
  obtain ⟨ref, href, hdom, e, hem, hei, heB⟩ := fockPOVM_effect_density M
  letI : IsProbabilityMeasure ref := href
  have hepos := matrix_density_posSemidef_ae ref M.effect e
    (ComposeEffect.effect_posSemidef M) hei heB
  let tests : Set (Matrix J J ℂ) := {F | F.IsHermitian ∧ ∀ v ∈ W, 0 ≤ star v ⬝ᵥ (F *ᵥ v)}
  have hetest := matrix_density_dual_positive_ae ref M.effect e tests
    (fun B hB F hF => hM B hB F hF.1 hF.2) hei heB
  obtain ⟨M', hLaw, hEff⟩ := compose_with_density_effect M Q κ hκ hκQ ref hdom e hei heB
  refine ⟨M', hLaw, ?_⟩
  intro C hC H hH hprod
  have hEff' : M'.effect C = fun p q =>
      ∫ x, e x p.1 q.1 * (Q x).effect (Prod.mk x ⁻¹' C) p.2 q.2 ∂ref := by
    funext p q
    exact hEff C hC p q
  rw [hEff']
  apply adaptive_block_positive_last_step ref W H hH hprod e hei
    (hepos.mono (fun x hx => hx.isHermitian))
  · filter_upwards [hetest] with x hx F hFH hFq
    exact hx F ⟨hFH, hFq⟩
  · intro a b
    exact (ComposeEffect.gE_measurable Q κ hκ hκQ hC a b).aestronglyMeasurable
  · exact ⟨1, fun x a b => ComposeEffect.gE_norm_le Q hC a b x⟩
  · exact ae_of_all ref (fun x => ComposeEffect.effect_posSemidef (Q x) _
      (measurable_prodMk_left hC))

/-- The adaptive last-step theorem only needs a finite submatrix of the accumulated effect.
The actual quantum basis may remain countably infinite. -/
theorem compose_preserves_submatrix_tests {J₀ K₀ J K Ω O : Type}
    [Countable J₀] [Nonempty J₀] [DecidableEq J₀] [DecidableEq K₀]
    [Fintype J] [Fintype K] [DecidableEq K] [MeasurableSpace Ω] [MeasurableSpace O]
    (M : FockPOVM J₀ Ω) (Q : Ω → FockPOVM K₀ O)
    (κ : Matrix K₀ K₀ ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ)
    (a : J → J₀) (b : K → K₀) (W : Set (J → ℂ))
    (hM : ∀ B, MeasurableSet B → ∀ F : Matrix J J ℂ, F.IsHermitian →
      (∀ v ∈ W, 0 ≤ star v ⬝ᵥ (F *ᵥ v)) →
        0 ≤ matrixPair F ((M.effect B).submatrix a a)) :
    ∃ M' : FockPOVM (J₀ × K₀) (Ω × O),
      (∀ (ρ : Matrix J₀ J₀ ℂ) (τ : Matrix K₀ K₀ ℂ), IsDensity ρ → IsDensity τ →
        M'.law (fun p q => ρ p.1 q.1 * τ p.2 q.2) = (M.law ρ) ⊗ₘ (κ τ)) ∧
      ∀ C, MeasurableSet C → ∀ H : Matrix (J × K) (J × K) ℂ, H.IsHermitian →
        (∀ v ∈ W, ∀ w : K → ℂ, 0 ≤
          star (fun p : J × K => v p.1 * w p.2) ⬝ᵥ
            (H *ᵥ (fun p : J × K => v p.1 * w p.2))) →
        0 ≤ matrixPair H ((M'.effect C).submatrix (Prod.map a b) (Prod.map a b)) := by
  obtain ⟨ref, href, hdom, e, hem, hei, heB⟩ := fockPOVM_effect_density M
  letI : IsProbabilityMeasure ref := href
  let e' : Ω → Matrix J J ℂ := fun x => (e x).submatrix a a
  let E' : Set Ω → Matrix J J ℂ := fun B => (M.effect B).submatrix a a
  have he'i : ∀ i j, Integrable (fun x => e' x i j) ref := fun i j => hei (a i) (a j)
  have he'B : ∀ B, MeasurableSet B → ∀ i j, ∫ x in B, e' x i j ∂ref = E' B i j :=
    fun B hB i j => heB B hB (a i) (a j)
  have hepos := matrix_density_posSemidef_ae ref E' e'
    (fun B hB => (ComposeEffect.effect_posSemidef_full M B hB).submatrix a) he'i he'B
  let tests : Set (Matrix J J ℂ) := {F | F.IsHermitian ∧ ∀ v ∈ W, 0 ≤ star v ⬝ᵥ (F *ᵥ v)}
  have hetest := matrix_density_dual_positive_ae ref E' e' tests
    (fun B hB F hF => hM B hB F hF.1 hF.2) he'i he'B
  obtain ⟨M', hLaw, hEff⟩ := compose_with_density_effect M Q κ hκ hκQ ref hdom e hei heB
  refine ⟨M', hLaw, ?_⟩
  intro C hC H hH hprod
  have hEff' : (M'.effect C).submatrix (Prod.map a b) (Prod.map a b) = fun p q =>
      ∫ x, e' x p.1 q.1 * (Q x).effect (Prod.mk x ⁻¹' C) (b p.2) (b q.2) ∂ref := by
    funext p q
    exact hEff C hC (Prod.map a b p) (Prod.map a b q)
  rw [hEff']
  apply adaptive_block_positive_last_step ref W H hH hprod e' he'i
    (hepos.mono (fun x hx => hx.isHermitian))
    (G := fun x => ((Q x).effect (Prod.mk x ⁻¹' C)).submatrix b b)
  · filter_upwards [hetest] with x hx F hFH hFq
    exact hx F ⟨hFH, hFq⟩
  · intro u v
    exact (ComposeEffect.gE_measurable Q κ hκ hκQ hC (b u) (b v)).aestronglyMeasurable
  · exact ⟨1, fun x u v => ComposeEffect.gE_norm_le Q hC (b u) (b v) x⟩
  · exact ae_of_all ref (fun x =>
      (ComposeEffect.effect_posSemidef_full (Q x) _ (measurable_prodMk_left hC)).submatrix b)

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5FiniteAdaptive -/
section
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix ComplexOrder

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-- Adaptive fresh-copy measurements on a fixed finite local Hilbert-space basis. -/
structure FiniteAdaptiveScheme (J : Type) [DecidableEq J] (N : ℕ) (O : Type) [MeasurableSpace O] where
  povm : (t : Fin N) → (Fin t → O) → FockPOVM J O
  round : Matrix J J ℂ → (t : Fin N) → Kernel (Fin t → O) O
  round_markov : ∀ ρ t, IsMarkovKernel (round ρ t)
  round_born : ∀ ρ, IsDensity ρ → ∀ (t : Fin N) (x : Fin t → O), round ρ t x = (povm t x).law ρ

/-! ### Product states on the first `k` copies, and appending a copy -/

private def prodState {N : ℕ} {J : Type} (k : ℕ) (hk : k ≤ N)
    (τ : Fin N → Matrix (J) (J) ℂ) :
    Matrix (Fin k → J) (Fin k → J) ℂ :=
  Matrix.of fun u v => ∏ t : Fin k, τ (Fin.castLE hk t) (u t) (v t)

private def snocEquiv (α : Type) (k : ℕ) : (Fin k → α) × α ≃ (Fin (k + 1) → α) where
  toFun p := Fin.snoc (α := fun _ => α) p.1 p.2
  invFun u := (Fin.init u, u (Fin.last k))
  left_inv p := by simp [Fin.init_snoc]
  right_inv u := Fin.snoc_init_self u

private lemma measurable_snoc (O : Type) [MeasurableSpace O] (k : ℕ) :
    Measurable fun p : (Fin k → O) × O => (Fin.snoc (α := fun _ => O) p.1 p.2 : Fin (k + 1) → O) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · have h : Measurable fun p : (Fin k → O) × O => p.1 j := (measurable_pi_apply j).comp measurable_fst
    simpa using h

private lemma prodState_succ {N k : ℕ} {J : Type} (hk1 : k + 1 ≤ N)
    (τ : Fin N → Matrix (J) (J) ℂ) :
    prodState (k + 1) hk1 τ = fun i j =>
      (fun p q : (Fin k → J) × J =>
        prodState k (Nat.le_of_succ_le hk1) τ p.1 q.1 * τ ⟨k, hk1⟩ p.2 q.2)
        ((snocEquiv (J) k).symm i) ((snocEquiv (J) k).symm j) := by
  funext i j
  simp only [prodState, Matrix.of_apply, snocEquiv, Equiv.coe_fn_symm_mk]
  rw [Fin.prod_univ_castSucc]
  rfl

/-! ### No copies: the one-point system -/

private lemma base_density (J : Type) [DecidableEq J] :
    IsDensity (fun (_ _ : Fin 0 → J) => (1 : ℂ)) := by
  classical
  refine ⟨⟨{
    left := fun m => if m = 0 then lp.single 2 (fun i => Fin.elim0 i) 1 else 0
    right := fun m => if m = 0 then lp.single 2 (fun i => Fin.elim0 i) 1 else 0
    summable := summable_of_ne_finset_zero (s := {0}) fun m hm => by
      have : m ≠ 0 := by simpa using hm
      simp [this]
    coefficients := ?_ }⟩, ?_, ?_⟩
  · intro i j
    rw [tsum_eq_single 0 (fun m hm => by simp [hm])]
    have hi : i = fun i => Fin.elim0 i := Subsingleton.elim _ _
    have hj : j = fun i => Fin.elim0 i := Subsingleton.elim _ _
    subst hi hj
    simp
  · intro s z
    have key : ∑ i ∈ s, ∑ j ∈ s, star (z i) * (1 : ℂ) * z j = ((‖∑ i ∈ s, z i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp
    rw [key]
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity⟩
  · have h : HasSum (fun _ : Fin 0 → J => ((1 : ℂ)).re) 1 := by
      have := hasSum_fintype (fun _ : Fin 0 → J => ((1 : ℂ)).re)
      simp
    exact ⟨h.summable, h.tsum_eq⟩

private def basePOVM (J : Type) [DecidableEq J] (O : Type) [MeasurableSpace O] :
    FockPOVM (Fin 0 → J) (Fin 0 → O) := by
  classical
  exact {
    effect := fun B => if (fun i => Fin.elim0 i) ∈ B then 1 else 0
    effect_form := by
      intro B _ s z
      by_cases hB : (fun i => Fin.elim0 i) ∈ B
      · have key : ∑ i ∈ s, ∑ j ∈ s, star (z i) * (1 : Matrix _ _ ℂ) i j * z j =
            ((∑ i ∈ s, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
          push_cast
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj])
            (fun h => (h hi).elim)]
          simp [← Complex.conj_mul']
        simp only [hB, if_true]
        rw [key]
        exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity, by rw [Complex.ofReal_re]⟩
      · simp only [hB, if_false, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]
        exact ⟨rfl, le_rfl, Finset.sum_nonneg fun i _ => by positivity⟩
    effect_univ := by simp
    law := fun _ => Measure.dirac (fun i => Fin.elim0 i)
    law_prob := fun _ _ => inferInstance
    law_born := by
      intro ρ hρ B hB
      have hd : ∀ i : Fin 0 → J, i = fun i => Fin.elim0 i := fun i =>
        Subsingleton.elim _ _
      have htr : (ρ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).re = 1 := by
        have h := hρ.2.2.2
        rwa [tsum_eq_single (fun i => Fin.elim0 i) (fun b hb => (hb (hd b)).elim)] at h
      rw [Measure.dirac_apply' _ hB]
      by_cases hmem : (fun i => Fin.elim0 i) ∈ B
      · simp only [hmem, if_true, Set.indicator_of_mem, Pi.one_apply]
        rw [tsum_eq_single (fun i => Fin.elim0 i) (fun b hb => (hb (hd b)).elim),
          tsum_eq_single (fun i => Fin.elim0 i) (fun b hb => (hb (hd b)).elim)]
        simp [htr]
      · simp [hmem] }

theorem reindex_with_effect {J J' Ω : Type} [DecidableEq J] [DecidableEq J'] [MeasurableSpace Ω]
    (M : FockPOVM J Ω) (e : J ≃ J') :
    ∃ M' : FockPOVM J' Ω,
      (∀ B i j, M'.effect B i j = M.effect B (e.symm i) (e.symm j)) ∧ ∀ ρ : Matrix J J ℂ, IsDensity ρ →
      M'.law (fun i j => ρ (e.symm i) (e.symm j)) = M.law ρ := by
  -- relabelling back a density operator on `ℓ²(J')` gives a density operator on `ℓ²(J)`
  have hden : ∀ ρ' : Matrix J' J' ℂ, IsDensity ρ' → IsDensity (fun i j : J => ρ' (e i) (e j)) := by
    intro ρ' h
    have h' := isDensity_reindex e.symm h
    simpa using h'
  refine ⟨{
    effect := fun B i j => M.effect B (e.symm i) (e.symm j)
    effect_form := ?_
    effect_univ := ?_
    law := fun ρ' => M.law (fun i j => ρ' (e i) (e j))
    law_prob := fun ρ' h => M.law_prob _ (hden ρ' h)
    law_born := ?_ }, (by intros; rfl), ?_⟩
  · intro B hB s z
    have h := M.effect_form B hB (s.map e.symm.toEmbedding) (fun a => z (e a))
    simpa [Finset.sum_map] using h
  · funext i j
    simp [M.effect_univ, Matrix.one_apply]
  · intro ρ' h B hB
    rw [M.law_born _ (hden ρ' h) B hB]
    congr 2
    rw [← Equiv.tsum_eq e.symm]
    refine tsum_congr fun i' => ?_
    rw [← Equiv.tsum_eq e.symm]
    refine tsum_congr fun j' => ?_
    simp
  · intro ρ _
    simp

/-- Deterministic outcome relabelling with its effect formula retained. -/
def mapOutcome {J Ω Ω' : Type} [DecidableEq J] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (M : FockPOVM J Ω) (f : Ω → Ω') (hf : Measurable f) : FockPOVM J Ω' where
  effect B := M.effect (f ⁻¹' B)
  effect_form B hB := M.effect_form _ (hf hB)
  effect_univ := by simpa using M.effect_univ
  law ρ := (M.law ρ).map f
  law_prob ρ hρ := by
    have := M.law_prob ρ hρ
    exact Measure.isProbabilityMeasure_map hf.aemeasurable
  law_born ρ hρ B hB := by
    rw [Measure.map_apply hf hB]
    exact M.law_born ρ hρ _ (hf hB)

/-- Tensor-product vectors on a tuple basis. -/
def tensorVector {J : Type} (k : ℕ) (φ : Fin k → J → ℂ) : (Fin k → J) → ℂ :=
  fun u => ∏ t, φ t (u t)

lemma matrixPair_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (H : Matrix J J ℂ) (A : Matrix I I ℂ) :
    matrixPair H (fun i j => A (e.symm i) (e.symm j)) =
      matrixPair (fun i j => H (e i) (e j)) A := by
  unfold matrixPair
  symm
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv e
  intro j
  simp

lemma quadratic_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (H : Matrix J J ℂ) (v : I → ℂ) :
    star v ⬝ᵥ ((fun i j => H (e i) (e j)) *ᵥ v) =
      star (fun j => v (e.symm j)) ⬝ᵥ (H *ᵥ (fun j => v (e.symm j))) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  apply Fintype.sum_equiv e
  intro i
  simp only [Equiv.symm_apply_apply]
  congr 1
  apply Fintype.sum_equiv e
  intro j
  simp

/-- The collective effect of every finite adaptive prefix lies in the dual cone of
matrices nonnegative on product vectors. -/
theorem finite_adaptive_stage {J O : Type} [Fintype J] [Nonempty J] [DecidableEq J]
    [MeasurableSpace O] {N : ℕ} (S : FiniteAdaptiveScheme J N O) :
    ∀ (k : ℕ) (hk : k ≤ N),
      ∃ M : FockPOVM (Fin k → J) (Fin k → O),
        (∀ τ : Fin N → Matrix J J ℂ, (∀ t, IsDensity (τ t)) →
          IsDensity (prodState k hk τ) ∧
            M.law (prodState k hk τ) = sequentialLaw (fun t => S.round (τ t) t) k hk) ∧
        ∀ B, MeasurableSet B → ∀ H : Matrix (Fin k → J) (Fin k → J) ℂ,
          H.IsHermitian → (∀ φ : Fin k → J → ℂ,
            0 ≤ star (tensorVector k φ) ⬝ᵥ (H *ᵥ tensorVector k φ)) →
          0 ≤ matrixPair H (M.effect B) := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨basePOVM J O, ?_, ?_⟩
    · intro τ hτ
      refine ⟨?_, rfl⟩
      have e : prodState 0 hk τ = fun _ _ => (1 : ℂ) := by
        funext u v
        simp [prodState]
      rw [e]
      exact base_density J
    · intro B hB H hH hq
      by_cases hBmem : (fun i : Fin 0 => Fin.elim0 i) ∈ B
      · have h := hq (fun t => Fin.elim0 t)
        simpa [matrixPair, basePOVM, hBmem, tensorVector, dotProduct, Matrix.mulVec] using h
      · simp [matrixPair, basePOVM, hBmem]
  | succ k ih =>
    intro hk1
    obtain ⟨M, hML, hMP⟩ := ih (Nat.le_of_succ_le hk1)
    let W : Set ((Fin k → J) → ℂ) := Set.range (tensorVector k)
    obtain ⟨M1, hM1, hM1P⟩ := compose_preserves_product_tests M
      (S.povm ⟨k, hk1⟩) (fun τ' => S.round τ' ⟨k, hk1⟩)
      (fun τ' => S.round_markov τ' ⟨k, hk1⟩)
      (fun τ' hτ' x => S.round_born τ' hτ' ⟨k, hk1⟩ x) W
      (fun B hB F hF hW => hMP B hB F hF (fun φ => hW _ ⟨φ, rfl⟩))
    obtain ⟨M2, hM2E, hM2⟩ := reindex_with_effect M1 (snocEquiv J k)
    let f : (Fin k → O) × O → (Fin (k+1) → O) := fun p => Fin.snoc p.1 p.2
    have hf : Measurable f := measurable_snoc O k
    let M3 := mapOutcome M2 f hf
    refine ⟨M3, ?_, ?_⟩
    · intro τ hτ
      obtain ⟨hD, hL⟩ := hML τ hτ
      have hprod := isDensity_prod hD (hτ ⟨k, hk1⟩)
      refine ⟨?_, ?_⟩
      · rw [prodState_succ]
        exact isDensity_reindex (snocEquiv J k) hprod
      · change (M2.law (prodState (k+1) hk1 τ)).map f = _
        rw [prodState_succ, hM2 _ hprod, hM1 _ _ hD (hτ ⟨k, hk1⟩), hL]
        rfl
    · intro B hB H hH hq
      change 0 ≤ matrixPair H (M2.effect (f ⁻¹' B))
      have hE : M2.effect (f ⁻¹' B) = fun i j =>
          M1.effect (f ⁻¹' B) ((snocEquiv J k).symm i) ((snocEquiv J k).symm j) := by
        funext i j
        exact hM2E _ i j
      rw [hE, matrixPair_reindex]
      apply hM1P _ (hf hB) _ (hH.submatrix (snocEquiv J k))
      rintro v ⟨φ, rfl⟩ w
      change 0 ≤ star (fun p : (Fin k → J) × J => tensorVector k φ p.1 * w p.2) ⬝ᵥ
        ((fun p q => H (snocEquiv J k p) (snocEquiv J k q)) *ᵥ
          (fun p : (Fin k → J) × J => tensorVector k φ p.1 * w p.2))
      rw [quadratic_reindex]
      have hv : (fun u => (fun p : (Fin k → J) × J => tensorVector k φ p.1 * w p.2)
          ((snocEquiv J k).symm u)) = tensorVector (k+1) (Fin.snoc φ w) := by
        funext u
        simp [tensorVector, snocEquiv, Fin.prod_univ_castSucc, Fin.init]
      rw [hv]
      exact hq (Fin.snoc φ w)

/-- Every finite adaptive measurement is represented by a collective POVM whose effects
are nonnegative against every Hermitian operator that is nonnegative on product vectors. -/
theorem finite_adaptive_product_positive {J O : Type} [Fintype J] [Nonempty J] [DecidableEq J]
    [MeasurableSpace O] {N : ℕ} (S : FiniteAdaptiveScheme J N O) :
    ∃ M : FockPOVM (Fin N → J) (Fin N → O),
      (∀ τ : Fin N → Matrix J J ℂ, (∀ t, IsDensity (τ t)) →
        M.law (fun u v => ∏ t, τ t (u t) (v t)) =
          sequentialLaw (fun t => S.round (τ t) t) N le_rfl) ∧
      ∀ B, MeasurableSet B → ∀ H : Matrix (Fin N → J) (Fin N → J) ℂ,
        H.IsHermitian → (∀ φ : Fin N → J → ℂ,
          0 ≤ star (tensorVector N φ) ⬝ᵥ (H *ᵥ tensorVector N φ)) →
        0 ≤ matrixPair H (M.effect B) := by
  obtain ⟨M, hML, hMP⟩ := finite_adaptive_stage S N le_rfl
  refine ⟨M, ?_, hMP⟩
  intro τ hτ
  exact (hML τ hτ).2

/-- Coordinatewise inclusion of a finite local test basis into a countable quantum basis. -/
def basisEmbed {I J : Type} (k : ℕ) (a : J → I) : (Fin k → J) → (Fin k → I) :=
  fun u t => a (u t)

/-- The adaptive induction can be carried out on finite test blocks while retaining
all original countable-basis POVMs and their exact Born laws. -/
theorem basis_adaptive_submatrix_stage {I J O : Type}
    [Countable I] [Nonempty I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [MeasurableSpace O] {N : ℕ} (S : FiniteAdaptiveScheme I N O) (a : J → I) :
    ∀ (k : ℕ) (hk : k ≤ N),
      ∃ M : FockPOVM (Fin k → I) (Fin k → O),
        (∀ τ : Fin N → Matrix I I ℂ, (∀ t, IsDensity (τ t)) →
          IsDensity (prodState k hk τ) ∧
            M.law (prodState k hk τ) = sequentialLaw (fun t => S.round (τ t) t) k hk) ∧
        ∀ B, MeasurableSet B → ∀ H : Matrix (Fin k → J) (Fin k → J) ℂ,
          H.IsHermitian → (∀ φ : Fin k → J → ℂ,
            0 ≤ star (tensorVector k φ) ⬝ᵥ (H *ᵥ tensorVector k φ)) →
          0 ≤ matrixPair H ((M.effect B).submatrix (basisEmbed k a) (basisEmbed k a)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨basePOVM I O, ?_, ?_⟩
    · intro τ hτ
      refine ⟨?_, rfl⟩
      have e : prodState 0 hk τ = fun _ _ => (1 : ℂ) := by
        funext u v
        simp [prodState]
      rw [e]
      exact base_density I
    · intro B hB H hH hq
      by_cases hBmem : (fun i : Fin 0 => Fin.elim0 i) ∈ B
      · have h := hq (fun t => Fin.elim0 t)
        simpa [matrixPair, basePOVM, hBmem, tensorVector, dotProduct, Matrix.mulVec,
          Matrix.submatrix_apply, basisEmbed] using h
      · simp [matrixPair, basePOVM, hBmem, Matrix.submatrix_apply]
  | succ k ih =>
    intro hk1
    obtain ⟨M, hML, hMP⟩ := ih (Nat.le_of_succ_le hk1)
    let W : Set ((Fin k → J) → ℂ) := Set.range (tensorVector k)
    obtain ⟨M1, hM1, hM1P⟩ := compose_preserves_submatrix_tests M
      (S.povm ⟨k, hk1⟩) (fun τ' => S.round τ' ⟨k, hk1⟩)
      (fun τ' => S.round_markov τ' ⟨k, hk1⟩)
      (fun τ' hτ' x => S.round_born τ' hτ' ⟨k, hk1⟩ x) (basisEmbed k a) a W
      (fun B hB F hF hW => hMP B hB F hF (fun φ => hW _ ⟨φ, rfl⟩))
    obtain ⟨M2, hM2E, hM2⟩ := reindex_with_effect M1 (snocEquiv I k)
    let f : (Fin k → O) × O → (Fin (k+1) → O) := fun p => Fin.snoc p.1 p.2
    have hf : Measurable f := measurable_snoc O k
    let M3 := mapOutcome M2 f hf
    refine ⟨M3, ?_, ?_⟩
    · intro τ hτ
      obtain ⟨hD, hL⟩ := hML τ hτ
      have hprod := isDensity_prod hD (hτ ⟨k, hk1⟩)
      refine ⟨?_, ?_⟩
      · rw [prodState_succ]
        exact isDensity_reindex (snocEquiv I k) hprod
      · change (M2.law (prodState (k+1) hk1 τ)).map f = _
        rw [prodState_succ, hM2 _ hprod, hM1 _ _ hD (hτ ⟨k, hk1⟩), hL]
        rfl
    · intro B hB H hH hq
      change 0 ≤ matrixPair H ((M2.effect (f ⁻¹' B)).submatrix
        (basisEmbed (k+1) a) (basisEmbed (k+1) a))
      have hE : (M2.effect (f ⁻¹' B)).submatrix (basisEmbed (k+1) a) (basisEmbed (k+1) a) =
          fun i j => ((M1.effect (f ⁻¹' B)).submatrix (Prod.map (basisEmbed k a) a)
            (Prod.map (basisEmbed k a) a)) ((snocEquiv J k).symm i) ((snocEquiv J k).symm j) := by
        funext i j
        rw [Matrix.submatrix_apply, hM2E]
        rfl
      rw [hE, matrixPair_reindex]
      apply hM1P _ (hf hB) _ (hH.submatrix (snocEquiv J k))
      rintro v ⟨φ, rfl⟩ w
      change 0 ≤ star (fun p : (Fin k → J) × J => tensorVector k φ p.1 * w p.2) ⬝ᵥ
        ((fun p q => H (snocEquiv J k p) (snocEquiv J k q)) *ᵥ
          (fun p : (Fin k → J) × J => tensorVector k φ p.1 * w p.2))
      rw [quadratic_reindex]
      have hv : (fun u => (fun p : (Fin k → J) × J => tensorVector k φ p.1 * w p.2)
          ((snocEquiv J k).symm u)) = tensorVector (k+1) (Fin.snoc φ w) := by
        funext u
        simp [tensorVector, snocEquiv, Fin.prod_univ_castSucc, Fin.init]
      rw [hv]
      exact hq (Fin.snoc φ w)

/-- Every finite principal tensor block of an adaptive effect is nonnegative against
operators nonnegative on product vectors, with no restriction on the outcome sigma algebra. -/
theorem basis_adaptive_submatrix_positive {I J O : Type}
    [Countable I] [Nonempty I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [MeasurableSpace O] {N : ℕ} (S : FiniteAdaptiveScheme I N O) (a : J → I) :
    ∃ M : FockPOVM (Fin N → I) (Fin N → O),
      (∀ τ : Fin N → Matrix I I ℂ, (∀ t, IsDensity (τ t)) →
        M.law (fun u v => ∏ t, τ t (u t) (v t)) =
          sequentialLaw (fun t => S.round (τ t) t) N le_rfl) ∧
      ∀ B, MeasurableSet B → ∀ H : Matrix (Fin N → J) (Fin N → J) ℂ,
        H.IsHermitian → (∀ φ : Fin N → J → ℂ,
          0 ≤ star (tensorVector N φ) ⬝ᵥ (H *ᵥ tensorVector N φ)) →
        0 ≤ matrixPair H ((M.effect B).submatrix (basisEmbed N a) (basisEmbed N a)) := by
  obtain ⟨M, hML, hMP⟩ := basis_adaptive_submatrix_stage S a N le_rfl
  exact ⟨M, fun τ hτ => (hML τ hτ).2, hMP⟩

/-- The finite-block product-positive tester property for the original bosonic adaptive scheme. -/
theorem adaptive_scheme_submatrix_product_positive {n N : ℕ} {J O : Type}
    [Fintype J] [DecidableEq J] [MeasurableSpace O]
    (S : AdaptiveScheme n N O) (a : J → Occupation (Fin n)) :
    ∃ M : FockPOVM (Fin N → Occupation (Fin n)) (Fin N → O),
      (∀ τ : Fin N → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ,
        (∀ t, IsDensity (τ t)) →
        M.law (fun u v => ∏ t, τ t (u t) (v t)) =
          sequentialLaw (fun t => S.round (τ t) t) N le_rfl) ∧
      ∀ B, MeasurableSet B → ∀ H : Matrix (Fin N → J) (Fin N → J) ℂ,
        H.IsHermitian → (∀ φ : Fin N → J → ℂ,
          0 ≤ star (tensorVector N φ) ⬝ᵥ (H *ᵥ tensorVector N φ)) →
        0 ≤ matrixPair H ((M.effect B).submatrix (basisEmbed N a) (basisEmbed N a)) := by
  exact basis_adaptive_submatrix_positive
    ⟨S.povm, S.round, S.round_markov, S.round_born⟩ a

/-- Coordinate evaluation from a larger finite basis to a selected finite basis. -/
def coordinateMatrix {L K : Type*} [DecidableEq K] (e : L → K) : Matrix L K ℂ :=
  fun a i => if e a = i then 1 else 0

lemma coordinateMatrix_mulVec {L K : Type*} [Fintype K] [DecidableEq K]
    (e : L → K) (v : K → ℂ) : coordinateMatrix e *ᵥ v = fun a => v (e a) := by
  funext a
  simp [coordinateMatrix, Matrix.mulVec, dotProduct]

lemma coordinateMatrix_mul_mul_conjTranspose {L K : Type*} [Fintype K] [DecidableEq K]
    (e : L → K) (A : Matrix K K ℂ) :
    coordinateMatrix e * A * (coordinateMatrix e).conjTranspose = A.submatrix e e := by
  ext a b
  simp [coordinateMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma matrixPair_eq_trace {L : Type*} [Fintype L] (H A : Matrix L L ℂ) :
    matrixPair H A = (H * A).trace := rfl

/-- Extending a test by coordinate inclusion preserves its pairing with a restricted effect. -/
lemma matrixPair_coordinate_lift {L K : Type*} [Fintype L] [Fintype K] [DecidableEq K]
    (e : L → K) (H : Matrix L L ℂ) (A : Matrix K K ℂ) :
    matrixPair ((coordinateMatrix e).conjTranspose * H * coordinateMatrix e) A =
      matrixPair H (A.submatrix e e) := by
  rw [matrixPair_eq_trace, matrixPair_eq_trace]
  calc
    _ = ((coordinateMatrix e).conjTranspose * (H * (coordinateMatrix e * A))).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((H * (coordinateMatrix e * A)) * (coordinateMatrix e).conjTranspose).trace :=
      Matrix.trace_mul_comm _ _
    _ = (H * (coordinateMatrix e * A * (coordinateMatrix e).conjTranspose)).trace := by
      rw [Matrix.mul_assoc]
    _ = _ := by rw [coordinateMatrix_mul_mul_conjTranspose]

lemma quadratic_coordinate_lift {L K : Type*} [Fintype L] [Fintype K] [DecidableEq K]
    (e : L → K) (H : Matrix L L ℂ) (v : K → ℂ) :
    star v ⬝ᵥ (((coordinateMatrix e).conjTranspose * H * coordinateMatrix e) *ᵥ v) =
      star (fun a => v (e a)) ⬝ᵥ (H *ᵥ (fun a => v (e a))) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, coordinateMatrix_mulVec]

/-- Different finite local bases can be used for different photon sectors.
The actual adaptive POVM still acts on the original Fock spaces. -/
theorem adaptive_scheme_dependent_submatrix_positive {n N : ℕ} {O : Type}
    [MeasurableSpace O] (S : AdaptiveScheme n N O)
    (J : Fin N → Type) [∀ t, Fintype (J t)]
    (a : ∀ t, J t → Occupation (Fin n)) :
    ∃ M : FockPOVM (Fin N → Occupation (Fin n)) (Fin N → O),
      (∀ τ : Fin N → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ,
        (∀ t, IsDensity (τ t)) →
        M.law (fun u v => ∏ t, τ t (u t) (v t)) =
          sequentialLaw (fun t => S.round (τ t) t) N le_rfl) ∧
      ∀ B, MeasurableSet B → ∀ H : Matrix (∀ t, J t) (∀ t, J t) ℂ,
        H.IsHermitian → (∀ φ : ∀ t, J t → ℂ,
          0 ≤ star (fun u => ∏ t, φ t (u t)) ⬝ᵥ (H *ᵥ (fun u => ∏ t, φ t (u t)))) →
        0 ≤ matrixPair H ((M.effect B).submatrix
          (fun u t => a t (u t)) (fun u t => a t (u t))) := by
  classical
  let a' : (Σ t, J t) → Occupation (Fin n) := fun p => a p.1 p.2
  obtain ⟨M, hLaw, hTest⟩ := adaptive_scheme_submatrix_product_positive S a'
  refine ⟨M, hLaw, ?_⟩
  intro B hB H hH hprod
  let e : (∀ t, J t) → (Fin N → Σ t, J t) := fun u t => ⟨t, u t⟩
  let A := coordinateMatrix e
  have hLift : (A.conjTranspose * H * A).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul A hH
  have hpos := hTest B hB (A.conjTranspose * H * A) hLift (by
    intro φ
    rw [quadratic_coordinate_lift]
    exact hprod (fun t j => φ t ⟨t, j⟩))
  rw [matrixPair_coordinate_lift] at hpos
  exact hpos

/-- Finite products of density arrays are density arrays. -/
theorem isDensity_fin_product {I : Type} [DecidableEq I] {N : ℕ}
    (τ : Fin N → Matrix I I ℂ) (hτ : ∀ t, IsDensity (τ t)) :
    IsDensity (fun u v : Fin N → I => ∏ t, τ t (u t) (v t)) := by
  have h : ∀ (k : ℕ) (hk : k ≤ N), IsDensity (prodState k hk τ) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have he : prodState 0 hk τ = fun _ _ => (1 : ℂ) := by
        funext u v
        simp [prodState]
      rw [he]
      exact base_density I
    | succ k ih =>
      intro hk
      rw [prodState_succ]
      exact isDensity_reindex (snocEquiv I k)
        (isDensity_prod (ih (Nat.le_of_succ_le hk)) (hτ ⟨k, hk⟩))
  exact h N le_rfl

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5SectorCompression -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

noncomputable section
namespace BosonicLearn.Prop5

/-- The collective finite basis for a fixed photon-number record. -/
def photonProductEmbedding {n N : ℕ} (k : Fin N → ℕ) :
    (∀ t, PhotonSector n (k t)) ↪ (Fin N → Occupation (Fin n)) where
  toFun u t := u t
  inj' := by
    intro u v huv
    funext t
    exact Subtype.ext (congrFun huv t)

@[simp] theorem mem_range_photonProductEmbedding {n N : ℕ} (k : Fin N → ℕ)
    (u : Fin N → Occupation (Fin n)) :
    u ∈ Set.range (photonProductEmbedding k) ↔ ∀ t, ∑ i, u t i = k t := by
  constructor
  · rintro ⟨v, rfl⟩ t
    exact (v t).property
  · intro hu
    exact ⟨fun t => ⟨u t, hu t⟩, rfl⟩

theorem normalized_sector_block {n : ℕ} (k : ℕ)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) :
    sectorBlock k (normalizedFiniteCut (photonSectorSet n k) ρ) =
      ((finiteCutMass (photonSectorSet n k) ρ)⁻¹ : ℂ) • sectorBlock k ρ := by
  ext u v
  simp [sectorBlock, normalizedFiniteCut, finiteCut, u.property, v.property]

theorem normalized_sector_block_posDef {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (hρ : (sectorBlock k ρ).PosDef) :
    (sectorBlock k (normalizedFiniteCut (photonSectorSet n k) ρ)).PosDef := by
  rw [normalized_sector_block]
  exact hρ.smul (by exact_mod_cast (inv_pos.mpr (photonSector_mass_pos hn k ρ hρ)))

/-- A tensor product of normalized photon-sector states is supported
on the corresponding product of finite sector bases. -/
theorem photon_product_supported {n N : ℕ} (k : Fin N → ℕ)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (u v : Fin N → Occupation (Fin n))
    (h : u ∉ Set.range (photonProductEmbedding k) ∨ v ∉ Set.range (photonProductEmbedding k)) :
    (∏ t, normalizedFiniteCut (photonSectorSet n (k t)) ρ (u t) (v t)) = 0 := by
  classical
  rcases h with hu | hv
  · have he : ∃ t, ∑ i, u t i ≠ k t := by
      simpa only [mem_range_photonProductEmbedding, not_forall] using hu
    obtain ⟨t, ht⟩ := he
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    simp [normalizedFiniteCut, finiteCut, ht]
  · have he : ∃ t, ∑ i, v t i ≠ k t := by
      simpa only [mem_range_photonProductEmbedding, not_forall] using hv
    obtain ⟨t, ht⟩ := he
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    simp [normalizedFiniteCut, finiteCut, ht]

/-- The compressed collective matrix is the tensor product of the
normalized finite sector blocks, with varying local dimensions. -/
theorem photon_product_compression {n N : ℕ} (k : Fin N → ℕ)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) :
    (Matrix.of (fun u v : Fin N → Occupation (Fin n) =>
      ∏ t, normalizedFiniteCut (photonSectorSet n (k t)) ρ (u t) (v t))).submatrix
        (photonProductEmbedding k) (photonProductEmbedding k) =
      (fun u v : ∀ t, PhotonSector n (k t) =>
        ∏ t, sectorBlock (k t) (normalizedFiniteCut (photonSectorSet n (k t)) ρ) (u t) (v t)) := rfl

/-- Entry formula used for joint measurability of the finite-sector
state family. All dependence on the physical state is explicit. -/
theorem photon_product_compression_apply {n N : ℕ} (k : Fin N → ℕ)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (u v : ∀ t, PhotonSector n (k t)) :
    ((Matrix.of (fun u v : Fin N → Occupation (Fin n) =>
      ∏ t, normalizedFiniteCut (photonSectorSet n (k t)) ρ (u t) (v t))).submatrix
        (photonProductEmbedding k) (photonProductEmbedding k)) u v =
      ∏ t, ((finiteCutMass (photonSectorSet n (k t)) ρ)⁻¹ : ℂ) * ρ (u t) (v t) := by
  change (∏ t, normalizedFiniteCut (photonSectorSet n (k t)) ρ (u t) (v t)) = _
  apply Finset.prod_congr rfl
  intro t _
  simp [normalizedFiniteCut, finiteCut, (u t).property, (v t).property]

theorem photon_product_compression_posDef {n N : ℕ} (hn : 1 ≤ n) (k : Fin N → ℕ)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (hρ : ∀ t, (sectorBlock (k t) ρ).PosDef) :
    ((Matrix.of (fun u v : Fin N → Occupation (Fin n) =>
      ∏ t, normalizedFiniteCut (photonSectorSet n (k t)) ρ (u t) (v t))).submatrix
        (photonProductEmbedding k) (photonProductEmbedding k)).PosDef := by
  rw [photon_product_compression]
  exact finite_tensor_posDef _ (fun t => normalized_sector_block_posDef hn (k t) ρ (hρ t))

/-- Measurement of a fixed photon-number product state can be carried
out on its finite collective basis, with exactly the same outcome law. -/
theorem compressed_photon_product_law {n N : ℕ} {O : Type} [MeasurableSpace O]
    (k : Fin N → ℕ) (M : FockPOVM (Fin N → Occupation (Fin n)) O)
    (P : FockPOVM (∀ t, PhotonSector n (k t)) O)
    (hP : P.effect = fun B => (M.effect B).submatrix
      (photonProductEmbedding k) (photonProductEmbedding k))
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (hρ : IsDensity (fun u v : Fin N → Occupation (Fin n) =>
      ∏ t, normalizedFiniteCut (photonSectorSet n (k t)) ρ (u t) (v t))) :
    P.law (fun u v : ∀ t, PhotonSector n (k t) =>
        ∏ t, sectorBlock (k t) (normalizedFiniteCut (photonSectorSet n (k t)) ρ) (u t) (v t)) =
      M.law (fun u v : Fin N → Occupation (Fin n) =>
        ∏ t, normalizedFiniteCut (photonSectorSet n (k t)) ρ (u t) (v t)) := by
  exact compressed_law_eq M P (photonProductEmbedding k) hP _ hρ (photon_product_supported k ρ)

theorem family_photon_product_isDensity {n N : ℕ} (hn : 1 ≤ n)
    (ν ξ : ℝ) (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) (k : Fin N → ℕ) :
    IsDensity (fun u v : Fin N → Occupation (Fin n) =>
      ∏ t, normalizedFiniteCut (photonSectorSet n (k t))
        (fugacityCoeff (fugacityFamily ν ξ X)) (u t) (v t)) :=
  isDensity_fin_product _ (fun t =>
    family_photon_state_isDensity hn ν ξ hν hνhi hξ hξhi X hX (k t))

theorem family_photon_product_compressed_isDensity {n N : ℕ} (hn : 1 ≤ n)
    (ν ξ : ℝ) (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) (k : Fin N → ℕ) :
    IsDensity ((Matrix.of (fun u v : Fin N → Occupation (Fin n) =>
      ∏ t, normalizedFiniteCut (photonSectorSet n (k t))
        (fugacityCoeff (fugacityFamily ν ξ X)) (u t) (v t))).submatrix
          (photonProductEmbedding k) (photonProductEmbedding k)) :=
  compressed_state_isDensity _ _
    (family_photon_product_isDensity hn ν ξ hν hνhi hξ hξhi X hX k)
    (photon_product_supported k _)

theorem family_photon_product_compressed_posDef {n N : ℕ} (hn : 1 ≤ n)
    (ν ξ : ℝ) (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) (k : Fin N → ℕ) :
    ((Matrix.of (fun u v : Fin N → Occupation (Fin n) =>
      ∏ t, normalizedFiniteCut (photonSectorSet n (k t))
        (fugacityCoeff (fugacityFamily ν ξ X)) (u t) (v t))).submatrix
          (photonProductEmbedding k) (photonProductEmbedding k)).PosDef :=
  photon_product_compression_posDef hn k _
    (fun t => family_sector_posDef ν ξ hν hνhi hξ hξhi X hX (k t))

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5FiniteLikelihood -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open scoped ENNReal Matrix ComplexOrder

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 800000

/-- Finite-dimensional POVMs have jointly measurable likelihoods for every
entrywise measurable family of states, on arbitrary outcome spaces. -/
theorem finite_povm_joint_density {I O Θ : Type} [Fintype I] [Nonempty I]
    [DecidableEq I] [MeasurableSpace O] [MeasurableSpace Θ]
    (M : FockPOVM I O) (ρ : Θ → Matrix I I ℂ)
    (hρm : ∀ i j, Measurable fun θ => ρ θ i j)
    (hρd : ∀ θ, IsDensity (ρ θ)) (hρp : ∀ θ, (ρ θ).PosSemidef) :
    ∃ ref : Measure O, IsProbabilityMeasure ref ∧
      ∃ p : Θ → O → ℝ≥0∞, Measurable (Function.uncurry p) ∧
        (∀ θ, IsProbabilityMeasure (ref.withDensity (p θ))) ∧
        (∀ θ, ref.withDensity (p θ) = M.law (ρ θ)) ∧
        (∀ θ θ', (ρ θ).PosDef → (ρ θ').PosDef →
          ∀ᵐ x ∂ref, p θ x = 0 ↔ p θ' x = 0) := by
  classical
  obtain ⟨ref, href, hdom, e, hem, hei, heB⟩ := fockPOVM_effect_density M
  letI : IsProbabilityMeasure ref := href
  have hep : ∀ᵐ x ∂ref, (e x).PosSemidef :=
    matrix_density_posSemidef_ae ref M.effect e (ComposeEffect.effect_posSemidef M) hei heB
  let F : Θ → O → ℂ := fun θ x => ∑ i, ∑ j, e x i j * ρ θ j i
  have hFm : Measurable (Function.uncurry F) := by
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact ((hem i j).comp measurable_snd).mul ((hρm j i).comp measurable_fst)
  have hFi : ∀ θ, Integrable (F θ) ref := by
    intro θ
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hei i j).mul_const (ρ θ j i)
  have hFnonneg : ∀ θ, ∀ᵐ x ∂ref, 0 ≤ (F θ x).re := by
    intro θ
    filter_upwards [hep] with x hx
    exact positive_effect_pairing_nonneg (e x) (ρ θ) hx (hρp θ)
  have hFB : ∀ θ B, MeasurableSet B →
      ∫ x in B, F θ x ∂ref = ∑ i, ∑ j, M.effect B i j * ρ θ j i := by
    intro θ B hB
    have hiB : ∀ i j, IntegrableOn (fun x => e x i j * ρ θ j i) B ref :=
      fun i j => ((hei i j).mul_const _).integrableOn
    change (∫ x in B, ∑ i, ∑ j, e x i j * ρ θ j i ∂ref) = _
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hiB i j)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => hiB i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const, heB B hB]
  let p : Θ → O → ℝ≥0∞ := fun θ x => ENNReal.ofReal (F θ x).re
  have hpm : Measurable (Function.uncurry p) := (Complex.measurable_re.comp hFm).ennreal_ofReal
  have hpLaw : ∀ θ, ref.withDensity (p θ) = M.law (ρ θ) := by
    intro θ
    ext B hB
    rw [withDensity_apply _ hB]
    change (∫⁻ x in B, ENNReal.ofReal (F θ x).re ∂ref) = _
    have hre : (∫ x in B, (F θ x).re ∂ref) = (∫ x in B, F θ x ∂ref).re :=
      integral_re ((hFi θ).integrableOn : Integrable (F θ) (ref.restrict B))
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => (F θ x).re) (hFi θ).re.integrableOn
      (ae_restrict_of_ae (hFnonneg θ)), hre,
      hFB θ B hB, M.law_born _ (hρd θ) B hB]
    simp only [tsum_fintype]
  refine ⟨ref, href, p, hpm, ?_, hpLaw, ?_⟩
  · intro θ
    rw [hpLaw θ]
    exact M.law_prob _ (hρd θ)
  · intro θ θ' hθ hθ'
    filter_upwards [hep] with x hx
    by_cases hezero : e x = 0
    · simp [p, F, hezero]
    · have hpos := positive_effect_pairing_pos (e x) (ρ θ) hx hezero hθ
      have hpos' := positive_effect_pairing_pos (e x) (ρ θ') hx hezero hθ'
      have hp : p θ x ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpos
      have hp' : p θ' x ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpos'
      exact iff_of_false hp hp'

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5PoolLikelihood -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5
set_option maxHeartbeats 600000

/-- Countably many dominated experiments can use one common probability
reference while preserving joint measurability and equality of zero sets. -/
theorem pool_likelihood_references {ι Θ Ω : Type*} [Countable ι] [Nonempty ι]
    [MeasurableSpace Θ] [MeasurableSpace Ω]
    (μ : ι → Measure Ω) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (p : ι → Θ → Ω → ℝ≥0∞) (hp : ∀ i, Measurable (Function.uncurry (p i)))
    (hzero : ∀ i θ θ', ∀ᵐ x ∂μ i, p i θ x = 0 ↔ p i θ' x = 0) :
    ∃ ref : Measure Ω, IsProbabilityMeasure ref ∧
      ∃ q : ι → Θ → Ω → ℝ≥0∞,
        (∀ i, Measurable (Function.uncurry (q i))) ∧
        (∀ i θ, ref.withDensity (q i θ) = (μ i).withDensity (p i θ)) ∧
        (∀ i θ θ', ∀ᵐ x ∂ref, q i θ x = 0 ↔ q i θ' x = 0) := by
  obtain ⟨ref, href, hdom⟩ := common_probability_reference μ hμ
  letI : IsProbabilityMeasure ref := href
  letI (i : ι) : IsProbabilityMeasure (μ i) := hμ i
  let r : ι → Ω → ℝ≥0∞ := fun i => (μ i).rnDeriv ref
  have hr : ∀ i, Measurable (r i) := fun i => Measure.measurable_rnDeriv _ _
  have hμr : ∀ i, ref.withDensity (r i) = μ i := fun i =>
    Measure.withDensity_rnDeriv_eq _ _ (hdom i)
  let q : ι → Θ → Ω → ℝ≥0∞ := fun i θ x => r i x * p i θ x
  refine ⟨ref, href, q, ?_, ?_, ?_⟩
  · intro i
    exact ((hr i).comp measurable_snd).mul (hp i)
  · intro i θ
    have hpθ : Measurable (p i θ) := (hp i).comp (measurable_const.prodMk measurable_id)
    rw [show (q i θ) = r i * p i θ from rfl, withDensity_mul ref (hr i) hpθ, hμr i]
  · intro i θ θ'
    have hz : ∀ᵐ x ∂ref, r i x ≠ 0 → (p i θ x = 0 ↔ p i θ' x = 0) := by
      apply (ae_withDensity_iff (hr i)).mp
      rw [hμr i]
      exact hzero i θ θ'
    filter_upwards [hz] with x hx
    by_cases hrx : r i x = 0
    · simp [q, hrx]
    · simp only [q, mul_eq_zero, hrx, false_or]
      exact hx hrx

/-- Summing positive-weight component models preserves their common zero set. -/
theorem weighted_likelihoods_same_zero {ι Θ Ω : Type*} [Countable ι]
    [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ι → Θ → Ω → ℝ≥0∞) (w : Θ → ι → ℝ≥0∞)
    (hw : ∀ θ i, w θ i ≠ 0)
    (hzero : ∀ i θ θ', ∀ᵐ x ∂μ, p i θ x = 0 ↔ p i θ' x = 0) :
    ∀ θ θ', ∀ᵐ x ∂μ,
      (∑' i, w θ i * p i θ x) = 0 ↔ (∑' i, w θ' i * p i θ' x) = 0 := by
  intro θ θ'
  filter_upwards [ae_all_iff.mpr fun i => hzero i θ θ'] with x hx
  simp only [ENNReal.tsum_eq_zero, mul_eq_zero, hw, false_or]
  exact forall_congr' hx

/-- A countable mixture of normalized density models is normalized. -/
theorem weighted_likelihood_probability {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ι → Ω → ℝ≥0∞) (hp : ∀ i, Measurable (p i))
    (hprob : ∀ i, IsProbabilityMeasure (μ.withDensity (p i)))
    (w : ι → ℝ≥0∞) (hw : ∑' i, w i = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ∑' i, w i * p i x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_tsum (f := fun i x => w i * p i x)
      (fun i => (measurable_const.mul (hp i)).aemeasurable)]
  have hmass : ∀ i, ∫⁻ x, p i x ∂μ = 1 := by
    intro i
    haveI := hprob i
    have h := measure_univ (μ := μ.withDensity (p i))
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h
  simp only [lintegral_const_mul _ (hp _), hmass, mul_one, hw]

/-- The density of a countable mixture is the weighted sum of the
component densities. -/
theorem withDensity_weighted_tsum {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ι → Ω → ℝ≥0∞) (hp : ∀ i, Measurable (p i))
    (w : ι → ℝ≥0∞) :
    μ.withDensity (fun x => ∑' i, w i * p i x) =
      Measure.sum (fun i => w i • μ.withDensity (p i)) := by
  have heq : (fun x => ∑' i, w i * p i x) = ∑' i, (fun x => w i * p i x) := by
    funext x
    exact (ENNReal.tsum_apply (f := fun i x => w i * p i x) (x := x)).symm
  rw [heq, withDensity_tsum (f := fun i x => w i * p i x)
    (fun i => measurable_const.mul (hp i))]
  congr 1
  funext i
  exact withDensity_smul (w i) (hp i)

/-- Forgetting the visible transcript retains the weighted hidden-record mean. -/
theorem weighted_density_cost_integral {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ι → Ω → ℝ≥0∞) (hp : ∀ i, Measurable (p i))
    (hprob : ∀ i, IsProbabilityMeasure (μ.withDensity (p i)))
    (w c : ι → ℝ≥0∞) :
    (∫⁻ x, ∑' i, (w i * p i x) * c i ∂μ) = ∑' i, w i * c i := by
  rw [lintegral_tsum (f := fun i x => (w i * p i x) * c i)
    (fun i => ((measurable_const.mul (hp i)).mul_const _).aemeasurable)]
  apply tsum_congr
  intro i
  have hmass : ∫⁻ x, p i x ∂μ = 1 := by
    haveI := hprob i
    have h := measure_univ (μ := μ.withDensity (p i))
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h
  rw [lintegral_mul_const (f := fun x => w i * p i x) (c i) (measurable_const.mul (hp i)),
    lintegral_const_mul _ (hp i),
    hmass, mul_one]

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5PosteriorRatio -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Cancel the ground-truth likelihood and the positive finite marginal
normalizer in Proposition 1 after inserting a local likelihood lower
bound. No finiteness assumptions on the numerators are needed. -/
theorem normalized_mass_le_of_likelihood_bound
    (B L R m p e ell : ℝ≥0∞)
    (hfirst : B * L ≤ e * p * R)
    (hlocal : ell * p ≤ L) (hR : R ≤ m)
    (hp0 : p ≠ 0) (hpfin : p ≠ ⊤)
    (hm0 : m ≠ 0) (hmfin : m ≠ ⊤)
    (hell0 : ell ≠ 0) (hellfin : ell ≠ ⊤) :
    B / m ≤ e / ell := by
  have hcancel : (B * ell) * p ≤ (e * m) * p := by
    calc
      (B * ell) * p = B * (ell * p) := by ac_rfl
      _ ≤ B * L := by gcongr
      _ ≤ e * p * R := hfirst
      _ ≤ e * p * m := by gcongr
      _ = (e * m) * p := by ac_rfl
  have hproduct : B * ell ≤ e * m :=
    (ENNReal.mul_le_mul_iff_left hp0 hpfin).mp hcancel
  apply (ENNReal.div_le_iff hm0 hmfin).mpr
  have heq : e / ell * m = (e * m) / ell := by
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [heq]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hell0) (Or.inl hellfin)).mpr hproduct

/-- The two exceptional events in the posterior-ratio argument are
combined by a union bound. The pointwise implication is only required
almost everywhere, allowing zero/infinite likelihood normalizers to be
discarded separately. -/
theorem tail_measure_le_of_two_good_events
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (t ε₁ ε₂ : ℝ≥0∞) (A B : Set Ω)
    (hpoint : ∀ᵐ x ∂μ, x ∈ A → x ∈ B → f x ≤ t)
    (hA : μ Aᶜ ≤ ε₁) (hB : μ Bᶜ ≤ ε₂) :
    μ {x | t < f x} ≤ ε₁ + ε₂ := by
  have hsubset : {x | t < f x} ≤ᵐ[μ] (Aᶜ ∪ Bᶜ : Set Ω) := by
    filter_upwards [hpoint] with x hx
    intro hfx
    by_cases hxA : x ∈ A
    · exact Or.inr (fun hxB => (not_lt_of_ge (hx hxA hxB)) hfx)
    · exact Or.inl hxA
  exact (measure_mono_ae hsubset).trans
    ((measure_union_le _ _).trans (add_le_add hA hB))

/-- A finite measure given by a density assigns full mass to points
where that density is both positive and finite. -/
theorem density_ne_zero_ne_top_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : Ω → ℝ≥0∞) (hp : Measurable p)
    [IsFiniteMeasure (μ.withDensity p)] :
    ∀ᵐ x ∂μ.withDensity p, p x ≠ 0 ∧ p x ≠ ⊤ := by
  have hfinite : (∫⁻ x, p x ∂μ) ≠ ⊤ := by
    have h := measure_ne_top (μ.withDensity p) Set.univ
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h
  apply (ae_withDensity_iff hp).mpr
  filter_upwards [ae_lt_top hp hfinite] with x hx
  intro hx0
  exact ⟨hx0, hx.ne⟩

/-- Translate a high-probability good-event statement in real notation
into an upper bound on its exceptional set. -/
theorem complement_le_of_ofReal_one_sub_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hgood : ENNReal.ofReal (1 - ε) ≤ μ A) : μ Aᶜ ≤ ENNReal.ofReal ε := by
  calc
    μ Aᶜ = 1 - μ A := by rw [measure_compl hA (measure_ne_top _ _), measure_univ]
    _ ≤ 1 - ENNReal.ofReal (1 - ε) := tsub_le_tsub_left hgood 1
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr hε1)]
      congr 1
      ring

/-- Abstract form of the combination of Propositions 1 and 3. The
normalizers need only be positive and finite almost everywhere. -/
theorem posterior_ratio_tail_of_likelihood_tails
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B L R m p : Ω → ℝ≥0∞) (e ell ε₁ ε₂ : ℝ≥0∞)
    (hell0 : ell ≠ 0) (hellfin : ell ≠ ⊤)
    (hvalid : ∀ᵐ x ∂μ,
      p x ≠ 0 ∧ p x ≠ ⊤ ∧ m x ≠ 0 ∧ m x ≠ ⊤ ∧ R x ≤ m x)
    (hfirst : μ {x | e * p x * R x < B x * L x} ≤ ε₁)
    (hlocal : μ {x | L x < ell * p x} ≤ ε₂) :
    μ {x | e / ell < B x / m x} ≤ ε₁ + ε₂ := by
  apply tail_measure_le_of_two_good_events μ (fun x => B x / m x) (e / ell) ε₁ ε₂
    {x | B x * L x ≤ e * p x * R x} {x | ell * p x ≤ L x}
  · filter_upwards [hvalid] with x hx
    intro hfirstx hlocalx
    exact normalized_mass_le_of_likelihood_bound (B x) (L x) (R x) (m x) (p x) e ell
      hfirstx hlocalx hx.2.2.2.2 hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hell0 hellfin
  · simpa only [Set.compl_setOf, not_le] using hfirst
  · simpa only [Set.compl_setOf, not_le] using hlocal

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5ReferenceChange -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Change reference for any component supported where the base density is
positive. This applies also to subprobability components of a mixture. -/
theorem withDensity_div_reference {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (a b : Ω → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b)
    [IsFiniteMeasure (μ.withDensity b)]
    (hzero : ∀ᵐ x ∂μ, b x = 0 → a x = 0) :
    (μ.withDensity b).withDensity (fun x => a x / b x) = μ.withDensity a := by
  rw [← withDensity_mul μ (g := fun x => a x / b x) hb (ha.div hb)]
  apply withDensity_congr_ae
  have hfinite : ∫⁻ x, b x ∂μ ≠ ∞ := by
    have h := measure_ne_top (μ.withDensity b) Set.univ
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h
  filter_upwards [ae_lt_top hb hfinite, hzero] with x hxt hxz
  change b x * (a x / b x) = a x
  by_cases hx0 : b x = 0
  · rw [hx0, zero_mul, hxz hx0]
  · rw [mul_comm, ENNReal.div_mul_cancel hx0 hxt.ne]

/-- Rebase a measurable family of normalized likelihoods at one member.
If all members have the same zero set, the rebased densities are positive
almost everywhere, without requiring the original reference to be faithful. -/
theorem positive_likelihood_reference {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (μ : Measure Ω) (p : Θ → Ω → ℝ≥0∞) (hp : Measurable (Function.uncurry p))
    (hprob : ∀ θ, IsProbabilityMeasure (μ.withDensity (p θ))) (θ₀ : Θ)
    (hzero : ∀ θ, ∀ᵐ x ∂μ, p θ x = 0 ↔ p θ₀ x = 0) :
    ∃ ref : Measure Ω, IsProbabilityMeasure ref ∧
    ∃ q : Θ → Ω → ℝ≥0∞, Measurable (Function.uncurry q) ∧
      (∀ θ, IsProbabilityMeasure (ref.withDensity (q θ))) ∧
      (∀ θ, ref.withDensity (q θ) = μ.withDensity (p θ)) ∧
      (∀ θ, ∀ᵐ x ∂ref, q θ x ≠ 0) := by
  have hpm : ∀ θ, Measurable (p θ) := fun θ => hp.comp (measurable_const.prodMk measurable_id)
  let ref : Measure Ω := μ.withDensity (p θ₀)
  let q : Θ → Ω → ℝ≥0∞ := fun θ x => p θ x / p θ₀ x
  have hqm : Measurable (Function.uncurry q) := hp.div ((hpm θ₀).comp measurable_snd)
  letI : IsProbabilityMeasure ref := hprob θ₀
  have hfinite : ∫⁻ x, p θ₀ x ∂μ ≠ ∞ := by
    have h := measure_ne_top ref Set.univ
    simpa only [ref, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h
  have hidentity : ∀ θ, ref.withDensity (q θ) = μ.withDensity (p θ) := by
    intro θ
    have hqθ : Measurable (q θ) := (hpm θ).div (hpm θ₀)
    rw [show ref = μ.withDensity (p θ₀) from rfl,
      ← withDensity_mul μ (hpm θ₀) hqθ]
    apply withDensity_congr_ae
    filter_upwards [ae_lt_top (hpm θ₀) hfinite, hzero θ] with x hxt hxz
    change p θ₀ x * (p θ x / p θ₀ x) = p θ x
    by_cases hx0 : p θ₀ x = 0
    · rw [hx0, zero_mul, (hxz.mpr hx0)]
    · rw [mul_comm, ENNReal.div_mul_cancel hx0 hxt.ne]
  refine ⟨ref, inferInstance, q, hqm, ?_, hidentity, ?_⟩
  · intro θ
    rw [hidentity θ]
    exact hprob θ
  · intro θ
    have hbase := density_ne_zero_ne_top_ae μ (p θ₀) (hpm θ₀)
    have hac : ref ≪ μ := withDensity_absolutelyContinuous μ (p θ₀)
    have hzero' := hac.ae_le (hzero θ)
    filter_upwards [hbase, hzero'] with x hxb hxz
    exact ENNReal.div_ne_zero.mpr ⟨fun h => hxb.1 (hxz.mp h), hxb.2⟩

/-- A common change of reference preserves local averaged likelihood bounds. -/
theorem likelihood_bound_div_reference {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (f : Z → ℝ≥0∞) (ell a r : ℝ≥0∞) (hr : r ≠ 0)
    (h : ell * a ≤ ∫⁻ z, f z ∂μ) :
    ell * (a / r) ≤ ∫⁻ z, f z / r ∂μ := by
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const' r⁻¹ f (ENNReal.inv_ne_top.mpr hr), ← mul_assoc]
  exact mul_le_mul' h le_rfl

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5MixtureModel -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5
set_option maxHeartbeats 700000

/-- A countable mixture of finite experiments with faithful state families
has one probability reference with jointly measurable component likelihoods.
The mixture likelihood is positive almost everywhere for each parameter. -/
theorem positive_mixture_component_model {ι Θ Ω : Type*} [Countable ι] [Nonempty ι]
    [MeasurableSpace Θ] [MeasurableSpace Ω]
    (μ : ι → Measure Ω) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (p : ι → Θ → Ω → ℝ≥0∞) (hp : ∀ i, Measurable (Function.uncurry (p i)))
    (hprob : ∀ i θ, IsProbabilityMeasure ((μ i).withDensity (p i θ)))
    (hzero : ∀ i θ θ', ∀ᵐ x ∂μ i, p i θ x = 0 ↔ p i θ' x = 0)
    (w : Θ → ι → ℝ≥0∞) (hwm : ∀ i, Measurable fun θ => w θ i)
    (hw0 : ∀ θ i, w θ i ≠ 0) (hwsum : ∀ θ, ∑' i, w θ i = 1) (θ₀ : Θ) :
    ∃ ref : Measure Ω, IsProbabilityMeasure ref ∧
      ∃ q : ι → Θ → Ω → ℝ≥0∞,
        (∀ i, Measurable (Function.uncurry (q i))) ∧
        (∀ i θ, IsProbabilityMeasure (ref.withDensity (q i θ))) ∧
        (∀ i θ, ref.withDensity (q i θ) = (μ i).withDensity (p i θ)) ∧
        Measurable (Function.uncurry (fun θ x => ∑' i, w θ i * q i θ x)) ∧
        (∀ θ, IsProbabilityMeasure (ref.withDensity (fun x => ∑' i, w θ i * q i θ x))) ∧
        (∀ θ, ∀ᵐ x ∂ref, (∑' i, w θ i * q i θ x) ≠ 0) := by
  obtain ⟨ν, hν, r, hr, hrLaw, hrzero⟩ := pool_likelihood_references μ hμ p hp hzero
  letI : IsProbabilityMeasure ν := hν
  have hrm : ∀ i θ, Measurable (r i θ) :=
    fun i θ => (hr i).comp (measurable_const.prodMk measurable_id)
  have hrprob : ∀ i θ, IsProbabilityMeasure (ν.withDensity (r i θ)) := by
    intro i θ
    rw [hrLaw i θ]
    exact hprob i θ
  let P : Θ → Ω → ℝ≥0∞ := fun θ x => ∑' i, w θ i * r i θ x
  have hPm : Measurable (Function.uncurry P) :=
    Measurable.tsum fun i => ((hwm i).comp measurable_fst).mul (hr i)
  have hPprob : ∀ θ, IsProbabilityMeasure (ν.withDensity (P θ)) :=
    fun θ => weighted_likelihood_probability ν (fun i => r i θ) (fun i => hrm i θ)
      (fun i => hrprob i θ) (w θ) (hwsum θ)
  have hPzero := weighted_likelihoods_same_zero ν r w hw0 hrzero
  let b : Ω → ℝ≥0∞ := P θ₀
  have hbm : Measurable b := hPm.comp (measurable_const.prodMk measurable_id)
  let ref : Measure Ω := ν.withDensity b
  letI : IsProbabilityMeasure ref := hPprob θ₀
  let q : ι → Θ → Ω → ℝ≥0∞ := fun i θ x => r i θ x / b x
  have hqm : ∀ i, Measurable (Function.uncurry (q i)) :=
    fun i => (hr i).div (hbm.comp measurable_snd)
  have hqLaw : ∀ i θ, ref.withDensity (q i θ) = (μ i).withDensity (p i θ) := by
    intro i θ
    have hz : ∀ᵐ x ∂ν, b x = 0 → r i θ x = 0 := by
      filter_upwards [hrzero i θ θ₀] with x hx
      intro hbx
      have hterm : w θ₀ i * r i θ₀ x = 0 := (ENNReal.tsum_eq_zero.mp hbx) i
      exact hx.mpr ((mul_eq_zero.mp hterm).resolve_left (hw0 θ₀ i))
    exact (withDensity_div_reference ν (r i θ) b (hrm i θ) hbm hz).trans (hrLaw i θ)
  have hqprob : ∀ i θ, IsProbabilityMeasure (ref.withDensity (q i θ)) := by
    intro i θ
    rw [hqLaw i θ]
    exact hprob i θ
  have hQm : Measurable (Function.uncurry (fun θ x => ∑' i, w θ i * q i θ x)) :=
    Measurable.tsum fun i => ((hwm i).comp measurable_fst).mul (hqm i)
  refine ⟨ref, inferInstance, q, hqm, hqprob, hqLaw, hQm, ?_, ?_⟩
  · intro θ
    exact weighted_likelihood_probability ref (fun i => q i θ)
      (fun i => (hqm i).comp (measurable_const.prodMk measurable_id))
      (fun i => hqprob i θ) (w θ) (hwsum θ)
  · intro θ
    have hac : ref ≪ ν := withDensity_absolutelyContinuous ν b
    have hz : ∀ᵐ x ∂ref, P θ x = 0 ↔ b x = 0 := hac.ae_le (hPzero θ θ₀)
    have hbvalid := density_ne_zero_ne_top_ae ν b hbm
    filter_upwards [hz, hbvalid] with x hx hbx
    have hfactor : (∑' i, w θ i * q i θ x) = P θ x / b x := by
      simp only [q, P, div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]
    rw [hfactor]
    exact ENNReal.div_ne_zero.mpr ⟨fun h => hbx.1 (hx.mp h), hbx.2⟩

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5PhysicalModels -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-- Extend the physical parameterization to all parameters by using
its zero-parameter state outside the prior support. -/
def supportPatch {n : ℕ} (X : Herm0 n) : Herm0 n := by
  classical
  exact if X ∈ Gsupp n then X else 0

@[simp] theorem supportPatch_eq {n : ℕ} {X : Herm0 n} (hX : X ∈ Gsupp n) :
    supportPatch X = X := by simp [supportPatch, hX]

theorem supportPatch_mem {n : ℕ} (X : Herm0 n) : supportPatch X ∈ Gsupp n := by
  unfold supportPatch
  split_ifs with h
  · exact h
  · exact zero_mem_gsupp n

theorem measurable_supportPatch (n : ℕ) : Measurable (@supportPatch n) :=
  Measurable.ite (gsupp_measurable n) measurable_id measurable_const

/-- The everywhere-defined physical state family. -/
def physicalState {n : ℕ} (ν ξ : ℝ) (X : Herm0 n) :
    Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ :=
  fugacityCoeff (fugacityFamily ν ξ (supportPatch X))

/-- Probability weight of a fixed hidden photon-number record. -/
def physicalRecordWeight {n N : ℕ} (ν ξ : ℝ) (X : Herm0 n) (k : Fin N → ℕ) : ℝ≥0∞ :=
  ∏ t, ENNReal.ofReal (finiteCutMass (photonSectorSet n (k t)) (physicalState ν ξ X))

/-- The visible transcript law conditional on a hidden photon record. -/
def physicalRecordLaw {n N : ℕ} {O : Type} [MeasurableSpace O]
    (S : AdaptiveScheme n N O) (ν ξ : ℝ) (X : Herm0 n) (k : Fin N → ℕ) :
    Measure (Fin N → O) :=
  sequentialLaw (fun t => S.round
    (normalizedFiniteCut (photonSectorSet n (k t)) (physicalState ν ξ X)) t) N le_rfl

/-- The faithful finite matrix seen by the compressed collective POVM. -/
def physicalRecordState {n N : ℕ} (ν ξ : ℝ) (X : Herm0 n) (k : Fin N → ℕ) :
    Matrix (∀ t, PhotonSector n (k t)) (∀ t, PhotonSector n (k t)) ℂ :=
  (Matrix.of (fun u v : Fin N → Occupation (Fin n) =>
    ∏ t, normalizedFiniteCut (photonSectorSet n (k t)) (physicalState ν ξ X) (u t) (v t))).submatrix
      (photonProductEmbedding k) (photonProductEmbedding k)

theorem measurable_physicalState_entry {n : ℕ} (ν ξ : ℝ) (u v : Occupation (Fin n)) :
    Measurable (fun X : Herm0 n => physicalState ν ξ X u v) :=
  (continuous_family_entry ν ξ u v).measurable.comp (measurable_supportPatch n)

theorem measurable_physicalSectorMass {n : ℕ} (ν ξ : ℝ) (k : ℕ) :
    Measurable (fun X : Herm0 n => finiteCutMass (photonSectorSet n k) (physicalState ν ξ X)) := by
  apply Finset.measurable_sum
  intro u _
  exact Complex.measurable_re.comp (measurable_physicalState_entry ν ξ u u)

theorem measurable_physicalRecordWeight {n N : ℕ} (ν ξ : ℝ) (k : Fin N → ℕ) :
    Measurable (fun X : Herm0 n => physicalRecordWeight ν ξ X k) :=
  Finset.measurable_prod _ (fun t _ => (measurable_physicalSectorMass ν ξ (k t)).ennreal_ofReal)

theorem measurable_physicalRecordState_entry {n N : ℕ} (ν ξ : ℝ) (k : Fin N → ℕ)
    (u v : ∀ t, PhotonSector n (k t)) :
    Measurable (fun X : Herm0 n => physicalRecordState ν ξ X k u v) := by
  simp only [physicalRecordState, photon_product_compression_apply]
  apply Finset.measurable_prod
  intro t _
  exact (Complex.measurable_ofReal.comp (measurable_physicalSectorMass ν ξ (k t))).inv.mul
    (measurable_physicalState_entry (n := n) ν ξ (u t).val (v t).val)

theorem physicalState_isDensity {n : ℕ} (ν ξ : ℝ)
    (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32) (X : Herm0 n) :
    IsDensity (physicalState ν ξ X) := by
  have hR := family_spectral_bounds ν ξ hν hνhi hξ hξhi (supportPatch X) (supportPatch_mem X)
  exact fugacityCoeff_isDensity _ hR.1 hR.2.1

theorem physicalRecordWeight_ne_zero {n N : ℕ} (hn : 1 ≤ n) (ν ξ : ℝ)
    (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32)
    (X : Herm0 n) (k : Fin N → ℕ) : physicalRecordWeight ν ξ X k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro t _
  apply ENNReal.ofReal_ne_zero_iff.mpr
  exact photonSector_mass_pos hn (k t) _
    (family_sector_posDef ν ξ hν hνhi hξ hξhi (supportPatch X) (supportPatch_mem X) (k t))

theorem physicalRecordWeight_sum_one {n N : ℕ} (ν ξ : ℝ)
    (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32) (X : Herm0 n) :
    (∑' k : Fin N → ℕ, physicalRecordWeight ν ξ X k) = 1 :=
  record_weights_sum_one _
    (photon_weights_sum_one _ (physicalState_isDensity ν ξ hν hνhi hξ hξhi X)) N

theorem physicalRecordState_isDensity {n N : ℕ} (hn : 1 ≤ n) (ν ξ : ℝ)
    (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32)
    (X : Herm0 n) (k : Fin N → ℕ) : IsDensity (physicalRecordState ν ξ X k) :=
  family_photon_product_compressed_isDensity hn ν ξ hν hνhi hξ hξhi
    (supportPatch X) (supportPatch_mem X) k

theorem physicalRecordState_posDef {n N : ℕ} (hn : 1 ≤ n) (ν ξ : ℝ)
    (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32)
    (X : Herm0 n) (k : Fin N → ℕ) : (physicalRecordState ν ξ X k).PosDef :=
  family_photon_product_compressed_posDef hn ν ξ hν hνhi hξ hξhi
    (supportPatch X) (supportPatch_mem X) k

theorem physicalRecordWeight_cost_mean {n N : ℕ} (hn : 1 ≤ n) (ν ξ : ℝ)
    (hν : 1 / (n : ℝ) ≤ ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32)
    (X : Herm0 n) :
    (∑' k : Fin N → ℕ, physicalRecordWeight ν ξ X k *
      ENNReal.ofReal (∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n))) ≤
        ENNReal.ofReal (13 * N * n * ν ^ 2) :=
  family_photon_record_cost_mean N ν ξ hn hν hνhi hξ hξhi
    (supportPatch X) (supportPatch_mem X)

/-- The patched experiment decomposes into its normalized hidden
photon-record experiments. -/
theorem physicalRecordLaw_mixture {n N : ℕ} {O : Type} [MeasurableSpace O]
    (S : AdaptiveScheme n N O) (hn : 1 ≤ n) (ν ξ : ℝ)
    (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32) (X : Herm0 n) :
    transcriptLaw S (physicalState ν ξ X) = Measure.sum (fun k : Fin N → ℕ =>
      physicalRecordWeight ν ξ X k • physicalRecordLaw S ν ξ X k) :=
  adaptive_family_photon_mixture S hn ν ξ hν hνhi hξ hξhi
    (supportPatch X) (supportPatch_mem X)

/-- All hidden photon-record experiments admit one probability
reference and jointly measurable component likelihoods. Their weighted
sum is everywhere normalized, positive almost everywhere, and agrees
with the physical adaptive transcript experiment on the prior support. -/
theorem physical_component_likelihood_model {n N : ℕ} {O : Type} [MeasurableSpace O]
    (S : AdaptiveScheme n N O) (hn : 1 ≤ n) (ν ξ : ℝ)
    (hν : 0 < ν) (hνhi : ν ≤ 1) (hξ : 0 < ξ) (hξhi : ξ < 1 / 32) :
    ∃ ref : Measure (Fin N → O), IsProbabilityMeasure ref ∧
      ∃ p : (Fin N → ℕ) → Herm0 n → (Fin N → O) → ℝ≥0∞,
        (∀ k, Measurable (Function.uncurry (p k))) ∧
        (∀ k X, IsProbabilityMeasure (ref.withDensity (p k X))) ∧
        (∀ k X, ref.withDensity (p k X) = physicalRecordLaw S ν ξ X k) ∧
        Measurable (Function.uncurry (fun X x =>
          ∑' k, physicalRecordWeight ν ξ X k * p k X x)) ∧
        (∀ X, IsProbabilityMeasure (ref.withDensity (fun x =>
          ∑' k, physicalRecordWeight ν ξ X k * p k X x))) ∧
        (∀ X, ∀ᵐ x ∂ref, (∑' k, physicalRecordWeight ν ξ X k * p k X x) ≠ 0) ∧
        (∀ X ∈ Gsupp n, ref.withDensity (fun x =>
          ∑' k, physicalRecordWeight ν ξ X k * p k X x) =
            transcriptLaw S (fugacityCoeff (fugacityFamily ν ξ X))) := by
  classical
  obtain ⟨M, hM⟩ := adaptive_scheme_product_povm S
  have hcomponent (k : Fin N → ℕ) :
      ∃ μ : Measure (Fin N → O), IsProbabilityMeasure μ ∧
        ∃ p : Herm0 n → (Fin N → O) → ℝ≥0∞,
          Measurable (Function.uncurry p) ∧
          (∀ X, IsProbabilityMeasure (μ.withDensity (p X))) ∧
          (∀ X, μ.withDensity (p X) = physicalRecordLaw S ν ξ X k) ∧
          (∀ X Y, ∀ᵐ x ∂μ, p X x = 0 ↔ p Y x = 0) := by
    letI (t : Fin N) : Nonempty (PhotonSector n (k t)) := photonSector_nonempty n hn (k t)
    obtain ⟨P, hP⟩ := fockPOVM_compression M (photonProductEmbedding k)
    obtain ⟨μ, hμ, p, hp, hprob, hlaw, hzero⟩ :=
      finite_povm_joint_density P (fun X => physicalRecordState ν ξ X k)
        (measurable_physicalRecordState_entry ν ξ k)
        (fun X => physicalRecordState_isDensity hn ν ξ hν hνhi hξ hξhi X k)
        (fun X => (physicalRecordState_posDef hn ν ξ hν hνhi hξ hξhi X k).posSemidef)
    refine ⟨μ, hμ, p, hp, hprob, ?_, ?_⟩
    · intro X
      rw [hlaw X]
      have hfull := family_photon_product_isDensity hn ν ξ hν hνhi hξ hξhi
        (supportPatch X) (supportPatch_mem X) k
      exact (compressed_law_eq M P (photonProductEmbedding k) hP _ hfull
        (photon_product_supported k (physicalState ν ξ X))).trans
          (hM (fun t => normalizedFiniteCut (photonSectorSet n (k t)) (physicalState ν ξ X))
            (fun t => family_photon_state_isDensity hn ν ξ hν hνhi hξ hξhi
              (supportPatch X) (supportPatch_mem X) (k t)))
    · intro X Y
      exact hzero X Y (physicalRecordState_posDef hn ν ξ hν hνhi hξ hξhi X k)
        (physicalRecordState_posDef hn ν ξ hν hνhi hξ hξhi Y k)
  choose μ hμ r hr hrprob hrLaw hrzero using hcomponent
  obtain ⟨ref, href, p, hp, hprob, hlaw, hPm, hPprob, hPpos⟩ :=
    positive_mixture_component_model μ hμ r hr hrprob hrzero (physicalRecordWeight ν ξ)
      (measurable_physicalRecordWeight ν ξ)
      (physicalRecordWeight_ne_zero hn ν ξ hν hνhi hξ hξhi)
      (physicalRecordWeight_sum_one ν ξ hν hνhi hξ hξhi) (0 : Herm0 n)
  have hLaw : ∀ k X, ref.withDensity (p k X) = physicalRecordLaw S ν ξ X k :=
    fun k X => (hlaw k X).trans (hrLaw k X)
  refine ⟨ref, href, p, hp, hprob, hLaw, hPm, hPprob, hPpos, ?_⟩
  intro X hX
  rw [withDensity_weighted_tsum ref (fun k => p k X)
    (fun k => (hp k).comp (measurable_const.prodMk measurable_id))]
  simp only [hLaw]
  rw [← physicalRecordLaw_mixture S hn ν ξ hν hνhi hξ hξhi X]
  simp only [physicalState, supportPatch_eq hX]

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5SectorAverage -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder BigOperators

namespace BosonicLearn.Prop5
noncomputable section

def productMatrix {ι : Type*} [Fintype ι] {J : ι → Type*}
    (A : (t : ι) → Matrix (J t) (J t) ℂ) : Matrix ((t : ι) → J t) ((t : ι) → J t) ℂ :=
  fun u v => ∏ t, A t (u t) (v t)

def productVector {ι : Type*} [Fintype ι] {J : ι → Type*}
    (φ : (t : ι) → J t → ℂ) : ((t : ι) → J t) → ℂ := fun u => ∏ t, φ t (u t)

theorem productMatrix_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι] {J : ι → Type*}
    [∀ t, Fintype (J t)] (A : (t : ι) → Matrix (J t) (J t) ℂ)
    (φ : (t : ι) → J t → ℂ) :
    star (productVector φ) ⬝ᵥ (productMatrix A *ᵥ productVector φ) =
      ∏ t, star (φ t) ⬝ᵥ (A t *ᵥ φ t) := by
  classical
  simp only [dotProduct, Matrix.mulVec, productMatrix, productVector, Pi.star_apply,
    star_prod, Finset.mul_sum]
  simp_rw [← Finset.prod_mul_distrib]
  calc
    _ = ∑ u : (t : ι) → J t, ∏ t, ∑ v : J t,
        star (φ t (u t)) * (A t (u t) v * φ t v) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (Fintype.prod_sum (fun t (v : J t) =>
        star (φ t (u t)) * (A t (u t) v * φ t v))).symm
    _ = _ := (Fintype.prod_sum (fun t (u : J t) =>
      ∑ v : J t, star (φ t u) * (A t u v * φ t v))).symm

theorem productMatrix_isHermitian {ι : Type*} [Fintype ι] {J : ι → Type*}
    (A : (t : ι) → Matrix (J t) (J t) ℂ) (hA : ∀ t, (A t).IsHermitian) :
    (productMatrix A).IsHermitian := by
  ext u v
  change star (∏ t, A t (v t) (u t)) = ∏ t, A t (u t) (v t)
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro t ht
  exact congrFun (congrFun (hA t) (u t)) (v t)

def averagedProductDifference {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {J : ι → Type*} (μ : Measure Ω) (A : Ω → (t : ι) → Matrix (J t) (J t) ℂ)
    (A₀ : (t : ι) → Matrix (J t) (J t) ℂ) (ell : ℝ) :
    Matrix ((t : ι) → J t) ((t : ι) → J t) ℂ :=
  fun u v => (∫ x, productMatrix (A x) u v ∂μ) - (ell : ℂ) * productMatrix A₀ u v

theorem averagedProductDifference_isHermitian {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] {J : ι → Type*}
    (μ : Measure Ω) (A : Ω → (t : ι) → Matrix (J t) (J t) ℂ)
    (A₀ : (t : ι) → Matrix (J t) (J t) ℂ) (ell : ℝ)
    (hA : ∀ᵐ x ∂μ, ∀ t, (A x t).IsHermitian) (hA₀ : ∀ t, (A₀ t).IsHermitian) :
    (averagedProductDifference μ A A₀ ell).IsHermitian := by
  have hInt : (show Matrix ((t : ι) → J t) ((t : ι) → J t) ℂ from
      fun u v => ∫ x, productMatrix (A x) u v ∂μ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro u v
    change (starRingEnd ℂ) (∫ x, productMatrix (A x) v u ∂μ) = _
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [hA] with x hx
    exact (productMatrix_isHermitian (A x) hx).apply u v
  exact hInt.sub ((productMatrix_isHermitian A₀ hA₀).smul
    (show IsSelfAdjoint (ell : ℂ) by simp [IsSelfAdjoint]))

/-- A finite quadratic form commutes with an entrywise Bochner integral. -/
theorem quadratic_entrywiseIntegral {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (H : Ω → Matrix I I ℂ)
    (hi : ∀ u v, Integrable (fun x => H x u v) μ) (φ : I → ℂ) :
    star φ ⬝ᵥ ((fun u v => ∫ x, H x u v ∂μ) *ᵥ φ) =
      ∫ x, star φ ⬝ᵥ (H x *ᵥ φ) ∂μ := by
  classical
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [integral_finsetSum _ (fun u _ => integrable_finsetSum _
    (fun v _ => ((hi u v).mul_const _).const_mul _))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum _ (fun v _ => ((hi u v).mul_const _).const_mul _)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [integral_const_mul, integral_mul_const]

theorem quadratic_matrix_sub_smul {I : Type*} [Fintype I]
    (A B : Matrix I I ℂ) (c : ℂ) (φ : I → ℂ) :
    star φ ⬝ᵥ ((A - c • B) *ᵥ φ) =
      star φ ⬝ᵥ (A *ᵥ φ) - c * (star φ ⬝ᵥ (B *ᵥ φ)) := by
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul]

theorem averagedProductDifference_quadratic {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] {J : ι → Type*} [∀ t, Fintype (J t)]
    (μ : Measure Ω) (A : Ω → (t : ι) → Matrix (J t) (J t) ℂ)
    (A₀ : (t : ι) → Matrix (J t) (J t) ℂ) (ell : ℝ)
    (hi : ∀ u v, Integrable (fun x => productMatrix (A x) u v) μ)
    (φ : (t : ι) → J t → ℂ) :
    star (productVector φ) ⬝ᵥ (averagedProductDifference μ A A₀ ell *ᵥ productVector φ) =
      (∫ x, ∏ t, star (φ t) ⬝ᵥ (A x t *ᵥ φ t) ∂μ) -
        (ell : ℂ) * ∏ t, star (φ t) ⬝ᵥ (A₀ t *ᵥ φ t) := by
  change star (productVector φ) ⬝ᵥ
    (((show Matrix ((t : ι) → J t) ((t : ι) → J t) ℂ from
      fun u v => ∫ x, productMatrix (A x) u v ∂μ) - (ell : ℂ) • productMatrix A₀) *ᵥ
      productVector φ) = _
  rw [quadratic_matrix_sub_smul, quadratic_entrywiseIntegral μ _ hi,
    productMatrix_quadratic]
  simp_rw [productMatrix_quadratic]

theorem quadratic_eq_ofReal {I : Type*} [Fintype I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (φ : I → ℂ) :
    star φ ⬝ᵥ (A *ᵥ φ) = (finiteQuadraticForm A φ : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re, finiteQuadraticForm, dotProduct, Matrix.mulVec,
      Pi.star_apply, Finset.mul_sum, mul_assoc]
  · exact hA.im_star_dotProduct_mulVec_self φ

theorem product_quadratic_re {ι : Type*} [Fintype ι] {J : ι → Type*}
    [∀ t, Fintype (J t)] (A : (t : ι) → Matrix (J t) (J t) ℂ)
    (hA : ∀ t, (A t).IsHermitian) (φ : (t : ι) → J t → ℂ) :
    (∏ t, star (φ t) ⬝ᵥ (A t *ᵥ φ t)).re = ∏ t, finiteQuadraticForm (A t) (φ t) := by
  simp_rw [quadratic_eq_ofReal _ (hA _), ← Complex.ofReal_prod, Complex.ofReal_re]

theorem integrable_product_quadratic {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] {J : ι → Type*} [∀ t, Fintype (J t)]
    (μ : Measure Ω) (A : Ω → (t : ι) → Matrix (J t) (J t) ℂ)
    (hi : ∀ u v, Integrable (fun x => productMatrix (A x) u v) μ)
    (φ : (t : ι) → J t → ℂ) :
    Integrable (fun x => ∏ t, star (φ t) ⬝ᵥ (A x t *ᵥ φ t)) μ := by
  simp_rw [← productMatrix_quadratic]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  exact integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ =>
    ((hi u v).mul_const _).const_mul _

/-- A lower bound on all product-vector expectations makes the integrated difference
nonnegative on all product vectors. The local spaces may depend on the copy index. -/
theorem averagedProductDifference_product_nonneg {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] {J : ι → Type*} [∀ t, Fintype (J t)]
    (μ : Measure Ω) (A : Ω → (t : ι) → Matrix (J t) (J t) ℂ)
    (A₀ : (t : ι) → Matrix (J t) (J t) ℂ) (ell : ℝ)
    (hi : ∀ u v, Integrable (fun x => productMatrix (A x) u v) μ)
    (hA : ∀ᵐ x ∂μ, ∀ t, (A x t).IsHermitian) (hA₀ : ∀ t, (A₀ t).IsHermitian)
    (hcross : ∀ φ : (t : ι) → J t → ℂ,
      ell * (∏ t, finiteQuadraticForm (A₀ t) (φ t)) ≤
        ∫ x, ∏ t, finiteQuadraticForm (A x t) (φ t) ∂μ)
    (φ : (t : ι) → J t → ℂ) :
    0 ≤ star (productVector φ) ⬝ᵥ
      (averagedProductDifference μ A A₀ ell *ᵥ productVector φ) := by
  apply Complex.nonneg_iff.mpr
  constructor
  · rw [averagedProductDifference_quadratic μ A A₀ ell hi,
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      product_quadratic_re A₀ hA₀]
    change 0 ≤ RCLike.re (∫ x, ∏ t, star (φ t) ⬝ᵥ (A x t *ᵥ φ t) ∂μ) - _
    rw [← integral_re (integrable_product_quadratic μ A hi φ)]
    have heq : (fun x => RCLike.re (∏ t, star (φ t) ⬝ᵥ (A x t *ᵥ φ t))) =ᵐ[μ]
        (fun x => ∏ t, finiteQuadraticForm (A x t) (φ t)) := by
      filter_upwards [hA] with x hx
      exact product_quadratic_re (A x) hx φ
    rw [integral_congr_ae heq]
    exact sub_nonneg.mpr (hcross φ)
  · exact ((averagedProductDifference_isHermitian μ A A₀ ell hA hA₀).im_star_dotProduct_mulVec_self _).symm

/-- Convert the nonzero-vector ratio hypothesis into a real cross-multiplied inequality
for every product vector, including products with a zero factor. -/
theorem product_vector_real_cross_of_ratio {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] {J : ι → Type*} [∀ t, Fintype (J t)]
    (μ : Measure Ω) (A : Ω → (t : ι) → Matrix (J t) (J t) ℂ)
    (A₀ : (t : ι) → Matrix (J t) (J t) ℂ) (ell : ℝ) (hell : 0 ≤ ell)
    (hi : ∀ u v, Integrable (fun x => productMatrix (A x) u v) μ)
    (hA : ∀ᵐ x ∂μ, ∀ t, (A x t).PosSemidef) (hA₀ : ∀ t, (A₀ t).PosDef)
    (hratio : ∀ φ : (t : ι) → J t → ℂ, (∀ t, φ t ≠ 0) →
      ENNReal.ofReal ell ≤ ∫⁻ x, ENNReal.ofReal
        (∏ t, finiteQuadraticForm (A x t) (φ t) / finiteQuadraticForm (A₀ t) (φ t)) ∂μ)
    (φ : (t : ι) → J t → ℂ) :
    ell * (∏ t, finiteQuadraticForm (A₀ t) (φ t)) ≤
      ∫ x, ∏ t, finiteQuadraticForm (A x t) (φ t) ∂μ := by
  classical
  have hnn : ∀ᵐ x ∂μ, 0 ≤ ∏ t, finiteQuadraticForm (A x t) (φ t) := by
    filter_upwards [hA] with x hx
    exact Finset.prod_nonneg fun t _ => finiteQuadraticForm_nonneg _ (hx t) _
  by_cases hz : ∃ t, φ t = 0
  · obtain ⟨t, ht⟩ := hz
    have hprod : (∏ t, finiteQuadraticForm (A₀ t) (φ t)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      simp [ht, finiteQuadraticForm]
    rw [hprod, mul_zero]
    exact integral_nonneg_of_ae hnn
  · have hφ : ∀ t, φ t ≠ 0 := not_exists.mp hz
    have hb : 0 < ∏ t, finiteQuadraticForm (A₀ t) (φ t) :=
      Finset.prod_pos fun t _ => finiteQuadraticForm_pos _ (hA₀ t) _ (hφ t)
    have hr := hratio φ hφ
    simp_rw [Finset.prod_div_distrib, ENNReal.ofReal_div_of_pos hb] at hr
    have hc := likelihood_cross_bound_of_ratio_bound μ
      (fun x => ENNReal.ofReal (∏ t, finiteQuadraticForm (A x t) (φ t)))
      (ENNReal.ofReal ell) (ENNReal.ofReal (∏ t, finiteQuadraticForm (A₀ t) (φ t)))
      (ne_of_gt (ENNReal.ofReal_pos.mpr hb)) ENNReal.ofReal_ne_top hr
    have hir : Integrable (fun x => ∏ t, finiteQuadraticForm (A x t) (φ t)) μ := by
      apply (integrable_product_quadratic μ A hi φ).re.congr
      filter_upwards [hA] with x hx
      exact product_quadratic_re (A x) (fun t => (hx t).isHermitian) φ
    rw [← ENNReal.ofReal_mul hell,
      ← ofReal_integral_eq_lintegral_ofReal hir hnn] at hc
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hnn)).mp hc

/-- Proposition 2's occupation-vector hypothesis produces the finite operator needed
by the adaptive product-vector positivity argument, for each photon record. -/
theorem sector_average_product_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n N : ℕ) (k : Fin N → ℕ)
    (R₀ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (R : Ω → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (ell : ℝ) (hell : 0 ≤ ell)
    (hi : ∀ u v : (t : Fin N) → PhotonSector n (k t),
      Integrable (fun x => ∏ t, R x (u t) (v t)) μ)
    (hR₀ : ∀ t, (sectorBlock (k t) R₀).PosDef)
    (hR : ∀ᵐ x ∂μ, ∀ t, (sectorBlock (k t) (R x)).PosSemidef)
    (hsector : ∀ ϕ : Fin N → Occupation (Fin n) → ℂ,
      (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
      ENNReal.ofReal ell ≤ ∫⁻ x, ENNReal.ofReal (∏ t,
        (∑' u, ∑' w, star (ϕ t u) * R x u w * ϕ t w).re /
        (∑' u, ∑' w, star (ϕ t u) * R₀ u w * ϕ t w).re) ∂μ) :
    let H := averagedProductDifference μ (fun x t => sectorBlock (k t) (R x))
      (fun t => sectorBlock (k t) R₀) ell
    H.IsHermitian ∧ ∀ φ : (t : Fin N) → PhotonSector n (k t) → ℂ,
      0 ≤ star (productVector φ) ⬝ᵥ (H *ᵥ productVector φ) := by
  dsimp only
  have hRH := hR.mono (fun x hx t => (hx t).isHermitian)
  have hR₀H := fun t => (hR₀ t).isHermitian
  constructor
  · exact averagedProductDifference_isHermitian μ _ _ ell hRH hR₀H
  · apply averagedProductDifference_product_nonneg μ _ _ ell hi hRH hR₀H
    apply product_vector_real_cross_of_ratio μ _ _ ell hell hi hR hR₀
    intro φ hφ
    have h := hsector (fun t => extendSector (φ t))
      (fun t u hu => extendSector_zero_off_sector (φ t) u hu)
      (fun t => extendSector_ne_zero (φ t) (hφ t))
    simpa only [occupation_quadratic_form_eq_sector] using h

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5PhiSupport -/
section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 800000

theorem matrix_entry_le_operator_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ ‖A‖ := by
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  have hi : ‖e i‖ = 1 := e.orthonormal.norm_eq_one i
  have hj : ‖e j‖ = 1 := e.orthonormal.norm_eq_one j
  have h := norm_inner_le_norm (𝕜 := ℂ) (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) A (e j))
  have he : inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) A (e j)) = A i j := by
    rw [EuclideanSpace.basisFun_inner]
    simp [e, EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct]
  rw [he, hi, one_mul] at h
  have hb := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (e j)
  rw [hj, mul_one] at hb
  exact h.trans hb

theorem matrix_trace_le_operator_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.trace‖ ≤ n * ‖A‖ := by
  calc
    ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, ‖A‖ := Finset.sum_le_sum fun i _ => matrix_entry_le_operator_norm A i i
    _ = n * ‖A‖ := by simp

/-- The local relative parametrization stays in the prior support throughout
the full parameter range used by the hard family. Only support is asserted;
the derivative/Jacobian claims of Lemma 8 are not needed here. -/
theorem PhiMap_mem_Gsupp {n : ℕ} (hn : 1 ≤ n) (X : Herm0 n) (hX : X ∈ Ggood n)
    (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (Z : Herm0 n) (hZ : Z ∈ herm0Ball ⊤ 0 (1 / 10)) :
    PhiMap X ξ Z ∈ Gsupp n := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  letI : NeZero n := ⟨by omega⟩
  have hXnorm : ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 := hX
  have hZnorm : ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10 := by
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10
    simpa [herm0Ball, WHMultiplicativity.schattenNorm] using hZ
  let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
  let d : ℂ := 1 + (ξ : ℂ) ^ 2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  let T : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt S * (Z : Matrix (Fin n) (Fin n) ℂ) * CFC.sqrt S
  let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  have hSp : S.PosSemidef := by
    have hx := (opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) X.property.1 3 hX).2
    have he : S = ((1 - 3 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (ξ : ℂ) • ((3 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X) := by
      dsimp [S]
      push_cast
      module
    rw [he]
    exact (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith))).add
      (hx.smul (Complex.zero_le_real.mpr hξ.le))
  have hsqrt : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hSp.nonneg
  have hSnorm : ‖S‖ ≤ 1 + 3 * ξ := by
    calc ‖S‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖(ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)‖ := norm_add_le _ _
      _ = 1 + ξ * ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ := by
        rw [norm_one, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ]
      _ ≤ 1 + 3 * ξ := by nlinarith only [hXnorm, hξ]
  have hTnorm : ‖T‖ ≤ (1 + 3 * ξ) / 10 := by
    calc ‖T‖ ≤ ‖CFC.sqrt S‖ * ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ * ‖CFC.sqrt S‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖CFC.sqrt S‖ * (1 / 10) * ‖CFC.sqrt S‖ := by gcongr
      _ = ‖S‖ / 10 := by rw [CFC.norm_sqrt S hSp.nonneg]; nlinarith [Real.sq_sqrt (norm_nonneg S)]
      _ ≤ (1 + 3 * ξ) / 10 := by linarith
  have htr : ‖((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace‖ ≤ n * (3 / 10) := by
    refine (matrix_trace_le_operator_norm _).trans ?_
    have hm := norm_mul_le (X : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin n) (Fin n) ℂ)
    have hab : ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ * ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 * (1 / 10) := by gcongr
    nlinarith only [hm, hab, hn0]
  have henorm : ‖e‖ ≤ 3 * ξ / 10 := by
    dsimp [e]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ,
      Complex.norm_natCast]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [htr, hξ, hn0]
  have hdform : d = 1 + (ξ : ℂ) * e := by dsimp [d, e]; ring
  have hdnorm : 1 - 3 * ξ ^ 2 / 10 ≤ ‖d‖ := by
    have heq : 1 - d = -(ξ : ℂ) * e := by rw [hdform]; ring
    have hrev := norm_sub_norm_le (1 : ℂ) d
    rw [norm_one, heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ] at hrev
    nlinarith only [hrev, henorm, hξ]
  have hdpos : 0 < ‖d‖ := by nlinarith only [hdnorm, hξ, hξ32]
  have hd0 : d ≠ 0 := norm_pos_iff.mp hdpos
  have hnum : ‖(X : Matrix (Fin n) (Fin n) ℂ) + T - e • (1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 4 * ‖d‖ := by
    have hnorm : ‖(X : Matrix (Fin n) (Fin n) ℂ) + T - e • (1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤
        ‖(X : Matrix (Fin n) (Fin n) ℂ) + T‖ + ‖e • (1 : Matrix (Fin n) (Fin n) ℂ)‖ := norm_sub_le _ _
    have hsum : ‖(X : Matrix (Fin n) (Fin n) ℂ) + T‖ ≤
        ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ + ‖T‖ := norm_add_le _ _
    rw [norm_smul, norm_one, mul_one] at hnorm
    nlinarith only [hnorm, hsum, hXnorm, hTnorm, henorm, hdnorm, hξ, hξ32]
  have hformula : (ξ⁻¹ : ℂ) •
      (d⁻¹ • (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1) =
      d⁻¹ • ((X : Matrix (Fin n) (Fin n) ℂ) + T - e • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    have hprod : CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S = S + (ξ : ℂ) • T := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
        hsqrt, T]
    rw [hprod]
    ext i j
    simp only [S, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    rw [hdform]
    push_cast
    have hden : 1 + (ξ : ℂ) * e ≠ 0 := by simpa only [hdform] using hd0
    have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
    field_simp [hden, hξc]
    <;> ring
  unfold PhiMap
  dsimp only
  split_ifs with h
  · change ‖(ξ⁻¹ : ℂ) •
        (d⁻¹ • (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1)‖ ≤ 4
    rw [hformula, norm_smul, norm_inv, mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hdpos).mpr hnum
  · simp [Gsupp, WHMultiplicativity.schattenNorm]

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5PhiMeasurable -/
section
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace BosonicLearn.Prop5

/-- The totalized relative-perturbation map is Borel measurable. The
matrix square root is constant because the base point is fixed. -/
theorem measurable_PhiMap {n : ℕ} (X₀ : Herm0 n) (ξ : ℝ) :
    Measurable (PhiMap X₀ ξ) := by
  classical
  letI : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
  letI : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩
  let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X₀ : Matrix (Fin n) (Fin n) ℂ)
  let M : Herm0 n → Matrix (Fin n) (Fin n) ℂ := fun Z =>
    (ξ⁻¹ : ℂ) • (((1 + (ξ : ℂ) ^ 2 *
      ((X₀ : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n)⁻¹) •
      (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1)
  have hM : Measurable M := by
    dsimp [M]
    fun_prop
  have hs : MeasurableSet {Z : Herm0 n | M Z ∈ Herm0 n} :=
    (Herm0_isClosed n).measurableSet.preimage hM
  have hf : Measurable (fun Z : {Z : Herm0 n | M Z ∈ Herm0 n} =>
      (⟨M Z, Z.property⟩ : Herm0 n)) := by
    change @Measurable _ _ _ (borel _) _
    rw [borel_comap]
    exact (hM.comp measurable_subtype_coe).subtype_mk
  unfold PhiMap
  change Measurable (fun Z => if h : M Z ∈ Herm0 n then (⟨M Z, h⟩ : Herm0 n) else 0)
  exact hf.dite (measurable_const : Measurable
    (fun _ : ({Z : Herm0 n | M Z ∈ Herm0 n}ᶜ : Set (Herm0 n)) => (0 : Herm0 n))) hs

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5FamilyEntries -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix BigOperators

namespace BosonicLearn.Prop5
noncomputable section

theorem continuous_fugacityCoeff_entry_family_entries {n : ℕ} (u v : Occupation (Fin n)) :
    Continuous (fun R : Matrix (Fin n) (Fin n) ℂ => fugacityCoeff R u v) := by
  classical
  unfold fugacityCoeff gammaFock
  fun_prop

theorem continuous_family_entry_family_entries {n : ℕ} (ν ξ : ℝ) (u v : Occupation (Fin n)) :
    Continuous (fun X : Herm0 n => fugacityCoeff (fugacityFamily ν ξ X) u v) := by
  apply (continuous_fugacityCoeff_entry_family_entries u v).comp
  unfold fugacityFamily
  fun_prop

theorem isCompact_Gsupp (n : ℕ) : IsCompact (Gsupp n) := by
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → ℂ))
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → ℂ))
  have hc : Continuous fun X : Herm0 n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
    apply Continuous.norm
    exact (LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
        continuous_subtype_val
  apply Metric.isCompact_of_isClosed_isBounded
  · simpa [Gsupp, WHMultiplicativity.schattenNorm] using isClosed_le hc continuous_const
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨4, ?_⟩
    intro X hX
    change ‖fun i j => (X : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ 4
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro j
    exact (matrix_entry_le_operator_norm (X : Matrix (Fin n) (Fin n) ℂ) i j).trans hX

theorem finite_cond_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Set Ω) : IsFiniteMeasure (cond μ s) := by
  constructor
  calc
    (cond μ s) Set.univ = (μ s)⁻¹ * μ s := by
      simp [ProbabilityTheory.cond, Measure.smul_apply]
    _ ≤ 1 := ENNReal.inv_mul_le_one _
    _ < ⊤ := by norm_num

theorem measurableSet_operator_ball (n : ℕ) (b : ℝ) :
    MeasurableSet (herm0Ball ⊤ (0 : Herm0 n) b) := by
  have hc : Continuous fun X : Herm0 n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
    apply Continuous.norm
    exact (LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
        continuous_subtype_val
  simpa [herm0Ball, WHMultiplicativity.schattenNorm] using
    measurableSet_le hc.measurable measurable_const

/-- Every finite tensor entry of the perturbed fugacity family is integrable under
the uniform perturbation measure. Polynomial continuity and compact prior support
give a bound, so no differentiability or explicit entry estimate is required. -/
theorem integrable_family_Phi_product_entry {ι : Type*} [Fintype ι]
    (n : ℕ) (hn : 1 ≤ n) (ν ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X₀ : Herm0 n) (hX₀ : X₀ ∈ Ggood n) (b : ℝ) (hb10 : b ≤ 1 / 10)
    (u v : ι → Occupation (Fin n)) :
    Integrable (fun Z => ∏ t, fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)) (u t) (v t))
      (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := by
  have := finite_cond_measure (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)
  let f := fun X : Herm0 n => ∏ t, fugacityCoeff (fugacityFamily ν ξ X) (u t) (v t)
  have hf : Continuous f := continuous_finsetProd _ fun t _ => continuous_family_entry_family_entries ν ξ (u t) (v t)
  obtain ⟨C, hC⟩ := (isCompact_Gsupp n).exists_bound_of_continuousOn hf.continuousOn
  apply Integrable.of_bound ((hf.measurable.comp (measurable_PhiMap X₀ ξ)).aestronglyMeasurable) C
  apply ae_cond_of_forall_mem (measurableSet_operator_ball n b)
  intro Z hZ
  apply hC
  apply PhiMap_mem_Gsupp hn X₀ hX₀ ξ hξ hξ32 Z
  exact le_trans hZ hb10

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5FamilySectorAverage -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

namespace BosonicLearn.Prop5
noncomputable section

/-- The physical fugacity-family specialization of the finite averaged-operator bridge.
All integrability, support, and faithfulness premises are discharged here. -/
theorem family_sector_average_of_rank_one_bound
    (n : ℕ) (hn : 1 ≤ n) (ν ξ : ℝ) (hνlo : 1 / (n : ℝ) ≤ ν) (hνhi : ν ≤ 1)
    (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32) (X₀ : Herm0 n) (hX₀ : X₀ ∈ Ggood n)
    (b : ℝ) (hb10 : b ≤ 1 / 10) (N : ℕ) (k : Fin N → ℕ)
    (ell : ℝ) (hell : 0 ≤ ell)
    (hsector : ∀ ϕ : Fin N → Occupation (Fin n) → ℂ,
      (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
      ENNReal.ofReal ell ≤ ∫⁻ Z, ENNReal.ofReal (∏ t,
        (∑' u, ∑' v, star (ϕ t u) *
          fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)) u v * ϕ t v).re /
        (∑' u, ∑' v, star (ϕ t u) * fugacityCoeff (fugacityFamily ν ξ X₀) u v * ϕ t v).re)
        ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) :
    let H := averagedProductDifference
      (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b))
      (fun Z t => sectorBlock (k t) (fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z))))
      (fun t => sectorBlock (k t) (fugacityCoeff (fugacityFamily ν ξ X₀))) ell
    H.IsHermitian ∧ ∀ φ : (t : Fin N) → PhotonSector n (k t) → ℂ,
      0 ≤ star (productVector φ) ⬝ᵥ (H *ᵥ productVector φ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hν : 0 < ν := (div_pos (by norm_num) hnR).trans_le hνlo
  have hXsupp : X₀ ∈ Gsupp n := le_trans hX₀ (by norm_num : (3 : ℝ) ≤ 4)
  apply sector_average_product_nonneg _ n N k _ _ ell hell
    (fun u v => integrable_family_Phi_product_entry n hn ν ξ hξ hξ32 X₀ hX₀ b hb10
      (fun t => (u t : Occupation (Fin n))) (fun t => (v t : Occupation (Fin n))))
    (fun t => family_sector_posDef ν ξ hν hνhi hξ hξ32 X₀ hXsupp (k t)) _ hsector
  apply ae_cond_of_forall_mem (measurableSet_operator_ball n b)
  intro Z hZ t
  exact (family_sector_posDef ν ξ hν hνhi hξ hξ32 (PhiMap X₀ ξ Z)
    (PhiMap_mem_Gsupp hn X₀ hX₀ ξ hξ hξ32 Z (le_trans hZ hb10)) (k t)).posSemidef

/-- Proposition 2 supplies a block-positive averaged sector operator for every photon record. -/
theorem proposition_2_sector_average :
    ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 →
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ X₀ ∈ Ggood n,
      ∀ b : ℝ, 0 < b → b ≤ 1 / 10 → ∀ (N : ℕ) (k : Fin N → ℕ),
        let ell := Real.exp (-(C * ξ ^ 2 * ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)))
        let H := averagedProductDifference
          (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b))
          (fun Z t => sectorBlock (k t) (fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z))))
          (fun t => sectorBlock (k t) (fugacityCoeff (fugacityFamily ν ξ X₀))) ell
        H.IsHermitian ∧ ∀ φ : (t : Fin N) → PhotonSector n (k t) → ℂ,
          0 ≤ star (productVector φ) ⬝ᵥ (H *ᵥ productVector φ) := by
  obtain ⟨C, hC, ξ₀, hξ₀, hξ32, hsector⟩ := proposition_2
  refine ⟨C, hC, ξ₀, hξ₀, hξ32, ?_⟩
  intro n hn ν hνlo hνhi ξ hξ hξξ X₀ hX₀ b hb hb10 N k
  apply family_sector_average_of_rank_one_bound n hn ν ξ hνlo hνhi hξ
    (hξξ.trans_lt hξ32) X₀ hX₀ b hb10 N k _ (Real.exp_pos _).le
  exact hsector n hn ν hνlo hνhi ξ hξ hξξ X₀ hX₀ b hb hb10 N k

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5SectorExperiment -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

namespace BosonicLearn.Prop5
noncomputable section

/-- Finite trace pairing commutes with entrywise integration. -/
theorem matrixPair_entrywiseIntegral {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (A : Ω → Matrix I I ℂ) (E : Matrix I I ℂ)
    (hi : ∀ i j, Integrable (fun x => A x i j) μ) :
    matrixPair (fun i j => ∫ x, A x i j ∂μ) E = ∫ x, matrixPair (A x) E ∂μ := by
  classical
  simp only [matrixPair]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hi i j).mul_const _))]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => (hi i j).mul_const _)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_mul_const]

theorem integrable_matrixPair {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (A : Ω → Matrix I I ℂ) (E : Matrix I I ℂ)
    (hi : ∀ i j, Integrable (fun x => A x i j) μ) :
    Integrable (fun x => matrixPair (A x) E) μ := by
  classical
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hi i j).mul_const _

theorem matrixPair_sub_smul {I : Type*} [Fintype I]
    (A B E : Matrix I I ℂ) (c : ℂ) :
    matrixPair (A - c • B) E = matrixPair A E - c * matrixPair B E := by
  simp only [matrixPair, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

/-- Positivity of the integrated difference is a lower bound on the expected pairing. -/
theorem matrixPair_average_nonneg_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] {J : ι → Type*} [∀ t, Fintype (J t)]
    (μ : Measure Ω) (A : Ω → (t : ι) → Matrix (J t) (J t) ℂ)
    (A₀ : (t : ι) → Matrix (J t) (J t) ℂ) (ell : ℝ)
    (E : Matrix (∀ t, J t) (∀ t, J t) ℂ)
    (hi : ∀ u v, Integrable (fun x => productMatrix (A x) u v) μ)
    (hp : 0 ≤ matrixPair (averagedProductDifference μ A A₀ ell) E) :
    ell * (matrixPair (productMatrix A₀) E).re ≤
      ∫ x, (matrixPair (productMatrix (A x)) E).re ∂μ := by
  have hp' := (Complex.nonneg_iff.mp hp).1
  change 0 ≤ (matrixPair ((show Matrix (∀ t, J t) (∀ t, J t) ℂ from
    fun u v => ∫ x, productMatrix (A x) u v ∂μ) -
    (ell : ℂ) • productMatrix A₀) E).re at hp'
  rw [matrixPair_sub_smul, matrixPair_entrywiseIntegral μ _ E hi,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hp'
  change 0 ≤ RCLike.re (∫ x, matrixPair (productMatrix (A x)) E ∂μ) -
    ell * (matrixPair (productMatrix A₀) E).re at hp'
  rw [← integral_re (integrable_matrixPair μ _ E hi)] at hp'
  exact sub_nonneg.mp hp'

/-- An adaptive finite-sector effect inherits every integrated product-vector lower bound. -/
theorem adaptive_product_average_event_bound {n N : ℕ} {O Ω : Type}
    [MeasurableSpace O] [MeasurableSpace Ω] (S : AdaptiveScheme n N O)
    (J : Fin N → Type) [∀ t, Fintype (J t)]
    (a : ∀ t, J t → Occupation (Fin n))
    (μ : Measure Ω) (A : Ω → (t : Fin N) → Matrix (J t) (J t) ℂ)
    (A₀ : (t : Fin N) → Matrix (J t) (J t) ℂ) (ell : ℝ)
    (hi : ∀ u v, Integrable (fun x => productMatrix (A x) u v) μ)
    (hA : ∀ᵐ x ∂μ, ∀ t, (A x t).IsHermitian) (hA₀ : ∀ t, (A₀ t).IsHermitian)
    (hcross : ∀ φ : (t : Fin N) → J t → ℂ,
      ell * (∏ t, finiteQuadraticForm (A₀ t) (φ t)) ≤
        ∫ x, ∏ t, finiteQuadraticForm (A x t) (φ t) ∂μ) :
    ∃ M : FockPOVM (Fin N → Occupation (Fin n)) (Fin N → O),
      (∀ τ : Fin N → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ,
        (∀ t, IsDensity (τ t)) →
        M.law (fun u v => ∏ t, τ t (u t) (v t)) =
          sequentialLaw (fun t => S.round (τ t) t) N le_rfl) ∧
      ∀ B, MeasurableSet B →
        ell * (matrixPair (productMatrix A₀) ((M.effect B).submatrix
          (fun u t => a t (u t)) (fun u t => a t (u t)))).re ≤
        ∫ x, (matrixPair (productMatrix (A x)) ((M.effect B).submatrix
          (fun u t => a t (u t)) (fun u t => a t (u t)))).re ∂μ := by
  classical
  obtain ⟨M, hML, hMT⟩ := adaptive_scheme_dependent_submatrix_positive S J a
  refine ⟨M, hML, ?_⟩
  intro B hB
  let E : Matrix (∀ t, J t) (∀ t, J t) ℂ :=
    (M.effect B).submatrix (fun u t => a t (u t)) (fun u t => a t (u t))
  have hp := hMT B hB (averagedProductDifference μ A A₀ ell)
    (averagedProductDifference_isHermitian μ A A₀ ell hA hA₀)
    (averagedProductDifference_product_nonneg μ A A₀ ell hi hA hA₀ hcross)
  exact matrixPair_average_nonneg_bound μ A A₀ ell E hi hp


theorem matrixPair_comm {I : Type*} [Fintype I] (A E : Matrix I I ℂ) :
    matrixPair A E = matrixPair E A := by
  classical
  unfold matrixPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem matrixPair_smul_left {I : Type*} [Fintype I]
    (A E : Matrix I I ℂ) (c : ℂ) : matrixPair (c • A) E = c * matrixPair A E := by
  simp only [matrixPair, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Product sector normalization is division by the product of sector masses. -/
theorem normalized_photon_productMatrix {n N : ℕ} (k : Fin N → ℕ)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) :
    productMatrix (fun t => sectorBlock (k t)
      (normalizedFiniteCut (photonSectorSet n (k t)) ρ)) =
      (((∏ t, finiteCutMass (photonSectorSet n (k t)) ρ)⁻¹ : ℝ) : ℂ) •
        productMatrix (fun t => sectorBlock (k t) ρ) := by
  ext u v
  simp only [productMatrix, normalized_sector_block, Matrix.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, ← Complex.ofReal_prod, Finset.prod_inv_distrib,
    Complex.ofReal_inv]

/-- Multiplying the conditional sector law by its mass recovers the unnormalized
finite trace pairing for the same adaptive collective effect. -/
theorem photon_record_weighted_born {n N : ℕ} {O : Type} [MeasurableSpace O]
    (k : Fin N → ℕ) (M : FockPOVM (Fin N → Occupation (Fin n)) O)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (hρ : IsDensity ρ)
    (hm : ∀ t, 0 < finiteCutMass (photonSectorSet n (k t)) ρ)
    (B : Set O) (hB : MeasurableSet B) :
    (∏ t, ENNReal.ofReal (finiteCutMass (photonSectorSet n (k t)) ρ)) *
      M.law (fun u v => ∏ t, normalizedFiniteCut (photonSectorSet n (k t)) ρ (u t) (v t)) B =
    ENNReal.ofReal (matrixPair (productMatrix (fun t => sectorBlock (k t) ρ))
      ((M.effect B).submatrix (photonProductEmbedding k) (photonProductEmbedding k))).re := by
  classical
  let m := ∏ t, finiteCutMass (photonSectorSet n (k t)) ρ
  have hmpos : 0 < m := Finset.prod_pos fun t _ => hm t
  have hd := isDensity_fin_product
    (fun t => normalizedFiniteCut (photonSectorSet n (k t)) ρ)
    (fun t => normalizedFiniteCut_isDensity _ ρ hρ (hm t))
  rw [M.law_born _ hd B hB,
    born_sum_compression (photonProductEmbedding k) (M.effect B) _ (photon_product_supported k ρ)]
  change (∏ t, ENNReal.ofReal (finiteCutMass (photonSectorSet n (k t)) ρ)) *
    ENNReal.ofReal (matrixPair ((M.effect B).submatrix (photonProductEmbedding k)
      (photonProductEmbedding k)) (productMatrix (fun t => sectorBlock (k t)
        (normalizedFiniteCut (photonSectorSet n (k t)) ρ)))).re = _
  rw [matrixPair_comm, normalized_photon_productMatrix, matrixPair_smul_left]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun t _ => (hm t).le),
    ← ENNReal.ofReal_mul hmpos.le]
  congr 1
  change m * (m⁻¹ * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ hmpos.ne', one_mul]


/-- The finite-sector adaptive lower bound, stated directly for weighted event laws.
The source space and all outcome sigma algebras are unrestricted. -/
theorem adaptive_photon_record_event_bound {n N : ℕ} {O Ω : Type}
    [MeasurableSpace O] [MeasurableSpace Ω] (S : AdaptiveScheme n N O)
    (k : Fin N → ℕ) (μ : Measure Ω)
    (ρ₀ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (ρ : Ω → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (ell : ℝ) (hell : 0 ≤ ell)
    (hi : ∀ u v : (t : Fin N) → PhotonSector n (k t),
      Integrable (fun x => ∏ t, ρ x (u t) (v t)) μ)
    (hD₀ : IsDensity ρ₀) (hD : ∀ᵐ x ∂μ, IsDensity (ρ x))
    (hm₀ : ∀ t, 0 < finiteCutMass (photonSectorSet n (k t)) ρ₀)
    (hm : ∀ᵐ x ∂μ, ∀ t, 0 < finiteCutMass (photonSectorSet n (k t)) (ρ x))
    (hP : ∀ᵐ x ∂μ, ∀ t, (sectorBlock (k t) (ρ x)).PosSemidef)
    (hH : (averagedProductDifference μ (fun x t => sectorBlock (k t) (ρ x))
      (fun t => sectorBlock (k t) ρ₀) ell).IsHermitian)
    (hq : ∀ φ : (t : Fin N) → PhotonSector n (k t) → ℂ,
      0 ≤ star (productVector φ) ⬝ᵥ
        (averagedProductDifference μ (fun x t => sectorBlock (k t) (ρ x))
          (fun t => sectorBlock (k t) ρ₀) ell *ᵥ productVector φ))
    (B : Set (Fin N → O)) (hB : MeasurableSet B) :
    ENNReal.ofReal ell * (∏ t, ENNReal.ofReal (finiteCutMass (photonSectorSet n (k t)) ρ₀)) *
      (sequentialLaw (fun t => S.round (normalizedFiniteCut (photonSectorSet n (k t)) ρ₀) t)
        N le_rfl) B ≤
      ∫⁻ x, (∏ t, ENNReal.ofReal (finiteCutMass (photonSectorSet n (k t)) (ρ x))) *
        (sequentialLaw (fun t => S.round (normalizedFiniteCut (photonSectorSet n (k t)) (ρ x)) t)
          N le_rfl) B ∂μ := by
  classical
  obtain ⟨M, hML, hMT⟩ := adaptive_scheme_dependent_submatrix_positive S
    (fun t => PhotonSector n (k t)) (fun _ => Subtype.val)
  let E := (M.effect B).submatrix (photonProductEmbedding k) (photonProductEmbedding k)
  have hp : 0 ≤ matrixPair (averagedProductDifference μ
      (fun x t => sectorBlock (k t) (ρ x)) (fun t => sectorBlock (k t) ρ₀) ell) E :=
    hMT B hB _ hH hq
  have hb := matrixPair_average_nonneg_bound μ
    (fun x t => sectorBlock (k t) (ρ x)) (fun t => sectorBlock (k t) ρ₀) ell E hi hp
  have hE : E.PosSemidef :=
    (ComposeEffect.effect_posSemidef_full M B hB).submatrix (photonProductEmbedding k)
  have hnn : ∀ᵐ x ∂μ,
      0 ≤ (matrixPair (productMatrix (fun t => sectorBlock (k t) (ρ x))) E).re := by
    filter_upwards [hP] with x hx
    exact (Complex.nonneg_iff.mp (matrixPair_posSemidef_nonneg _ E
      (finite_tensor_posSemidef _ hx) hE)).1
  have hi' : Integrable (fun x =>
      (matrixPair (productMatrix (fun t => sectorBlock (k t) (ρ x))) E).re) μ :=
    (integrable_matrixPair μ
      (fun x => productMatrix (fun t => sectorBlock (k t) (ρ x))) E hi).re
  have hb' := ENNReal.ofReal_le_ofReal hb
  rw [ENNReal.ofReal_mul hell, ofReal_integral_eq_lintegral_ofReal hi' hnn] at hb'
  have hbase := photon_record_weighted_born k M ρ₀ hD₀ hm₀ B hB
  rw [hML _ (fun t => normalizedFiniteCut_isDensity _ ρ₀ hD₀ (hm₀ t))] at hbase
  rw [mul_assoc, hbase]
  apply hb'.trans_eq
  apply lintegral_congr_ae
  filter_upwards [hD, hm] with x hx hmx
  have hx' := photon_record_weighted_born k M (ρ x) hx hmx B hB
  rw [hML _ (fun t => normalizedFiniteCut_isDensity _ (ρ x) hx (hmx t))] at hx'
  exact hx'.symm


/-- For the physical hard family all analytic premises of the record event bound
follow from the support bounds. Only the averaged sector operator remains as input. -/
theorem family_photon_record_event_bound {n N : ℕ} {O : Type} [MeasurableSpace O]
    (S : AdaptiveScheme n N O) (hn : 1 ≤ n)
    (ν ξ : ℝ) (hνlo : 1 / (n : ℝ) ≤ ν) (hνhi : ν ≤ 1)
    (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32) (X₀ : Herm0 n) (hX₀ : X₀ ∈ Ggood n)
    (b : ℝ) (hb10 : b ≤ 1 / 10) (k : Fin N → ℕ) (ell : ℝ) (hell : 0 ≤ ell)
    (haverage :
      let H := averagedProductDifference
        (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b))
        (fun Z t => sectorBlock (k t) (fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z))))
        (fun t => sectorBlock (k t) (fugacityCoeff (fugacityFamily ν ξ X₀))) ell
      H.IsHermitian ∧ ∀ φ : (t : Fin N) → PhotonSector n (k t) → ℂ,
        0 ≤ star (productVector φ) ⬝ᵥ (H *ᵥ productVector φ))
    (B : Set (Fin N → O)) (hB : MeasurableSet B) :
    ENNReal.ofReal ell * (∏ t, ENNReal.ofReal (finiteCutMass (photonSectorSet n (k t))
      (fugacityCoeff (fugacityFamily ν ξ X₀)))) *
      (sequentialLaw (fun t => S.round (normalizedFiniteCut (photonSectorSet n (k t))
        (fugacityCoeff (fugacityFamily ν ξ X₀))) t) N le_rfl) B ≤
      ∫⁻ Z, (∏ t, ENNReal.ofReal (finiteCutMass (photonSectorSet n (k t))
        (fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z))))) *
        (sequentialLaw (fun t => S.round (normalizedFiniteCut (photonSectorSet n (k t))
          (fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)))) t) N le_rfl) B
          ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hν : 0 < ν := (div_pos (by norm_num) hnR).trans_le hνlo
  have hXsupp : X₀ ∈ Gsupp n := le_trans hX₀ (by norm_num : (3 : ℝ) ≤ 4)
  have hfd : ∀ X ∈ Gsupp n, IsDensity (fugacityCoeff (fugacityFamily ν ξ X)) := by
    intro X hX
    have hR := family_spectral_bounds ν ξ hν hνhi hξ hξ32 X hX
    exact fugacityCoeff_isDensity _ hR.1 hR.2.1
  have hXs : ∀ᵐ Z ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b),
      PhiMap X₀ ξ Z ∈ Gsupp n := by
    apply ae_cond_of_forall_mem (measurableSet_operator_ball n b)
    intro Z hZ
    exact PhiMap_mem_Gsupp hn X₀ hX₀ ξ hξ hξ32 Z (le_trans hZ hb10)
  apply adaptive_photon_record_event_bound S k _ _ _ ell hell
    (fun u v => integrable_family_Phi_product_entry n hn ν ξ hξ hξ32 X₀ hX₀ b hb10
      (fun t => (u t : Occupation (Fin n))) (fun t => (v t : Occupation (Fin n))))
    (hfd X₀ hXsupp) (hXs.mono fun Z hZ => hfd _ hZ)
    (fun t => photonSector_mass_pos hn (k t) _
      (family_sector_posDef ν ξ hν hνhi hξ hξ32 X₀ hXsupp (k t))) _ _
    haverage.1 haverage.2 B hB
  · filter_upwards [hXs] with Z hZ t
    exact photonSector_mass_pos hn (k t) _
      (family_sector_posDef ν ξ hν hνhi hξ hξ32 _ hZ (k t))
  · filter_upwards [hXs] with Z hZ t
    exact (family_sector_posDef ν ξ hν hνhi hξ hξ32 _ hZ (k t)).posSemidef

/-- Proposition 2 controls every event of an arbitrary adaptive transcript,
conditional on any fixed photon-number record. -/
theorem proposition_2_adaptive_record_event_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 →
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ X₀ ∈ Ggood n,
      ∀ b : ℝ, 0 < b → b ≤ 1 / 10 → ∀ (N : ℕ) (O : Type) [MeasurableSpace O]
        (S : AdaptiveScheme n N O) (k : Fin N → ℕ) (B : Set (Fin N → O)),
        MeasurableSet B →
        let ell := Real.exp (-(C * ξ ^ 2 * ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)))
        ENNReal.ofReal ell * (∏ t, ENNReal.ofReal (finiteCutMass (photonSectorSet n (k t))
          (fugacityCoeff (fugacityFamily ν ξ X₀)))) *
          (sequentialLaw (fun t => S.round (normalizedFiniteCut (photonSectorSet n (k t))
            (fugacityCoeff (fugacityFamily ν ξ X₀))) t) N le_rfl) B ≤
          ∫⁻ Z, (∏ t, ENNReal.ofReal (finiteCutMass (photonSectorSet n (k t))
            (fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z))))) *
            (sequentialLaw (fun t => S.round (normalizedFiniteCut (photonSectorSet n (k t))
              (fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)))) t) N le_rfl) B
              ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) := by
  obtain ⟨C, hC, ξ₀, hξ₀, hξ32, hsector⟩ := proposition_2_sector_average
  refine ⟨C, hC, ξ₀, hξ₀, hξ32, ?_⟩
  intro n hn ν hνlo hνhi ξ hξ hξξ X₀ hX₀ b hb hb10 N O _ S k B hB
  exact family_photon_record_event_bound S hn ν ξ hνlo hνhi hξ (hξξ.trans_lt hξ32)
    X₀ hX₀ b hb10 k _ (Real.exp_pos _).le
    (hsector n hn ν hνlo hνhi ξ hξ hξξ X₀ hX₀ b hb hb10 N k) B hB

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5Coarsening -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Exponential likelihood lower bounds survive averaging hidden records.
The cost becomes its conditional mean; this is the Jensen step used when
forgetting photon-number refinements of a measurement transcript. -/
theorem exponential_bound_of_mixture {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : Ω → ℝ) (F : Ω → ℝ≥0∞)
    (hq : Integrable q μ) (hq_nonneg : 0 ≤ᵐ[μ] q)
    (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ᵐ x ∂μ, ENNReal.ofReal (Real.exp (-(C * q x))) ≤ F x) :
    ENNReal.ofReal (Real.exp (-(C * ∫ x, q x ∂μ))) ≤ ∫⁻ x, F x ∂μ := by
  have hexp_meas : AEStronglyMeasurable (fun x => Real.exp (-(C * q x))) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable ((hq.aestronglyMeasurable.const_mul C).neg)
  have hexp_int : Integrable (fun x => Real.exp (-(C * q x))) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hexp_meas
    filter_upwards [hq_nonneg] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hC hx))
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    ((hq.const_mul C).neg) hexp_int
  simp only [Pi.neg_apply, integral_neg, integral_const_mul] at hj
  calc
    ENNReal.ofReal (Real.exp (-(C * ∫ x, q x ∂μ))) ≤
        ENNReal.ofReal (∫ x, Real.exp (-(C * q x)) ∂μ) := ENNReal.ofReal_le_ofReal hj
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (-(C * q x))) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hexp_int
        (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))
    _ ≤ ∫⁻ x, F x ∂μ := lintegral_mono_ae hF

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5CountableCoarsening -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5
set_option maxHeartbeats 600000

/-- Jensen's inequality for a countable, not necessarily normalized mixture.
The exponential cost of the conditional mean is bounded by the mixture of
exponential costs. This is the pointwise photon-record coarsening step. -/
theorem countable_exponential_mixture {ι : Type*} [Countable ι]
    (a : ι → ℝ≥0∞) (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hA0 : (∑' i, a i) ≠ 0) (hAt : (∑' i, a i) ≠ ∞)
    (hB : (∑' i, a i * ENNReal.ofReal (q i)) ≠ ∞)
    (C : ℝ) (hC : 0 ≤ C) :
    ENNReal.ofReal (Real.exp (-(C *
      ((∑' i, a i * ENNReal.ofReal (q i)) / ∑' i, a i).toReal))) * (∑' i, a i) ≤
      ∑' i, a i * ENNReal.ofReal (Real.exp (-(C * q i))) := by
  classical
  letI : MeasurableSpace ι := ⊤
  let μ : Measure ι := Measure.count.withDensity (fun i => a i / ∑' j, a j)
  have hsum : ∀ f : ι → ℝ≥0∞,
      ∫⁻ i, f i ∂μ = (∑' i, a i * f i) / ∑' i, a i := by
    intro f
    rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) (measurable_of_countable _),
      lintegral_count]
    simp only [Pi.mul_apply, div_eq_mul_inv, mul_right_comm (a _) ((∑' j, a j)⁻¹),
      ENNReal.tsum_mul_right]
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [← lintegral_one, hsum]
    simpa using ENNReal.div_self hA0 hAt
  letI := hprob
  have hqint : Integrable q μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (measurable_of_countable q).aestronglyMeasurable (Filter.Eventually.of_forall hq)).mp
    rw [hsum]
    exact ENNReal.div_ne_top hB hA0
  have hqmean : ∫ i, q i ∂μ =
      ((∑' i, a i * ENNReal.ofReal (q i)) / ∑' i, a i).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hq)
      hqint.aestronglyMeasurable, hsum]
  have hj := exponential_bound_of_mixture μ q
    (fun i => ENNReal.ofReal (Real.exp (-(C * q i)))) hqint
    (Filter.Eventually.of_forall hq) C hC (Filter.Eventually.of_forall fun _ => le_rfl)
  rw [hqmean, hsum] at hj
  have hm := mul_le_mul' hj (le_refl (∑' i, a i))
  simpa only [ENNReal.div_mul_cancel hA0 hAt] using hm

/-- A hidden countable record can be forgotten without losing the
exponential likelihood bound. Its cost is replaced by a measurable
conditional mean, with no assumptions on the visible outcome space. -/
theorem countable_likelihood_coarsening {ι Z Ω : Type*} [Countable ι]
    [MeasurableSpace Z] [MeasurableSpace Ω]
    (ref : Measure Ω) (μ : Measure Z)
    (a : ι → Ω → ℝ≥0∞) (ha : ∀ i, Measurable (a i))
    (f : ι → Z → Ω → ℝ≥0∞) (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (cost : ι → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (hAfin : ∫⁻ x, ∑' i, a i x ∂ref ≠ ∞)
    (M : ℝ≥0∞) (hMt : M ≠ ∞)
    (hcostmean : (∫⁻ x, ∑' i, a i x * ENNReal.ofReal (cost i) ∂ref) ≤ M)
    (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ᵐ x ∂ref, ∀ i,
      a i x * ENNReal.ofReal (Real.exp (-(C * cost i))) ≤ ∫⁻ z, f i z x ∂μ) :
    ∃ q : Ω → ℝ, Measurable q ∧ (∀ x, 0 ≤ q x) ∧
      (∫⁻ x, ENNReal.ofReal (q x) ∂(ref.withDensity (fun x => ∑' i, a i x))) ≤ M ∧
      ∀ᵐ x ∂ref,
        ENNReal.ofReal (Real.exp (-(C * q x))) * (∑' i, a i x) ≤
          ∫⁻ z, ∑' i, f i z x ∂μ := by
  let A : Ω → ℝ≥0∞ := fun x => ∑' i, a i x
  let B : Ω → ℝ≥0∞ := fun x => ∑' i, a i x * ENNReal.ofReal (cost i)
  have hAm : Measurable A := Measurable.ennreal_tsum ha
  have hBm : Measurable B := Measurable.ennreal_tsum fun i => (ha i).mul_const _
  let q : Ω → ℝ := fun x => (B x / A x).toReal
  have hqm : Measurable q := (hBm.div hAm).ennreal_toReal
  refine ⟨q, hqm, fun x => ENNReal.toReal_nonneg, ?_, ?_⟩
  · change (∫⁻ x, ENNReal.ofReal (q x) ∂(ref.withDensity A)) ≤ M
    rw [lintegral_withDensity_eq_lintegral_mul _ hAm hqm.ennreal_ofReal]
    apply le_trans (lintegral_mono fun x => ?_) hcostmean
    change A x * ENNReal.ofReal ((B x / A x).toReal) ≤ B x
    calc
      A x * ENNReal.ofReal ((B x / A x).toReal) ≤ A x * (B x / A x) :=
        mul_le_mul' le_rfl ENNReal.ofReal_toReal_le
      _ = B x * (A x * (A x)⁻¹) := by rw [div_eq_mul_inv]; ac_rfl
      _ ≤ B x * 1 := mul_le_mul' le_rfl (ENNReal.mul_inv_le_one _)
      _ = B x := mul_one _
  · have hBfin : ∫⁻ x, B x ∂ref ≠ ∞ := ne_top_of_le_ne_top hMt hcostmean
    filter_upwards [ae_lt_top hAm hAfin, ae_lt_top hBm hBfin, hlocal] with x hAx hBx hx
    by_cases hA0 : A x = 0
    · change ENNReal.ofReal _ * A x ≤ _
      rw [hA0, mul_zero]
      exact bot_le
    · calc
        ENNReal.ofReal (Real.exp (-(C * q x))) * (∑' i, a i x) ≤
            ∑' i, a i x * ENNReal.ofReal (Real.exp (-(C * cost i))) :=
          countable_exponential_mixture (fun i => a i x) cost hcost hA0 hAx.ne hBx.ne C hC
        _ ≤ ∑' i, ∫⁻ z, f i z x ∂μ := ENNReal.tsum_le_tsum hx
        _ = ∫⁻ z, ∑' i, f i z x ∂μ :=
          (lintegral_tsum fun i => ((hf i).comp (measurable_id.prodMk measurable_const)).aemeasurable).symm

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5MeasureLikelihood -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Eventwise domination by a mixture of experiments implies the
corresponding pointwise likelihood inequality, on an arbitrary outcome space. -/
theorem likelihood_ae_of_event_bound {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (μ : Measure Z) [SFinite μ] (ref : Measure Ω) [SigmaFinite ref]
    (a : Ω → ℝ≥0∞) (ha : Measurable a)
    (f : Z → Ω → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) (ell : ℝ≥0∞)
    (hB : ∀ B, MeasurableSet B →
      ell * (ref.withDensity a) B ≤ ∫⁻ z, (ref.withDensity (f z)) B ∂μ) :
    ∀ᵐ x ∂ref, ell * a x ≤ ∫⁻ z, f z x ∂μ := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (measurable_const.mul ha)
  intro B hBmeas _
  change (∫⁻ x in B, ell * a x ∂ref) ≤ ∫⁻ x in B, ∫⁻ z, f z x ∂μ ∂ref
  rw [lintegral_const_mul _ ha]
  have hswap : (∫⁻ x in B, ∫⁻ z, f z x ∂μ ∂ref) =
      ∫⁻ z, (ref.withDensity (f z)) B ∂μ := by
    rw [lintegral_lintegral_swap]
    · exact lintegral_congr fun z => (withDensity_apply (f z) hBmeas).symm
    · exact (hf.comp measurable_swap).aemeasurable
  rw [hswap, ← withDensity_apply a hBmeas]
  exact hB B hBmeas

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5MixtureExponential -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5
set_option maxHeartbeats 800000

/-- Eventwise photon-sector likelihood bounds yield a measurable cost on
the visible transcript, with its original hidden-record expectation bound. -/
theorem weighted_model_exponential_cost {ι Θ Z Ω : Type*} [Countable ι]
    [MeasurableSpace Θ] [MeasurableSpace Z] [MeasurableSpace Ω]
    (ref : Measure Ω) [IsProbabilityMeasure ref] (μ : Measure Z) [SFinite μ]
    (p : ι → Θ → Ω → ℝ≥0∞) (hp : ∀ i, Measurable (Function.uncurry (p i)))
    (hprob : ∀ i θ, IsProbabilityMeasure (ref.withDensity (p i θ)))
    (w : Θ → ι → ℝ≥0∞) (hwm : ∀ i, Measurable fun θ => w θ i)
    (hwsum : ∀ θ, ∑' i, w θ i = 1)
    (θ₀ : Θ) (Φ : Z → Θ) (hΦ : Measurable Φ)
    (cost : ι → ℝ) (hcost : ∀ i, 0 ≤ cost i) (C : ℝ) (hC : 0 ≤ C)
    (M : ℝ≥0∞) (hMt : M ≠ ∞)
    (hcostmean : (∑' i, w θ₀ i * ENNReal.ofReal (cost i)) ≤ M)
    (hlocal : ∀ i B, MeasurableSet B →
      ENNReal.ofReal (Real.exp (-(C * cost i))) *
        (w θ₀ i * (ref.withDensity (p i θ₀)) B) ≤
          ∫⁻ z, w (Φ z) i * (ref.withDensity (p i (Φ z))) B ∂μ) :
    ∃ q : Ω → ℝ, Measurable q ∧ (∀ x, 0 ≤ q x) ∧
      (∫⁻ x, ENNReal.ofReal (q x)
        ∂(ref.withDensity (fun x => ∑' i, w θ₀ i * p i θ₀ x))) ≤ M ∧
      ∀ᵐ x ∂ref,
        ENNReal.ofReal (Real.exp (-(C * q x))) * (∑' i, w θ₀ i * p i θ₀ x) ≤
          ∫⁻ z, ∑' i, w (Φ z) i * p i (Φ z) x ∂μ := by
  let a : ι → Ω → ℝ≥0∞ := fun i x => w θ₀ i * p i θ₀ x
  let f : ι → Z → Ω → ℝ≥0∞ := fun i z x => w (Φ z) i * p i (Φ z) x
  have hpm : ∀ i θ, Measurable (p i θ) :=
    fun i θ => (hp i).comp (measurable_const.prodMk measurable_id)
  have ha : ∀ i, Measurable (a i) := fun i => measurable_const.mul (hpm i θ₀)
  have hf : ∀ i, Measurable (Function.uncurry (f i)) := fun i =>
    (((hwm i).comp hΦ).comp measurable_fst).mul
      ((hp i).comp ((hΦ.comp measurable_fst).prodMk measurable_snd))
  have hwLaw : ∀ i θ B, MeasurableSet B →
      (ref.withDensity (fun x => w θ i * p i θ x)) B =
        w θ i * (ref.withDensity (p i θ)) B := by
    intro i θ B hB
    rw [show (fun x => w θ i * p i θ x) = w θ i • p i θ from rfl,
      withDensity_smul _ (hpm i θ), Measure.smul_apply, smul_eq_mul]
  have hlocal' : ∀ᵐ x ∂ref, ∀ i,
      a i x * ENNReal.ofReal (Real.exp (-(C * cost i))) ≤ ∫⁻ z, f i z x ∂μ := by
    apply ae_all_iff.mpr
    intro i
    have h := likelihood_ae_of_event_bound μ ref (a i) (ha i) (f i) (hf i)
      (ENNReal.ofReal (Real.exp (-(C * cost i)))) (fun B hB => by
        change ENNReal.ofReal _ * (ref.withDensity (fun x => w θ₀ i * p i θ₀ x)) B ≤
          ∫⁻ z, (ref.withDensity (fun x => w (Φ z) i * p i (Φ z) x)) B ∂μ
        simp only [hwLaw i _ B hB]
        exact hlocal i B hB)
    simpa only [mul_comm] using h
  have hcostmean' : (∫⁻ x, ∑' i, a i x * ENNReal.ofReal (cost i) ∂ref) ≤ M := by
    change (∫⁻ x, ∑' i, (w θ₀ i * p i θ₀ x) * ENNReal.ofReal (cost i) ∂ref) ≤ M
    rw [weighted_density_cost_integral ref (fun i => p i θ₀) (fun i => hpm i θ₀)
      (fun i => hprob i θ₀)]
    exact hcostmean
  have hAprob : IsProbabilityMeasure (ref.withDensity (fun x => ∑' i, a i x)) :=
    weighted_likelihood_probability ref (fun i => p i θ₀) (fun i => hpm i θ₀)
      (fun i => hprob i θ₀) (w θ₀) (hwsum θ₀)
  have hAfin : (∫⁻ x, ∑' i, a i x ∂ref) ≠ ∞ := by
    letI := hAprob
    have h := measure_ne_top (ref.withDensity (fun x => ∑' i, a i x)) Set.univ
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h
  exact countable_likelihood_coarsening ref μ a ha f hf cost hcost hAfin M hMt
    hcostmean' C hC hlocal'

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5Model -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-- A positive, jointly measurable adaptive likelihood model and its
exponential comparison, derived from the fixed-sector estimate. -/
theorem adaptive_likelihood_model_proved
    (n : ℕ) (hn : 1 ≤ n) (ν ξ C : ℝ)
    (hνlo : 1 / (n : ℝ) ≤ ν) (hνhi : ν ≤ 1)
    (hξlo : 0 < ξ) (hξhi : ξ < 1 / 32) (hC : 0 < C)
    (hsector : ∀ X₀ ∈ Ggood n, ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∀ (M : ℕ) (k : Fin M → ℕ) (ϕ : Fin M → Occupation (Fin n) → ℂ),
        (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
        ENNReal.ofReal (Real.exp
          (-(C * ξ ^ 2 * ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)))) ≤
          ∫⁻ Z, ENNReal.ofReal (∏ t,
            (∑' u, ∑' v, star (ϕ t u) *
              fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)) u v * ϕ t v).re /
            (∑' u, ∑' v, star (ϕ t u) *
              fugacityCoeff (fugacityFamily ν ξ X₀) u v * ϕ t v).re)
            ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)))
    (N : ℕ) (O : Type) [MeasurableSpace O] (S : AdaptiveScheme n N O) :
    ∃ ref : Measure (Fin N → O), IsProbabilityMeasure ref ∧
    ∃ p : Herm0 n → (Fin N → O) → ℝ≥0∞,
      Measurable (Function.uncurry p) ∧
      (∀ X, IsProbabilityMeasure (ref.withDensity (p X))) ∧
      (∀ X, ∀ᵐ x ∂ref, p X x ≠ 0) ∧
      (∀ X ∈ Gsupp n,
        transcriptLaw S (fugacityCoeff (fugacityFamily ν ξ X)) = ref.withDensity (p X)) ∧
      ∀ X₀ ∈ Ggood n, ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
        ∃ q : (Fin N → O) → ℝ,
          Measurable q ∧ (∀ x, 0 ≤ q x) ∧
          (∫⁻ x, ENNReal.ofReal (q x) ∂(ref.withDensity (p X₀))) ≤
            ENNReal.ofReal (13 * (N : ℝ) * n * ν ^ 2) ∧
          ∀ᵐ x ∂(ref.withDensity (p X₀)),
            ENNReal.ofReal (Real.exp (-(C * ξ ^ 2 * q x))) * p X₀ x ≤
              ∫⁻ Z, p (PhiMap X₀ ξ Z) x
                ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hν : 0 < ν := (div_pos (by norm_num) hnR).trans_le hνlo
  obtain ⟨ref, href, p, hp, hprob, hlaw, hPm, hPprob, hPpos, hphysical⟩ :=
    physical_component_likelihood_model S hn ν ξ hν hνhi hξlo hξhi
  letI := href
  refine ⟨ref, href, (fun X x => ∑' k, physicalRecordWeight ν ξ X k * p k X x),
    hPm, hPprob, hPpos, (fun X hX => (hphysical X hX).symm), ?_⟩
  intro X₀ hX₀ b hb hb10
  let μ := cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)
  letI : IsFiniteMeasure μ := finite_cond_measure _ _
  have hXsupp : X₀ ∈ Gsupp n := le_trans hX₀ (by norm_num : (3 : ℝ) ≤ 4)
  have hXs : ∀ᵐ Z ∂μ, PhiMap X₀ ξ Z ∈ Gsupp n := by
    apply ae_cond_of_forall_mem (measurableSet_operator_ball n b)
    intro Z hZ
    exact PhiMap_mem_Gsupp hn X₀ hX₀ ξ hξlo hξhi Z (le_trans hZ hb10)
  have hlocal : ∀ (k : Fin N → ℕ) B, MeasurableSet B →
      ENNReal.ofReal (Real.exp (-((C * ξ ^ 2) *
        ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)))) *
        (physicalRecordWeight ν ξ X₀ k * (ref.withDensity (p k X₀)) B) ≤
      ∫⁻ Z, physicalRecordWeight ν ξ (PhiMap X₀ ξ Z) k *
        (ref.withDensity (p k (PhiMap X₀ ξ Z))) B ∂μ := by
    intro k B hB
    simp only [hlaw]
    have havg := family_sector_average_of_rank_one_bound n hn ν ξ hνlo hνhi
      hξlo hξhi X₀ hX₀ b hb10 N k
      (Real.exp (-(C * ξ ^ 2 * ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n))))
      (Real.exp_pos _).le (hsector X₀ hX₀ b hb hb10 N k)
    have hevent := family_photon_record_event_bound S hn ν ξ hνlo hνhi hξlo hξhi
      X₀ hX₀ b hb10 k _ (Real.exp_pos _).le havg B hB
    have hrhs : (∫⁻ Z, physicalRecordWeight ν ξ (PhiMap X₀ ξ Z) k *
        (physicalRecordLaw S ν ξ (PhiMap X₀ ξ Z) k) B ∂μ) =
      ∫⁻ Z, (∏ t, ENNReal.ofReal (finiteCutMass (photonSectorSet n (k t))
        (fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z))))) *
        (sequentialLaw (fun t => S.round (normalizedFiniteCut (photonSectorSet n (k t))
          (fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)))) t) N le_rfl) B ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hXs] with Z hZ
      simp only [physicalRecordWeight, physicalRecordLaw, physicalState, supportPatch_eq hZ]
    rw [hrhs]
    simpa only [physicalRecordWeight, physicalRecordLaw, physicalState,
      supportPatch_eq hXsupp, mul_assoc] using hevent
  obtain ⟨q, hq, hqnn, hmean, hbound⟩ := weighted_model_exponential_cost ref μ p hp hprob
    (physicalRecordWeight ν ξ) (measurable_physicalRecordWeight ν ξ)
    (physicalRecordWeight_sum_one ν ξ hν hνhi hξlo hξhi) X₀ (PhiMap X₀ ξ)
    (measurable_PhiMap X₀ ξ)
    (fun k => ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n))
    (fun k => Finset.sum_nonneg fun t _ => by positivity)
    (C * ξ ^ 2) (mul_nonneg hC.le (sq_nonneg ξ))
    (ENNReal.ofReal (13 * (N : ℝ) * n * ν ^ 2)) ENNReal.ofReal_ne_top
    (physicalRecordWeight_cost_mean hn ν ξ hνlo hνhi hξlo hξhi X₀) hlocal
  refine ⟨q, hq, hqnn, hmean, ?_⟩
  exact (withDensity_absolutelyContinuous _ _).ae_le hbound

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5LikelihoodMarkov -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- A nonnegative cost with bounded mean turns a pointwise exponential
likelihood lower bound into a high-probability lower bound. This includes
the zero-cost case, needed for protocols with no samples. -/
theorem exponential_lower_tail_of_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : Ω → ℝ) (F : Ω → ℝ≥0∞)
    (hq : Measurable q) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hF : ∀ᵐ x ∂μ, ENNReal.ofReal (Real.exp (-q x)) ≤ F x)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hmean : (∫⁻ x, ENNReal.ofReal (q x) ∂μ) ≤ ENNReal.ofReal M) :
    μ {x | F x < ENNReal.ofReal (Real.exp (-M / δ))} ≤ ENNReal.ofReal δ := by
  by_cases hM0 : M = 0
  · subst M
    have hz : (fun x => ENNReal.ofReal (q x)) =ᵐ[μ] 0 :=
      (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp hq)).mp
        (le_zero_iff.mp (by simpa using hmean))
    have hbad : μ {x | F x < ENNReal.ofReal (Real.exp (-(0 : ℝ) / δ))} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hz, hF] with x hx hFx
      have hqx : q x = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (hq_nonneg x)
      simpa [hqx] using not_lt_of_ge hFx
    rw [hbad]
    exact zero_le
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    have hthreshold : 0 < M / δ := div_pos hMpos hδ
    have hsubset :
        {x | F x < ENNReal.ofReal (Real.exp (-M / δ))} ≤ᵐ[μ]
          {x | ENNReal.ofReal (M / δ) ≤ ENNReal.ofReal (q x)} := by
      filter_upwards [hF] with x hFx
      intro hx
      have hlt : Real.exp (-q x) < Real.exp (-M / δ) := by
        exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mp (hFx.trans_lt hx)
      have hqgt : M / δ < q x := by
        have hexp := Real.exp_lt_exp.mp hlt
        rw [neg_div] at hexp
        linarith
      exact ENNReal.ofReal_le_ofReal hqgt.le
    calc
      μ {x | F x < ENNReal.ofReal (Real.exp (-M / δ))}
          ≤ μ {x | ENNReal.ofReal (M / δ) ≤ ENNReal.ofReal (q x)} :=
        measure_mono_ae hsubset
      _ ≤ (∫⁻ x, ENNReal.ofReal (q x) ∂μ) / ENNReal.ofReal (M / δ) :=
        meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp hq).aemeasurable
          (ne_of_gt (ENNReal.ofReal_pos.mpr hthreshold)) ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M / ENNReal.ofReal (M / δ) := by gcongr
      _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_div_of_pos hthreshold]
        congr 1
        field_simp

/-- The photon-number second moment in Equation (92) bounds the mean
of one summand in Proposition 2 by `13 n nu^2`. -/
theorem photon_cost_mean_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : Ω → ℝ) (hk : Measurable k) (n ν : ℝ) (hn : 0 < n)
    (hmoment : (∫⁻ x, ENNReal.ofReal (k x ^ 2) ∂μ) ≤
      ENNReal.ofReal (12 * ν ^ 2 * n ^ 2)) :
    (∫⁻ x, ENNReal.ofReal (n * ν ^ 2 + k x ^ 2 / n) ∂μ) ≤
      ENNReal.ofReal (13 * n * ν ^ 2) := by
  have hbase : 0 ≤ n * ν ^ 2 := mul_nonneg hn.le (sq_nonneg ν)
  have hsplit (x : Ω) :
      ENNReal.ofReal (n * ν ^ 2 + k x ^ 2 / n) =
        ENNReal.ofReal (n * ν ^ 2) + ENNReal.ofReal (k x ^ 2) / ENNReal.ofReal n := by
    rw [ENNReal.ofReal_add hbase (div_nonneg (sq_nonneg _) hn.le),
      ENNReal.ofReal_div_of_pos hn]
  simp_rw [hsplit]
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const, measure_univ, mul_one]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const (μ := μ) (f := fun x => ENNReal.ofReal (k x ^ 2))
    ((ENNReal.ofReal n)⁻¹) (by fun_prop)]
  calc
    ENNReal.ofReal (n * ν ^ 2) +
        (∫⁻ x, ENNReal.ofReal (k x ^ 2) ∂μ) * (ENNReal.ofReal n)⁻¹
        ≤ ENNReal.ofReal (n * ν ^ 2) +
          ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) / ENNReal.ofReal n := by
      simp only [div_eq_mul_inv]
      gcongr
    _ = ENNReal.ofReal (13 * n * ν ^ 2) := by
      rw [← ENNReal.ofReal_div_of_pos hn,
        ← ENNReal.ofReal_add hbase (by positivity)]
      congr 1
      field_simp
      <;> ring

/-- Sum the photon-number costs over all copies. Independence of the
photon counts is not needed for this moment bound. -/
theorem total_photon_cost_mean_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (k : Fin N → Ω → ℝ) (hk : ∀ t, Measurable (k t))
    (n ν C ξ : ℝ) (hn : 0 < n) (hC : 0 ≤ C)
    (hmoment : ∀ t, (∫⁻ x, ENNReal.ofReal (k t x ^ 2) ∂μ) ≤
      ENNReal.ofReal (12 * ν ^ 2 * n ^ 2)) :
    (∫⁻ x, ENNReal.ofReal (C * ξ ^ 2 * ∑ t, (n * ν ^ 2 + k t x ^ 2 / n)) ∂μ) ≤
      ENNReal.ofReal (13 * C * (N : ℝ) * n * ν ^ 2 * ξ ^ 2) := by
  have hcoef : 0 ≤ C * ξ ^ 2 := mul_nonneg hC (sq_nonneg ξ)
  have hcost (t : Fin N) (x : Ω) : 0 ≤ n * ν ^ 2 + k t x ^ 2 / n := by positivity
  have hsplit (x : Ω) :
      ENNReal.ofReal (C * ξ ^ 2 * ∑ t, (n * ν ^ 2 + k t x ^ 2 / n)) =
        ENNReal.ofReal (C * ξ ^ 2) * ∑ t, ENNReal.ofReal (n * ν ^ 2 + k t x ^ 2 / n) := by
    rw [ENNReal.ofReal_mul hcoef]
    rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => hcost t x)]
  have hmeas (t : Fin N) : Measurable (fun x => ENNReal.ofReal (n * ν ^ 2 + k t x ^ 2 / n)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.add ((hk t).pow_const 2 |>.div_const n))
  simp_rw [hsplit]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun t _ => hmeas t)),
    lintegral_finsetSum _ (fun t _ => hmeas t)]
  calc
    ENNReal.ofReal (C * ξ ^ 2) *
        ∑ t, (∫⁻ x, ENNReal.ofReal (n * ν ^ 2 + k t x ^ 2 / n) ∂μ)
        ≤ ENNReal.ofReal (C * ξ ^ 2) * ∑ _t : Fin N, ENNReal.ofReal (13 * n * ν ^ 2) := by
      gcongr with t _
      exact photon_cost_mean_le μ (k t) (hk t) n ν hn (hmoment t)
    _ = ENNReal.ofReal (13 * C * (N : ℝ) * n * ν ^ 2 * ξ ^ 2) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        ← ENNReal.ofReal_mul hcoef]
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The probability-theoretic part of Proposition 3: Proposition 2's
pointwise likelihood estimate and Equation (92)'s photon moments imply
the high-probability averaged likelihood bound, with `C3 = 13 C2`.
No independence hypothesis on the photon counts is necessary. -/
theorem photon_likelihood_lower_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (k : Fin N → Ω → ℝ) (hk : ∀ t, Measurable (k t))
    (n ν C ξ δ : ℝ) (hn : 0 < n) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hmoment : ∀ t, (∫⁻ x, ENNReal.ofReal (k t x ^ 2) ∂μ) ≤
      ENNReal.ofReal (12 * ν ^ 2 * n ^ 2))
    (F : Ω → ℝ≥0∞)
    (hF : ∀ᵐ x ∂μ,
      ENNReal.ofReal (Real.exp (-(C * ξ ^ 2 * ∑ t, (n * ν ^ 2 + k t x ^ 2 / n)))) ≤ F x) :
    μ {x | F x < ENNReal.ofReal
      (Real.exp (-(13 * C * (N : ℝ) * n * ν ^ 2 * ξ ^ 2) / δ))} ≤
        ENNReal.ofReal δ := by
  apply exponential_lower_tail_of_lintegral μ
    (fun x => C * ξ ^ 2 * ∑ t, (n * ν ^ 2 + k t x ^ 2 / n)) F
  · exact measurable_const.mul
      (Finset.measurable_sum _ fun t _ => measurable_const.add ((hk t).pow_const 2 |>.div_const n))
  · intro x
    positivity
  · exact hF
  · positivity
  · exact hδ
  · exact total_photon_cost_mean_le μ N k hk n ν C ξ hn hC hmoment

/-- Scale a nonnegative mean bound by a nonnegative real coefficient. -/
theorem scaled_cost_mean_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : Ω → ℝ) (hq : Measurable q)
    (a M : ℝ) (ha : 0 ≤ a)
    (hmean : (∫⁻ x, ENNReal.ofReal (q x) ∂μ) ≤ ENNReal.ofReal M) :
    (∫⁻ x, ENNReal.ofReal (a * q x) ∂μ) ≤ ENNReal.ofReal (a * M) := by
  simp_rw [ENNReal.ofReal_mul ha]
  rw [lintegral_const_mul (μ := μ) (f := fun x => ENNReal.ofReal (q x))
    (ENNReal.ofReal a) (by fun_prop)]
  gcongr

/-- The likelihood-tail bound in cross-multiplied form. The density
`p` need only be positive and finite almost everywhere under `mu`. -/
theorem scaled_exponential_lower_tail_of_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : Ω → ℝ) (L p : Ω → ℝ≥0∞)
    (hq : Measurable q) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hp : ∀ᵐ x ∂μ, p x ≠ 0 ∧ p x ≠ ⊤)
    (hL : ∀ᵐ x ∂μ, ENNReal.ofReal (Real.exp (-q x)) * p x ≤ L x)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hmean : (∫⁻ x, ENNReal.ofReal (q x) ∂μ) ≤ ENNReal.ofReal M) :
    μ {x | L x < ENNReal.ofReal (Real.exp (-M / δ)) * p x} ≤ ENNReal.ofReal δ := by
  have hquot : ∀ᵐ x ∂μ, ENNReal.ofReal (Real.exp (-q x)) ≤ L x / p x := by
    filter_upwards [hp, hL] with x hpx hLx
    exact (ENNReal.le_div_iff_mul_le (Or.inl hpx.1) (Or.inl hpx.2)).mpr hLx
  have htail := exponential_lower_tail_of_lintegral μ q (fun x => L x / p x)
    hq hq_nonneg hquot M δ hM hδ hmean
  have hsubset :
      {x | L x < ENNReal.ofReal (Real.exp (-M / δ)) * p x} ≤ᵐ[μ]
        {x | L x / p x < ENNReal.ofReal (Real.exp (-M / δ))} := by
    filter_upwards [hp] with x hpx
    intro hx
    exact (lt_iff_lt_of_le_iff_le
      (ENNReal.le_div_iff_mul_le (Or.inl hpx.1) (Or.inl hpx.2))).mpr hx
  exact (measure_mono_ae hsubset).trans htail

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5AdaptiveLikelihood -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Proposition 2 yields an adaptive likelihood lower-tail estimate.
Its conclusion gives
the full dominated statistical model needed by Proposition 1.
The theorem includes `N=0` and arbitrary measurable outcome spaces. -/
theorem adaptive_likelihood_lower_tail :
    ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 →
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ (N : ℕ) (O : Type) [MeasurableSpace O] (S : AdaptiveScheme n N O),
      ∃ ref : Measure (Fin N → O), IsProbabilityMeasure ref ∧
      ∃ p : Herm0 n → (Fin N → O) → ℝ≥0∞,
        Measurable (Function.uncurry p) ∧
        (∀ X, IsProbabilityMeasure (ref.withDensity (p X))) ∧
        (∀ X, ∀ᵐ x ∂ref, p X x ≠ 0) ∧
        (∀ X ∈ Gsupp n,
          transcriptLaw S (fugacityCoeff (fugacityFamily ν ξ X)) = ref.withDensity (p X)) ∧
        ∀ X₀ ∈ Ggood n, ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
        ∀ δ : ℝ, 0 < δ →
          (ref.withDensity (p X₀)) {x |
            (∫⁻ Z, p (PhiMap X₀ ξ Z) x
              ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b))) <
            ENNReal.ofReal (Real.exp (-(C * (N : ℝ) * n * ν ^ 2 * ξ ^ 2) / δ)) * p X₀ x}
              ≤ ENNReal.ofReal δ := by
  obtain ⟨C₂, hC₂, ξ₀, hξ₀, hξ₀lt, hfixed⟩ := proposition_2
  refine ⟨13 * C₂, by positivity, ξ₀, hξ₀, hξ₀lt, ?_⟩
  intro n hn ν hνlo hνhi ξ hξlo hξhi N O _ S
  obtain ⟨ref, href, p, hp, hprob, hpos, hmodel, hcost⟩ :=
    adaptive_likelihood_model_proved n hn ν ξ C₂ hνlo hνhi hξlo (hξhi.trans_lt hξ₀lt) hC₂
      (hfixed n hn ν hνlo hνhi ξ hξlo hξhi) N O S
  refine ⟨ref, href, p, hp, hprob, hpos, hmodel, ?_⟩
  intro X₀ hX₀ b hbpos hbhi δ hδ
  obtain ⟨q, hq, hqnonneg, hmean, hL⟩ := hcost X₀ hX₀ b hbpos hbhi
  letI := hprob X₀
  have hpmeas : Measurable (p X₀) := hp.comp (measurable_const.prodMk measurable_id)
  have hcoefficient : 0 ≤ C₂ * ξ ^ 2 := mul_nonneg hC₂.le (sq_nonneg ξ)
  apply scaled_exponential_lower_tail_of_lintegral (ref.withDensity (p X₀))
    (fun x => C₂ * ξ ^ 2 * q x) _ (p X₀)
  · exact measurable_const.mul hq
  · intro x
    exact mul_nonneg hcoefficient (hqnonneg x)
  · exact density_ne_zero_ne_top_ae ref (p X₀) hpmeas
  · exact hL
  · positivity
  · exact hδ
  · have h := scaled_cost_mean_le (ref.withDensity (p X₀)) q hq
      (C₂ * ξ ^ 2) (13 * (N : ℝ) * n * ν ^ 2) hcoefficient hmean
    have heq : C₂ * ξ ^ 2 * (13 * (N : ℝ) * n * ν ^ 2) =
        13 * C₂ * (N : ℝ) * n * ν ^ 2 * ξ ^ 2 := by ring
    simpa only [heq] using h

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5PosteriorFromModel -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped MatrixOrder

namespace BosonicLearn.Prop5

theorem ofReal_exp_div (u v : ℝ) :
    ENNReal.ofReal (Real.exp (-u)) / ENNReal.ofReal (Real.exp (-v)) =
      ENNReal.ofReal (Real.exp (-u + v)) := by
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  congr 2
  ring

/-- Conditional restriction is always finite, including its zero-value
conventions when the conditioning event has zero or infinite mass. -/
theorem finite_cond {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (s : Set Θ) : IsFiniteMeasure (cond μ s) := by
  constructor
  calc
    (cond μ s) Set.univ = (μ s)⁻¹ * μ s := by
      simp [ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_apply_univ]
    _ ≤ 1 := ENNReal.inv_mul_le_one (μ s)
    _ < ⊤ := by norm_num

/-- Combine the two likelihood events for a fixed ground truth, using
the Bayesian density formula. This is the finite-parameter algebra of
Equations (94)--(95), before integrating over good ground truths. -/
theorem posterior_tail_at_of_density_model
    {n : ℕ} {T : Type} [MeasurableSpace T]
    [IsProbabilityMeasure (priorMu n)]
    (ref : Measure T) (p : Herm0 n → T → ℝ≥0∞)
    (hp : Measurable (Function.uncurry p))
    (hprob : ∀ X, IsProbabilityMeasure (ref.withDensity (p X)))
    (P : Kernel T (Herm0 n)) (X₀ : Herm0 n) (ξ a b c D δ : ℝ)
    (hnormal : ∀ᵐ x ∂ref,
      (∫⁻ X, p X x ∂priorMu n) ≠ 0 ∧ (∫⁻ X, p X x ∂priorMu n) ≠ ⊤)
    (hposterior : ∀ᵐ x ∂ref,
      P x = (∫⁻ X, p X x ∂priorMu n)⁻¹ • (priorMu n).withDensity (fun X => p X x))
    (hfirst : ENNReal.ofReal (1 - Real.exp (-(n : ℝ) ^ 2)) ≤
      (ref.withDensity (p X₀)) {x |
        (∫⁻ X in herm0Ball 1 X₀ (n * a), p X x ∂priorMu n) *
          (∫⁻ Z, p (PhiMap X₀ ξ Z) x
            ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) ≤
        ENNReal.ofReal (Real.exp (-(c * (n : ℝ) ^ 2))) * p X₀ x *
          (∫⁻ X in PhiMap X₀ ξ '' herm0Ball ⊤ 0 b, p X x ∂priorMu n)})
    (hlocal : (ref.withDensity (p X₀)) {x |
      (∫⁻ Z, p (PhiMap X₀ ξ Z) x
        ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) <
      ENNReal.ofReal (Real.exp (-D / δ)) * p X₀ x} ≤ ENNReal.ofReal δ) :
    (ref.withDensity (p X₀)) {x |
      ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2 + D / δ)) <
        P x (herm0Ball 1 X₀ (n * a))} ≤
      ENNReal.ofReal δ + ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2)) := by
  letI := hprob X₀
  let Q : Measure (Herm0 n) := cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)
  letI : IsFiniteMeasure Q := finite_cond _ _
  let B : T → ℝ≥0∞ := fun x => ∫⁻ X in herm0Ball 1 X₀ (n * a), p X x ∂priorMu n
  let R : T → ℝ≥0∞ := fun x => ∫⁻ X in PhiMap X₀ ξ '' herm0Ball ⊤ 0 b, p X x ∂priorMu n
  let L : T → ℝ≥0∞ := fun x => ∫⁻ Z, p (PhiMap X₀ ξ Z) x ∂Q
  let m : T → ℝ≥0∞ := fun x => ∫⁻ X, p X x ∂priorMu n
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(c * (n : ℝ) ^ 2)))
  let ell : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-D / δ))
  have hp₀ : Measurable (p X₀) := hp.comp (measurable_const.prodMk measurable_id)
  have hB : Measurable B := hp.lintegral_prod_left
  have hR : Measurable R := hp.lintegral_prod_left
  have hpPhi : Measurable (Function.uncurry (fun Z x => p (PhiMap X₀ ξ Z) x)) :=
    hp.comp (((measurable_PhiMap X₀ ξ).comp measurable_fst).prodMk measurable_snd)
  have hL : Measurable L := hpPhi.lintegral_prod_left
  have hmeasFirst : MeasurableSet {x | B x * L x ≤ e * p X₀ x * R x} :=
    measurableSet_le (hB.mul hL) ((measurable_const.mul hp₀).mul hR)
  have hfirstTail : (ref.withDensity (p X₀)) {x | e * p X₀ x * R x < B x * L x} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2)) := by
    have h := complement_le_of_ofReal_one_sub_le (ref.withDensity (p X₀))
      {x | B x * L x ≤ e * p X₀ x * R x} hmeasFirst
      (Real.exp (-(n : ℝ) ^ 2)) (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))) hfirst
    simpa only [Set.compl_ofPred, not_le] using h
  have hvalid : ∀ᵐ x ∂ref.withDensity (p X₀),
      p X₀ x ≠ 0 ∧ p X₀ x ≠ ⊤ ∧ m x ≠ 0 ∧ m x ≠ ⊤ ∧ R x ≤ m x := by
    filter_upwards [density_ne_zero_ne_top_ae ref (p X₀) hp₀,
      (withDensity_absolutelyContinuous ref (p X₀)).ae_le hnormal] with x hx hn
    exact ⟨hx.1, hx.2, hn.1, hn.2, setLIntegral_le_lintegral _ _⟩
  have htail := posterior_ratio_tail_of_likelihood_tails (ref.withDensity (p X₀))
    B L R m (p X₀) e ell (ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2))) (ENNReal.ofReal δ)
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top
    hvalid hfirstTail hlocal
  have hmass : ∀ᵐ x ∂ref.withDensity (p X₀),
      P x (herm0Ball 1 X₀ (n * a)) = B x / m x := by
    have hball : MeasurableSet (herm0Ball 1 X₀ (n * a)) :=
      Prop5Geometry.measurableSet_trace_ball X₀ (n * a)
    filter_upwards [(withDensity_absolutelyContinuous ref (p X₀)).ae_le hposterior] with x hx
    rw [hx, Measure.smul_apply, withDensity_apply _ hball]
    simp only [smul_eq_mul, div_eq_mul_inv]
    exact mul_comm _ _
  have hexp : e / ell = ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2 + D / δ)) := by
    dsimp [e, ell]
    rw [neg_div]
    convert ofReal_exp_div (c * (n : ℝ) ^ 2) (D / δ) using 1 <;> ring_nf
  calc
    (ref.withDensity (p X₀)) {x |
        ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2 + D / δ)) < P x (herm0Ball 1 X₀ (n * a))}
        = (ref.withDensity (p X₀)) {x | e / ell < B x / m x} := by
      apply measure_congr
      filter_upwards [hmass] with x hx
      change (_ < _) = (_ < _)
      rw [hx, hexp]
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2)) + ENNReal.ofReal δ := htail
    _ = ENNReal.ofReal δ + ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2)) := add_comm _ _

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5PosteriorDensity -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-- A dominated likelihood has a joint density even when the data space is arbitrary. -/
theorem swapped_joint_density {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (π : Measure Θ) (μ : Measure Ω) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (p : Θ → Ω → ℝ≥0∞) (hp : Measurable (Function.uncurry p))
    (K : Kernel Θ Ω) [IsMarkovKernel K]
    (hK : ∀ᵐ θ ∂π, K θ = μ.withDensity (p θ)) :
    (π ⊗ₘ K).map Prod.swap =
      (μ.prod π).withDensity (fun z : Ω × Θ => p z.2 z.1) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_swap]
  change (∫⁻ a, (f ∘ Prod.swap) a ∂π ⊗ₘ K) = _
  rw [Measure.lintegral_compProd (hf.comp measurable_swap)]
  calc ∫⁻ θ, ∫⁻ x, f (x, θ) ∂K θ ∂π =
      ∫⁻ θ, ∫⁻ x, p θ x * f (x, θ) ∂μ ∂π := by
        apply lintegral_congr_ae
        filter_upwards [hK] with θ hθ
        rw [hθ]
        exact lintegral_withDensity_eq_lintegral_mul μ
          (hp.of_uncurry_left) (hf.comp measurable_prodMk_right)
    _ = ∫⁻ x, ∫⁻ θ, p θ x * f (x, θ) ∂π ∂μ :=
      lintegral_lintegral_swap ((hp.mul (hf.comp measurable_swap)).aemeasurable)
    _ = ∫⁻ z, f z ∂(μ.prod π).withDensity (fun z : Ω × Θ => p z.2 z.1) := by
      symm
      calc
        _ = ∫⁻ z, p z.2 z.1 * f z ∂μ.prod π :=
          lintegral_withDensity_eq_lintegral_mul _ (hp.comp measurable_swap) hf
        _ = _ := lintegral_prod _ ((hp.comp measurable_swap).mul hf).aemeasurable

/-- The data marginal has density given by the prior average of its likelihood. -/
theorem posterior_marginal_density {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (π : Measure Θ) (μ : Measure Ω) (ρ : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (p : Θ → Ω → ℝ≥0∞) (hp : Measurable (Function.uncurry p))
    (K : Kernel Θ Ω) [IsMarkovKernel K] (P : Kernel Ω Θ) [IsMarkovKernel P]
    (hK : ∀ᵐ θ ∂π, K θ = μ.withDensity (p θ))
    (hjoint : (π ⊗ₘ K).map Prod.swap = ρ ⊗ₘ P) :
    ρ = μ.withDensity (fun x => ∫⁻ θ, p θ x ∂π) := by
  have hJ : ρ ⊗ₘ P = (μ.prod π).withDensity (fun z : Ω × Θ => p z.2 z.1) :=
    hjoint.symm.trans (swapped_joint_density π μ p hp K hK)
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    (∫⁻ x, f x ∂ρ) = (∫⁻ z : Ω × Θ, f z.1 ∂(ρ ⊗ₘ P)) := by
      simpa only [Function.comp_def, lintegral_const, measure_univ, mul_one] using
        (Measure.lintegral_compProd (μ := ρ) (κ := P) (hf.comp measurable_fst)).symm
    _ = (∫⁻ z, f z.1 ∂(μ.prod π).withDensity (fun z : Ω × Θ => p z.2 z.1)) := by
      rw [hJ]
    _ = (∫⁻ z : Ω × Θ, p z.2 z.1 * f z.1 ∂μ.prod π) :=
      lintegral_withDensity_eq_lintegral_mul _ (hp.comp measurable_swap)
        (hf.comp measurable_fst)
    _ = (∫⁻ x, ∫⁻ θ, p θ x * f x ∂π ∂μ) :=
      lintegral_prod _ ((hp.comp measurable_swap).mul (hf.comp measurable_fst)).aemeasurable
    _ = (∫⁻ x, (∫⁻ θ, p θ x ∂π) * f x ∂μ) := by
      apply lintegral_congr
      intro x
      exact lintegral_mul_const _ (hp.of_uncurry_right)
    _ = (∫⁻ x, f x ∂μ.withDensity (fun x => ∫⁻ θ, p θ x ∂π)) :=
      (lintegral_withDensity_eq_lintegral_mul _ hp.lintegral_prod_left hf).symm

/-- Strictly positive likelihoods make the evidence strictly positive almost everywhere. -/
theorem evidence_ne_zero_ae {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (π : Measure Θ) (μ : Measure Ω) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (p : Θ → Ω → ℝ≥0∞) (hp : Measurable (Function.uncurry p))
    (hpos : ∀ θ, ∀ᵐ x ∂μ, p θ x ≠ 0) :
    ∀ᵐ x ∂μ, (∫⁻ θ, p θ x ∂π) ≠ 0 := by
  have hswap : ∀ᵐ x ∂μ, ∀ᵐ θ ∂π, p θ x ≠ 0 :=
    (Measure.ae_ae_comm ((measurableSet_eq_fun hp measurable_const).compl)).mp (ae_of_all π hpos)
  filter_upwards [hswap] with x hx
  intro hz
  have hzero := (lintegral_eq_zero_iff hp.of_uncurry_right).mp hz
  obtain ⟨θ, hθz, hθn⟩ := (hzero.and hx).exists
  exact hθn hθz

/-- Bayes' density formula for arbitrary data spaces and countably generated parameter spaces.
The equality holds with respect to the reference data law, hence under each dominated likelihood. -/
theorem posterior_density_of_positive {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Θ]
    (π : Measure Θ) (μ : Measure Ω) (ρ : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (p : Θ → Ω → ℝ≥0∞) (hp : Measurable (Function.uncurry p))
    (K : Kernel Θ Ω) [IsMarkovKernel K] (P : Kernel Ω Θ) [IsMarkovKernel P]
    (hK : ∀ᵐ θ ∂π, K θ = μ.withDensity (p θ))
    (hjoint : (π ⊗ₘ K).map Prod.swap = ρ ⊗ₘ P)
    (hpos : ∀ θ, ∀ᵐ x ∂μ, p θ x ≠ 0) :
    ρ = μ.withDensity (fun x => ∫⁻ θ, p θ x ∂π) ∧ μ ≪ ρ ∧
      ∀ᵐ x ∂μ, (∫⁻ θ, p θ x ∂π) ≠ 0 ∧ (∫⁻ θ, p θ x ∂π) ≠ ∞ ∧
        P x = (∫⁻ θ, p θ x ∂π)⁻¹ • π.withDensity (fun θ => p θ x) := by
  classical
  let m : Ω → ℝ≥0∞ := fun x => ∫⁻ θ, p θ x ∂π
  have hm : Measurable m := hp.lintegral_prod_left
  have hρ : ρ = μ.withDensity m := posterior_marginal_density π μ ρ p hp K P hK hjoint
  have hm0 : ∀ᵐ x ∂μ, m x ≠ 0 := evidence_ne_zero_ae π μ p hp hpos
  have hmass : ∫⁻ x, m x ∂μ = 1 := by
    rw [← setLIntegral_univ, ← withDensity_apply m MeasurableSet.univ, ← hρ]
    simp
  have hmfin : ∀ᵐ x ∂μ, m x ≠ ∞ := (ae_lt_top hm (by rw [hmass]; exact ENNReal.one_ne_top)).mono
    fun x hx => hx.ne
  have hac : μ ≪ ρ := by
    rw [hρ]
    exact withDensity_absolutelyContinuous' hm.aemeasurable hm0
  let q : Ω → Θ → ℝ≥0∞ := fun x θ => if m x ≠ 0 ∧ m x ≠ ∞ then (m x)⁻¹ * p θ x else 1
  have hgood : MeasurableSet {x | m x ≠ 0 ∧ m x ≠ ∞} :=
    ((measurableSet_eq_fun hm measurable_const).compl).inter ((measurableSet_eq_fun hm measurable_const).compl)
  have hq : Measurable (Function.uncurry q) :=
    Measurable.ite (hgood.preimage measurable_fst)
      ((hm.comp measurable_fst).inv.mul (hp.comp measurable_swap)) measurable_const
  let Q : Kernel Ω Θ := (Kernel.const Ω π).withDensity q
  have hQprob : IsMarkovKernel Q := by
    constructor
    intro x
    apply IsProbabilityMeasure.mk
    rw [Kernel.withDensity_apply (Kernel.const Ω π) hq, Kernel.const_apply,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    by_cases hx : m x ≠ 0 ∧ m x ≠ ∞
    · simp only [q, if_pos hx]
      rw [lintegral_const_mul _ hp.of_uncurry_right]
      exact ENNReal.inv_mul_cancel hx.1 hx.2
    · simp [q, hx]
  have hQeq : ∀ x, m x ≠ 0 ∧ m x ≠ ∞ →
      Q x = (m x)⁻¹ • π.withDensity (fun θ => p θ x) := by
    intro x hx
    rw [Kernel.withDensity_apply (Kernel.const Ω π) hq, Kernel.const_apply]
    simp only [q, if_pos hx]
    exact withDensity_smul _ hp.of_uncurry_right
  have hJQ : ρ ⊗ₘ Q = (μ.prod π).withDensity (fun z : Ω × Θ => p z.2 z.1) := by
    change ρ ⊗ₘ (Kernel.const Ω π).withDensity q = _
    rw [Measure.compProd_withDensity hq, Measure.compProd_const, hρ,
      prod_withDensity_left hm]
    change ((μ.prod π).withDensity (m ∘ Prod.fst)).withDensity (Function.uncurry q) = _
    rw [← withDensity_mul _ (hm.comp measurable_fst) hq]
    apply withDensity_congr_ae
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      ((hm.comp measurable_fst).mul hq) (hp.comp measurable_swap))).mpr
    filter_upwards [hm0, hmfin] with x hx0 hxt
    exact ae_of_all π fun θ => by
      change m x * (if m x ≠ 0 ∧ m x ≠ ∞ then (m x)⁻¹ * p θ x else 1) = p θ x
      rw [if_pos (And.intro hx0 hxt)]
      rw [← mul_assoc, ENNReal.mul_inv_cancel hx0 hxt, one_mul]
  have hPQ : P =ᵐ[ρ] Q := Kernel.ae_eq_of_compProd_eq
    (hjoint.symm.trans (swapped_joint_density π μ p hp K hK) |>.trans hJQ.symm)
  refine ⟨hρ, hac, ?_⟩
  filter_upwards [hm0, hmfin, hac.ae_eq hPQ] with x hx0 hxt hxPQ
  exact ⟨hx0, hxt, hxPQ.trans (hQeq x ⟨hx0, hxt⟩)⟩

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5PosteriorReduction -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Quantitative Proposition 4, reduced to Propositions 1 and 2 and
the explicit adaptive likelihood-model bridge. No estimator or
learning-hardness statement is an input. -/
theorem posterior_tail_from_model :
    ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ n : ℕ, n₀ ≤ n →
      ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 →
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ N : ℕ,
      ∀ (O : Type) [MeasurableSpace O] (S : AdaptiveScheme n N O)
        (K : Kernel (Herm0 n) (Fin N → O)), IsMarkovKernel K →
        (∀ X ∈ Gsupp n,
          K X = transcriptLaw S (fugacityCoeff (fugacityFamily ν ξ X))) →
      ∀ (ρ : Measure (Fin N → O)), IsProbabilityMeasure ρ →
      ∀ (P : Kernel (Fin N → O) (Herm0 n)), IsMarkovKernel P →
        Measure.map Prod.swap (priorMu n ⊗ₘ K) = ρ ⊗ₘ P →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        (∫⁻ X₀ in Ggood n,
          K X₀ {x |
            ENNReal.ofReal (Real.exp
              (-c * (n : ℝ) ^ 2 + C * (N : ℝ) * n * ν ^ 2 * ξ ^ 2 / δ)) <
              P x (herm0Ball 1 X₀ (n * a))}
          ∂(priorMu n)) ≤
            ENNReal.ofReal δ + ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2)) := by
  obtain ⟨a₀, ha₀, c, hc, ξ₁, hξ₁, hξ₁lt, n₁, hratio⟩ :=
    proposition_1 (1 / 10) (by norm_num) le_rfl
  obtain ⟨C, hC, ξ₂, hξ₂, hξ₂lt, hmodelTail⟩ := adaptive_likelihood_lower_tail
  refine ⟨min ξ₁ ξ₂, lt_min hξ₁ hξ₂, (min_le_left _ _).trans_lt hξ₁lt,
    a₀, ha₀, c, hc, C, hC, max 1 n₁, le_max_left _ _, ?_⟩
  intro a ha ha₀ n hn ν hνlo hνhi ξ hξlo hξhi N O _ S K hK hKlaw ρ hρ P hP hbayes δ hδ hδhi
  have hnpos : 1 ≤ n := (le_max_left _ _).trans hn
  have hnratio : n₁ ≤ n := (le_max_right _ _).trans hn
  have hξratio : ξ ≤ ξ₁ := hξhi.trans (min_le_left _ _)
  have hξmodel : ξ ≤ ξ₂ := hξhi.trans (min_le_right _ _)
  obtain ⟨ref, href, p, hp, hprob, hpos, hphysical, hlocal⟩ :=
    hmodelTail n hnpos ν hνlo hνhi ξ hξlo hξmodel N O S
  letI := href
  letI := hρ
  letI := hK
  letI := hP
  obtain ⟨hprior, hsupp⟩ := priorMu_prob n
  letI := hprior
  letI : SecondCountableTopology (Herm0 n) :=
    @TopologicalSpace.Subtype.secondCountableTopology (Fin n → Fin n → ℂ) _
      (fun X => X ∈ Herm0 n) inferInstance
  have hKeq : ∀ᵐ X ∂priorMu n, K X = ref.withDensity (p X) :=
    hsupp.mono fun X hX => (hKlaw X hX).trans (hphysical X hX)
  obtain ⟨_, _, hposterior⟩ :=
    posterior_density_of_positive (priorMu n) ref ρ p hp K P hKeq hbayes hpos
  have hnormal : ∀ᵐ x ∂ref,
      (∫⁻ X, p X x ∂priorMu n) ≠ 0 ∧ (∫⁻ X, p X x ∂priorMu n) ≠ ⊤ :=
    hposterior.mono fun _ hx => ⟨hx.1, hx.2.1⟩
  have hidentity : ∀ᵐ x ∂ref,
      P x = (∫⁻ X, p X x ∂priorMu n)⁻¹ • (priorMu n).withDensity (fun X => p X x) :=
    hposterior.mono fun _ hx => hx.2.2
  have hpoint (X₀ : Herm0 n) (hX₀ : X₀ ∈ Ggood n) :
      K X₀ {x |
        ENNReal.ofReal (Real.exp
          (-c * (n : ℝ) ^ 2 + C * (N : ℝ) * n * ν ^ 2 * ξ ^ 2 / δ)) <
          P x (herm0Ball 1 X₀ (n * a))} ≤
        ENNReal.ofReal δ + ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2)) := by
    have hsupport : X₀ ∈ Gsupp n :=
      le_trans hX₀ (by norm_num : (3 : ℝ) ≤ 4)
    rw [hKlaw X₀ hsupport, hphysical X₀ hsupport]
    apply posterior_tail_at_of_density_model ref p hp hprob P X₀ ξ a (1 / 10) c
      (C * (N : ℝ) * n * ν ^ 2 * ξ ^ 2) δ hnormal hidentity
    · exact hratio a ha ha₀ n hnratio ξ hξlo hξratio X₀ hX₀ (Fin N → O) ref p hp hprob
    · exact hlocal X₀ hX₀ (1 / 10) (by norm_num) le_rfl δ hδ
  have hG : MeasurableSet (Ggood n) := by
    unfold Ggood WHMultiplicativity.schattenNorm
    have hc' : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) M :=
      LinearMap.continuous_of_finiteDimensional
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)
    exact (isClosed_le (hc'.comp continuous_subtype_val).norm continuous_const).measurableSet
  calc
    (∫⁻ X₀ in Ggood n,
        K X₀ {x | ENNReal.ofReal (Real.exp
          (-c * (n : ℝ) ^ 2 + C * (N : ℝ) * n * ν ^ 2 * ξ ^ 2 / δ)) <
            P x (herm0Ball 1 X₀ (n * a))} ∂priorMu n)
        ≤ ∫⁻ _X₀ in Ggood n,
          ENNReal.ofReal δ + ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2)) ∂priorMu n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hG] with X₀ hX₀
      exact hpoint X₀ hX₀
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2)) := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact mul_le_of_le_one_right' prob_le_one

end BosonicLearn.Prop5

end

/- Local helper source: Definitions.Def_BosonicLearn_tracelessGUE -/
section
open MeasureTheory

namespace BosonicLearn

/-- Unnormalized traceless-GUE density in the convention of Definition 6 and
Equation (32) of Chen--Mele--Mele--Preskill, arXiv:2609.26705. Its covariance
on the real Hilbert space of traceless Hermitian matrices is `2/n` times the
identity. The arbitrary normalization of additive Haar measure cancels below. -/
noncomputable def tracelessGUEWeight (n : ℕ) : Measure (Herm0 n) :=
  (Measure.addHaar : Measure (Herm0 n)).withDensity
    (fun X => ENNReal.ofReal (Real.exp (-(n / 4 : ℝ) *
      WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2)))

/-- The normalized, unconditioned traceless Gaussian unitary ensemble.
This is the law of `G - (Tr G/n) I` when `G` has diagonal variance `2/n`
and independent real/imaginary off-diagonal variances `1/n`.
The equivalence with independent coordinates is mathematical background;
this definition fixes the density directly. -/
noncomputable def tracelessGUE (n : ℕ) : Measure (Herm0 n) :=
  ProbabilityTheory.cond (tracelessGUEWeight n) Set.univ

end BosonicLearn

end

/- Local helper source: Solutions.Prop5Prior -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BosonicLearn.Prop5

/-- Conditioning on a superset of a good event cannot increase its failure probability. -/
theorem cond_superset_compl_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G S : Set Ω) (hG : MeasurableSet G) (hS : MeasurableSet S) (hGS : G ⊆ S) :
    ProbabilityTheory.cond μ S Gᶜ ≤ μ Gᶜ := by
  by_cases hzero : μ S = 0
  · rw [cond_eq_zero_of_meas_eq_zero hzero]
    simp
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ S) := cond_isProbabilityMeasure hzero
  rw [prob_compl_eq_one_sub hG, prob_compl_eq_one_sub hG]
  apply tsub_le_tsub_left
  rw [cond_apply hS, Set.inter_eq_right.mpr hGS]
  calc
    μ G = 1 * μ G := (one_mul _).symm
    _ ≤ (μ S)⁻¹ * μ G := mul_le_mul' (ENNReal.one_le_inv.mpr prob_le_one) le_rfl

/-- The same conditioning comparison for an arbitrary finite unnormalized law. -/
theorem cond_superset_compl_le_normalized {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (hfin : m Set.univ ≠ ⊤)
    (G S : Set Ω) (hG : MeasurableSet G) (hS : MeasurableSet S) (hGS : G ⊆ S) :
    ProbabilityTheory.cond m S Gᶜ ≤ ProbabilityTheory.cond m Set.univ Gᶜ := by
  by_cases hzero : m Set.univ = 0
  · have hm : m = 0 := Measure.measure_univ_eq_zero.mp hzero
    simp [hm, ProbabilityTheory.cond]
  have : IsProbabilityMeasure (ProbabilityTheory.cond m Set.univ) :=
    cond_isProbabilityMeasure_of_finite hzero hfin
  have h := cond_superset_compl_le (ProbabilityTheory.cond m Set.univ) G S hG hS hGS
  have heq : ProbabilityTheory.cond (ProbabilityTheory.cond m Set.univ) S = ProbabilityTheory.cond m S := by
    simpa using cond_cond_eq_cond_inter' MeasurableSet.univ hS hfin
  simpa only [heq] using h

/-- Local abbreviation for the reusable unconditioned Gaussian density. -/
noncomputable abbrev gueWeight (n : ℕ) : Measure (Herm0 n) := tracelessGUEWeight n

/-- The prior is exactly the traceless Gaussian density conditioned on `Gsupp`. -/
theorem priorMu_eq_cond_gueWeight (n : ℕ) :
    priorMu n = ProbabilityTheory.cond (gueWeight n) (Gsupp n) := by
  have hs : MeasurableSet (Gsupp n) := by
    have hc : Continuous fun X : Herm0 n =>
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
      apply Continuous.norm
      exact (LinearMap.continuous_of_finiteDimensional
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
          continuous_subtype_val
    simpa [Gsupp, WHMultiplicativity.schattenNorm] using
      measurableSet_le hc.measurable measurable_const
  unfold priorMu ProbabilityTheory.cond gueWeight tracelessGUEWeight
  dsimp only
  rw [← restrict_withDensity hs, Measure.restrict_apply_univ]

/-- The prior's bad-set mass is no larger than the unconditioned traceless-GUE
bad-set mass. No loss in the exponential rate is needed. -/
theorem prior_bad_le_gue_bad (n : ℕ) (hfin : gueWeight n Set.univ ≠ ⊤) :
    priorMu n (Ggood n)ᶜ ≤ ProbabilityTheory.cond (gueWeight n) Set.univ (Ggood n)ᶜ := by
  have hc : Continuous fun X : Herm0 n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
    apply Continuous.norm
    exact (LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
        continuous_subtype_val
  have hG : MeasurableSet (Ggood n) := by
    simpa [Ggood, WHMultiplicativity.schattenNorm] using
      measurableSet_le hc.measurable measurable_const
  have hS : MeasurableSet (Gsupp n) := by
    simpa [Gsupp, WHMultiplicativity.schattenNorm] using
      measurableSet_le hc.measurable measurable_const
  rw [priorMu_eq_cond_gueWeight]
  apply cond_superset_compl_le_normalized (gueWeight n) hfin (Ggood n) (Gsupp n) hG hS
  intro X hX
  exact le_trans hX (by norm_num : (3 : ℝ) ≤ 4)


/-- A radial Gaussian is integrable for any finite-dimensional real norm. -/
theorem integrable_exp_neg_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : Measure E) [m.IsAddHaarMeasure] (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : E => Real.exp (-b * ‖x‖ ^ 2)) m := by
  rcases subsingleton_or_nontrivial E with hsub | hnon
  · have : CompactSpace E := ⟨Set.finite_univ.isCompact⟩
    have : IsFiniteMeasure m := ⟨isCompact_univ.measure_lt_top⟩
    have hconst : (fun x : E => Real.exp (-b * ‖x‖ ^ 2)) = fun _ => (1 : ℝ) := by
      funext x
      rw [Subsingleton.elim x 0]
      simp
    rw [hconst]
    exact integrable_const 1
  · apply (integrable_fun_norm_addHaar m (f := fun r : ℝ => Real.exp (-b * r ^ 2))).mpr
    simpa only [smul_eq_mul, Real.rpow_natCast] using
      integrableOn_rpow_mul_exp_neg_mul_sq hb
        (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))


/-- Frobenius norm in the published Schatten convention. -/
theorem schatten_two_eq_sqrt (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 X = Real.sqrt (∑ i, ∑ j, ‖X j i‖ ^ 2) := by
  unfold WHMultiplicativity.schattenNorm
  rw [if_neg (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2]
  have hfun : (fun x : ℝ => x ^ ((2 : ℝ) / 2)) = fun x => x := by
    funext x
    rw [div_self (by norm_num), Real.rpow_one]
  rw [hfun, cfc_id' ℝ (X.conjTranspose * X)
    (by rw [← Matrix.star_eq_conjTranspose]; exact IsSelfAdjoint.star_mul_self X)]
  rw [Real.sqrt_eq_rpow]
  congr 1
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.conj_mul', ← Complex.ofReal_pow]


/-- The entrywise supremum norm is bounded by the Frobenius norm. -/
theorem norm_le_schatten_two (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖fun i j => X i j‖ ≤ WHMultiplicativity.schattenNorm 2 X := by
  rw [schatten_two_eq_sqrt]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro j
  have hs : (0 : ℝ) ≤ ∑ a, ∑ b, ‖X b a‖ ^ 2 := by positivity
  have h1 : ‖X i j‖ ^ 2 ≤ ∑ b, ‖X b j‖ ^ 2 :=
    Finset.single_le_sum (fun b _ => sq_nonneg (‖X b j‖)) (Finset.mem_univ i)
  have h2 : (∑ b, ‖X b j‖ ^ 2) ≤ ∑ a, ∑ b, ‖X b a‖ ^ 2 :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg (‖X b a‖))) (Finset.mem_univ j)
  nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ a, ∑ b, ‖X b a‖ ^ 2), norm_nonneg (X i j)]

/-- The unconditioned traceless-GUE density has finite mass. -/
theorem gueWeight_finite (n : ℕ) (hn : 0 < n) : gueWeight n Set.univ ≠ ⊤ := by
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → ℂ))
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → ℂ))
  have hi := integrable_exp_neg_norm_sq (Measure.addHaar : Measure (Herm0 n))
    (n / 4 : ℝ) (by positivity)
  let f : Herm0 n → ℝ := fun X => Real.exp (-(n / 4 : ℝ) *
    WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2)
  have hcont : Continuous f := by
    dsimp only [f]
    simp_rw [schatten_two_eq_sqrt]
    have he : ∀ i j : Fin n, Continuous (fun X : Herm0 n => (X : Matrix (Fin n) (Fin n) ℂ) i j) :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    apply Real.continuous_exp.comp
    apply Continuous.mul continuous_const
    apply Continuous.pow
    apply Real.continuous_sqrt.comp
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    exact (he j i).norm.pow 2
  have hint : Integrable f (Measure.addHaar : Measure (Herm0 n)) := by
    apply hi.mono' hcont.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro X
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hX := norm_le_schatten_two n (X : Matrix (Fin n) (Fin n) ℂ)
    have hF : 0 ≤ WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) := by
      rw [schatten_two_eq_sqrt]
      positivity
    have hb : (0 : ℝ) ≤ n / 4 := by positivity
    change ‖X‖ ≤ WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) at hX
    have hsq : ‖X‖ ^ 2 ≤ WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2 := by
      nlinarith [norm_nonneg X]
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left hsq hb)
  have hf : ∀ᵐ X ∂(Measure.addHaar : Measure (Herm0 n)), 0 ≤ f X :=
    Filter.Eventually.of_forall (fun X => (Real.exp_pos _).le)
  have hfin := (hasFiniteIntegral_iff_ofReal hf).mp hint.hasFiniteIntegral
  unfold gueWeight tracelessGUEWeight
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hfin.ne


/-- The Gaussian weight has positive mass in every dimension. -/
theorem gueWeight_pos (n : ℕ) : 0 < gueWeight n Set.univ := by
  let f : Herm0 n → ℝ≥0∞ := fun X => ENNReal.ofReal (Real.exp (-(n / 4 : ℝ) *
    WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2))
  have hf : Measurable f := by
    dsimp only [f]
    simp_rw [schatten_two_eq_sqrt]
    apply Continuous.measurable
    apply ENNReal.continuous_ofReal.comp
    apply Real.continuous_exp.comp
    apply Continuous.mul continuous_const
    apply Continuous.pow
    apply Real.continuous_sqrt.comp
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    have he : Continuous (fun X : Herm0 n => (X : Matrix (Fin n) (Fin n) ℂ) j i) :=
      (continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val)
    exact he.norm.pow 2
  have hpos : ∀ X, 0 < f X := fun X => ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hsupp : Function.support f = Set.univ := by
    ext X
    simp [Function.mem_support, (hpos X).ne']
  unfold gueWeight tracelessGUEWeight
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change 0 < ∫⁻ X, f X ∂(Measure.addHaar : Measure (Herm0 n))
  rw [lintegral_pos_iff_support hf, hsupp]
  exact isOpen_univ.measure_pos _ ⟨0, Set.mem_univ _⟩

/-- The normalized unconditioned density is a genuine probability law. -/
theorem gue_probability (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (ProbabilityTheory.cond (gueWeight n) Set.univ) :=
  cond_isProbabilityMeasure_of_finite (gueWeight_pos n).ne' (gueWeight_finite n hn)

/-- The conditioning bridge with normalization discharged. -/
theorem prior_bad_le_gue_bad_of_pos (n : ℕ) (hn : 0 < n) :
    priorMu n (Ggood n)ᶜ ≤ ProbabilityTheory.cond (gueWeight n) Set.univ (Ggood n)ᶜ :=
  prior_bad_le_gue_bad n (gueWeight_finite n hn)

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5GUEGeometry -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

section Rayleigh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The supremum of Rayleigh quotients, including zero. On a nonzero traceless
Hermitian operator this is its largest eigenvalue. -/
noncomputable def upperRayleigh (T : E →L[ℂ] E) : ℝ := ⨆ v, T.rayleighQuotient v

lemma bddAbove_rayleigh (T : E →L[ℂ] E) : BddAbove (Set.range T.rayleighQuotient) :=
  ⟨‖T‖, fun _ ⟨v, hv⟩ => hv ▸ (le_abs_self _).trans (T.rayleighQuotient_le_norm v)⟩

lemma rayleigh_le_upperRayleigh (T : E →L[ℂ] E) (v : E) :
    T.rayleighQuotient v ≤ upperRayleigh T := le_ciSup (bddAbove_rayleigh T) v

lemma upperRayleigh_nonneg (T : E →L[ℂ] E) : 0 ≤ upperRayleigh T := by
  simpa using rayleigh_le_upperRayleigh T 0

lemma upperRayleigh_le_norm (T : E →L[ℂ] E) : upperRayleigh T ≤ ‖T‖ := by
  apply ciSup_le
  intro v
  exact (le_abs_self _).trans (T.rayleighQuotient_le_norm v)

lemma upperRayleigh_le_add_norm_sub (T S : E →L[ℂ] E) :
    upperRayleigh T ≤ upperRayleigh S + ‖T - S‖ := by
  apply ciSup_le
  intro v
  have heq : T.rayleighQuotient v = S.rayleighQuotient v + (T - S).rayleighQuotient v := by
    rw [← ContinuousLinearMap.rayleighQuotient_add]
    congr 1
    abel
  rw [heq]
  exact add_le_add (rayleigh_le_upperRayleigh S v)
    ((le_abs_self _).trans ((T - S).rayleighQuotient_le_norm v))

/-- Rayleigh maxima are 1-Lipschitz for operator norm. -/
theorem upperRayleigh_lipschitz (T S : E →L[ℂ] E) :
    |upperRayleigh T - upperRayleigh S| ≤ ‖T - S‖ := by
  have h1 := upperRayleigh_le_add_norm_sub T S
  have h2 := upperRayleigh_le_add_norm_sub S T
  rw [norm_sub_rev S T] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Both signs of the Rayleigh maximum control a self-adjoint operator norm. -/
theorem norm_le_max_upperRayleigh (T : E →L[ℂ] E) (hT : T.IsSymmetric) :
    ‖T‖ ≤ max (upperRayleigh T) (upperRayleigh (-T)) := by
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro v
  have h1 := rayleigh_le_upperRayleigh T v
  have h2 := rayleigh_le_upperRayleigh (-T) v
  rw [ContinuousLinearMap.rayleighQuotient_neg_apply] at h2
  exact abs_le.mpr ⟨by linarith [le_max_right (upperRayleigh T) (upperRayleigh (-T))],
    h1.trans (le_max_left _ _)⟩

end Rayleigh


open scoped Matrix.Norms.Frobenius in
/-- The published Schatten 2-norm agrees with the matrix Frobenius norm. -/
theorem schatten_two_eq_frobenius (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 X = ‖X‖ := by
  rw [schatten_two_eq_sqrt, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  rw [Finset.sum_comm]
  simp only [Real.rpow_two]

open scoped Matrix.Norms.Frobenius in
/-- Euclidean operator norm is bounded by the Frobenius norm. -/
theorem operator_norm_le_schatten_two (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ ≤ WHMultiplicativity.schattenNorm 2 X := by
  rw [schatten_two_eq_frobenius]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X)
  intro v
  have h := Matrix.frobenius_norm_mul X (Matrix.replicateCol Unit (WithLp.ofLp v))
  rw [← Matrix.replicateCol_mulVec, Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol] at h
  exact h

/-- The largest Rayleigh quotient is 1-Lipschitz in the Frobenius metric. -/
theorem matrix_upperRayleigh_lipschitz (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    |upperRayleigh (Matrix.toEuclideanCLM (𝕜 := ℂ) X) -
      upperRayleigh (Matrix.toEuclideanCLM (𝕜 := ℂ) Y)| ≤
      WHMultiplicativity.schattenNorm 2 (X - Y) := by
  refine (upperRayleigh_lipschitz _ _).trans ?_
  rw [← map_sub]
  exact operator_norm_le_schatten_two n (X - Y)

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5GUEMax -/
section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-- Finite maxima preserve integrability. -/
lemma integrable_finset_sup' {Ω T : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : T → Ω → ℝ) (hX : ∀ t, Integrable (X t) μ)
    (s : Finset T) (hs : s.Nonempty) :
    Integrable (fun ω => s.sup' hs (fun t => X t ω)) μ := by
  have h := Finset.sup'_induction hs X (p := fun f => Integrable f μ)
    (fun _ ha _ hb => ha.sup hb) (fun t _ => hX t)
  convert h using 1
  funext ω
  exact (Finset.sup'_apply hs X ω).symm

/-- On a separable parameter space, a continuous process dominated by an integrable
function has its ordinary expected supremum below the finite-marginal expected supremum.
This supplies the analytic bridge needed to apply abstract Gaussian comparison to Rayleigh maxima. -/
theorem integral_iSup_le_processESup {Ω T : Type} [MeasurableSpace Ω]
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    (μ : Measure Ω) (X : T → Ω → ℝ)
    (hX : ∀ t, AEStronglyMeasurable (X t) μ)
    (hcont : ∀ ω, Continuous (fun t => X t ω))
    (g : Ω → ℝ) (hg : Integrable g μ) (hbound : ∀ t ω, ‖X t ω‖ ≤ g ω) :
    ((∫ ω, (⨆ t, X t ω) ∂μ : ℝ) : EReal) ≤
      HighDimProb.RandomProcesses.processESup μ X := by
  classical
  let d : ℕ → T := TopologicalSpace.denseSeq T
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq T
  let s : ℕ → Finset T := fun n => (Finset.range (n+1)).image d
  have hs : ∀ n, (s n).Nonempty := fun n =>
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)).image d
  let f : ℕ → Ω → ℝ := fun n ω => (s n).sup' (hs n) (fun t => X t ω)
  have hi : ∀ t, Integrable (X t) μ := fun t => hg.mono' (hX t) (ae_of_all μ (hbound t))
  have hfi : ∀ n, Integrable (f n) μ := fun n => integrable_finset_sup' μ X hi (s n) (hs n)
  have hfb : ∀ n ω, ‖f n ω‖ ≤ g ω := by
    intro n ω
    obtain ⟨t, _, ht⟩ := Finset.exists_mem_eq_sup' (hs n) (fun t => X t ω)
    change ‖(s n).sup' (hs n) (fun t => X t ω)‖ ≤ g ω
    rw [ht]
    exact hbound t ω
  have hmono : ∀ ω, Monotone (fun n => f n ω) := by
    intro ω n m hnm
    exact Finset.sup'_mono _ (Finset.image_subset_image
      (Finset.range_mono (Nat.add_le_add_right hnm 1))) (hs n)
  have hb : ∀ ω, BddAbove (Set.range (fun n => f n ω)) := fun ω =>
    ⟨g ω, fun _ ⟨n, hn⟩ => hn ▸ (le_abs_self _).trans (hfb n ω)⟩
  have hBX : ∀ ω, BddAbove (Set.range (fun t => X t ω)) := fun ω =>
    ⟨g ω, fun _ ⟨t, ht⟩ => ht ▸ (le_abs_self _).trans (hbound t ω)⟩
  have heq : ∀ ω, (⨆ n, f n ω) = ⨆ t, X t ω := by
    intro ω
    apply le_antisymm
    · apply ciSup_le
      intro n
      exact Finset.sup'_le (hs n) _ (fun t _ => le_ciSup (hBX ω) t)
    · apply ciSup_le
      intro t
      refine hd.induction_on (p := fun t => X t ω ≤ ⨆ n, f n ω) t
        (isClosed_le (hcont ω) continuous_const) ?_
      intro k
      apply (Finset.le_sup' (fun t => X t ω) ?_).trans (le_ciSup (hb ω) k)
      exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩
  have hlim : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (⨆ t, X t ω)) := by
    intro ω
    rw [← heq ω]
    exact tendsto_atTop_ciSup (hmono ω) (hb ω)
  have hiLim := tendsto_integral_of_dominated_convergence g
    (fun n => (hfi n).aestronglyMeasurable) hg (fun n => ae_of_all μ (hfb n))
    (ae_of_all μ hlim)
  apply le_of_tendsto' ((continuous_coe_real_ereal.tendsto _).comp hiLim)
  intro n
  exact le_iSup (fun s : {s : Finset T // s.Nonempty} =>
    ((∫ ω, s.1.sup' s.2 (fun t => X t ω) ∂μ : ℝ) : EReal)) ⟨s n, hs n⟩

/-- Any integrable envelope bounds the finite-marginal expected supremum. -/
theorem processESup_le_integral {Ω T : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : T → Ω → ℝ) (hX : ∀ t, Integrable (X t) μ)
    (g : Ω → ℝ) (hg : Integrable g μ) (hbound : ∀ t ω, X t ω ≤ g ω) :
    HighDimProb.RandomProcesses.processESup μ X ≤ ((∫ ω, g ω ∂μ : ℝ) : EReal) := by
  apply iSup_le
  intro s
  apply EReal.coe_le_coe_iff.mpr
  apply integral_mono (integrable_finset_sup' μ X hX s.1 s.2) hg
  intro ω
  exact Finset.sup'_le s.2 _ (fun t _ => hbound t ω)

/-- A directly usable version of Sudakov--Fernique for continuous processes.
It controls the usual real expected maximum by an integrable comparison envelope. -/
theorem expected_sup_le_of_gaussian_comparison {Ω T : Type} [MeasurableSpace Ω]
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : T → Ω → ℝ)
    (hXG : IsGaussianProcess X μ) (hYG : IsGaussianProcess Y μ)
    (hXmean : ∀ t, ∫ ω, X t ω ∂μ = 0) (hYmean : ∀ t, ∫ ω, Y t ω ∂μ = 0)
    (hinc : ∀ t s, ∫ ω, (X t ω - X s ω)^2 ∂μ ≤ ∫ ω, (Y t ω - Y s ω)^2 ∂μ)
    (hX : ∀ t, AEStronglyMeasurable (X t) μ)
    (hcont : ∀ ω, Continuous (fun t => X t ω))
    (gX : Ω → ℝ) (hgX : Integrable gX μ) (hbX : ∀ t ω, ‖X t ω‖ ≤ gX ω)
    (hY : ∀ t, Integrable (Y t) μ)
    (gY : Ω → ℝ) (hgY : Integrable gY μ) (hbY : ∀ t ω, Y t ω ≤ gY ω) :
    (∫ ω, (⨆ t, X t ω) ∂μ) ≤ ∫ ω, gY ω ∂μ := by
  apply EReal.coe_le_coe_iff.mp
  exact (integral_iSup_le_processESup μ X hX hcont gX hgX hbX).trans
    ((HighDimProb.RandomProcesses.sudakov_fernique μ X Y hXG hYG hXmean hYmean hinc).trans
      (processESup_le_integral μ Y hY gY hgY hbY))

section RayleighIndex
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Unit vectors together with a distinguished zero vector. This compact index space
represents the nonnegative Rayleigh maximum, including the zero-dimensional case. -/
abbrev RayleighIndex (E : Type) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1 ⊕ Unit

/-- The Rayleigh process on unit vectors, extended by zero at its distinguished point. -/
def indexedRayleigh (T : E →L[ℂ] E) : RayleighIndex E → ℝ :=
  Sum.elim (fun v => T.rayleighQuotient v) (fun _ => 0)

lemma indexedRayleigh_norm_le (T : E →L[ℂ] E) (v : RayleighIndex E) :
    ‖indexedRayleigh T v‖ ≤ ‖T‖ := by
  cases v with
  | inl v => exact T.rayleighQuotient_le_norm v
  | inr v => simp [indexedRayleigh]

lemma continuous_indexedRayleigh (T : E →L[ℂ] E) : Continuous (indexedRayleigh T) := by
  apply continuous_sum_dom.mpr
  constructor
  · have heq : (indexedRayleigh T ∘ Sum.inl) =
        fun v : Metric.sphere (0 : E) 1 => T.reApplyInnerSelf v := by
      funext v
      simp [indexedRayleigh, ContinuousLinearMap.rayleighQuotient]
    rw [heq]
    exact T.reApplyInnerSelf_continuous.comp continuous_subtype_val
  · exact continuous_const

lemma iSup_indexedRayleigh (T : E →L[ℂ] E) :
    (⨆ v : RayleighIndex E, indexedRayleigh T v) = upperRayleigh T := by
  have hb : BddAbove (Set.range (indexedRayleigh T)) :=
    ⟨‖T‖, fun _ ⟨v, hv⟩ => hv ▸ (le_abs_self _).trans (indexedRayleigh_norm_le T v)⟩
  apply le_antisymm
  · apply ciSup_le
    intro v
    cases v with
    | inl v => exact rayleigh_le_upperRayleigh T v
    | inr v => exact upperRayleigh_nonneg T
  · apply ciSup_le
    intro v
    by_cases hv : v = 0
    · simpa [hv, indexedRayleigh] using le_ciSup hb (Sum.inr ())
    · have hmem : T.rayleighQuotient v ∈ T.rayleighQuotient '' ({0}ᶜ : Set E) :=
        ⟨v, hv, rfl⟩
      rw [T.image_rayleigh_eq_image_rayleigh_sphere (show (0 : ℝ) < 1 by norm_num)] at hmem
      obtain ⟨w, hw, heq⟩ := hmem
      simpa [indexedRayleigh, heq] using le_ciSup hb (Sum.inl ⟨w, hw⟩)

lemma continuous_rayleigh_at (v : E) :
    Continuous (fun T : E →L[ℂ] E => T.rayleighQuotient v) := by
  have h : Continuous (fun T : E →L[ℂ] E => T v) := continuous_id.clm_apply continuous_const
  exact (RCLike.continuous_re.comp (h.inner continuous_const)).div_const _

/-- The operator maximum can be bounded using Gaussian comparison on the unit sphere
with its distinguished zero vector. Only an integrable operator-norm envelope is needed. -/
theorem expected_upperRayleigh_le_of_comparison {Ω : Type} [MeasurableSpace Ω]
    [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → E →L[ℂ] E)
    (Y : RayleighIndex E → Ω → ℝ)
    (hXG : IsGaussianProcess (fun v ω => indexedRayleigh (T ω) v) μ)
    (hYG : IsGaussianProcess Y μ)
    (hXm : ∀ v, ∫ ω, indexedRayleigh (T ω) v ∂μ = 0)
    (hYm : ∀ v, ∫ ω, Y v ω ∂μ = 0)
    (hinc : ∀ v w, ∫ ω, (indexedRayleigh (T ω) v - indexedRayleigh (T ω) w)^2 ∂μ ≤
      ∫ ω, (Y v ω - Y w ω)^2 ∂μ)
    (hT : Integrable (fun ω => ‖T ω‖) μ)
    (g : Ω → ℝ) (hg : Integrable g μ) (hYb : ∀ v ω, Y v ω ≤ g ω) :
    (∫ ω, upperRayleigh (T ω) ∂μ) ≤ ∫ ω, g ω ∂μ := by
  simpa only [iSup_indexedRayleigh] using expected_sup_le_of_gaussian_comparison μ
    (fun v ω => indexedRayleigh (T ω) v) Y hXG hYG hXm hYm hinc
    (fun v => (hXG.hasGaussianLaw_eval v).integrable.aestronglyMeasurable)
    (fun ω => continuous_indexedRayleigh (T ω))
    (fun ω => ‖T ω‖) hT (fun v ω => indexedRayleigh_norm_le (T ω) v)
    (fun v => (hYG.hasGaussianLaw_eval v).integrable) g hg hYb

/-- The linear comparison process used for the complex Gaussian Rayleigh process. -/
def indexedLinearComparison (c : ℝ) (g : E) : RayleighIndex E → ℝ :=
  Sum.elim (fun v => c * (inner ℂ g (v : E)).re) (fun _ => 0)

lemma indexedLinearComparison_le (c : ℝ) (hc : 0 ≤ c) (g : E) (v : RayleighIndex E) :
    indexedLinearComparison c g v ≤ c * ‖g‖ := by
  cases v with
  | inl v =>
      apply mul_le_mul_of_nonneg_left _ hc
      calc
        (inner ℂ g (v : E)).re ≤ ‖inner ℂ g (v : E)‖ := Complex.re_le_norm _
        _ ≤ ‖g‖ * ‖(v : E)‖ := norm_inner_le_norm _ _
        _ = ‖g‖ := by rw [norm_eq_of_mem_sphere v, mul_one]
  | inr v => exact mul_nonneg hc (norm_nonneg g)

end RayleighIndex

/-- The elementary second-moment bound for a real mean. -/
theorem integral_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    (∫ ω, f ω ∂μ) ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  have hv := variance_nonneg f μ
  rw [variance_eq_sub hf] at hv
  have hsecond : 0 ≤ ∫ ω, (f ω)^2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  have hsq := Real.sq_sqrt hsecond
  have hn := Real.sqrt_nonneg (∫ ω, (f ω)^2 ∂μ)
  simp only [Pi.pow_apply] at hv
  nlinarith

/-- The linear comparison envelope has mean at most `2√2` when its complex Gaussian
vector has total second moment at most `2n`. -/
theorem comparison_envelope_mean_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (Z : Ω → E)
    (hZ : MemLp (fun ω => ‖Z ω‖) 2 μ)
    (hsecond : (∫ ω, ‖Z ω‖^2 ∂μ) ≤ 2 * n) :
    (∫ ω, (2 / Real.sqrt n) * ‖Z ω‖ ∂μ) ≤ 2 * Real.sqrt 2 := by
  rw [integral_const_mul]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  calc
    (2 / Real.sqrt n) * (∫ ω, ‖Z ω‖ ∂μ) ≤
        (2 / Real.sqrt n) * Real.sqrt (2 * n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (integral_le_sqrt_integral_sq μ _ hZ).trans (Real.sqrt_le_sqrt hsecond)
    _ = 2 * Real.sqrt 2 := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp



section Projector
variable {ι : Type*} [Fintype ι]

/-- The rank-one projector encoded as a Euclidean vector of matrix entries. -/
def projectorVector (u : EuclideanSpace ℂ ι) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 (fun ij => u ij.1 * star (u ij.2))

lemma inner_projectorVector (u v : EuclideanSpace ℂ ι) :
    inner ℂ (projectorVector u) (projectorVector v) =
      inner ℂ u v * star (inner ℂ u v) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, projectorVector,
    starRingEnd_apply, star_mul, star_star, star_sum]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma real_inner_projectorVector (u v : EuclideanSpace ℂ ι) :
    (inner ℂ (projectorVector u) (projectorVector v)).re = ‖inner ℂ u v‖^2 := by
  rw [inner_projectorVector, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma norm_projectorVector_sq (u : EuclideanSpace ℂ ι) :
    ‖projectorVector u‖^2 = ‖u‖^4 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  change (inner ℂ (projectorVector u) (projectorVector u)).re = _
  rw [real_inner_projectorVector, inner_self_eq_norm_sq_to_K]
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm]
  ring

lemma projectorVector_dist_sq (u v : EuclideanSpace ℂ ι)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖projectorVector u - projectorVector v‖^2 = 2 * (1 - ‖inner ℂ u v‖^2) := by
  rw [norm_sub_sq (𝕜 := ℂ), norm_projectorVector_sq, norm_projectorVector_sq,
    ]
  change ‖u‖^4 - 2 * (inner ℂ (projectorVector u) (projectorVector v)).re + ‖v‖^4 = _
  rw [real_inner_projectorVector, hu, hv]
  ring

lemma unit_projector_increment_bound (u v : EuclideanSpace ℂ ι)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖projectorVector u - projectorVector v‖^2 ≤ 2 * ‖u-v‖^2 := by
  rw [projectorVector_dist_sq u v hu hv, norm_sub_sq (𝕜 := ℂ), hu, hv]
  have hre : (inner ℂ u v).re^2 ≤ ‖inner ℂ u v‖^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg (inner ℂ u v).im]
  change 2 * (1 - ‖inner ℂ u v‖^2) ≤
    2 * (1^2 - 2 * (inner ℂ u v).re + 1^2)
  nlinarith [sq_nonneg (1 - (inner ℂ u v).re)]

/-- Matrix entries as a Euclidean vector; its norm is the Frobenius norm. -/
def matrixVector (A : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

lemma inner_projector_matrixVector [DecidableEq ι] (A : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    inner ℂ (projectorVector v) (matrixVector A) =
      inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) A v) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, projectorVector, matrixVector,
    starRingEnd_apply, star_mul, star_star, Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma rayleigh_unit_eq_real_inner_projector [DecidableEq ι]
    (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) A).rayleighQuotient v =
      (inner ℂ (projectorVector v) (matrixVector A)).re := by
  rw [inner_projector_matrixVector, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, hv, one_pow, div_one]
  exact inner_re_symm (𝕜 := ℂ) _ _

lemma norm_matrixVector (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖matrixVector A‖ = WHMultiplicativity.schattenNorm 2 A := by
  rw [schatten_two_eq_sqrt, ← Real.sqrt_sq (norm_nonneg (matrixVector A)),
    EuclideanSpace.norm_sq_eq]
  congr 1
  simp only [matrixVector, WithLp.ofLp_toLp, Fintype.sum_prod_type]
  exact Finset.sum_comm

end Projector

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5GaussianDensity -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace BosonicLearn.Prop5

/-- An integrable product density is the density of the product measures. -/
theorem pi_withDensity_ofReal {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (hn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod_dep (fun i => (hf i).restrict))
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => hn i (x i))))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg (hn i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hn i))

/-- Transporting a density through a measurable equivalence composes it with the inverse. -/
theorem map_withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (e : E ≃ᵐ F) (f : E → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator hs]
  rw [lintegral_map (show Measurable (s.indicator (fun y => f (e.symm y))) from
    (hf.comp e.symm.measurable).indicator hs) e.measurable]
  rw [← lintegral_indicator (e.measurable hs)]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ s <;> simp [Set.indicator, hx]

/-- Independent real Gaussian coordinates have the product of their scalar densities. -/
theorem pi_gaussian_density {ι : Type*} [Fintype ι] (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : ι => gaussianReal 0 v) =
      (volume : Measure (ι → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 v (x i))) := by
  simp_rw [gaussianReal_of_var_ne_zero _ hv]
  exact pi_withDensity_ofReal (fun _ => volume) (fun _ => gaussianPDFReal 0 v)
    (fun _ => integrable_gaussianPDFReal 0 v) (fun _ => gaussianPDFReal_nonneg 0 v)

theorem prod_gaussianPDFReal {ι : Type*} [Fintype ι] (v : ℝ≥0) (x : ι → ℝ) :
    (∏ i, gaussianPDFReal 0 v (x i)) =
      (Real.sqrt (2 * Real.pi * v))⁻¹ ^ Fintype.card ι *
        Real.exp (-(∑ i, x i ^ 2) / (2 * v)) := by
  simp only [gaussianPDFReal, sub_zero, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← Real.exp_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib]

/-- A nonzero finite constant multiplying a measure does not change its normalization. -/
theorem cond_smul_univ {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    ProbabilityTheory.cond (c • μ) Set.univ = ProbabilityTheory.cond μ Set.univ := by
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply,
    smul_eq_mul, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm c⁻¹,
    ENNReal.inv_mul_cancel_right hc0 hct]

theorem map_cond_univ {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (f : E → F) (hf : Measurable f) :
    (ProbabilityTheory.cond μ Set.univ).map f =
      ProbabilityTheory.cond (μ.map f) Set.univ := by
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.map_smul,
    Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]

/-- A product of centered real Gaussians is the normalized radial Gaussian density. -/
theorem pi_gaussian_eq_cond_radial {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : ι => gaussianReal 0 v) =
      ProbabilityTheory.cond
        ((volume : Measure (ι → ℝ)).withDensity
          (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v))))) Set.univ := by
  let c : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ ^ Fintype.card ι
  have hc : 0 < c := by
    dsimp [c]
    apply pow_pos
    apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))
  have heq : Measure.pi (fun _ : ι => gaussianReal 0 v) =
      ENNReal.ofReal c • (volume : Measure (ι → ℝ)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v)))) := by
    rw [pi_gaussian_density v hv]
    simp_rw [prod_gaussianPDFReal]
    change (volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (c * Real.exp (-(∑ i, x i ^ 2) / (2 * v)))) = _
    simp_rw [ENNReal.ofReal_mul hc.le]
    exact withDensity_smul _ (by fun_prop)
  calc
    _ = ProbabilityTheory.cond (Measure.pi (fun _ : ι => gaussianReal 0 v)) Set.univ :=
      (ProbabilityTheory.cond_univ _).symm
    _ = _ := by
      rw [heq]
      exact cond_smul_univ _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top

/-- Normalizing a density makes it independent of the normalization of additive Haar measure. -/
theorem cond_withDensity_haar_eq {E : Type*} [AddCommGroup E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [LocallyCompactSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] (f : E → ℝ≥0∞) :
    ProbabilityTheory.cond (μ.withDensity f) Set.univ =
      ProbabilityTheory.cond (ν.withDensity f) Set.univ := by
  have heq : μ = (Measure.addHaarScalarFactor μ ν : ℝ≥0∞) • ν :=
    Measure.isAddLeftInvariant_eq_smul μ ν
  rw [heq, withDensity_smul_measure]
  exact cond_smul_univ _ _
    (by exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne')
    ENNReal.coe_ne_top

/-- A quadratic form represented by orthonormal real coordinates has its expected Gaussian
density with respect to any additive Haar measure. No determinant normalization is needed. -/
theorem map_pi_gaussian_eq_cond_quadratic {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyCompactSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : (ι → ℝ) ≃L[ℝ] E)
    (Q : E → ℝ) (he : ∀ x, Q (e x) = ∑ i, x i ^ 2)
    (v : ℝ≥0) (hv : v ≠ 0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)).map e =
      ProbabilityTheory.cond (μ.withDensity
        (fun y => ENNReal.ofReal (Real.exp (-Q y / (2 * v))))) Set.univ := by
  rw [pi_gaussian_eq_cond_radial v hv, map_cond_univ _ _ e.continuous.measurable]
  let em := e.toHomeomorph.toMeasurableEquiv
  have hmap := map_withDensity_equiv (volume : Measure (ι → ℝ)) em
    (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v)))) (by fun_prop)
  change (Measure.map e ((volume : Measure (ι → ℝ)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v)))))) =
      (Measure.map e volume).withDensity
        (fun y => ENNReal.ofReal (Real.exp (-(∑ i, (e.symm y) i ^ 2) / (2 * v)))) at hmap
  rw [hmap]
  have he' : ∀ y, (∑ i, (e.symm y) i ^ 2) = Q y := by
    intro y
    simpa only [e.apply_symm_apply] using (he (e.symm y)).symm
  simp_rw [he']
  exact cond_withDensity_haar_eq _ μ _

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5GUECoordinates -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace BosonicLearn.Prop5

noncomputable section

/-- Flattening matrix entries gives the usual Frobenius Hilbert space. -/
def frobeniusMatrixEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] EuclideanSpace ℂ (Fin n × Fin n) where
  toFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  invFun x := fun i j => x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := (PiLp.continuous_toLp _ _).comp (by fun_prop)
  continuous_invFun := by fun_prop

def FrobHerm0 (n : ℕ) : Submodule ℝ (EuclideanSpace ℂ (Fin n × Fin n)) :=
  (Herm0 n).map (frobeniusMatrixEquiv n).toLinearMap

def frobeniusHerm0Equiv (n : ℕ) : Herm0 n ≃L[ℝ] FrobHerm0 n :=
  (frobeniusMatrixEquiv n).submoduleMap (Herm0 n)

theorem norm_frobeniusMatrixEquiv (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖frobeniusMatrixEquiv n A‖ = WHMultiplicativity.schattenNorm 2 A := by
  rw [schatten_two_eq_sqrt, ← Real.sqrt_sq (norm_nonneg (frobeniusMatrixEquiv n A)),
    EuclideanSpace.norm_sq_eq]
  congr 1
  change (∑ ij : Fin n × Fin n, ‖A ij.1 ij.2‖ ^ 2) = _
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Orthonormal real coordinates of the traceless Hermitian Frobenius space. -/
noncomputable def gueCoordinates (n : ℕ) :
    (Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) ≃L[ℝ] Herm0 n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => ℝ)).symm.trans
    ((stdOrthonormalBasis ℝ (FrobHerm0 n)).repr.symm.toContinuousLinearEquiv.trans
      (frobeniusHerm0Equiv n).symm)

theorem schatten_two_gueCoordinates (n : ℕ)
    (x : Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) :
    WHMultiplicativity.schattenNorm 2
      (gueCoordinates n x : Matrix (Fin n) (Fin n) ℂ) ^ 2 = ∑ i, x i ^ 2 := by
  rw [← norm_frobeniusMatrixEquiv]
  change ‖((frobeniusHerm0Equiv n) (gueCoordinates n x) : FrobHerm0 n)‖ ^ 2 = _
  simp only [gueCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change ‖(stdOrthonormalBasis ℝ (FrobHerm0 n)).repr.symm (WithLp.toLp 2 x)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map, EuclideanSpace.norm_sq_eq]
  simp

/-- The density-defined traceless GUE is exactly the orthonormal-coordinate Gaussian law. -/
theorem map_gaussian_gueCoordinates (n : ℕ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) =>
      gaussianReal 0 (2 / (n : ℝ≥0)))).map (gueCoordinates n) = tracelessGUE n := by
  have : SecondCountableTopology (Herm0 n) :=
    @TopologicalSpace.Subtype.secondCountableTopology (Fin n → Fin n → ℂ) _
      (fun X => X ∈ Herm0 n) inferInstance
  have hv : (2 / (n : ℝ≥0)) ≠ 0 := div_ne_zero (by norm_num) (by exact_mod_cast hn.ne')
  rw [map_pi_gaussian_eq_cond_quadratic (Measure.addHaar : Measure (Herm0 n))
    (gueCoordinates n)
    (fun X => WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2)
    (schatten_two_gueCoordinates n) _ hv]
  unfold tracelessGUE tracelessGUEWeight
  congr 2
  funext X
  congr 2
  simp only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
  field_simp
  ring

def gueStandardMap (n : ℕ) :
    (Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) →L[ℝ] Herm0 n :=
  (gueCoordinates n).toContinuousLinearMap.comp
    ((Real.sqrt (2 / (n : ℝ))) • ContinuousLinearMap.id ℝ _)

theorem map_standardGaussian_gueStandardMap (n : ℕ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 1)).map
      (gueStandardMap n) = tracelessGUE n := by
  have hscale : (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 1)).map
      (fun x => Real.sqrt (2 / (n : ℝ)) • x) =
      Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 (2 / (n : ℝ≥0))) := by
    change (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 1)).map
      (fun x i => Real.sqrt (2 / (n : ℝ)) * x i) = _
    rw [Measure.pi_map_pi (f := fun _ z => Real.sqrt (2 / (n : ℝ)) * z)
      (fun _ => by fun_prop)]
    congr 1
    funext i
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mk, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
    exact Real.sq_sqrt (by positivity)
  have hcomp : (gueStandardMap n : _ → _) =
      (gueCoordinates n) ∘ (fun x => Real.sqrt (2 / (n : ℝ)) • x) := rfl
  rw [hcomp, ← Measure.map_map (gueCoordinates n).continuous.measurable (by fun_prop), hscale]
  exact map_gaussian_gueCoordinates n hn

theorem schatten_two_gueStandardMap (n : ℕ)
    (x : Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) :
    WHMultiplicativity.schattenNorm 2
      (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ) =
      Real.sqrt (2 / (n : ℝ)) * Real.sqrt (∑ i, x i ^ 2) := by
  have hsq := schatten_two_gueCoordinates n (Real.sqrt (2 / (n : ℝ)) • x)
  change WHMultiplicativity.schattenNorm 2 (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ) ^ 2 = _ at hsq
  have hnrm : 0 ≤ WHMultiplicativity.schattenNorm 2 (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← norm_frobeniusMatrixEquiv]
    exact norm_nonneg _
  rw [← Real.sqrt_sq hnrm, hsq]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg _)]

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5GaussianTail -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Two Lipschitz Gaussian observables with a common mean bound have a
nonasymptotic upper tail with the union-bound factor two. -/
theorem gaussian_two_observable_tail {ι : Type*} [Fintype ι]
    (f g : (ι → ℝ) → ℝ) (L m t : ℝ) (hL : 0 < L) (ht : 0 ≤ t)
    (hf : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hg : ∀ x y, |g x - g y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hmf : (∫ x, f x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤ m)
    (hmg : (∫ x, g x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤ m) :
    (Measure.pi fun _ : ι => gaussianReal 0 1) {x | m + t < max (f x) (g x)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  let μ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  have hf' := (GaussianMatrix.gaussian_concentration_vector f L hL hf (t / L)
    (div_nonneg ht hL.le)).2
  have hg' := (GaussianMatrix.gaussian_concentration_vector g L hL hg (t / L)
    (div_nonneg ht hL.le)).2
  have hcancel : L * (t / L) = t := by field_simp
  have hexp : -(t / L) ^ 2 / 2 = -t ^ 2 / (2 * L ^ 2) := by ring
  rw [hcancel, hexp] at hf' hg'
  have hsub : {x | m + t < max (f x) (g x)} ⊆
      {x | (∫ y, f y ∂μ) + t ≤ f x} ∪ {x | (∫ y, g y ∂μ) + t ≤ g x} := by
    intro x hx
    change m + t < max (f x) (g x) at hx
    rcases lt_max_iff.mp hx with h | h
    · apply Or.inl
      change (∫ y, f y ∂μ) + t ≤ f x
      exact (add_le_add hmf le_rfl).trans h.le
    · apply Or.inr
      change (∫ y, g y ∂μ) + t ≤ g x
      exact (add_le_add hmg le_rfl).trans h.le
  calc
    μ {x | m + t < max (f x) (g x)} ≤
        μ ({x | (∫ y, f y ∂μ) + t ≤ f x} ∪ {x | (∫ y, g y ∂μ) + t ≤ g x}) :=
      measure_mono hsub
    _ ≤ μ {x | (∫ y, f y ∂μ) + t ≤ f x} + μ {x | (∫ y, g y ∂μ) + t ≤ g x} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) +
        ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := add_le_add hf' hg'
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring

/-- Transport of the Gaussian two-observable bound through an exact model law. -/
theorem gaussian_mapped_two_observable_tail {ι Θ : Type*} [Fintype ι] [MeasurableSpace Θ]
    (P : Measure Θ) (F : (ι → ℝ) → Θ) (hF : Measurable F)
    (hlaw : Measure.map F (Measure.pi fun _ : ι => gaussianReal 0 1) = P)
    (d : Θ → ℝ) (hd : Measurable d) (f g : (ι → ℝ) → ℝ)
    (L m t : ℝ) (hL : 0 < L) (ht : 0 ≤ t)
    (hf : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hg : ∀ x y, |g x - g y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hmf : (∫ x, f x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤ m)
    (hmg : (∫ x, g x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤ m)
    (hobs : ∀ x, d (F x) ≤ max (f x) (g x)) :
    P {X | m + t < d X} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  rw [← hlaw, Measure.map_apply hF (measurableSet_lt measurable_const hd)]
  refine (measure_mono ?_).trans (gaussian_two_observable_tail f g L m t hL ht hf hg hmf hmg)
  intro x hx
  exact hx.trans_le (hobs x)

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5GUEConcentration -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace BosonicLearn.Prop5

noncomputable section

def gueRayleigh (n : ℕ) (x : Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) : ℝ :=
  upperRayleigh (Matrix.toEuclideanCLM (𝕜 := ℂ)
    (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ))

theorem continuous_upperRayleigh {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    Continuous (upperRayleigh : (E →L[ℂ] E) → ℝ) := by
  apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
  intro T S
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    upperRayleigh_lipschitz T S

theorem continuous_gueRayleigh (n : ℕ) : Continuous (gueRayleigh n) := by
  apply continuous_upperRayleigh.comp
  exact ((LinearMap.continuous_of_finiteDimensional
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
      continuous_subtype_val).comp (gueStandardMap n).continuous

theorem gueRayleigh_lipschitz (n : ℕ)
    (x y : Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) :
    |gueRayleigh n x - gueRayleigh n y| ≤
      Real.sqrt (2 / (n : ℝ)) * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  have h := matrix_upperRayleigh_lipschitz n
    (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ)
    (gueStandardMap n y : Matrix (Fin n) (Fin n) ℂ)
  change |gueRayleigh n x - gueRayleigh n y| ≤
    WHMultiplicativity.schattenNorm 2 ((gueStandardMap n x - gueStandardMap n y : Herm0 n) :
      Matrix (Fin n) (Fin n) ℂ) at h
  rw [← map_sub, schatten_two_gueStandardMap] at h
  exact h

theorem pi_standardGaussian_map_neg {ι : Type*} [Fintype ι] :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x => -x) =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  change (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x i => -x i) = _
  rw [Measure.pi_map_pi (f := fun _ z => -z) (fun _ => by fun_prop)]
  simp_rw [gaussianReal_map_neg, neg_zero]

theorem integral_gueRayleigh_neg (n : ℕ) :
    (∫ x, gueRayleigh n (-x) ∂(Measure.pi fun _ => gaussianReal 0 1)) =
      ∫ x, gueRayleigh n x ∂(Measure.pi fun _ => gaussianReal 0 1) := by
  rw [← integral_map (by fun_prop) (continuous_gueRayleigh n).aestronglyMeasurable,
    pi_standardGaussian_map_neg]

/-- The sharp Gaussian operator tail follows from the expected Rayleigh maximum bound. -/
theorem gue_operator_tail_of_mean (n : ℕ) (hn : 0 < n) (m t : ℝ) (ht : 0 ≤ t)
    (hm : (∫ x, gueRayleigh n x ∂(Measure.pi fun _ => gaussianReal 0 1)) ≤ m) :
    tracelessGUE n {X | m + t <
      WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ)} ≤
        ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * t ^ 2 / 4)) := by
  have hL : 0 < Real.sqrt (2 / (n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hd : Measurable (fun X : Herm0 n => WHMultiplicativity.schattenNorm ⊤
      (X : Matrix (Fin n) (Fin n) ℂ)) := by
    have hc : Continuous fun X : Herm0 n =>
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
      apply Continuous.norm
      exact (LinearMap.continuous_of_finiteDimensional
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
          continuous_subtype_val
    simpa [WHMultiplicativity.schattenNorm] using hc.measurable
  have hg : ∀ x y, |gueRayleigh n (-x) - gueRayleigh n (-y)| ≤
      Real.sqrt (2 / (n : ℝ)) * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
    intro x y
    convert gueRayleigh_lipschitz n (-x) (-y) using 1
    simp only [Pi.neg_apply]
    congr 3
    funext i
    ring
  have hobs : ∀ x, WHMultiplicativity.schattenNorm ⊤
      (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ) ≤
      max (gueRayleigh n x) (gueRayleigh n (-x)) := by
    intro x
    have hsym : (Matrix.toEuclideanCLM (𝕜 := ℂ)
      (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ)).IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (gueStandardMap n x).property.1
    have h := norm_le_max_upperRayleigh _ hsym
    simpa [WHMultiplicativity.schattenNorm, gueRayleigh, map_neg,
      Submodule.coe_neg] using h
  have h := gaussian_mapped_two_observable_tail (tracelessGUE n) (gueStandardMap n)
    (gueStandardMap n).continuous.measurable (map_standardGaussian_gueStandardMap n hn)
    (fun X => WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ)) hd
    (gueRayleigh n) (fun x => gueRayleigh n (-x)) (Real.sqrt (2 / (n : ℝ))) m t hL ht
    (gueRayleigh_lipschitz n) hg hm (by rwa [integral_gueRayleigh_neg]) hobs
  convert h using 2
  congr 2
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5GaussianProcess -/
section
open MeasureTheory ProbabilityTheory

noncomputable section
namespace BosonicLearn.Prop5

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [FiniteDimensional ℝ K] [MeasurableSpace K] [BorelSpace K]

/-- The canonical process of a standard Gaussian vector, indexed by arbitrary coefficient vectors. -/
theorem isGaussianProcess_inner_stdGaussian {T : Type*} (a : T → K) :
    IsGaussianProcess (fun t x => inner ℝ (a t) x) (stdGaussian K) := by
  constructor
  intro I
  exact IsGaussian.hasGaussianLaw_id.map
    (ContinuousLinearMap.pi (fun t : I => innerSL ℝ (a t)))

/-- Every canonical Gaussian coordinate has zero mean. -/
theorem integral_inner_stdGaussian (a : K) :
    (∫ x, inner ℝ a x ∂stdGaussian K) = 0 :=
  integral_strongDual_stdGaussian (innerSL ℝ a)

/-- The canonical Gaussian metric is precisely the Hilbert-space distance. -/
theorem integral_sq_inner_sub_stdGaussian (a b : K) :
    (∫ x, (inner ℝ a x - inner ℝ b x)^2 ∂stdGaussian K) = ‖a-b‖^2 := by
  have hm := integral_strongDual_stdGaussian (innerSL ℝ (a-b))
  have hv := variance_dual_stdGaussian (innerSL ℝ (a-b))
  rw [variance_of_integral_eq_zero (by fun_prop) hm, innerSL_apply_norm] at hv
  simpa only [innerSL_apply_apply, inner_sub_left] using hv

/-- The norm of a finite-dimensional standard Gaussian is square-integrable. -/
theorem memLp_norm_stdGaussian : MemLp (fun x : K => ‖x‖) 2 (stdGaussian K) :=
  IsGaussian.memLp_two_id.norm

/-- The total second moment of an isotropic standard Gaussian equals its real dimension. -/
theorem integral_norm_sq_stdGaussian :
    (∫ x : K, ‖x‖^2 ∂stdGaussian K) = (Module.finrank ℝ K : ℝ) := by
  let b := stdOrthonormalBasis ℝ K
  have heq : (fun x : K => ‖x‖^2) =
      (fun x => ∑ i : Fin (Module.finrank ℝ K), (inner ℝ (b i) x)^2) := by
    funext x
    exact (b.sum_sq_inner_right x).symm
  rw [heq, integral_finsetSum]
  · have hval : ∀ i : Fin (Module.finrank ℝ K),
        (∫ x : K, (inner ℝ (b i) x)^2 ∂stdGaussian K) = 1 := by
      intro i
      have h := integral_sq_inner_sub_stdGaussian (b i) (0 : K)
      simpa using h
    simp [hval]
  · intro i hi
    exact (IsGaussian.hasGaussianLaw_id.map (innerSL ℝ (b i))).memLp_two.integrable_sq

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5GUEExpectation -/
section
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace BosonicLearn.Prop5
noncomputable section
set_option maxHeartbeats 1000000

/-- Gaussian comparison of finite-marginal expected suprema allows different probability spaces. -/
theorem processESup_comparison_two_spaces {Ω Ω' T : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : T → Ω → ℝ) (Y : T → Ω' → ℝ)
    (hXG : IsGaussianProcess X μ) (hYG : IsGaussianProcess Y ν)
    (hXm : ∀ t, ∫ ω, X t ω ∂μ = 0) (hYm : ∀ t, ∫ ω, Y t ω ∂ν = 0)
    (hinc : ∀ t s, ∫ ω, (X t ω - X s ω)^2 ∂μ ≤ ∫ ω, (Y t ω - Y s ω)^2 ∂ν) :
    HighDimProb.RandomProcesses.processESup μ X ≤
      HighDimProb.RandomProcesses.processESup ν Y := by
  classical
  apply iSup_le
  intro s
  have : Nonempty s.1 := s.2.to_subtype
  have hmax (Z : T → ℝ) : s.1.sup' s.2 Z = ⨆ t : s.1, Z t := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun t ht => le_ciSup
        (Set.finite_range (fun u : s.1 => Z u)).bddAbove ⟨t, ht⟩)
    · exact ciSup_le (fun t => Finset.le_sup' Z t.property)
  have h := GaussianMatrix.sudakov_fernique (fun t : s.1 => X t) (fun t : s.1 => Y t)
    (hXG.hasGaussianLaw s.1) (hYG.hasGaussianLaw s.1)
    (fun t => hXm t) (fun t => hYm t) (fun t u => hinc t u)
  apply le_trans (b := ((∫ ω, s.1.sup' s.2 (fun t => Y t ω) ∂ν : ℝ) : EReal))
  · apply EReal.coe_le_coe_iff.mpr
    simpa only [hmax] using h
  · exact le_iSup (fun s : {s : Finset T // s.Nonempty} =>
      ((∫ ω, s.1.sup' s.2 (fun t => Y t ω) ∂ν : ℝ) : EReal)) s

/-- A continuous Gaussian process is bounded in mean by an integrable envelope of a
comparison process, even when the processes use different sample spaces. -/
theorem expected_sup_le_of_gaussian_comparison_two_spaces {Ω Ω' T : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    (μ : Measure Ω) (ν : Measure Ω') (X : T → Ω → ℝ) (Y : T → Ω' → ℝ)
    (hXG : IsGaussianProcess X μ) (hYG : IsGaussianProcess Y ν)
    (hXm : ∀ t, ∫ ω, X t ω ∂μ = 0) (hYm : ∀ t, ∫ ω, Y t ω ∂ν = 0)
    (hinc : ∀ t s, ∫ ω, (X t ω - X s ω)^2 ∂μ ≤ ∫ ω, (Y t ω - Y s ω)^2 ∂ν)
    (hcont : ∀ ω, Continuous (fun t => X t ω))
    (gX : Ω → ℝ) (hgX : Integrable gX μ) (hbX : ∀ t ω, ‖X t ω‖ ≤ gX ω)
    (gY : Ω' → ℝ) (hgY : Integrable gY ν) (hbY : ∀ t ω, Y t ω ≤ gY ω) :
    (∫ ω, (⨆ t, X t ω) ∂μ) ≤ ∫ ω, gY ω ∂ν := by
  apply EReal.coe_le_coe_iff.mp
  exact (integral_iSup_le_processESup μ X
    (fun t => (hXG.hasGaussianLaw_eval t).integrable.aestronglyMeasurable)
    hcont gX hgX hbX).trans
    ((processESup_comparison_two_spaces μ ν X Y hXG hYG hXm hYm hinc).trans
      (processESup_le_integral ν Y (fun t => (hYG.hasGaussianLaw_eval t).integrable) gY hgY hbY))

def gueHilbertOperator (n : ℕ) :
    FrobHerm0 n →L[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  (LinearMap.toContinuousLinearMap
    (((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap.restrictScalars ℝ).comp
      (Herm0 n).subtype)).comp
    ((Real.sqrt (2 / (n : ℝ))) • (frobeniusHerm0Equiv n).symm.toContinuousLinearMap)

def gueCoefficient (n : ℕ) : RayleighIndex (EuclideanSpace ℂ (Fin n)) → FrobHerm0 n :=
  Sum.elim (fun v => Real.sqrt (2 / (n : ℝ)) •
    (FrobHerm0 n).orthogonalProjectionOnto (projectorVector (v : EuclideanSpace ℂ (Fin n))))
    (fun _ => 0)

def gueComparisonCoefficient (n : ℕ) :
    RayleighIndex (EuclideanSpace ℂ (Fin n)) → EuclideanSpace ℂ (Fin n) :=
  Sum.elim (fun v => (2 / Real.sqrt n) • (v : EuclideanSpace ℂ (Fin n))) (fun _ => 0)

theorem real_inner_euclidean_eq_re {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℂ ι) : inner ℝ u v = (inner ℂ u v).re := by
  simp only [PiLp.inner_apply, Complex.inner, RCLike.inner_apply, Complex.re_sum]

theorem indexedRayleigh_gueHilbertOperator (n : ℕ) (Z : FrobHerm0 n)
    (v : RayleighIndex (EuclideanSpace ℂ (Fin n))) :
    indexedRayleigh (gueHilbertOperator n Z) v = inner ℝ (gueCoefficient n v) Z := by
  cases v with
  | inr v => simp [indexedRayleigh, gueCoefficient]
  | inl v =>
    change (Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((Real.sqrt (2 / (n : ℝ)) • (frobeniusHerm0Equiv n).symm Z : Herm0 n) :
        Matrix (Fin n) (Fin n) ℂ)).rayleighQuotient v = _
    rw [rayleigh_unit_eq_real_inner_projector _ _ (norm_eq_of_mem_sphere v)]
    rw [← real_inner_euclidean_eq_re]
    change inner ℝ (projectorVector (v : EuclideanSpace ℂ (Fin n)))
      (frobeniusMatrixEquiv n
        ((Real.sqrt (2 / (n : ℝ)) • (frobeniusHerm0Equiv n).symm Z : Herm0 n) :
          Matrix (Fin n) (Fin n) ℂ)) = _
    have heq : frobeniusMatrixEquiv n
        ((Real.sqrt (2 / (n : ℝ)) • (frobeniusHerm0Equiv n).symm Z : Herm0 n) :
          Matrix (Fin n) (Fin n) ℂ) = Real.sqrt (2 / (n : ℝ)) • (Z : EuclideanSpace ℂ (Fin n × Fin n)) := by
      change ((frobeniusHerm0Equiv n)
        (Real.sqrt (2 / (n : ℝ)) • (frobeniusHerm0Equiv n).symm Z) :
          EuclideanSpace ℂ (Fin n × Fin n)) = _
      rw [map_smul, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    rw [heq]
    change inner ℝ (projectorVector (v : EuclideanSpace ℂ (Fin n)))
      (Real.sqrt (2 / (n : ℝ)) • (Z : EuclideanSpace ℂ (Fin n × Fin n))) =
      inner ℝ (Real.sqrt (2 / (n : ℝ)) • (FrobHerm0 n).orthogonalProjectionOnto
        (projectorVector (v : EuclideanSpace ℂ (Fin n)))) Z
    rw [real_inner_smul_left (F := FrobHerm0 n), real_inner_smul_right]
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

theorem gue_scales (n : ℕ) (hn : 0 < n) :
    (Real.sqrt (2 / (n : ℝ))) ^ 2 * 2 = (2 / Real.sqrt (n : ℝ)) ^ 2 := by
  rw [Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt (by positivity)]
  field_simp

theorem gueCoefficient_increment (n : ℕ) (hn : 0 < n)
    (v w : RayleighIndex (EuclideanSpace ℂ (Fin n))) :
    ‖gueCoefficient n v - gueCoefficient n w‖ ^ 2 ≤
      ‖gueComparisonCoefficient n v - gueComparisonCoefficient n w‖ ^ 2 := by
  have hc : 0 ≤ Real.sqrt (2 / (n : ℝ)) := Real.sqrt_nonneg _
  have hd : 0 ≤ 2 / Real.sqrt (n : ℝ) := by positivity
  have hzero (u : Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1) :
      ‖gueCoefficient n (Sum.inl u)‖ ^ 2 ≤ ‖gueComparisonCoefficient n (Sum.inl u)‖ ^ 2 := by
    have hp := (FrobHerm0 n).norm_orthogonalProjectionOnto_apply_le (projectorVector (u : EuclideanSpace ℂ (Fin n)))
    have hp2 : ‖(FrobHerm0 n).orthogonalProjectionOnto (projectorVector (u : EuclideanSpace ℂ (Fin n)))‖ ^ 2 ≤ 1 := by
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hp 2
      rw [norm_projectorVector_sq, norm_eq_of_mem_sphere u] at hsq
      simpa using hsq
    change ‖Real.sqrt (2 / (n : ℝ)) • (FrobHerm0 n).orthogonalProjectionOnto (projectorVector (u : EuclideanSpace ℂ (Fin n)))‖ ^ 2 ≤
      ‖(2 / Real.sqrt (n : ℝ)) • (u : EuclideanSpace ℂ (Fin n))‖ ^ 2
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hc, abs_of_nonneg hd, mul_pow, norm_eq_of_mem_sphere u, mul_one]
    have hs := gue_scales n hn
    have hmul := mul_le_mul_of_nonneg_left hp2 (sq_nonneg (Real.sqrt (2 / (n : ℝ))))
    nlinarith [sq_nonneg (Real.sqrt (2 / (n : ℝ)))]
  cases v with
  | inr v =>
    cases w with
    | inr w => simp [gueCoefficient, gueComparisonCoefficient]
    | inl w => simpa [gueCoefficient, gueComparisonCoefficient] using hzero w
  | inl v =>
    cases w with
    | inr w => simpa [gueCoefficient, gueComparisonCoefficient] using hzero v
    | inl w =>
      have hp := (FrobHerm0 n).norm_orthogonalProjectionOnto_apply_le
        (projectorVector (v : EuclideanSpace ℂ (Fin n)) - projectorVector (w : EuclideanSpace ℂ (Fin n)))
      have hp2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
      have hi := unit_projector_increment_bound (ι := Fin n) (v : EuclideanSpace ℂ (Fin n)) (w : EuclideanSpace ℂ (Fin n))
        (norm_eq_of_mem_sphere v) (norm_eq_of_mem_sphere w)
      change ‖Real.sqrt (2 / (n : ℝ)) • (FrobHerm0 n).orthogonalProjectionOnto (projectorVector (v : EuclideanSpace ℂ (Fin n))) -
        Real.sqrt (2 / (n : ℝ)) • (FrobHerm0 n).orthogonalProjectionOnto (projectorVector (w : EuclideanSpace ℂ (Fin n)))‖ ^ 2 ≤
        ‖(2 / Real.sqrt (n : ℝ)) • (v : EuclideanSpace ℂ (Fin n)) -
          (2 / Real.sqrt (n : ℝ)) • (w : EuclideanSpace ℂ (Fin n))‖ ^ 2
      rw [← smul_sub, ← smul_sub, ← map_sub, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hd,
        mul_pow, mul_pow]
      calc
        _ ≤ (Real.sqrt (2 / (n : ℝ))) ^ 2 *
            (2 * ‖(v : EuclideanSpace ℂ (Fin n)) - w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hp2.trans hi) (sq_nonneg _)
        _ = _ := by rw [← mul_assoc, gue_scales n hn]

/-- Sudakov--Fernique bounds the mean largest GUE eigenvalue by the mean norm of a
standard complex Gaussian vector, with the sharp scaling. -/
theorem gueHilbert_mean_le_envelope (n : ℕ) (hn : 0 < n) :
    (∫ Z, upperRayleigh (gueHilbertOperator n Z) ∂stdGaussian (FrobHerm0 n)) ≤
      ∫ g : EuclideanSpace ℂ (Fin n), (2 / Real.sqrt n) * ‖g‖ ∂stdGaussian _ := by
  let X := fun v Z => inner ℝ (gueCoefficient n v) Z
  let Y := fun v g => inner ℝ (gueComparisonCoefficient n v) g
  have hcont : ∀ Z, Continuous (fun v => X v Z) := by
    intro Z
    convert continuous_indexedRayleigh (gueHilbertOperator n Z) using 1
    funext v
    exact (indexedRayleigh_gueHilbertOperator n Z v).symm
  have hgX : Integrable (fun Z => ‖gueHilbertOperator n Z‖) (stdGaussian (FrobHerm0 n)) :=
    (IsGaussian.hasGaussianLaw_id.map (gueHilbertOperator n)).integrable.norm
  have hgY : Integrable (fun g : EuclideanSpace ℂ (Fin n) => (2 / Real.sqrt n) * ‖g‖)
      (stdGaussian _) := IsGaussian.integrable_id.norm.const_mul _
  have h := expected_sup_le_of_gaussian_comparison_two_spaces
    (stdGaussian (FrobHerm0 n)) (stdGaussian (EuclideanSpace ℂ (Fin n))) X Y
    (isGaussianProcess_inner_stdGaussian (gueCoefficient n))
    (isGaussianProcess_inner_stdGaussian (gueComparisonCoefficient n))
    (fun v => integral_inner_stdGaussian (gueCoefficient n v))
    (fun v => integral_inner_stdGaussian (gueComparisonCoefficient n v))
    (fun v w => by
      change (∫ Z, (inner ℝ (gueCoefficient n v) Z - inner ℝ (gueCoefficient n w) Z)^2
        ∂stdGaussian (FrobHerm0 n)) ≤ _
      rw [integral_sq_inner_sub_stdGaussian (K := FrobHerm0 n),
        integral_sq_inner_sub_stdGaussian]
      exact gueCoefficient_increment n hn v w)
    hcont (fun Z => ‖gueHilbertOperator n Z‖) hgX
    (fun v Z => by
      change ‖inner ℝ (gueCoefficient n v) Z‖ ≤ _
      rw [← indexedRayleigh_gueHilbertOperator]
      exact indexedRayleigh_norm_le _ _)
    (fun g => (2 / Real.sqrt n) * ‖g‖) hgY (fun v g => by
      cases v with
      | inr v => simp [Y, gueComparisonCoefficient]; positivity
      | inl v =>
        change inner ℝ ((2 / Real.sqrt n) • (v : EuclideanSpace ℂ (Fin n))) g ≤ _
        rw [real_inner_smul_left]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [norm_eq_of_mem_sphere v, one_mul] using real_inner_le_norm (v : EuclideanSpace ℂ (Fin n)) g)
  simpa only [X, ← indexedRayleigh_gueHilbertOperator, iSup_indexedRayleigh] using h

theorem gueHilbert_mean_le (n : ℕ) (hn : 0 < n) :
    (∫ Z, upperRayleigh (gueHilbertOperator n Z) ∂stdGaussian (FrobHerm0 n)) ≤
      2 * Real.sqrt 2 := by
  apply (gueHilbert_mean_le_envelope n hn).trans
  apply comparison_envelope_mean_le (stdGaussian (EuclideanSpace ℂ (Fin n))) n hn id
    memLp_norm_stdGaussian
  change (∫ g : EuclideanSpace ℂ (Fin n), ‖g‖ ^ 2 ∂stdGaussian _) ≤ _
  rw [integral_norm_sq_stdGaussian]
  simp [finrank_real_of_complex]

theorem integral_gueRayleigh_eq_hilbert (n : ℕ) :
    (∫ x, gueRayleigh n x ∂(Measure.pi fun _ => gaussianReal 0 1)) =
      ∫ Z, upperRayleigh (gueHilbertOperator n Z) ∂stdGaussian (FrobHerm0 n) := by
  let b := stdOrthonormalBasis ℝ (FrobHerm0 n)
  have hmap : (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 1)).map
      (fun x => b.repr.symm (WithLp.toLp 2 x)) = stdGaussian (FrobHerm0 n) := by
    rw [show (fun x => b.repr.symm (WithLp.toLp 2 x)) = b.repr.symm ∘ WithLp.toLp 2 from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian, stdGaussian_map]
  rw [← hmap, integral_map (by fun_prop)
    (show AEStronglyMeasurable (fun Z => upperRayleigh (gueHilbertOperator n Z)) _ from
      (continuous_upperRayleigh.comp (gueHilbertOperator n).continuous).aestronglyMeasurable)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change upperRayleigh (Matrix.toEuclideanCLM (𝕜 := ℂ)
    (gueCoordinates n (Real.sqrt (2 / (n : ℝ)) • x) : Matrix (Fin n) (Fin n) ℂ)) = _
  rw [map_smul]
  rfl

theorem gueRayleigh_mean_le (n : ℕ) (hn : 0 < n) :
    (∫ x, gueRayleigh n x ∂(Measure.pi fun _ => gaussianReal 0 1)) ≤ 2 * Real.sqrt 2 := by
  rw [integral_gueRayleigh_eq_hilbert]
  exact gueHilbert_mean_le n hn

/-- The unconditioned traceless-GUE concentration estimate follows from proved Gaussian
comparison and concentration, with all coordinate and density identifications checked. -/
theorem gue_operator_tail_proved (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    tracelessGUE n {X | 2 * Real.sqrt 2 + t <
      WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ)} ≤
      ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * t ^ 2 / 4)) :=
  gue_operator_tail_of_mean n hn (2 * Real.sqrt 2) t ht.le (gueRayleigh_mean_le n hn)

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5PriorReduction -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- An explicit exponential bound for the paper's conditioned prior,
derived from Gaussian comparison and concentration. -/
theorem prior_good_tail_from_gue :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        priorMu n (Ggood n)ᶜ ≤ ENNReal.ofReal (Real.exp (-c * (n : ℝ))) := by
  refine ⟨1 / 512, by norm_num, 512, by norm_num, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hnreal : (512 : ℝ) ≤ n := by exact_mod_cast hn
  have hedge : 2 * Real.sqrt 2 + (1 / 8 : ℝ) ≤ 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hp := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hset : (Ggood n)ᶜ ⊆ {X : Herm0 n | 2 * Real.sqrt 2 + (1 / 8 : ℝ) <
      WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ)} := by
    intro X hX
    have hx : 3 < WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) := by
      simpa only [Ggood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] using hX
    exact hedge.trans_lt hx
  have htwo : 2 ≤ Real.exp ((n : ℝ) / 512) := by
    have h := Real.add_one_le_exp ((n : ℝ) / 512)
    linarith
  have hexp : 2 * Real.exp (-(n : ℝ) * (1 / 8 : ℝ) ^ 2 / 4) ≤
      Real.exp (-(1 / 512 : ℝ) * n) := by
    calc
      2 * Real.exp (-(n : ℝ) * (1 / 8 : ℝ) ^ 2 / 4) ≤
          Real.exp ((n : ℝ) / 512) * Real.exp (-(n : ℝ) * (1 / 8 : ℝ) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-(1 / 512 : ℝ) * n) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    priorMu n (Ggood n)ᶜ ≤ tracelessGUE n (Ggood n)ᶜ := prior_bad_le_gue_bad_of_pos n hnpos
    _ ≤ tracelessGUE n {X | 2 * Real.sqrt 2 + (1 / 8 : ℝ) <
        WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ)} := measure_mono hset
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (1 / 8 : ℝ) ^ 2 / 4)) :=
      gue_operator_tail_proved n (by omega) (1 / 8) (by norm_num)
    _ ≤ ENNReal.ofReal (Real.exp (-(1 / 512 : ℝ) * n)) := ENNReal.ofReal_le_ofReal hexp

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5Reduction -/
section
open MeasureTheory ProbabilityTheory BosonicLearn
open scoped ENNReal

set_option maxHeartbeats 500000
set_option linter.style.haveILetI false

namespace BosonicLearn.Prop5

private theorem measurableSet_Ggood (n : ℕ) : MeasurableSet (Ggood n) := by
  unfold Ggood WHMultiplicativity.schattenNorm
  have hc : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) M :=
    LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)
  exact (isClosed_le (hc.comp continuous_subtype_val).norm continuous_const).measurableSet

end BosonicLearn.Prop5

theorem solution :
    ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ →
      ∀ η : ℝ, 0 < η → ∃ κ : ℝ, 0 < κ ∧ ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
        ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
        ∀ N : ℕ, (N : ℝ) * ν ^ 2 * ξ ^ 2 ≤ κ * n →
        ∀ (O : Type) [MeasurableSpace O] (S : AdaptiveScheme n N O) (A : Kernel (Fin N → O) (Herm0 n)),
          IsMarkovKernel A →
          ∫⁻ X₀, ∫⁻ x, A x {Y | WHMultiplicativity.schattenNorm 1 ((Y - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ n * a / 2}
              ∂(transcriptLaw S (fugacityCoeff (fugacityFamily ν ξ X₀))) ∂(priorMu n)
            ≤ ENNReal.ofReal (1 / 10 + η)  := by
  obtain ⟨ξ₀, hξ₀, hξ₀lt, a₀, ha₀, c, hc, C, hC, n₀, hn₀, htail⟩ := Prop5.posterior_tail_from_model
  obtain ⟨cg, hcg, ng, hng, hgood⟩ := Prop5.prior_good_tail_from_gue
  obtain ⟨κ, hκ, ne, hne, herror⟩ := Prop5.posterior_error_constants c C cg hc hC hcg
  refine ⟨ξ₀, hξ₀, hξ₀lt, a₀, ha₀, ?_⟩
  intro a ha ha₀ η hη
  refine ⟨κ, hκ, max n₀ (max ng ne), ?_⟩
  intro n hn ν hν hν1 ξ hξ hξ₀ N hN O _ S A hA
  have hn₀' : n₀ ≤ n := (le_max_left _ _).trans hn
  have hng' : ng ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hne' : ne ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn1 : 1 ≤ n := hn₀.trans hn₀'
  have hξlt : ξ < 1 / 32 := hξ₀.trans_lt hξ₀lt
  obtain ⟨K, hK, hKlaw⟩ := Prop5.transcript_kernel_exists S ν ξ hn1 hν hν1 hξ hξlt
  haveI : IsMarkovKernel K := hK
  haveI : IsMarkovKernel A := hA
  obtain ⟨hμ, hsupp⟩ := priorMu_prob n
  haveI : IsProbabilityMeasure (priorMu n) := hμ
  haveI : PolishSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (PolishSpace (Fin n → Fin n → ℂ))
  haveI : PolishSpace (Herm0 n) := (Herm0_isClosed n).polishSpace
  let J : Measure ((Fin N → O) × Herm0 n) := (priorMu n ⊗ₘ K).map Prod.swap
  haveI : IsProbabilityMeasure J := Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  let ρ : Measure (Fin N → O) := J.fst
  let P : Kernel (Fin N → O) (Herm0 n) := J.condKernel
  haveI : IsProbabilityMeasure ρ := inferInstanceAs (IsProbabilityMeasure J.fst)
  haveI : IsMarkovKernel P := inferInstanceAs (IsMarkovKernel J.condKernel)
  have hbayes : Measure.map Prod.swap (priorMu n ⊗ₘ K) = ρ ⊗ₘ P :=
    (Measure.disintegrate J J.condKernel).symm
  let R : Herm0 n → Herm0 n → Prop := fun Y X =>
    WHMultiplicativity.schattenNorm 1 ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ n * a / 2
  let Q : Herm0 n → Herm0 n → Prop := fun X Z =>
    WHMultiplicativity.schattenNorm 1 ((Z - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ n * a
  have hR : MeasurableSet {p : Herm0 n × Herm0 n | R p.1 p.2} :=
    Prop5Geometry.measurableSet_trace_relation n (n * a / 2)
  have hQ : MeasurableSet {p : Herm0 n × Herm0 n | Q p.1 p.2} := by
    have heq : {p : Herm0 n × Herm0 n | Q p.1 p.2} =
        {p : Herm0 n × Herm0 n | WHMultiplicativity.schattenNorm 1
          ((p.1 - p.2 : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ n * a} := by
      ext p
      change WHMultiplicativity.schattenNorm 1
        ((p.2 - p.1 : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ n * a ↔
          WHMultiplicativity.schattenNorm 1
            ((p.1 - p.2 : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ n * a
      rw [Prop5Geometry.trace_distance_symm p.2 p.1]
    rw [heq]
    exact Prop5Geometry.measurableSet_trace_relation n (n * a)
  have htri : ∀ Y X Z, R Y X → R Y Z → Q X Z := by
    intro Y X Z hYX hYZ
    have ht := Prop5Geometry.trace_ball_pair X Y Z (n * a / 2) hYX hYZ
    change WHMultiplicativity.schattenNorm 1
      ((Z - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ n * a
    calc
      _ ≤ 2 * (n * a / 2) := ht
      _ = n * a := by ring
  have ht := htail a ha ha₀ n hn₀' ν hν hν1 ξ hξ hξ₀ N O S K hK hKlaw
    ρ inferInstance P inferInstance hbayes (1 / 400) (by norm_num) (by norm_num)
  have hs := Prop5.bayes_success_sq_le_of_tail (priorMu n) K ρ P A hbayes R Q hR hQ htri
    (Ggood n) (Prop5.measurableSet_Ggood n)
    (ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2 + C * N * n * ν ^ 2 * ξ ^ 2 / (1 / 400))))
    (ENNReal.ofReal (1 / 400) + ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2))) ht
  have he := herror n hne' N ν ξ hN
  have hb : ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2 + C * N * n * ν ^ 2 * ξ ^ 2 / (1 / 400))) +
      priorMu n (Ggood n)ᶜ +
      (ENNReal.ofReal (1 / 400) + ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2))) ≤
        ENNReal.ofReal (1 / 100) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2 + C * N * n * ν ^ 2 * ξ ^ 2 / (1 / 400))) +
          ENNReal.ofReal (Real.exp (-cg * n)) +
          (ENNReal.ofReal (1 / 400) + ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2))) := by
        exact add_le_add (add_le_add le_rfl (hgood n hng')) le_rfl
      _ ≤ ENNReal.ofReal (1 / 100) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        simpa only [neg_mul, add_assoc, add_comm, add_left_comm] using he
  have hs' := hs.trans hb
  have hprob : (∫⁻ X₀, ∫⁻ x, A x {Y | R Y X₀} ∂K X₀ ∂priorMu n) ≤ ENNReal.ofReal (1 / 10) := by
    have heq : ENNReal.ofReal (1 / 100) = (ENNReal.ofReal (1 / 10)) ^ 2 := by
      rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 10)]
      norm_num
    rw [heq] at hs'
    exact (ENNReal.pow_le_pow_left_iff (by norm_num : 2 ≠ 0)).mp hs'
  have hconvert : (∫⁻ X₀, ∫⁻ x, A x {Y | R Y X₀} ∂K X₀ ∂priorMu n) =
      ∫⁻ X₀, ∫⁻ x, A x {Y | R Y X₀}
        ∂transcriptLaw S (fugacityCoeff (fugacityFamily ν ξ X₀)) ∂priorMu n := by
    apply lintegral_congr_ae
    filter_upwards [hsupp] with X hX
    rw [hKlaw X hX]
  rw [hconvert] at hprob
  exact hprob.trans (ENNReal.ofReal_le_ofReal (by linarith))

end
