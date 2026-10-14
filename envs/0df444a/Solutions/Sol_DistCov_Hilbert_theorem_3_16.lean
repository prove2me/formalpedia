-- Prove2me | solution 1 for DistCov.Hilbert.theorem_3_16
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T21:14:46.600741+00:00
-- url     : https://prove2.me/submissions/f660d665-5d79-4c82-83aa-14ab67668e07

import Theorems.Thm_DistCov_Hilbert_hilbert_strict_negType
import Theorems.Thm_DistCov_Hilbert_Ddiff_eq_baryDiff
import Theorems.Thm_DistCov_Hilbert_errata_x_continuity
import Theorems.Thm_DistCov_Hilbert_finite_projections_agree
import Theorems.Thm_DistCov_Hilbert_ext_of_finite_projections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace MeasureTheory.Measure
open scoped Topology NNReal
namespace DistCovStrong
open DistCov.Hilbert
abbrev E := DistCov.Indep.L2N

def e (n : ℕ) : E := lp.single 2 n (1 : ℝ)

def trunc (N : ℕ) (u : E) : E := ∑ n ∈ Finset.range N, lp.single 2 n (u n)

lemma trunc_tendsto (u : E) : Tendsto (fun N => trunc N u) atTop (𝓝 u) :=
  (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) u).tendsto_sum_nat

lemma single_eq_smul (u : E) (n : ℕ) : lp.single 2 n (u n) = u n • e n := by
  simpa [e] using (lp.single_smul (E := fun _ : ℕ => ℝ) 2 n (u n) (1 : ℝ))

lemma separable_H : SeparableSpace E := by
  let S := Submodule.span ℝ (Set.range e)
  have hs : IsSeparable (closure (S : Set E)) := (Set.countable_range e).isSeparable.span.closure
  apply isSeparable_univ_iff.mp
  apply hs.mono
  intro u hu
  apply mem_closure_of_tendsto (trunc_tendsto u)
  exact Eventually.of_forall fun N => S.sum_mem fun n hn => by
    rw [single_eq_smul]
    exact S.smul_mem _ (Submodule.subset_span ⟨n, rfl⟩)

local instance : SeparableSpace E := separable_H


lemma finite_sum_as_prefix (v : ℕ →₀ ℝ) : ∃ N : ℕ, ∀ u : E,
    (∑ i ∈ v.support, u i * v i) = ∑ i : Fin N, u i * v i := by
  classical
  let N := v.support.sup id + 1
  have hsub : v.support ⊆ Finset.range N := by
    intro i hi
    apply Finset.mem_range.mpr
    have hh : i ≤ v.support.sup id := Finset.le_sup (f := id) hi
    omega
  refine ⟨N, fun u => ?_⟩
  rw [Fin.sum_univ_eq_sum_range (fun i => u i * v i)]
  apply Finset.sum_subset hsub
  intro i hi hni
  simp [Finsupp.notMem_support_iff.mp hni]

lemma strong_l2 : DistCov.Indep.StrongNegType E := by
  refine ⟨(hilbert_strict_negType E).1, ?_⟩
  intro μ ν hμ hν h₁ h₂ hD
  letI := hμ
  letI := hν
  obtain ⟨hI,he⟩ := Ddiff_eq_baryDiff μ ν h₁ h₂
  have hi : ∫ p, (baryDiff μ ν p)^2 ∂(rho.prod volume) = 0 := by linarith
  have hz := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg (baryDiff μ ν p)) hI).mp hi
  have hb : baryDiff μ ν =ᵐ[rho.prod volume] 0 := by
    filter_upwards [hz] with p hp
    change (baryDiff μ ν p)^2 = 0 at hp
    change baryDiff μ ν p = 0
    exact sq_eq_zero_iff.mp hp
  have hf := finite_projections_agree μ ν h₁ h₂
    (fun K => errata_x_continuity μ ν h₁ h₂ K hb)
  apply ext_of_finite_projections μ ν
  intro v s
  obtain ⟨N,hN⟩ := finite_sum_as_prefix v
  simpa only [hN] using hf N (fun i => v i) s

lemma basis_countable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [SecondCountableTopology H] (w : Set H) (b : HilbertBasis w ℝ H)
    (hb : (b : w → H) = Subtype.val) : w.Countable := by
  have hd : IsDiscrete w := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro x hx
    refine ⟨Metric.ball x 1, Metric.isOpen_ball, ?_⟩
    ext y
    constructor
    · rintro ⟨hy,hyw⟩
      change y = x
      by_contra hne
      have hi : (⟨x,hx⟩ : w) ≠ ⟨y,hyw⟩ := fun he => hne (congrArg Subtype.val he).symm
      have hn := norm_sub_sq_real (b ⟨x,hx⟩) (b ⟨y,hyw⟩)
      rw [b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one, b.orthonormal.inner_eq_zero hi] at hn
      simp only [dist_eq_norm, Metric.mem_ball] at hy
      rw [hb] at hn
      have hp : 0 ≤ ‖x-y‖ := norm_nonneg _
      have hl : ‖x-y‖ < 1 := by simpa [norm_sub_rev] using hy
      nlinarith
    · intro hy
      have hxy : y = x := hy
      subst y
      exact ⟨by simp, hx⟩
  exact (HereditarilyLindelofSpace.isLindelof w).countable_of_isDiscrete hd

def coordIsometry (n : ℕ) : ℝ →ₗᵢ[ℝ] E :=
  (lp.lsingle (E := fun _ : ℕ => ℝ) 2 n).toLinearIsometry (by exact lp.isometry_single (E := fun _ : ℕ => ℝ) (p := 2) n)

lemma coords_orthogonal {ι : Type*} (k : ι ↪ ℕ) :
    OrthogonalFamily ℝ (fun _ : ι => ℝ) (fun i => coordIsometry (k i)) := by
  intro i j hij a b
  change inner ℝ (lp.single 2 (k i) a : E) (lp.single 2 (k j) b : E) = 0
  rw [lp.inner_single_left, lp.coeFn_single, Pi.single_eq_of_ne (fun he => hij (k.injective he))]
  simp

lemma exists_l2_embedding (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H] : Nonempty (H →ₗᵢ[ℝ] E) := by
  classical
  obtain ⟨w,b,hb⟩ := exists_hilbertBasis ℝ H
  letI : Countable w := (basis_countable w b hb).to_subtype
  letI := Encodable.ofCountable w
  let k : w ↪ ℕ := ⟨Encodable.encode, Encodable.encode_injective⟩
  exact ⟨(coords_orthogonal k).linearIsometry.comp b.repr.toLinearIsometry⟩

lemma firstMoment_map {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] (f : H →ₗᵢ[ℝ] E)
    (μ : Measure H) (h : DistCov.Indep.FiniteFirstMoment μ) :
    DistCov.Indep.FiniteFirstMoment (μ.map f) := by
  obtain ⟨o,ho⟩ := h
  refine ⟨f o, ?_⟩
  rw [f.isometry.isClosedEmbedding.measurableEmbedding.integrable_map_iff]
  simpa only [Function.comp_def, f.dist_map] using ho

lemma energy_map {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] (f : H →ₗᵢ[ℝ] E)
    (μ ν : Measure H) [SFinite μ] [SFinite ν] :
    DistCov.Indep.energy (μ.map f) (ν.map f) = DistCov.Indep.energy μ ν := by
  have hd : StronglyMeasurable (fun p : E × E => dist p.1 p.2) :=
    (continuous_fst.dist continuous_snd).stronglyMeasurable
  unfold DistCov.Indep.energy
  rw [Measure.map_prod_map μ ν f.continuous.measurable f.continuous.measurable,
    integral_map (f.continuous.measurable.prodMap f.continuous.measurable).aemeasurable hd.aestronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall fun p => f.dist_map p.1 p.2)

lemma Ddiff_map {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] (f : H →ₗᵢ[ℝ] E)
    (μ ν : Measure H) [SFinite μ] [SFinite ν] :
    DistCov.Indep.Ddiff (μ.map f) (ν.map f) = DistCov.Indep.Ddiff μ ν := by
  unfold DistCov.Indep.Ddiff
  rw [energy_map, energy_map, energy_map]
end DistCovStrong

 theorem solution (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] :
    DistCov.Indep.StrongNegType H := by
  refine ⟨(DistCov.Hilbert.hilbert_strict_negType H).1, ?_⟩
  intro μ ν hμ hν h₁ h₂ hD
  letI := hμ
  letI := hν
  obtain ⟨f⟩ := DistCovStrong.exists_l2_embedding H
  have hf : MeasurableEmbedding f := f.isometry.isClosedEmbedding.measurableEmbedding
  have hmp : IsProbabilityMeasure (μ.map f) := isProbabilityMeasure_map hf.measurable.aemeasurable
  have hnp : IsProbabilityMeasure (ν.map f) := isProbabilityMeasure_map hf.measurable.aemeasurable
  have he := DistCovStrong.strong_l2.2 (μ.map f) (ν.map f) hmp hnp
    (DistCovStrong.firstMoment_map f μ h₁) (DistCovStrong.firstMoment_map f ν h₂)
    (by rw [DistCovStrong.Ddiff_map f μ ν, hD])
  exact hf.map_injective he
#print axioms solution
