-- Prove2me | solution 1 for FunctionalInequalities.Analysis.trace_integral_bound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:34.625059+00:00
-- url     : https://prove2.me/submissions/231d7d51-f60c-4879-92a2-819cfc87ee16

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
import Theorems.Thm_FunctionalInequalities_Analysis_forall_posDef_add_log_det_le_trace_iff_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_le_integral_mul_sum_iteratedFDeriv_readable
import Theorems.Thm_FunctionalInequalities_Analysis_expansion_secondDifference_readable

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12D8MollifiedLogdetBound
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
private lemma FunctionalInequalities.Analysis.matrix_quadratic_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin A v⟫ =
      ∑ i, ∑ j, v.ofLp i * (A i j * v.ofLp j) := by
  rw [Matrix.toLpLin_apply 2 2, PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
private lemma FunctionalInequalities.Analysis.trace_spectral_quadratic {n : ℕ}
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsHermitian)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (J * A).trace =
      ∑ i, hJ.eigenvalues i *
        ⟪hJ.eigenvectorBasis i, Matrix.toEuclideanLin A (hJ.eigenvectorBasis i)⟫ := by
  classical
  let U : Matrix (Fin n) (Fin n) ℝ := hJ.eigenvectorUnitary
  let D := Matrix.diagonal hJ.eigenvalues
  have hs : J = U * D * star U := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id_eq] using hJ.spectral_theorem
  have he (i : Fin n) :
      (star U * A * U) i i =
        ⟪hJ.eigenvectorBasis i, Matrix.toEuclideanLin A (hJ.eigenvectorBasis i)⟫ := by
    rw [matrix_quadratic_sum]
    simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Finset.sum_mul,
      U, Matrix.IsHermitian.eigenvectorUnitary_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    (J * A).trace = (U * D * star U * A).trace := by rw [hs]
    _ = (D * (star U * A) * U).trace := by
      rw [Matrix.mul_assoc U D (star U), Matrix.mul_assoc U (D * star U) A,
        Matrix.trace_mul_comm U ((D * star U) * A), Matrix.mul_assoc D (star U) A]
    _ = (D * (star U * A * U)).trace := by rw [Matrix.mul_assoc]
    _ = _ := by
      simp only [D, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, he]
set_option maxHeartbeats 800000 in
private lemma FunctionalInequalities.Analysis.second_weight_integrable {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => u y * iteratedFDeriv ℝ 2 χ y (fun _ => v)) volume := by
  let L := ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ (fun _ => v)
  have hc : Continuous (fun y => iteratedFDeriv ℝ 2 χ y (fun _ => v)) := by
    change Continuous (L ∘ iteratedFDeriv ℝ 2 χ)
    exact L.continuous.comp (ContDiff.continuous_iteratedFDeriv (by norm_num) hχ)
  have hs : HasCompactSupport (fun y => iteratedFDeriv ℝ 2 χ y (fun _ => v)) := by
    change HasCompactSupport (L ∘ iteratedFDeriv ℝ 2 χ)
    exact (hχc.iteratedFDeriv 2).comp_left (g := L) (map_zero L)
  exact (hu.mul hc).integrable_of_hasCompactSupport hs.mul_left
set_option maxHeartbeats 800000 in
 lemma solution {n : ℕ}
    {u F χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧
        F y ≤ Real.log B.det ∧ ∃ g : EuclideanSpace ℝ (Fin n),
          ∀ ε > 0, ∀ᶠ z in 𝓝 y,
            |u z - FunctionalInequalities.Analysis.quadraticAt B y g (u y) z| ≤ ε * ‖z - y‖ ^ 2)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ y, 0 ≤ χ y)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, Matrix.toEuclideanLin H v⟫ =
        ∫ y, u y * iteratedFDeriv ℝ 2 χ y (fun _ => v))
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.PosDef) :
    (∫ y, (F y + Real.log J.det + n) * χ y) ≤ (J * H).trace := by
  classical
  let v := hJ.isHermitian.eigenvectorBasis
  let c := hJ.isHermitian.eigenvalues
  have hc (i : Fin n) : 0 ≤ c i := (hJ.eigenvalues_pos i).le
  have hg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
        (F y + Real.log J.det + n) - ε ≤
          ∑ i, c i * ((u (y + t • v i) + u (y - t • v i) - 2 * u y) / t ^ 2) := by
    filter_upwards [hae] with y hy
    obtain ⟨B, _, hB, hFB, g, hexp⟩ := hy
    have hlim :
        Tendsto (fun t : ℝ => ∑ i, c i *
          ((u (y + t • v i) + u (y - t • v i) - 2 * u y) / t ^ 2))
          (𝓝[>] 0) (𝓝 ((J * B).trace)) := by
      rw [FunctionalInequalities.Analysis.trace_spectral_quadratic hJ.isHermitian B]
      exact tendsto_finsetSum _ fun i _ =>
        (FunctionalInequalities.Analysis.expansion_secondDifference_readable hexp (v i)).const_mul (c i)
    have htr : F y + Real.log J.det + n ≤ (J * B).trace :=
      ((FunctionalInequalities.Analysis.forall_posDef_add_log_det_le_trace_iff_readable hB.posSemidef (F y)).mpr
        ⟨hB, (Real.le_log_iff_exp_le hB.det_pos).mp hFB⟩) J hJ
    intro ε hε
    have hev := hlim.eventually_const_lt (show
      F y + Real.log J.det + n - ε < (J * B).trace by linarith)
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp hev
    refine ⟨δ, hδ, fun t ht htd => (hd ⟨?_, ht⟩).le⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htd
  have hi := FunctionalInequalities.Analysis.integral_mul_le_integral_mul_sum_iteratedFDeriv_readable hconv
    (fun i : Fin n => v i) hc hχ hχc hχ0
    ((hF.add continuous_const).add continuous_const).aestronglyMeasurable hg
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hdi (i : Fin n) := FunctionalInequalities.Analysis.second_weight_integrable hu hχ hχc (v i)
  have he :
      (∫ y, u y * ∑ i, c i * iteratedFDeriv ℝ 2 χ y (fun _ => v i)) =
        (J * H).trace := by
    calc
      _ = ∫ y, ∑ i, c i * (u y * iteratedFDeriv ℝ 2 χ y (fun _ => v i)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, c i * ∫ y, u y * iteratedFDeriv ℝ 2 χ y (fun _ => v i) := by
        rw [integral_finsetSum _ (fun i _ => (hdi i).const_mul (c i))]
        simp only [integral_const_mul]
      _ = _ := by
        rw [FunctionalInequalities.Analysis.trace_spectral_quadratic hJ.isHermitian H]
        apply Finset.sum_congr rfl
        intro i _
        rw [hH]
  exact he ▸ hi
