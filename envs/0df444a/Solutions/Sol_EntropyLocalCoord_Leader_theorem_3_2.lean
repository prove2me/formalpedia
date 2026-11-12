-- Prove2me | solution 1 for EntropyLocalCoord.Leader.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:35.006734+00:00
-- url     : https://prove2.me/submissions/f3126e4a-7444-4a89-8814-7eb59cc790a9

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model
import Theorems.Thm_EntropyLocalCoord_Leader_ileader_le_entropy_cost
import Theorems.Thm_EntropyLocalCoord_Leader_ineff_chain

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace EntropyLocalCoord.Dev.Thm32

open EntropyLocalCoord.Leader

/-- any profile: the sigma algebra is below the ambient one. -/
lemma sourceSigma_le {n k : ℕ} {S : InformationSkeleton n k} (π : CoordinationProfile S)
    (i : Fin n) : sourceSigma π.Z (S.B i) ≤ π.mΩ := by
  refine iSup₂_le fun j _ => ?_
  exact (π.Z_measurable j).comap_le

lemma memLp_two {n k : ℕ} {S : InformationSkeleton n k} (π : CoordinationProfile S) (i : Fin n) :
    MemLp (π.X i) 2 π.P := by
  have hm : Measurable (π.X i) := (π.X_measurable i).mono (sourceSigma_le π i) le_rfl
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  by_contra h
  have := π.second_moment i
  rw [integral_undef h] at this
  exact zero_ne_one this

lemma cov_le_one {n k : ℕ} {S : InformationSkeleton n k} (π : CoordinationProfile S)
    (i j : Fin n) : π.cov i j ≤ 1 := by
  have hi := memLp_two π i
  have hj := memLp_two π j
  have hii : Integrable (fun ω => π.X i ω ^ 2) π.P := (memLp_two_iff_integrable_sq
    (((π.X_measurable i).mono (sourceSigma_le π i) le_rfl).aestronglyMeasurable)).1 hi
  have hjj : Integrable (fun ω => π.X j ω ^ 2) π.P := (memLp_two_iff_integrable_sq
    (((π.X_measurable j).mono (sourceSigma_le π j) le_rfl).aestronglyMeasurable)).1 hj
  have hij : Integrable (π.X i * π.X j) π.P := hi.integrable_mul hj
  unfold CoordinationProfile.cov
  rw [covariance_eq_sub hi hj, π.mean_zero i]
  simp only [zero_mul, sub_zero]
  have : ∫ ω, (π.X i * π.X j) ω ∂π.P ≤ ∫ ω, (π.X i ω ^ 2 + π.X j ω ^ 2) / 2 ∂π.P := by
    refine integral_mono hij ((hii.add hjj).div_const 2) fun ω => ?_
    simp only [Pi.mul_apply]
    nlinarith [sq_nonneg (π.X i ω - π.X j ω)]
  have h2 : ∫ ω, (π.X i ω ^ 2 + π.X j ω ^ 2) / 2 ∂π.P = 1 := by
    rw [integral_div, integral_add hii hjj, π.second_moment i, π.second_moment j]; norm_num
  have : (∫ ω, π.X i ω * π.X j ω ∂π.P) ≤ 1 := by simpa [h2] using this
  simpa using this

/-- Cost is nonnegative for any profile. -/
theorem cost_nonneg {n k : ℕ} {S : InformationSkeleton n k} (G : SimpleGraph (Fin n))
    (π : CoordinationProfile S) : 0 ≤ cost G π := by
  unfold cost
  refine div_nonneg (Finset.sum_nonneg fun e _ => ?_) (Nat.cast_nonneg _)
  induction e using Sym2.ind with
  | _ i j =>
    simp only [CoordinationProfile.edgeLoss, Sym2.lift_mk]
    linarith [cov_le_one π i j]

lemma h_cont : Continuous h := by
  unfold h
  exact Real.binEntropy_continuous.div_const _

end EntropyLocalCoord.Dev.Thm32

open EntropyLocalCoord.Leader EntropyLocalCoord.Dev.Thm32 in
theorem EntropyLocalCoord.Leader.chk_theorem_3_2 {n k : ℕ} (G : SimpleGraph (Fin n))
    (S : InformationSkeleton n k) :
    Ileader G S ≤ 2 * h (1 / 2 * Ibin G S) := by
  classical
  obtain ⟨⟨π0, hπ0, _⟩, _, _, _⟩ := ineff_chain G S
  have hne : {c | ∃ π : CoordinationProfile S, π.IsBinary ∧ cost G π = c}.Nonempty :=
    ⟨_, π0, hπ0.1, rfl⟩
  have hbdd : BddBelow {c | ∃ π : CoordinationProfile S, π.IsBinary ∧ cost G π = c} :=
    ⟨0, by rintro c ⟨π', _, rfl⟩; exact cost_nonneg G π'⟩
  have hmem : Ibin G S ∈ closure {c | ∃ π : CoordinationProfile S, π.IsBinary ∧ cost G π = c} :=
    csInf_mem_closure hne hbdd
  have hclosed : IsClosed {c : ℝ | Ileader G S ≤ 2 * h (1 / 2 * c)} :=
    isClosed_le continuous_const (continuous_const.mul
      (h_cont.comp (continuous_const.mul continuous_id)))
  have hsub : {c | ∃ π : CoordinationProfile S, π.IsBinary ∧ cost G π = c} ⊆
      {c : ℝ | Ileader G S ≤ 2 * h (1 / 2 * c)} := by
    rintro c ⟨π, hπ, rfl⟩
    exact ileader_le_entropy_cost G S π hπ
  exact closure_minimal hsub hclosed hmem
end

theorem solution : type_of% @EntropyLocalCoord.Leader.chk_theorem_3_2 := @EntropyLocalCoord.Leader.chk_theorem_3_2
