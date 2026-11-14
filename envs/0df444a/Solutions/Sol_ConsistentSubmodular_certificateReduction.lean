-- Prove2me | solution 1 for ConsistentSubmodular.certificateReduction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:46:50.391922+00:00
-- url     : https://prove2.me/submissions/fdac4bf5-f266-4521-bc5e-7a14692ccf33

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ArrivalEncoding
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RecourseBound
import Theorems.Thm_ConsistentSubmodular_RoundedWindowFamily_assemble
import Theorems.Thm_ConsistentSubmodular_guarantee_of_uniform_programs
import Theorems.Thm_ConsistentSubmodular_uniformRoundedFamilies
import Theorems.Thm_ConsistentSubmodular_accuracy_slack
import Theorems.Thm_ConsistentSubmodular_reductionRecourse_rate

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

theorem natAdd_notMem_encodedArrivals (j : Fin W.lastStage) :
    Fin.natAdd n j ∉ W.encodedArrivals j.castSucc := by
  intro hx
  simp only [encodedArrivals, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.natAddEmb_apply, Fin.val_castSucc] at hx
  obtain ⟨a, ha, hax⟩ := hx
  have hv := congrArg Fin.val hax
  simp only [Fin.val_natAdd] at hv
  omega

theorem encodedArrivals_succ (j : Fin W.lastStage) :
    W.encodedArrivals j.succ = insert (Fin.natAdd n j) (W.encodedArrivals j.castSucc) := by
  ext x
  simp only [encodedArrivals, Finset.mem_insert, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.natAddEmb_apply, Fin.val_succ, Fin.val_castSucc]
  constructor
  · rintro ⟨a, ha, hax⟩
    by_cases haj : a.val = j.val
    · left
      rw [← hax, show a = j from Fin.ext haj]
    · right
      exact ⟨a, by omega, hax⟩
  · rintro (hx | ⟨a, ha, hax⟩)
    · exact ⟨j, by omega, hx.symm⟩
    · exact ⟨a, by omega, hax⟩

theorem encode_singleArrivals : W.encode.SingleArrivals :=
  fun j => ⟨Fin.natAdd n j, W.natAdd_notMem_encodedArrivals j, W.encodedArrivals_succ j⟩

end WindowInstance

/-- Certificates for all single-arrival windows give certificates for all
windows, with the same level and segment budget. -/
theorem admitsCertificates_of_arrivals {α : ℝ} {L : ℕ → ℕ}
    (h : AdmitsArrivalCertificates α L) : AdmitsCertificates α L :=
  fun _ W => (h _ W.encode W.encode_singleArrivals).map WindowInstance.Certificate.ofEncode

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

theorem TransferParameters.list_fits {N H k : ℕ} (p : TransferParameters N H k) (L : ℕ) :
    L * p.core ≤ (4 * N * p.candidates * L) * p.interval := by
  have h := Nat.mul_le_mul_left L (p.core_le.trans p.enough_time)
  nlinarith

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

/-- A level at most the slack needs no recourse: the empty trajectory meets it. -/
theorem consistentGuarantee_of_le_slack {α ε : ℝ} (h : α ≤ ε) (R : ℕ) :
    ConsistentGuarantee α ε R := by
  intro n k f
  refine ⟨fun _ => ∅, ⟨rfl, fun _ => ⟨Finset.empty_subset _, by simp⟩,
    fun _ => by simp [recourse]⟩, ?_⟩
  intro t A _ _
  have hA := f.nonnegative A
  have h0 := f.nonnegative ∅
  nlinarith

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

theorem uniform_programs_of_rounded_families {α : ℝ} {N H L : ℕ}
    (h : HasUniformRoundedFamilies α N H L) :
    HasUniformPrograms α N H (4 * N * (4 * N + 1) * (3 * L + 1)) := by
  intro n k f p
  obtain ⟨W, ⟨T⟩⟩ := h n k f p
  apply W.assemble T (by omega)
  have hh := p.list_fits (3 * L + 1)
  rwa [p.candidates_eq] at hh

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

theorem accuracy_ge (ε : ℝ) : 200 ≤ accuracy ε := Nat.le_add_left _ _

theorem rateConstant_nonneg (C : ℕ) : 0 ≤ rateConstant C := by
  unfold rateConstant
  have h : 0 ≤ Real.log (1200 * ((C : ℝ) + 1)) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    nlinarith)
  positivity

theorem reductionConstant_nonneg (C : ℕ) : 0 ≤ reductionConstant C := by
  unfold reductionConstant
  have := rateConstant_nonneg C
  positivity

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace Reduction

/-- Certificates at level `α` give an `(α - ε)`-approximation whose recourse
depends only on the accuracy and on the segment budget, not on `α`. -/
theorem guarantee_of_certificates (O : CertificateFamily) {ε : ℝ} {N : ℕ} (hN : 200 ≤ N)
    (hNε : 20 * ((1 : ℝ) / N) < ε) :
    ConsistentGuarantee O.level ε (reductionRecourse N (O.budget (3 * N + 1))) :=
  guarantee_of_uniform_programs hN O.level_le hNε
    (uniform_programs_of_rounded_families (uniformRoundedFamilies O N hN))

/-- Theorem 5 (reduction from consistency to clairvoyant certificates), with
consistency `O(ε⁻³ log(1/ε))`. For `ε ≥ 3/4` every level is at most the slack,
so no recourse is needed. -/
theorem certificateReduction : CertificateReductionGoal := by
  intro C
  refine ⟨reductionConstant C, fun ε hε hε1 => ?_⟩
  by_cases hεα : ε < 3 / 4
  · refine ⟨reductionRecourse (accuracy ε) ((C + 1) * (3 * accuracy ε + 2)),
      reductionRecourse_rate C hε hεα, ?_⟩
    intro α hα0 hα harrivals
    have hcert := admitsCertificates_of_arrivals harrivals
    let O : CertificateFamily := {
      level := α
      budget := fun m => (C + 1) * (m + 1)
      level_nonneg := hα0.le
      level_le := hα
      budget_pos := fun m => by positivity
      certificates := fun n W =>
        (hcert n W).map (fun Z => Z.mono (Nat.mul_le_mul_right _ (Nat.le_succ C))) }
    exact guarantee_of_certificates O (accuracy_ge ε) (accuracy_slack hε)
  · refine ⟨0, ?_, fun α _ hα _ => consistentGuarantee_of_le_slack (by linarith) 0⟩
    have hlog : 0 ≤ Real.log (1 / ε) :=
      Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    have hK := reductionConstant_nonneg C
    have hpow : 0 ≤ (1 / ε) ^ 3 := pow_nonneg (div_nonneg zero_le_one hε.le) 3
    push_cast
    positivity

end Reduction

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution : CertificateReductionGoal :=
  Reduction.certificateReduction

end
