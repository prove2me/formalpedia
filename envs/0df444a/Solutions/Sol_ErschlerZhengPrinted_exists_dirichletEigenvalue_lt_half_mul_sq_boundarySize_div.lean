-- Prove2me | solution 1 for ErschlerZhengPrinted.exists_dirichletEigenvalue_lt_half_mul_sq_boundarySize_div
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-04T11:37:13.83042+00:00
-- url     : https://prove2.me/submissions/d2f22f91-ed65-4e17-92fb-2f7b0da95fe7

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels

section
/-!
# D1F: the printed (5.1) fails (Erschler–Zheng p. 24)

Three states, `0` absorbing and `1 ↔ 2` swapping, `π ≡ 1`, `Ω = {0, 1}`: `|∂Ω| = 1`, `π(Ω) = 2`,
but `δ₀` has Dirichlet form `0`, so `λ₁(Ω) = 0 < 1/8`. Transplanted from
`erschler-zheng-mission/checks/lean/MarkovGuards.lean` (`printed_cheeger_fails`).
-/

open DurrettProbability MarkovChain

namespace ErschlerZhengPrinted

namespace D1F

noncomputable def P3 : Fin 3 → Fin 3 → ℝ := fun a b =>
  if (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then 1 else 0

lemma P3_nonneg (a b : Fin 3) : 0 ≤ P3 a b := by unfold P3; split_ifs <;> norm_num

lemma isTransition_P3 : IsTransition P3 :=
  ⟨P3_nonneg, fun _ => (hasSum_fintype _).summable, fun a => by
    rw [tsum_fintype]; fin_cases a <;> simp [P3]⟩

lemma isReversible_P3 : IsReversible P3 (fun _ => 1) := by
  intro a b; fin_cases a <;> fin_cases b <;> simp [P3]

end D1F

end ErschlerZhengPrinted
end

section
open DurrettProbability MarkovChain
open ErschlerZhengPrinted
open D1F in
theorem solution :
    ∃ (P : Fin 3 → Fin 3 → ℝ) (π : Fin 3 → ℝ) (Ω : Finset (Fin 3)),
      IsTransition P ∧ (∀ x, 0 < π x) ∧ IsReversible P π ∧ Ω.Nonempty ∧
        dirichletEigenvalue P π Ω < 1 / 2 * (boundarySize P π Ω / ∑ x ∈ Ω, π x) ^ 2 := by
  refine ⟨P3, fun _ => 1, {0, 1}, isTransition_P3, fun _ => one_pos, isReversible_P3,
    by simp, ?_⟩
  have hb : boundarySize P3 (fun _ => 1) {0, 1} = 1 := by
    simp only [boundarySize, one_mul]
    rw [Finset.sum_pair (by decide)]
    rw [tsum_fintype, tsum_fintype,
      ← Finset.sum_subtype (Finset.univ.filter (· ∉ ({0, 1} : Finset (Fin 3)))) (by simp),
      ← Finset.sum_subtype (Finset.univ.filter (· ∉ ({0, 1} : Finset (Fin 3)))) (by simp)]
    have hf : Finset.univ.filter (· ∉ ({0, 1} : Finset (Fin 3))) = {2} := by decide
    rw [hf]; simp [P3]
  have hl : dirichletEigenvalue P3 (fun _ => 1) {0, 1} ≤ 0 := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro e ⟨f, -, -, rfl⟩
      unfold dirichletForm
      exact mul_nonneg (by norm_num) (tsum_nonneg fun p =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (P3_nonneg _ _)) zero_le_one)
    · refine ⟨fun x => if x = 0 then 1 else 0, ?_, ?_, ?_⟩
      · intro x hx; fin_cases x <;> simp_all
      · simp [normSq, tsum_fintype]
      · simp [dirichletForm, tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_three, P3]
  rw [hb]
  have : (∑ x ∈ ({0, 1} : Finset (Fin 3)), (fun _ => (1 : ℝ)) x) = 2 := by
    rw [Finset.sum_pair (by decide)]; norm_num
  rw [this]
  linarith
end
