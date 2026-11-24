-- Prove2me | solution 1 for Formalism.G0.DetDividesP.red_of_valGE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:59.131802+00:00
-- url     : https://prove2.me/submissions/45599557-c0cf-4614-a38e-0a37aeb575c7

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_msMat_mul_nMat
import Theorems.Thm_Formalism_G0_DetDividesP_msDualMat_mul_msMat_transpose
import Theorems.Thm_Formalism_G0_DetDividesP_aeval_set_scale
import Theorems.Thm_Formalism_G0_DetDividesP_sum_sum_mat
import Theorems.Thm_Formalism_G0_DetDividesP_sum_smul_one
import Theorems.Thm_Formalism_G0_DetDividesP_sum_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (_hr : 0 < r) (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (d : ι → ℕ)
    (G : MvPolynomial (ι × Fin r) K) (th : ℕ)
    (hAS : ∀ l, A l ∈ S ∧ vec (A l) = true) (hG : MultiHom G d) (hV : ValGE vec S d G th)
    (hB : (∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) < th) :
    Red A G (th - ∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) := by
  classical
  intro L _ _ g x hx
  have hv := hV L g
  let y : ι × Fin r → L[X] := fun p =>
    if p.1 ∈ S then
      (if vec p.1 then
        (if p.1 ∈ Set.range A then C (x p) else ∑ c, nMat g p.2 c * C (x (p.1, c)))
       else ∑ c, (msMat g).transpose p.2 c * C (x (p.1, c)))
    else C (x p)
  let ev : MvPolynomial (ι × Fin r) L[X] →ₐ[K] L[X] := (MvPolynomial.aeval y).restrictScalars K
  have h1 := map_dvd ev hv
  have hC : ev (MvPolynomial.C (X ^ (th + ∑ i ∈ S.filter (fun i => vec i = false), d i))) =
      X ^ (th + ∑ i ∈ S.filter (fun i => vec i = false), d i) := by
    simp [ev]
  have hsub : ev (substS (K := K) vec S g G) = MvPolynomial.aeval
      (fun p => if p.1 ∈ S.filter (fun i => i ∉ Set.range A) then X * ptA A g x p else ptA A g x p) G := by
    unfold substS
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    refine congrArg (fun f => MvPolynomial.aeval f G) ?_
    funext p
    obtain ⟨i, a⟩ := p
    have hev : ∀ (M : Matrix (Fin r) (Fin r) L[X]),
        ev (∑ b, MvPolynomial.C (M a b) * MvPolynomial.X (i, b)) = ∑ b, M a b * y (i, b) := by
      intro M
      simp only [ev, map_sum, map_mul, AlgHom.restrictScalars_apply, MvPolynomial.aeval_C,
        MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
    by_cases hS : i ∈ S
    · by_cases hvi : vec i = true
      · simp only [if_pos hS, if_pos hvi]
        rw [hev]
        by_cases hA : i ∈ Set.range A
        · have hy : ∀ b, y (i, b) = C (x (i, b)) := fun b => by
            simp only [y, if_pos hS, if_pos hvi, if_pos hA]
          have hU : i ∉ S.filter (fun i => i ∉ Set.range A) := by
            simp only [Finset.mem_filter, hA, not_true_eq_false, and_false, not_false_eq_true]
          simp only [hy, if_neg hU, ptA, if_pos hA]
        · have hy : ∀ b, y (i, b) = ∑ c, nMat g b c * C (x (i, c)) := fun b => by
            simp only [y, if_pos hS, if_pos hvi, if_neg hA]
          have hU : i ∈ S.filter (fun i => i ∉ Set.range A) := by
            simp only [Finset.mem_filter, hA, hS, not_false_eq_true, and_self]
          simp only [hy, if_pos hU, ptA, if_neg hA]
          rw [sum_sum_mat, msMat_mul_nMat, sum_smul_one]
      · have hA : i ∉ Set.range A := by
          rintro ⟨l, rfl⟩; exact hvi (hAS l).2
        simp only [if_pos hS, if_neg hvi]
        rw [hev]
        have hy : ∀ b, y (i, b) = ∑ c, (msMat g).transpose b c * C (x (i, c)) := fun b => by
          simp only [y, if_pos hS, if_neg hvi]
        have hU : i ∈ S.filter (fun i => i ∉ Set.range A) := by
          simp only [Finset.mem_filter, hA, hS, not_false_eq_true, and_self]
        simp only [hy, if_pos hU, ptA, if_neg hA]
        rw [sum_sum_mat, msDualMat_mul_msMat_transpose, sum_smul_one]
    · have hA : i ∉ Set.range A := by
        rintro ⟨l, rfl⟩; exact hS (hAS l).1
      have hU : i ∉ S.filter (fun i => i ∉ Set.range A) := by
        simp only [Finset.mem_filter, hS, false_and, not_false_eq_true]
      simp only [if_neg hS, if_neg hU, ptA, if_neg hA, ev, AlgHom.restrictScalars_apply,
        MvPolynomial.aeval_X, y]
  rw [hC, hsub, aeval_set_scale hG, sum_split vec S A d hAS] at h1
  have he : th + ∑ i ∈ S.filter (fun i => vec i = false), d i =
      ((∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) +
        ∑ i ∈ S.filter (fun i => vec i = false), d i) +
      (th - ∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) := by omega
  rw [he, pow_add] at h1
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ X_ne_zero)).mp h1
end Formalism.G0.DetDividesP
