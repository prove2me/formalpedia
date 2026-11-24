-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.linear_form_integrality_on_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:27.707564+00:00
-- url     : https://prove2.me/submissions/6cad7164-0f7a-4447-8db2-c32e235e4e6b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : LinearFormIntegralityOnSupport := by
  intro q _ n n' fW f
  have swap : ∀ (x : Matrix (Fin n') (Fin n) ℤ) (l : Fin n → ℤ),
      ∑ i, fW i * ((x.mulVec l) i : ZMod q) = ∑ j, compF fW x j * (l j : ZMod q) := by
    intro x l
    simp only [compF, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
  constructor
  · intro x hx l hl η hη
    exact hη (x.mulVec l) (by rw [swap, hx]; exact hl)
  · intro hn hfW hf
    obtain ⟨i0, hi0⟩ : ∃ i, fW i ≠ 0 := by by_contra h; push Not at h; exact hfW (funext h)
    obtain ⟨j0, hj0⟩ : ∃ j, f j ≠ 0 := by by_contra h; push Not at h; exact hf (funext h)
    obtain ⟨j1, hj1⟩ : ∃ j : Fin n, j ≠ j0 := by
      by_cases h : (j0 : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, by intro h'; rw [← h'] at h; simp at h⟩
      · exact ⟨⟨0, by omega⟩, by intro h'; rw [← h'] at h; simp at h⟩
    have hq : (q:ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    refine ⟨fun i j => if i = i0 ∧ j = j1 then 1 else 0,
      fun j => if j = j1 then 1 else if j = j0 then -((f j1 / f j0 : ZMod q).val : ℤ) else 0,
      fun i => ((fW i).val : ℚ) / q, ?_, ?_, ?_⟩
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j1), ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hj1.symm, Finset.mem_univ j0⟩)]
      rw [Finset.sum_eq_zero]
      · simp [hj1.symm]; field_simp; ring
      · intro j hj
        simp only [Finset.mem_erase] at hj
        simp [hj.1, hj.2.1]
    · intro μ hμ
      have : ((∑ i, ((fW i).val : ℤ) * μ i : ℤ) : ZMod q) = 0 := by push_cast; simpa using hμ
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      obtain ⟨z, hz⟩ := this
      refine ⟨z, ?_⟩
      have h2 : (∑ i, ((fW i).val : ℚ) * (μ i : ℚ)) = (q:ℚ) * z := by exact_mod_cast hz
      have h3 : ∑ i, ((fW i).val : ℚ) / q * (μ i : ℚ) = (∑ i, ((fW i).val : ℚ) * (μ i : ℚ)) / q := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; ring
      rw [h3, h2]; field_simp
    · rintro ⟨z, hz⟩
      have hv : ∀ i, (Matrix.mulVec (fun i j => if i = i0 ∧ j = j1 then (1:ℤ) else 0 : Matrix (Fin n') (Fin n) ℤ)
          (fun j => if j = j1 then 1 else if j = j0 then -((f j1 / f j0 : ZMod q).val : ℤ) else 0)) i = if i = i0 then 1 else 0 := by
        intro i
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single j1]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      simp only [hv] at hz
      rw [Finset.sum_eq_single i0 (by intro i _ hi; simp [hi]) (by simp)] at hz
      simp only [if_true, Int.cast_one, mul_one] at hz
      have h4 : ((fW i0).val : ℚ) = (q:ℚ) * z := by rw [hz]; field_simp
      have h5 : ((fW i0).val : ℤ) = (q:ℤ) * z := by exact_mod_cast h4
      have h6 : ((((fW i0).val : ℤ)) : ZMod q) = 0 := by rw [h5]; simp
      apply hi0; simpa using h6
end Formalism.HermitianLattices.LocalLatticeBases
