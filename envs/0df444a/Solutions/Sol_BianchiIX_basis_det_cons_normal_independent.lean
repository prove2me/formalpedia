-- Prove2me | solution 1 for BianchiIX.basis_det_cons_normal_independent
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:43:27.014714+00:00
-- url     : https://prove2.me/submissions/928e8c3e-ae91-4401-bfbb-71a11311f76a

import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace BianchiIX
end BianchiIX

section
noncomputable section
open BianchiIX
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]

private theorem BianchiIX.basis_det_zero_of_covector (b : Module.Basis ι ℝ E) {l : E →ₗ[ℝ] ℝ}
    (hl : l ≠ 0) {v : ι → E} (hv : ∀ i, l (v i) = 0) : b.det v = 0 := by
  by_contra hdet
  have hspan := ((b.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr hdet)).2
  have hker : Submodule.span ℝ (Set.range v) ≤ LinearMap.ker l :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv i)
  apply hl
  ext x
  exact hker (by rw [hspan]; trivial)

end
end

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]


/-- Contraction to a regular level set is independent of the normalized transverse vector. -/
theorem solution {n : ℕ} (b : Module.Basis (Fin (n + 1)) ℝ E)
    {l : E →ₗ[ℝ] ℝ} {X Y : E} {v : Fin n → E}
    (hX : l X = 1) (hY : l Y = 1) (hv : ∀ i, l (v i) = 0) :
    b.det (Fin.cons Y v) = b.det (Fin.cons X v) := by
  have hl : l ≠ 0 := by intro hz; simp [hz] at hX
  have hz : b.det (Fin.cons (Y - X) v) = 0 := by
    apply basis_det_zero_of_covector b hl
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hX, hY]
    · exact hv j
  have H := b.det.map_update_add (Fin.cons X v) 0 (Y - X) X
  simpa only [Fin.update_cons_zero, sub_add_cancel, hz, zero_add] using H
