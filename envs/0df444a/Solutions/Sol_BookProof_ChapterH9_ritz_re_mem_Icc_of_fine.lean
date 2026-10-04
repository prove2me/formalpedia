-- Prove2me | solution 1 for BookProof.ChapterH9.ritz_re_mem_Icc_of_fine
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:36:54.375797+00:00
-- url     : https://prove2.me/submissions/f323f5c5-198c-40e7-a02a-cca0e67969b2

import Definitions.Def_ChapterH4

open BookProof.ChapterH4 ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hJiso : ∀ x : F, ‖J x‖ = ‖x‖)
    {lam : ℂ} {y : F} (hy : ‖y‖ = 1) (heig : compress Vn X y = lam • y)
    {a b : ℝ} (hlow : ∀ x : G, ‖x‖ = 1 → a ≤ (inner ℂ x (compress Vm X x) : ℂ).re)
    (hhigh : ∀ x : G, ‖x‖ = 1 → (inner ℂ x (compress Vm X x) : ℂ).re ≤ b) :
    a ≤ lam.re ∧ lam.re ≤ b := by
  have hnorm : ‖J y‖ = 1 := (hJiso y).trans hy
  have hq : inner ℂ (J y) (compress Vm X (J y)) = lam := by
    calc
      inner ℂ (J y) (compress Vm X (J y)) = inner ℂ y (compress Vn X y) := by
        simp only [hJ, compress, adjoint_comp, comp_apply, adjoint_inner_right]
      _ = lam := by
        rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K, hy]
        simp
  simpa only [hq] using And.intro (hlow (J y) hnorm) (hhigh (J y) hnorm)

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
