-- Prove2me | solution 1 for BookProof.BrstLeakage.norm_flow_sub_flow_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:44:31.507415+00:00
-- url     : https://prove2.me/submissions/be9daed8-65c4-4e6b-8c7d-bed00d70a488

-- Generated from ChapterBrstTruncationLeakage.lean — solution of BookProof.BrstLeakage.norm_flow_sub_flow_apply_le
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
import Theorems.Thm_BookProof_BrstLeakage_norm_flow_apply
import Theorems.Thm_BookProof_BrstLeakage_hasDerivAt_duhamel
open BookProof.BrstLeakage



open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (t : ℝ) (ht : 0 ≤ t) (x : E) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖(A - B) (flow B s x)‖ ≤ K) :
    ‖flow B t x - flow A t x‖ ≤ K * t := by

  set X : E →L[ℂ] E := (-Complex.I) • A with hXdef
  set Y : E →L[ℂ] E := (-Complex.I) • B with hYdef
  set g : ℝ → E := fun u => (exp ((t - u) • X)) ((exp (u • Y)) x) with hg
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt g ((exp ((t - s) • X)) ((Y - X) ((exp (s • Y)) x))) (Set.Icc 0 t) s :=
    fun s _ => (hasDerivAt_duhamel X Y t s x).hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t,
      ‖(exp ((t - s) • X)) ((Y - X) ((exp (s • Y)) x))‖ ≤ K := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1, hs.2.le⟩
    have h1 : ‖(exp ((t - s) • X)) ((Y - X) ((exp (s • Y)) x))‖ = ‖(Y - X) (flow B s x)‖ := by
      have := norm_flow_apply hA (t - s) ((Y - X) ((exp (s • Y)) x))
      simpa [flow, hXdef, hYdef] using this
    have h2 : (Y - X) (flow B s x) = (-Complex.I) • ((B - A) (flow B s x)) := by
      simp [hXdef, hYdef, ContinuousLinearMap.sub_apply, smul_sub]
    have h3 : ‖(Y - X) (flow B s x)‖ = ‖(A - B) (flow B s x)‖ := by
      rw [h2]
      simp [norm_smul, ContinuousLinearMap.sub_apply, ← norm_neg (A (flow B s x) - _)]
    rw [h1, h3]
    exact hK s hs'
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound t
    (Set.right_mem_Icc.mpr ht)
  have hgt : g t = flow B t x := by simp [hg, flow, hYdef]
  have hg0 : g 0 = flow A t x := by simp [hg, flow, hXdef]
  rw [hgt, hg0] at hmvt
  simpa using hmvt
