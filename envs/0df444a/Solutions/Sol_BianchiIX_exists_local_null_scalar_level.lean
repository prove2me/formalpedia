-- Prove2me | solution 1 for BianchiIX.exists_local_null_scalar_level
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:05:26.470192+00:00
-- url     : https://prove2.me/submissions/cba19d64-7775-49dc-b053-89e9fcf15d61

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.exists_local_null_preimage {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 1 f x) (hdet : (fderiv ℝ f x).det ≠ 0) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧
      ∀ Z : Set (Fin n → ℝ), volume Z = 0 → volume (U ∩ f ⁻¹' Z) = 0 := by
  let L := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hdet
  have hd : HasFDerivAt f (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x := by
    rw [show (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = fderiv ℝ f x from
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  let g := hf.localInverse hd (by norm_num)
  have hg : ContDiffAt ℝ 1 g (f x) := hf.to_localInverse hd (by norm_num)
  have hleft : ∀ᶠ y in 𝓝 x, g (f y) = y := (hf.hasStrictFDerivAt' hd (by norm_num)).eventually_left_inverse
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (hg.eventually (by norm_num))
  obtain ⟨U, hU, hUo, hxU⟩ := mem_nhds_iff.mp
    ((hf.continuousAt.eventually (hVo.mem_nhds hxV)).and hleft)
  refine ⟨U, hUo, hxU, fun Z hZ => ?_⟩
  have hnull : volume (g '' (Z ∩ V)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun z hz => ((show ContDiffAt ℝ 1 g z from hV hz.2).differentiableAt
        (by norm_num)).differentiableWithinAt)
      (measure_mono_null inter_subset_left hZ)
  apply measure_mono_null _ hnull
  intro y hy
  exact ⟨f y, ⟨hy.2, (hU hy.1).1⟩, (hU hy.1).2⟩

end
end


/-- Replacing one coordinate by a scalar with a nonzero partial derivative gives a local null chart. -/
theorem solution {n : ℕ} {g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hg : ContDiffAt ℝ 1 g x) {i : Fin n}
    (hi : fderiv ℝ g x (Pi.single i 1) ≠ 0) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ volume (U ∩ {y | g y = 0}) = 0 := by
  classical
  let f : (Fin n → ℝ) → (Fin n → ℝ) := fun y j => if j = i then g y else y j
  let D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.pi
    (fun j => if j = i then fderiv ℝ g x else ContinuousLinearMap.proj j)
  have hf : ContDiffAt ℝ 1 f x := by
    apply contDiffAt_pi.mpr
    intro j
    by_cases hj : j = i
    · simpa [f, hj] using hg
    · simp only [f, hj, if_false]
      fun_prop
  have hd : HasFDerivAt f D x := by
    apply hasFDerivAt_pi.mpr
    intro j
    by_cases hj : j = i
    · simpa [f, D, hj] using (hg.differentiableAt (by norm_num)).hasFDerivAt
    · simpa [f, D, hj] using (hasFDerivAt_apply j x)
  have hker : LinearMap.ker D.toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hvj (j : Fin n) (hj : j ≠ i) : v j = 0 := by
      have H := congrFun hv j
      simpa [D, hj] using H
    have hvi : v = v i • Pi.single i (1 : ℝ) := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [Pi.single_eq_of_ne hj, hvj j hj]
    have H := congrFun hv i
    have H' : fderiv ℝ g x v = 0 := by simpa [D] using H
    rw [hvi, map_smul] at H'
    have hv0 : v i = 0 := (mul_eq_zero.mp H').resolve_right hi
    rw [hvi, hv0, zero_smul]
  have hdet : (fderiv ℝ f x).det ≠ 0 := by
    rw [hd.fderiv]
    exact fun H => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp H) hker
  obtain ⟨U, hU, hxU, H⟩ := exists_local_null_preimage hf hdet
  refine ⟨U, hU, hxU, ?_⟩
  have hnull : volume {z : Fin n → ℝ | z i = 0} = 0 :=
    Measure.pi_hyperplane (fun _ => (volume : Measure ℝ)) i 0
  convert H {z | z i = 0} hnull using 1
  simp [f]
