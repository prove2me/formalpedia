-- Prove2me | solution 1 for BianchiIX.volume_transverseAxisWallOrbitPreimage
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:37:28.912237+00:00
-- url     : https://prove2.me/submissions/bd564150-1ffa-40a8-81ac-bbbef5d35d30

import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Theorems.Thm_BianchiIX_exists_transverse_axisWall_arrival
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal

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

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.volume_fst_image_eq_zero_of_local_null {n : ℕ} {S : Set ((Fin n → ℝ) × ℝ)}
    (H : ∀ p ∈ S, ∃ V : Set ((Fin n → ℝ) × ℝ), IsOpen V ∧ p ∈ V ∧
      ∃ Z : Set (Fin n → ℝ), volume Z = 0 ∧ ∀ q ∈ S ∩ V, q.1 ∈ Z) :
    volume (Prod.fst '' S) = 0 := by
  classical
  by_cases hS : S.Nonempty
  · let : Nonempty S := hS.to_subtype
    choose V hVo hpV Z hZ hcover using (fun p : S => H p.val p.property)
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover V hVo
      (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩)
    apply measure_mono_null (t := ⋃ m : ℕ, Z (f m)) _ (measure_iUnion_null fun m => hZ (f m))
    rintro y ⟨p, hp, rfl⟩
    obtain ⟨m, hm⟩ := mem_iUnion.mp (hf hp)
    exact mem_iUnion.mpr ⟨m, hcover (f m) p ⟨hp, hm⟩⟩
  · simp only [Set.not_nonempty_iff_eq_empty.mp hS, image_empty, measure_empty]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallChart_negative {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) : mainWallChart h y 0 < 0 :=
  neg_neg_of_pos (Real.sqrt_pos.mpr hy)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallCoordinates_chart (h : ℝ) (y : SectionCoordinates) :
    mainWallCoordinates (mainWallChart h y) = y := by
  ext i
  fin_cases i <;> simp [mainWallCoordinates, mainWallChart]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.axisWallCoordinates_chart (A : NormalizedSymmetry) (h : ℝ) (y : SectionCoordinates) :
    axisWallCoordinates A (axisWallChart A h y) = y := by
  simp [axisWallCoordinates, axisWallChart, mainWallCoordinates_chart]

end
end


/-- A null wall target has null orbit preimage on every transverse chart, simultaneously for all existing times. -/
theorem solution (A : NormalizedSymmetry) {h t₀ : ℝ}
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hh : 0 < h) (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    {Z : Set SectionCoordinates} (hchart : Z ⊆ mainWallChartDomain h) (hZ : volume Z = 0) :
    volume (U ∩ transverseAxisWallOrbitPreimage C A h t₀ Z) = 0 := by
  let S : Set (SectionCoordinates × ℝ) := {p | p.1 ∈ U ∧
    p.2 ∈ normalizedMaxDomain (C p.1) t₀ ∧ ∃ z ∈ Z,
      axisWallChart A h z = normalizedMaxCurve (C p.1) t₀ p.2}
  have hlevel {p : SectionCoordinates × ℝ} (hpS : p ∈ S) :
      A.map (normalizedMaxCurve (C p.1) t₀ p.2) 2 = h := by
    obtain ⟨z, _, hz⟩ := hpS.2.2
    rw [← hz, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have htarget {p : SectionCoordinates × ℝ} (hpS : p ∈ S) :
      axisWallCoordinates A (normalizedMaxCurve (C p.1) t₀ p.2) ∈ Z := by
    obtain ⟨z, hz, heq⟩ := hpS.2.2
    rwa [← heq, axisWallCoordinates_chart]
  have hnull : volume (Prod.fst '' S) = 0 := by
    apply volume_fst_image_eq_zero_of_local_null
    intro p hpS
    have hneg : A.map (normalizedMaxCurve (C p.1) t₀ p.2) 0 < 0 := by
      obtain ⟨z, hz, heq⟩ := hpS.2.2
      rw [← heq, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
      exact mainWallChart_negative (hchart hz)
    obtain ⟨R, hR, hdet, hnear⟩ := exists_transverse_axisWall_arrival A (hC p.1 hpS.1)
      (hp p.1 hpS.1) ((show ∀ᶠ y in 𝓝 p.1, y ∈ U from hU.mem_nhds hpS.1).mono
        fun y hy => hc y hy) (hflux p.1 hpS.1) hpS.2.1 hh (hlevel hpS) hneg
    obtain ⟨W, hWo, hpW, hWnull⟩ := exists_local_null_preimage hR hdet
    have hfst : ∀ᶠ q : SectionCoordinates × ℝ in 𝓝 p, q.1 ∈ W :=
      continuousAt_fst.eventually (hWo.mem_nhds hpW)
    obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp (hnear.and hfst)
    refine ⟨V, hVo, hpV, W ∩ R ⁻¹' Z, hWnull Z hZ, ?_⟩
    intro q hq
    refine ⟨(hV hq.2).2, ?_⟩
    change R q.1 ∈ Z
    rw [(hV hq.2).1 (hlevel hq.1)]
    exact htarget hq.1
  apply measure_mono_null _ hnull
  rintro y ⟨hy, t, ht, z, hz, heq⟩
  exact ⟨(y, t), ⟨hy, ht, z, hz, heq⟩, rfl⟩
