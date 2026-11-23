-- Prove2me | solution 1 for Bl.CurryModusPonens.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:05.867606+00:00
-- url     : https://prove2.me/submissions/8adf5fcb-93cf-41d7-b3b2-fe13b3c311e1

import Mathlib
import Definitions.Def_Lemmata_CurryModusPonens_CurryMp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_1 u_2
namespace Bl.CurryModusPonens
open MeasureTheory in
private lemma curry_mp {ι : Type u_1} {κ : Type u_2} {X : Type} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (Function.curry : (ι × κ → X) → ι → κ → X)
      (Measure.pi fun _ : ι × κ => μ) (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ) := by
  refine ⟨(MeasurableEquiv.curry ι κ X).measurable, ?_⟩
  have h : (Measure.pi fun _ : ι × κ => μ) =
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ).map (MeasurableEquiv.curry ι κ X).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [MeasurableEquiv.map_apply]
    have hpre : (MeasurableEquiv.curry ι κ X).symm ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f
      simp [MeasurableEquiv.coe_curry_symm, Set.mem_pi, Prod.forall]
    rw [hpre, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  rw [h]
  exact (MeasurableEquiv.curry ι κ X).map_map_symm
end Bl.CurryModusPonens
end

set_option autoImplicit false
universe u_1 u_2
open Bl Bl.CurryModusPonens
namespace Bl.CurryModusPonens
theorem _root_.solution :
  ∀ (ι : Type u_1) (κ : Type u_2) [inst : Fintype.{u_1} ι] [inst_1 : Fintype.{u_2} κ],
  @MeasureTheory.MeasurePreserving.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} ι κ → Complex) (ι → κ → Complex)
    (@MeasureTheory.MeasureSpace.toMeasurableSpace.{max u_1 u_2} (Prod.{u_1, u_2} ι κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{max u_1 u_2, 0} (Prod.{u_1, u_2} ι κ)
        (@instFintypeProd.{u_1, u_2} ι κ inst inst_1) (fun (a : Prod.{u_1, u_2} ι κ) ↦ Complex)
        fun (i : Prod.{u_1, u_2} ι κ) ↦
        @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
          Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace))
    (@MeasureTheory.MeasureSpace.toMeasurableSpace.{max u_1 u_2} (ι → κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{u_1, u_2} ι inst (fun (a : ι) ↦ κ → Complex) fun (i : ι) ↦
        @MeasureTheory.MeasureSpace.pi.{u_2, 0} κ inst_1 (fun (a : κ) ↦ Complex) fun (i : κ) ↦
          @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
            Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace))
    (@Function.curry.{u_1, u_2, 1} ι κ Complex)
    (@MeasureTheory.MeasureSpace.volume.{max u_1 u_2} (Prod.{u_1, u_2} ι κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{max u_1 u_2, 0} (Prod.{u_1, u_2} ι κ)
        (@instFintypeProd.{u_1, u_2} ι κ inst inst_1) (fun (a : Prod.{u_1, u_2} ι κ) ↦ Complex)
        fun (i : Prod.{u_1, u_2} ι κ) ↦
        @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
          Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace))
    (@MeasureTheory.MeasureSpace.volume.{max u_1 u_2} (ι → κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{u_1, u_2} ι inst (fun (a : ι) ↦ κ → Complex) fun (i : ι) ↦
        @MeasureTheory.MeasureSpace.pi.{u_2, 0} κ inst_1 (fun (a : κ) ↦ Complex) fun (i : κ) ↦
          @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
            Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace)) := by
  intro ι κ _ _
  exact curry_mp _
end Bl.CurryModusPonens
