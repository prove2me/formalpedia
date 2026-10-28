-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_lipschitzWith_weak_fderiv_comp_gradient_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:28.114998+00:00
-- url     : https://prove2.me/submissions/8584b0b5-d096-420f-a95f-234a2c9f5489

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_congr_ae_readable
import Theorems.Thm_FunctionalInequalities_Analysis_ae_fderiv_mongeAmpere_exponent_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_lipschitzWith_neg_add_comp_gradient_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_lipschitz_readable

noncomputable section
section WeakCoordinateComposition
open MeasureTheory Set
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
/-- Closed composition of the existing negative-exponent result with the
original Lipschitz potential. A local helper, not a new public interface. -/
private theorem FunctionalInequalities.Analysis.exists_lipschitz_comp_gradient {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hULip : LipschitzWith L u) (hGradLip : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∃ C : NNReal, LipschitzWith C (fun x => V (gradient u x)) := by
  obtain ⟨LF, hNegCompLip⟩ :=
    exists_lipschitzWith_neg_add_comp_gradient_readable hULip hGradLip hV
  have hSum := hNegCompLip.add hULip
  change LipschitzWith (LF + L) (fun x => (-u x + V (gradient u x)) + u x) at hSum
  have hCancel : (fun x => (-u x + V (gradient u x)) + u x) =
      (fun x => V (gradient u x)) := by
    funext x
    ring
  rw [hCancel] at hSum
  exact ⟨LF + L, hSum⟩
/-- The scalar derivative bound and compact-local L2 calculation already used
by the accepted Piola-row consumer, with an arbitrary Lipschitz scalar f. -/
private theorem FunctionalInequalities.Analysis.memLp_coordinate_fderiv_of_lipschitz {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {C : NNReal}
    (hLip : LipschitzWith C f) (j : Fin n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ j))
      2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hMeas : Measurable (fun x => fderiv ℝ f x (e j)) :=
    (show Continuous (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A (e j)) from
      continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ f)
  have hBound (x : EuclideanSpace ℝ (Fin n)) : ‖fderiv ℝ f x (e j)‖ ≤ (C : ℝ) := by
    have hEval := (fderiv ℝ f x).le_opNorm (e j)
    rw [e.norm_eq_one j, mul_one] at hEval
    exact hEval.trans (norm_fderiv_le_of_lipschitz ℝ hLip)
  exact MemLp.of_bound hMeas.aestronglyMeasurable (C : ℝ)
    (Filter.Eventually.of_forall hBound)
set_option maxHeartbeats 800000 in
/-- Actual weak derivative of a smooth coordinate derivative composed with a
C1 potential's Lipschitz gradient. Supporting component for weak Letwin (2.6). -/
theorem solution {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hULip : LipschitzWith L u)
    (hGradLip : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (a : Fin n) :
    ∃ C : NNReal,
      LipschitzWith C (fun x => fderiv ℝ W (gradient u x)
        (EuclideanSpace.basisFun (Fin n) ℝ a)) ∧
      ∀ j : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong
          (fun x => fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
          (fun x => ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp
            (fun x => ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let V : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => fderiv ℝ W z (EuclideanSpace.basisFun (Fin n) ℝ a)
  have hV : ContDiff ℝ 1 V := by
    change ContDiff ℝ 1
      (fun z => fderiv ℝ W z (EuclideanSpace.basisFun (Fin n) ℝ a))
    exact (hW.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  obtain ⟨C, hCompLip⟩ :=
    FunctionalInequalities.Analysis.exists_lipschitz_comp_gradient hULip hGradLip hV
  have hCoord (z : EuclideanSpace ℝ (Fin n)) (b : Fin n) :
      fderiv ℝ V z (EuclideanSpace.basisFun (Fin n) ℝ b) =
        FunctionalInequalities.Probability.Stein.hessianMatrix W z b a := by
    change fderiv ℝ
        (fun y => fderiv ℝ W y (EuclideanSpace.basisFun (Fin n) ℝ a)) z
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      bilinearIteratedFDerivTwo ℝ W z
        (EuclideanSpace.basisFun (Fin n) ℝ b)
        (EuclideanSpace.basisFun (Fin n) ℝ a)
    exact
      (FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply
        hW z (EuclideanSpace.basisFun (Fin n) ℝ b)
        (EuclideanSpace.basisFun (Fin n) ℝ a)).symm
  refine ⟨C, ?_, ?_⟩
  · simpa only [V] using hCompLip
  · intro j
    constructor
    · change FunctionalInequalities.Analysis.HasWeakDerivAlong
        (fun x => V (gradient u x))
        (fun x => ∑ b : Fin n,
          FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
        (EuclideanSpace.basisFun (Fin n) ℝ j)
      have hExp :=
        FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_readable
          hu hGradLip hV
      have hDiffComp :
          ∀ᵐ x : EuclideanSpace ℝ (Fin n)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            DifferentiableAt ℝ (fun y => V (gradient u y)) x :=
        hCompLip.ae_differentiableAt (μ := volume)
      have hAe :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n)))]
            (fun x => ∑ b : Fin n,
              FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a) := by
        filter_upwards [hExp, hDiffComp] with x hxExp hxComp
        have hux : DifferentiableAt ℝ u x :=
          hu.differentiable one_ne_zero x
        have hsum :=
          hux.hasFDerivAt.neg.add hxComp.hasFDerivAt
        have hEval := congrArg
          (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
            A (EuclideanSpace.basisFun (Fin n) ℝ j))
          hsum.fderiv
        have hfun :
            (-u + (fun y => V (gradient u y))) =
              (fun y => -u y + V (gradient u y)) := by
          funext y
          rfl
        rw [hfun] at hEval
        have heval :
            fderiv ℝ (fun y => -u y + V (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ j) =
              -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
                fderiv ℝ (fun y => V (gradient u y)) x
                  (EuclideanSpace.basisFun (Fin n) ℝ j) := by
          simpa only [neg_apply, add_apply] using hEval
        have hSum :
            (∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
              fderiv ℝ V (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ b)) =
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
                FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a := by
          apply Finset.sum_congr rfl
          intro b _
          rw [hCoord]
        have hxExp' := hxExp j
        rw [hSum] at hxExp'
        linarith [heval, hxExp']
      have hWeakClassical :
          FunctionalInequalities.Analysis.HasWeakDerivAlong
            (fun x => V (gradient u x))
            (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j))
            (EuclideanSpace.basisFun (Fin n) ℝ j) :=
        FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_readable hCompLip
          (EuclideanSpace.basisFun (Fin n) ℝ j)
      exact hWeakClassical.congr_ae_readable
        (Filter.Eventually.of_forall (fun x => rfl)) hAe
    · intro S hS
      have hClassicalL2 :=
        FunctionalInequalities.Analysis.memLp_coordinate_fderiv_of_lipschitz hCompLip j S hS
      have hExp :=
        FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_readable
          hu hGradLip hV
      have hDiffComp :
          ∀ᵐ x : EuclideanSpace ℝ (Fin n)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            DifferentiableAt ℝ (fun y => V (gradient u y)) x :=
        hCompLip.ae_differentiableAt (μ := volume)
      have hAe :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n)))]
            (fun x => ∑ b : Fin n,
              FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a) := by
        filter_upwards [hExp, hDiffComp] with x hxExp hxComp
        have hux : DifferentiableAt ℝ u x :=
          hu.differentiable one_ne_zero x
        have hsum :=
          hux.hasFDerivAt.neg.add hxComp.hasFDerivAt
        have hEval := congrArg
          (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
            A (EuclideanSpace.basisFun (Fin n) ℝ j))
          hsum.fderiv
        have hfun :
            (-u + (fun y => V (gradient u y))) =
              (fun y => -u y + V (gradient u y)) := by
          funext y
          rfl
        rw [hfun] at hEval
        have heval :
            fderiv ℝ (fun y => -u y + V (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ j) =
              -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
                fderiv ℝ (fun y => V (gradient u y)) x
                  (EuclideanSpace.basisFun (Fin n) ℝ j) := by
          simpa only [neg_apply, add_apply] using hEval
        have hSum :
            (∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
              fderiv ℝ V (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ b)) =
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
                FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a := by
          apply Finset.sum_congr rfl
          intro b _
          rw [hCoord]
        have hxExp' := hxExp j
        rw [hSum] at hxExp'
        linarith [heval, hxExp']
      have hRestricted :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S]
            (fun x => ∑ b : Fin n,
              FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a) :=
        MeasureTheory.ae_restrict_of_ae hAe
      exact (MeasureTheory.memLp_congr_ae hRestricted).mp hClassicalL2
