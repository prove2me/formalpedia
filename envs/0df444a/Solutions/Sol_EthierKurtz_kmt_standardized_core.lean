-- Prove2me | solution 1 for EthierKurtz.kmt_standardized_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:07:15.465477+00:00
-- url     : https://prove2.me/submissions/4834ce24-ae3e-47df-89cd-fc3d81c80792
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_EthierKurtz_kmt_general_core
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

theorem solution
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => 0 < a0 /\ forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real))
    (hmean : MeasureTheory.integral (mu : Measure Real) (fun x : Real => x) = 0)
    (hvariance : variance (fun x : Real => x) (mu : Measure Real) = 1) :
      Exists fun Q : ProbabilityMeasure (Prod (Nat -> Real) {b : NNReal -> Real // Continuous b}) =>
      iIndepFun (fun (i : Nat) (z : Prod (Nat -> Real) {b : NNReal -> Real // Continuous b}) => z.1 i) (Q : Measure (Prod (Nat -> Real) {b : NNReal -> Real // Continuous b})) /\
      (forall i : Nat, HasLaw (fun (z : Prod (Nat -> Real) {b : NNReal -> Real // Continuous b}) => z.1 i) (mu : Measure Real) (Q : Measure (Prod (Nat -> Real) {b : NNReal -> Real // Continuous b}))) /\
      IsBrownianReal (fun t (z : Prod (Nat -> Real) {b : NNReal -> Real // Continuous b}) => z.2.val t) (Q : Measure (Prod (Nat -> Real) {b : NNReal -> Real // Continuous b})) /\
      Exists fun C : Real => Exists fun K : Real => Exists fun lam : Real => 0 < C /\ 0 < K /\ 0 < lam /\
        let m := MeasureTheory.integral (mu : Measure Real) (fun x : Real => x)
        let sigma := Real.sqrt (variance (fun x : Real => x) (mu : Measure Real))
        let W := fun (t : NNReal) (z : Prod (Nat -> Real) {b : NNReal -> Real // Continuous b}) =>
          m * (t : Real) + sigma * z.2.val t
        forall n : Nat, 1 <= n -> forall x : Real, 0 < x ->
          (Q : Measure (Prod (Nat -> Real) {b : NNReal -> Real // Continuous b})) {z | Exists fun k : Nat => 1 <= k /\ k <= n /\
            C * Real.log (n : Real) + x <
              abs ((Finset.sum (Finset.range k) fun i => z.1 i) - W (k : NNReal) z)} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by
  have h := EthierKurtz.kmt_general_core mu hexp
  simpa [hmean, hvariance] using h