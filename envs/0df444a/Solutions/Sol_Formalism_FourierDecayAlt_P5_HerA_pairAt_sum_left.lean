-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerA.pairAt_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:44:05.854041+00:00
-- url     : https://prove2.me/submissions/b7111ce1-8370-4015-af0d-9597f80815bd

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumPairAtStarMul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_hsInner_zero_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P5.HerA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
section Gen
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
variable {μ : Measure (Mt k r)} {U : Submodule ℂ (RadSp k r z z' π π')}
private theorem pairAt_zero_left' (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairAt μ 0 Ψ c = 0 := by
  simp only [pairAt, Submodule.coe_zero, Pi.zero_apply, hsInner_zero_left, integral_zero]
end Gen
section Top
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
end Top
end Formalism.FourierDecayAlt.P5.HerA
end
end

set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
variable {μ : Measure (Mt k r)} {U : Submodule ℂ (RadSp k r z z' π π')}
namespace Formalism.FourierDecayAlt.P5.HerA
theorem _root_.solution (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {ι : Type} (s : Finset ι)
    (Φ : ι → RadSp k r z z' π π') (hΦ : ∀ i, Φ i ∈ U) {Ψ : RadSp k r z z' π π'} (hΨ : Ψ ∈ U) :
    pairAt μ (∑ i ∈ s, Φ i) Ψ c = ∑ i ∈ s, pairAt μ (Φ i) Ψ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, pairAt_zero_left']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      pairAt_add_left hU hc (hΦ j) (U.sum_mem fun i _ => hΦ i) hΨ, ih]
end Formalism.FourierDecayAlt.P5.HerA
