-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.cda_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:51:40.372319+00:00
-- url     : https://prove2.me/submissions/866e86f6-202d-49ad-9efd-909e3cde16f6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → Mat k r → ℂ} {x : Mat k r}
    (h : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) : ContDiffAt ℝ ∞ (fun g => ∏ i ∈ s, f i g) x := by
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Mat k r => (1 : ℂ)) x)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
end Formalism.FourierDecayAlt.P.MinorPolynomials
