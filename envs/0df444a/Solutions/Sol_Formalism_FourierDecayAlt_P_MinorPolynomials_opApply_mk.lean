-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.opApply_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:27:14.774924+00:00
-- url     : https://prove2.me/submissions/3ad18515-0683-48c6-961d-a761de151d68

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_mkTerm_word
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_mkTerm_word


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
variable [FiniteDimensional ℂ Wp]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (Lf : FS k r nf)
    (hL : ∀ e ∈ Lf, ∀ X ∈ e.2, inLie k r X) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    opApply (Lf.map (mkTerm D fib)) F g = shape D fib F Lf g := by
  unfold opApply shape
  rw [List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro e he
  simp only [Function.comp_apply]
  rw [mkTerm_word D fib (hL e he)]
  rfl
end Formalism.FourierDecayAlt.P.MinorPolynomials
