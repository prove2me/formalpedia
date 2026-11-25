-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:38:02.699163+00:00
-- url     : https://prove2.me/submissions/958f08bc-5e7a-4ca9-bb68-807b75110d1e

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDensNonnegOfKappa
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_fst_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexOrder ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
open Formalism.FourierDecayAlt.P5.WordTransvectionCongruences
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5.WordTransvectionCongruences
theorem _root_.solution (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (n : ℕ) (Φ : RadSp k r z z' π π') (p : (Fin r → ℂ) × Mx k r)
    (hp : p ∈ DomR k r z z') :
    ((((L.ζ * L.ζb * L.GGi) ^ n).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 =
      (fnVal k r z z' 0 p.2 * fnVal k r z z' 2 p.2 * fnVal k r z z' 5 p.2) ^ n •
        (Φ : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 := by
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, hgi, -⟩ := hAL
  induction n generalizing Φ with
  | zero => simp only [pow_zero, one_smul]; rfl
  | succ n ih =>
    rw [pow_succ, pr_fst_mul, Module.End.mul_apply, ih, pr_fst_mul, pr_fst_mul, Module.End.mul_apply,
      Module.End.mul_apply, hz, hzb, hgi]
    simp only [mkP]
    rw [X.fn_apply 0 _ p hp, X.fn_apply 2 _ p hp, X.fn_apply 5 _ p hp, smul_smul, smul_smul, smul_smul, pow_succ]
    ring_nf
end Formalism.FourierDecayAlt.P5.WordTransvectionCongruences
