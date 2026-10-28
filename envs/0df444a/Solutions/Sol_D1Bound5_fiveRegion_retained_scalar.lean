-- Prove2me | solution 1 for D1Bound5.fiveRegion_retained_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:55:26.879079+00:00
-- url     : https://prove2.me/submissions/0755246d-f552-45c1-9779-7f83b4d54f3f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_CoupledPhaseBounds_Definitions
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions
import Theorems.Thm_D1Bound5_fiveRegion_parameters

section
namespace D1Bound5

/-- Scalar use of the actual H48 retained estimate. The phase bound is
kept coupled to the relabeled residual throughout. This intermediate
lemma is subsequently supplied with the tuple's actual analytic data. -/
theorem _root_.solution (r : Fin 5) (A B S T C R Phi : ℝ)
    (hA : 1 ≤ A) (hBm : fiveRegionMinB r ≤ B) (hBS : B ≤ S)
    (hR : 0 < R) (hRQ : R ≤ fiveRegionTriangle r) (hPhi : 0 ≤ Phi)
    (hphase : R^2*Phi < fiveRegionPhase r)
    (hfront : fiveRegionFrontier r*A*B*S < T)
    (hret : (9999/10000 : ℝ)*(200/19)^2*
      (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2*(A^2*T^5/S^2) < C) :
    fiveRegionGap r*(A^7*B^5*S^3) < C ∧
    (fiveRegionCoupledGap r*((3535/409600 : ℝ)*Phi))*(A^7*B^5*S^3) < C := by
  let m := fiveRegionMinB r
  let Q := fiveRegionTriangle r
  let H := fiveRegionRetained r
  let e : ℝ := (51051/400000)/m^2
  let d : ℝ := 1-e*Q
  have hp := fiveRegion_parameters r
  have hm : 0 < m := by dsimp [m]; linarith only [hp.1]
  have hB : 0 < B := hm.trans_le hBm
  have hS : 0 < S := hB.trans_le hBS
  have hA0 : 0 < A := by linarith only [hA]
  have hQ : 0 < Q := hp.2.2.2.2.2.2.2.2.1
  have ht : 0 < fiveRegionFrontier r := by linarith only [hp.2.2.1]
  have hT : 0 < T := lt_trans (by positivity) hfront
  have he : 0 < e := by dsimp [e]; positivity
  have heQ : e*Q < 1 := by
    convert hp.2.2.2.2.2.2.2.2.2.1 using 1 <;> dsimp [e,Q,m] <;> ring
  have hd : 0 < d := by dsimp [d]; linarith only [heQ]
  have hHeq : H = (9999/10000 : ℝ)*(200/19)^2*(fiveRegionFrontier r)^5*d^2 := by
    dsimp [H,fiveRegionRetained,d,e,Q,m]
    ring
  have hH : 0 < H := by rw [hHeq]; positivity
  have hbase : 0 < A^7*B^5*S^3 := by positivity
  have hdenom : m^2 ≤ A^2*B^2 := by
    calc
      m^2 = (1 : ℝ)^2*m^2 := by ring
      _ ≤ A^2*B^2 := by gcongr
  have herr : (51051/400000 : ℝ)/(A^2*B^2) ≤ e := by
    dsimp [e]
    apply (div_le_div_iff₀ (by positivity : 0 < A^2*B^2) (pow_pos hm 2)).mpr
    nlinarith only [hdenom]
  have hdelta : d/R ≤ 1/R-(51051/400000 : ℝ)/(A^2*B^2) := by
    calc
      d/R ≤ (1-e*R)/R := by
        apply div_le_div_of_nonneg_right _ hR.le
        dsimp [d]
        exact sub_le_sub_left (mul_le_mul_of_nonneg_left hRQ he.le) 1
      _ = 1/R-e := by field_simp [hR.ne']
      _ ≤ _ := sub_le_sub_left herr (1/R)
  have hdR : 0 < d/R := div_pos hd hR
  have hsquare : (d/R)^2 ≤ (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2 := by
    exact (sq_le_sq₀ hdR.le (hdR.le.trans hdelta)).mpr hdelta
  have hpower : (fiveRegionFrontier r*A*B*S)^5 ≤ T^5 := by gcongr
  have hmain : (H/R^2)*(A^7*B^5*S^3) < C := by
    calc
      (H/R^2)*(A^7*B^5*S^3) =
          (9999/10000 : ℝ)*(200/19)^2*(d/R)^2*
            (A^2*(fiveRegionFrontier r*A*B*S)^5/S^2) := by
        dsimp [H,fiveRegionRetained,d,e,Q,m]
        field_simp [hR.ne',hS.ne']
        <;> ring
      _ ≤ (9999/10000 : ℝ)*(200/19)^2*
          (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2*(A^2*T^5/S^2) := by gcongr
      _ < C := hret
  have hG : fiveRegionGap r < H/Q^2 := hp.2.2.2.2.2.2.2.2.2.2.1
  have hrho : fiveRegionCoupledGap r < H/((3535/409600 : ℝ)*fiveRegionPhase r) :=
    hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hRQs : R^2 ≤ Q^2 := (sq_le_sq₀ hR.le hQ.le).mpr hRQ
  have hHQ : H/Q^2 ≤ H/R^2 := by
    apply (div_le_div_iff₀ (pow_pos hQ 2) (pow_pos hR 2)).mpr
    exact mul_le_mul_of_nonneg_left hRQs hH.le
  have hF : 0 < fiveRegionPhase r := hp.2.2.2.2.2.2.1
  have hPhiBound : Phi ≤ fiveRegionPhase r/R^2 :=
    (le_div_iff₀ (pow_pos hR 2)).mpr (by nlinarith only [hphase])
  have hCoupled : fiveRegionCoupledGap r*((3535/409600 : ℝ)*Phi) ≤ H/R^2 := by
    calc
      _ ≤ (H/((3535/409600 : ℝ)*fiveRegionPhase r))*((3535/409600 : ℝ)*Phi) := by
        exact mul_le_mul_of_nonneg_right hrho.le (by positivity)
      _ = (H/fiveRegionPhase r)*Phi := by field_simp [hF.ne']
      _ ≤ (H/fiveRegionPhase r)*(fiveRegionPhase r/R^2) := by gcongr
      _ = H/R^2 := by field_simp [hF.ne']
  exact ⟨(mul_le_mul_of_nonneg_right (hG.le.trans hHQ) hbase.le).trans_lt hmain,
    (mul_le_mul_of_nonneg_right hCoupled hbase.le).trans_lt hmain⟩

end D1Bound5
end
