-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappa_rotateCoord_circle_phase_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:34.945826+00:00
-- url     : https://prove2.me/submissions/a3b92597-99dd-4d44-8856-a0c34011e799

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_Phi_rotateCoord_circle_phase
public import Theorems.Thm_DimdPolyLEAN_circleChar_eq_fourier_nat


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (F : Pkappa d kappa) (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      evalPkappa kappa F
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
      ∑ alpha ∈ F.support,
        F alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
  classical
  unfold evalPkappa
  rw [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  have hphase :=
    Phi_rotateCoord_circle_phase
      (kappa := kappa) (alpha := alpha) (q0 := q0) x z
  have hchar : circleChar (alpha q0) x = (fourier ((alpha q0 : Nat) : Int) x : ℂ) :=
    circleChar_eq_fourier_nat (alpha q0) x
  calc
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
        (F alpha *
          Phi kappa alpha
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)))
      = F alpha *
          ((fourier ((kappa q0 : Nat) : Int) x : ℂ) *
            Phi kappa alpha
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) := by ring
    _ = F alpha * ((fourier ((alpha q0 : Nat) : Int) x : ℂ) * Phi kappa alpha z) := by rw [hphase]
    _ = F alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
          rw [hchar]
          ring
end DimdPolyLEAN
