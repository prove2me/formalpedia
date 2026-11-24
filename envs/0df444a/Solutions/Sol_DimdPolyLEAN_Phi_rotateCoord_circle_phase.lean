-- Prove2me | solution 1 for DimdPolyLEAN.Phi_rotateCoord_circle_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:39.748286+00:00
-- url     : https://prove2.me/submissions/e2ef5c6a-dcae-4334-9bba-b2634e17b577

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_Phi_rotate_one_exp
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private lemma fourier_mk_eq_exp
    (n : ℤ) (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : Circle) : ℂ) =
      Complex.exp (Complex.I * (n : ℂ) * θ) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (kappa alpha : MultiIndex d) (q0 : Fin d)
    (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      Phi kappa alpha
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
    (fourier ((alpha q0 : Nat) : Int) x : ℂ) *
      Phi kappa alpha z := by
  induction x using Quotient.inductionOn with
  | h θ =>
      rw [fourier_mk_eq_exp ((kappa q0 : Nat) : Int) θ,
        fourier_mk_eq_exp ((alpha q0 : Nat) : Int) θ,
        fourier_mk_eq_exp (1 : Int) θ]
      have hone :
        Complex.exp (Complex.I * ((1 : ℤ) : ℂ) * θ) =
            Complex.exp (Complex.I * θ) := by
        simp_all
      rw [hone, Phi_rotate_one_exp]
      have hphase :
          Complex.exp (Complex.I * (((kappa q0 : Nat) : Int) : ℂ) * θ) *
              (Complex.exp
                (Complex.I * (((alpha q0 : ℤ) - (kappa q0 : ℤ) : ℂ) * θ)) *
                Phi kappa alpha z) =
            Complex.exp (Complex.I * (((alpha q0 : Nat) : Int) : ℂ) * θ) *
              Phi kappa alpha z := by
        rw [← mul_assoc, ← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
      exact hphase
end DimdPolyLEAN
