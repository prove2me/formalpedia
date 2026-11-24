-- Prove2me | solution 1 for DimdPolyLEAN.Phi_rotate_one_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:41.703908+00:00
-- url     : https://prove2.me/submissions/056ea141-f274-4157-8ac8-9c63559579b4

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_Hermite1DimdLEAN_oneVariableAngularFactorization
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private lemma oneDimPhi_phaseLaw
    (k n : Nat) (t : ℝ) (z : ℂ) :
    Hermite1DimdLEAN.oneDimPhi k n (Complex.exp (Complex.I * t) * z) =
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
        Hermite1DimdLEAN.oneDimPhi k n z := by
  obtain ⟨radial, hradial⟩ := Hermite1DimdLEAN.oneVariableAngularFactorization k n
  have hz : ((‖z‖ : ℂ) * Complex.exp (Complex.I * z.arg)) = z := by
    simp [mul_comm Complex.I (z.arg : ℂ), Complex.norm_mul_exp_arg_mul_I z]
  have hrot :
      Complex.exp (Complex.I * t) * z =
        ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
    calc
      Complex.exp (Complex.I * t) * z =
          Complex.exp (Complex.I * t) * ((‖z‖ : ℂ) * Complex.exp (Complex.I * z.arg)) := by rw [hz]
      _ = ((‖z‖ : ℂ) * Complex.exp (Complex.I * t)) * Complex.exp (Complex.I * z.arg) := by ring_nf
      _ = (‖z‖ : ℂ) * (Complex.exp (Complex.I * t) * Complex.exp (Complex.I * z.arg)) := by
            rw [mul_assoc]
      _ = ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
            rw [← Complex.exp_add]
            congr 1
            ring_nf
  have hleft :
      Hermite1DimdLEAN.oneDimPhi k n ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa using hradial ‖z‖ (t + z.arg)
  have hright :
      Hermite1DimdLEAN.oneDimPhi k n z =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa [hz] using hradial ‖z‖ z.arg
  have hexp :
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
          Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) := by
    rw [show Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) =
        Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * t)) +
          Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) by ring_nf]
    rw [Complex.exp_add]
  calc
    Hermite1DimdLEAN.oneDimPhi k n (Complex.exp (Complex.I * t) * z) =
        Hermite1DimdLEAN.oneDimPhi k n
          ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by rw [hrot]
    _ = Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := hleft
    _ = Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
          Hermite1DimdLEAN.oneDimPhi k n z := by
          rw [hexp, hright]
          ring_nf
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
    {d : Nat} (kappa alpha : MultiIndex d) (q0 : Fin d) (t : ℝ) (z : Cd d) :
    Phi kappa alpha (Function.update z q0 (Complex.exp (Complex.I * t) * z q0)) =
      Complex.exp (Complex.I * (((alpha q0 : ℤ) - (kappa q0 : ℤ) : ℂ) * t)) *
        Phi kappa alpha z := by
  classical
  rw [Phi_eq_PhiKappaAlpha, Phi_eq_PhiKappaAlpha]
  unfold Hermite1DimdLEAN.PhiKappaAlpha
  have hupdate :
      (fun q : Fin d =>
        Hermite1DimdLEAN.oneDimPhi (kappa q) (alpha q)
          (Function.update z q0 (Complex.exp (Complex.I * t) * z q0) q)) =
        Function.update
          (fun q : Fin d => Hermite1DimdLEAN.oneDimPhi (kappa q) (alpha q) (z q))
          q0
          (Hermite1DimdLEAN.oneDimPhi (kappa q0) (alpha q0)
            (Complex.exp (Complex.I * t) * z q0)) := by
    funext q
    by_cases hq : q = q0
    · simp_all
    · simp [Function.update, hq]
  rw [hupdate, Finset.prod_update_of_mem (s := Finset.univ) (i := q0) (by simp), oneDimPhi_phaseLaw]
  conv_rhs =>
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (s := Finset.univ) (i := q0) (by simp)]
  ring_nf
end DimdPolyLEAN
