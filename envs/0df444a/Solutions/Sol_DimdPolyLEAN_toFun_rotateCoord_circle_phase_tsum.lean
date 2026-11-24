-- Prove2me | solution 1 for DimdPolyLEAN.toFun_rotateCoord_circle_phase_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:17.366553+00:00
-- url     : https://prove2.me/submissions/99b93268-37c8-463c-9209-1f0d80ae2d58

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_Phi_rotateCoord_circle_phase
public import Theorems.Thm_DimdPolyLEAN_summable_skappa_eval_mul
public import Theorems.Thm_DimdPolyLEAN_circleChar_eq_fourier_nat
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (U : Skappa d kappa) (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      toFun kappa U
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
      ∑' alpha : Idx d,
        coeffSkappa U alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
  classical
  let zrot : Cd d :=
    Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)
  let cκ : ℂ := fourier ((kappa q0 : Nat) : Int) x
  have hsum_rot : Summable (fun alpha : Idx d => coeffSkappa U alpha * Phi kappa alpha zrot) :=
    summable_skappa_eval_mul kappa U zrot
  unfold toFun
  change cκ * (∑' alpha : Idx d, coeffSkappa U alpha * Phi kappa alpha zrot) =
    ∑' alpha : Idx d, coeffSkappa U alpha * Phi kappa alpha z * circleChar (alpha q0) x
  rw [← hsum_rot.tsum_mul_left cκ]
  exact tsum_congr fun alpha => by
    have hphase :=
      Phi_rotateCoord_circle_phase (kappa := kappa) (alpha := alpha) (q0 := q0) x z
    have hchar : circleChar (alpha q0) x = (fourier ((alpha q0 : Nat) : Int) x : ℂ) :=
      circleChar_eq_fourier_nat (alpha q0) x
    dsimp [cκ, zrot]
    calc
      (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
          (coeffSkappa U alpha *
            Phi kappa alpha
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)))
        = coeffSkappa U alpha *
            ((fourier ((kappa q0 : Nat) : Int) x : ℂ) *
              Phi kappa alpha
                (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) := by ring
      _ = coeffSkappa U alpha *
            ((fourier ((alpha q0 : Nat) : Int) x : ℂ) * Phi kappa alpha z) := by rw [hphase]
      _ = coeffSkappa U alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
            rw [hchar]
            ring
end DimdPolyLEAN
