-- Prove2me | solution 1 for DimdPolyLEAN.toFun_smul_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:25.065343+00:00
-- url     : https://prove2.me/submissions/16ecd2cf-6573-4743-855f-aa1c1a45b989

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (kappa : MultiIndex d) (w : ℂ) (U : Skappa d kappa) :
    toFun kappa (w • U) = fun z => w * toFun kappa U z := by
  funext z
  calc
    (∑' alpha : Idx d, (w • U).coeff alpha * Phi kappa alpha z) =
        ∑' alpha : Idx d, w * (U.coeff alpha * Phi kappa alpha z) :=
          tsum_congr fun alpha => mul_assoc w (U.coeff alpha) (Phi kappa alpha z)
    _ = w * ∑' alpha : Idx d, U.coeff alpha * Phi kappa alpha z := by rw [tsum_mul_left]
end DimdPolyLEAN
