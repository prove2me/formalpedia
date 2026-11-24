-- Prove2me | solution 1 for DimdPolyLEAN.annulusMassPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:54.006796+00:00
-- url     : https://prove2.me/submissions/1bb26244-fda8-47d0-a707-f269a5c3732b

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private theorem toFun_ofPkappa_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) :
    toFun kappa (ofPkappa kappa F) = evalPkappa kappa F := by
  let _ := hd
  ext z
  rw [toFun, evalPkappa, Finsupp.sum]
  have hzero :
      ∀ alpha ∉ F.support,
        coeffSkappa (ofPkappa kappa F) alpha * Phi kappa alpha z = 0 := by
    intro alpha halpha
    simp [coeffSkappa, ofPkappa, Finsupp.notMem_support_iff.mp halpha]
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [coeffSkappa, ofPkappa]
private theorem ofPkappa_total_mass_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) :
    (∫ z, ‖toFun kappa (ofPkappa kappa F) z‖ ^ 2 ∂ gammaD d) = ‖F‖ ^ 2 := by
  let _ := hd
  simpa [toFun_ofPkappa_wip hd kappa F] using evalPkappa_total_mass hd kappa F
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (J : Nat) (H : Pkappa d kappa) :
    lowAnnulusMass J (ofPkappa kappa H) + highAnnulusMass J (ofPkappa kappa H) = ‖H‖ ^ 2 := by
  let _ := hd
  /-
  This is the assembly-facing finite partition identity. The eventual proof
  should keep the coercion `Pkappa -> Skappa` hidden behind this lemma.
  -/
  unfold highAnnulusMass
  ring_nf
  simpa using ofPkappa_total_mass_wip hd kappa H
end DimdPolyLEAN
