-- Prove2me | solution 1 for DimdPolyLEAN.summable_sq_Phi_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:16.827032+00:00
-- url     : https://prove2.me/submissions/7e50e86b-10d4-47b0-b6f4-d1b52cad730b

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_summable_norm_sq_Phi_eval
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private theorem summable_sq_hermite_phi_eval
    (k : Nat) (z : ℂ) :
    Summable (fun n : Nat => ‖HermitekLEAN.Phi k n z‖ ^ 2) := by
  exact HermitekLEAN.summable_norm_sq_Phi_eval k z
private theorem summable_sq_phi1D_eval
    (k : Nat) (z : ℂ) :
    Summable (fun m : Nat => ‖phi1D k m z‖ ^ 2) := by
  have hEq :
      (fun m : Nat => ‖phi1D k m z‖ ^ 2) =
        fun m : Nat => ‖HermitekLEAN.Phi k m z‖ ^ 2 := by
    funext m
    have hphi : phi1D k m z = HermitekLEAN.Phi k m z :=
      phi1D_eq_oneDimPhi k m z
    simp [hphi]
  simpa [hEq] using summable_sq_hermite_phi_eval k z
private theorem Phi_norm_sq_eq_prod
    {d : Nat} (kappa alpha : MultiIndex d) (z : Cd d) :
    ‖Phi kappa alpha z‖ ^ 2 =
      Finset.prod Finset.univ
        (fun q : Fin d => ‖phi1D (kappa q) (alpha q) (z q)‖ ^ 2) := by
  simp [Phi, norm_prod, Finset.prod_pow]
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
    {d : Nat} (kappa : MultiIndex d) (z : Cd d) :
    Summable (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2) := by
  refine summable_of_sum_le
    (c := Finset.prod Finset.univ
      (fun q : Fin d => ∑' n : Nat, ‖phi1D (kappa q) n (z q)‖ ^ 2))
    (fun alpha : Idx d => sq_nonneg _) ?_
  intro E
  let J : Fin d -> Nat := fun q => Finset.sup E (fun alpha : Idx d => alpha q)
  let B : Finset (Idx d) := Fintype.piFinset fun q : Fin d => Finset.range (J q + 1)
  have hE_subset : E ⊆ B := by
    intro alpha halpha
    dsimp [B]
    rw [Fintype.mem_piFinset]
    intro q
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (s := E) (f := fun beta : Idx d => beta q) halpha
  have hsum_E_le_B :
      Finset.sum E (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2) <=
        Finset.sum B (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hE_subset (fun alpha _ _ => sq_nonneg _)
  have hbox_eq :
      Finset.sum B (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2) =
        Finset.prod Finset.univ
          (fun q : Fin d =>
            Finset.sum (Finset.range (J q + 1))
              (fun n : Nat => ‖phi1D (kappa q) n (z q)‖ ^ 2)) := by
    dsimp [B]
    symm
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    exact (Phi_norm_sq_eq_prod kappa alpha z).symm
  have hprod_le :
      Finset.prod Finset.univ
          (fun q : Fin d =>
            Finset.sum (Finset.range (J q + 1))
              (fun n : Nat => ‖phi1D (kappa q) n (z q)‖ ^ 2)) <=
        Finset.prod Finset.univ
          (fun q : Fin d =>
            ∑' n : Nat, ‖phi1D (kappa q) n (z q)‖ ^ 2) :=
    Finset.prod_le_prod
      (fun q _ => Finset.sum_nonneg fun n _ => sq_nonneg _)
      (fun q _ => (summable_sq_phi1D_eval (kappa q) (z q)).sum_le_tsum
          (Finset.range (J q + 1)) (fun n _ => sq_nonneg _))
  exact le_trans hsum_E_le_B (by rw [hbox_eq]; exact hprod_le)
end DimdPolyLEAN
