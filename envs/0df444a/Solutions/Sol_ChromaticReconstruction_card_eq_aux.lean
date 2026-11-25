-- Prove2me | solution 1 for ChromaticReconstruction.card_eq_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:54:45.963747+00:00
-- url     : https://prove2.me/submissions/8d2e4c23-5c88-44ac-b148-1507b5c00f40

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2
import Theorems.Thm_ChromaticReconstruction_edgeFinset_nonempty_of_connected
import Theorems.Thm_ChromaticReconstruction_cFactor_ne_zero
import Theorems.Thm_ChromaticReconstruction_pderiv_phi_uniform
import Theorems.Thm_ChromaticReconstruction_coeff_psi_pderiv_two
import Theorems.Thm_ChromaticReconstruction_coeff_chromSymm_eq_zero
import Theorems.Thm_ChromaticReconstruction_coeff_chromSymm_pair
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q) (G' : SimpleGraph V) (H' : SimpleGraph W)
    (hG' : G'.Connected) (h2 : 2 ≤ Fintype.card V)
    (h' : phi (uniformLeafExt q G') = phi (uniformLeafExt q H'))
    (hne : Fintype.card V ≠ Fintype.card W) : False := by
  set N := Fintype.card V + Fintype.card W + 3
  have e := congrArg (pderiv (q * 2 - 1)) h'
  rw [pderiv_phi_uniform q N 2 hq G' (by omega) (by omega) (by omega) (by omega),
    pderiv_phi_uniform q N 2 hq H' (by omega) (by omega) (by omega) (by omega)] at e
  have e2 := congrArg (coeff ((Multiset.toFinsupp (Multiset.replicate
    (Fintype.card V - 2) 1)).mapDomain (fun r => q * r))) e
  simp only [coeff_smul, coeff_C_mul] at e2
  rw [coeff_psi_pderiv_two q (by omega) G', coeff_psi_pderiv_two q (by omega) H'] at e2
  rw [coeff_chromSymm_pair, coeff_chromSymm_eq_zero H' _ (by
    simp only [Multiset.sum_cons, Multiset.sum_replicate, smul_eq_mul, mul_one]
    omega)] at e2
  simp only [mul_zero, smul_eq_mul, mul_neg, neg_eq_zero, mul_eq_zero,
    cFactor_ne_zero hq, false_or, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, card_eq_zero] at e2
  exact (edgeFinset_nonempty_of_connected hG' h2).ne_empty e2
end ChromaticReconstruction
