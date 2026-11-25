-- Prove2me | solution 1 for ChromaticReconstruction.pderiv_phi_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:47:47.643827+00:00
-- url     : https://prove2.me/submissions/dd2bdd15-eff0-447b-98a5-1a5ca4ad1681

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2
import Theorems.Thm_ChromaticReconstruction_pderiv_opD
import Theorems.Thm_ChromaticReconstruction_phi_uniformLeafExt_eq_opD


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution (q N r : ℕ) (hq : 2 ≤ q) (G : SimpleGraph V) (hN : Fintype.card V < N)
    (hrN : r < N) (hr : 1 ≤ r) (hqr : q * r - 1 ≠ 1) :
    pderiv (q * r - 1) (phi (uniformLeafExt q G)) =
      cFactor q (Fintype.card V) • (C (r : ℚ) * psiQ q (pderiv r (chromSymm G))) := by
  rw [phi_uniformLeafExt_eq_opD q N hq G hN, Derivation.map_smul, pderiv_opD q N r hq hrN hr hqr]
  rfl
end ChromaticReconstruction
