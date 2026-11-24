-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.mulVec_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:36.649921+00:00
-- url     : https://prove2.me/submissions/c2bd1d93-3a1a-4960-8eb4-817f491510bb

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {F : Type} [Field F] [Fintype F]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution {j n : ℕ} (M : Matrix (Fin j) (Fin n) F) (hM : LinearIndependent F M.row) :
    Function.Surjective M.mulVec := by
  have h1 : M.rank = j := by simpa using hM.rank_matrix
  have h2 : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, h1]; simp
  intro y
  have : y ∈ LinearMap.range M.mulVecLin := by rw [h2]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x, hx⟩
end Formalism.HermitianLatticeCounting.P.S4aux
