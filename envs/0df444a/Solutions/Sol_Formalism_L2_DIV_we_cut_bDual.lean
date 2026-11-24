-- Prove2me | solution 1 for Formalism.L2.DIV.we_cut_bDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:56:19.345977+00:00
-- url     : https://prove2.me/submissions/031dbbcf-87df-4b8c-a06b-4dc2c6a7de11

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
import Theorems.Thm_Formalism_L2_DIV_we_hw_norm_ne
import Theorems.Thm_Formalism_L2_DIV_weForm_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.GradedWeylDivisibility
variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
namespace Formalism.L2.DIV
theorem _root_.solution (S : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)) (hS : ∀ x ∈ S, x ∈ dualWeyl ℚ r n ν) :
    weCut r n ν (bDual r n hn ν S) = Formalism.HermitianLatticesTheory.dual (weForm hn ν) (weCut r n ν S) := by
  have hc := we_hw_norm_ne hn ν
  ext x
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    Submodule.mem_one, weForm_apply]
  constructor
  · rintro ⟨-, h⟩ y hy
    obtain ⟨z, hz⟩ := h y.1 hy
    replace hz : fockQ x.1 y.1 = z * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := hz
    refine ⟨z, ?_⟩
    rw [we_fock_symm, hz, mul_div_assoc, div_self hc, mul_one]
    rfl
  · intro h
    refine ⟨x.2, fun Q hQ => ?_⟩
    obtain ⟨z, hz⟩ := h ⟨Q, hS Q hQ⟩ hQ
    refine ⟨z, ?_⟩
    show fockQ x.1 Q = _
    rw [we_fock_symm]
    have hz' : (z : ℚ) = fockQ Q x.1 / fockQ (hw ℚ hn ν) (hw ℚ hn ν) := hz
    rw [hz', div_mul_cancel₀ _ hc]
end Formalism.L2.DIV
