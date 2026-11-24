-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.comm_wtspC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:16.180086+00:00
-- url     : https://prove2.me/submissions/14e88724-a64b-4dc1-ba4f-e4a44f68c479

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_cartan_eigC
import Theorems.Thm_Formalism_CountingSumsFrames_eig_supp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ Cs, ∀ x, Q (glAct p LL j c c x) = glAct p LL j c c (Q x)) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j Cs μ, Q x ∈ WtSpC p LL j Cs μ := by
  intro x hx
  rw [WtSpC, mem_restrictSupport_iff]
  intro m hm c hc
  have h1 : glAct p LL j c c (Q x) = ((μ c : ℤ) : ℚ_[p]) • Q x := by
    rw [← hQ c hc, cartan_eigC LL j Cs μ x hx c hc, map_smul]
  have := eig_supp LL j c (μ c) (Q x) h1
  rw [mem_restrictSupport_iff] at this
  exact this hm
end Formalism.InvariantFactorPaths.L4
