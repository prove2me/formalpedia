-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.first_weight_le_of_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:24.115401+00:00
-- url     : https://prove2.me/submissions/bb193e88-9753-4ccc-88c5-8849da842e12

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport

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
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (h0 : (0 : Fin r) ∈ Cs)
    (Mt : WithTop ℤ) (μ : Fin r → ℤ) (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hh0 : h ≠ 0)
    (h1 : h ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt})
    (h3 : h ∈ WtSpC p LL j Cs μ) : ((μ 0 : ℤ) : WithTop ℤ) ≤ Mt := by
  have hne : h.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    exact hh0
  obtain ⟨m, hm⟩ := hne
  rw [mem_restrictSupport_iff] at h1
  rw [WtSpC, mem_restrictSupport_iff] at h3
  have a := h1 (Finset.mem_coe.mpr hm)
  have b := h3 (Finset.mem_coe.mpr hm)
  rw [Set.mem_setOf_eq] at a b
  rw [← b 0 h0]
  exact a
end Formalism.InvariantFactorPaths.L4
