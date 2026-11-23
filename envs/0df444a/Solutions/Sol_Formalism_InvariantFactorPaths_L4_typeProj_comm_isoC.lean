-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.typeProj_comm_isoC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:53.655193+00:00
-- url     : https://prove2.me/submissions/4b285f19-1c09-469a-9fb3-b6ecea18ad15

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_CountingSumsFrames_comm_of_stable


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
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ la, ∀ x ∈ IsoC p LL j Cs la, Q x ∈ IsoC p LL j Cs la) : ∀ x, P (Q x) = Q (P x) := by
  apply comm_of_stable P Q hP.1
  · intro x hx
    rw [hP.2.1] at hx ⊢
    have hle : (⨆ la ∈ T, IsoC p LL j Cs la) ≤ (⨆ la ∈ T, IsoC p LL j Cs la).comap Q := by
      refine iSup₂_le fun la hla => ?_
      intro y hy
      exact (le_iSup₂ (f := fun la (_ : la ∈ T) => IsoC p LL j Cs la) la hla) (hQ la y hy)
    exact hle hx
  · intro x hx
    rw [hP.2.2] at hx ⊢
    have hle : (⨆ (la : Fin r → ℤ), ⨆ (_ : la ∉ T), IsoC p LL j Cs la) ≤
        (⨆ (la : Fin r → ℤ), ⨆ (_ : la ∉ T), IsoC p LL j Cs la).comap Q := by
      refine iSup₂_le fun la hla => ?_
      intro y hy
      exact (le_iSup₂ (f := fun la (_ : la ∉ T) => IsoC p LL j Cs la) la hla) (hQ la y hy)
    exact hle hx
end Formalism.InvariantFactorPaths.L4
