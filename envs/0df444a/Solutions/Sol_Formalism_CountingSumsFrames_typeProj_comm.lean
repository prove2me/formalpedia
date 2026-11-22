-- Prove2me | solution 1 for Formalism.CountingSumsFrames.typeProj_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:45.194746+00:00
-- url     : https://prove2.me/submissions/8c14812b-9084-44da-bbd7-3730b473bd94

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_comm_of_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ la, ∀ x ∈ IsoC p LL j univ la, Q x ∈ IsoC p LL j univ la) : ∀ x, P (Q x) = Q (P x) := by
  obtain ⟨hPP, hran, hker⟩ := hP
  have hsup : ∀ S : Set (Fin r → ℤ), ∀ x ∈ (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la),
      Q x ∈ (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la) := by
    intro S
    have : (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la) ≤
        (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la).comap Q := by
      refine iSup₂_le fun la hla => ?_
      intro x hx
      exact (le_iSup₂ (f := fun la (_ : la ∈ S) => IsoC p LL j univ la) la hla) (hQ la x hx)
    exact fun x hx => this hx
  refine comm_of_stable P Q hPP ?_ ?_
  · rw [hran]; exact hsup T
  · rw [hker]; exact hsup Tᶜ
end Formalism.CountingSumsFrames
