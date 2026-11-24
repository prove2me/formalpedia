-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.proj_preserves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:08:32.630407+00:00
-- url     : https://prove2.me/submissions/3edf49e0-bade-49ee-b145-8b702dd3202e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
variable {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r] (d : L → ℕ)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hP : PROJ K v p C0) (hD : DVRHyp v p) {S S'' : Finset L} {th th'' : ℤ}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d (Aset sg S th) π)
    (hS : S ⊆ S'' ∨ S'' ⊆ S ∨ Disjoint S S'') {F : MvPolynomial (L × Fin r) K}
    (hF : F ∈ PolK K r d) (hFW : F ∈ Aset sg S'' th'') : π F ∈ Aset sg S'' th'' := by
  obtain ⟨⟨π'', hπ''⟩, -⟩ := hP hD L sg r d S'' th''
  have hfix : π'' F = F := (hπ'' F hF).2.2.1 hFW
  have hcomm : π (π'' F) = π'' (π F) := by
    rcases hS with h | h | h
    · exact ((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inl h) th'' π'' hπ'' F hF
    · exact (((hP hD L sg r d S'' th'').2 π'' hπ'').2.1 S (Or.inl h) th π hπ F hF).symm
    · exact ((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inr h) th'' π'' hπ'' F hF
  have hE : π F = π'' (π F) := by rw [← hcomm, hfix]
  rw [hE]
  exact (hπ'' (π F) (hπ F hF).1).2.1
end Formalism.MainNotions.PlaneGram
