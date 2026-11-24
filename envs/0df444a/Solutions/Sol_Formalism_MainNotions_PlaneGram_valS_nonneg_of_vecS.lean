-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_nonneg_of_vecS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:30:56.258599+00:00
-- url     : https://prove2.me/submissions/defc8728-934a-42ff-81a7-92c1988697b5

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_valS_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_mem
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lord_nonneg_of_mem
import Theorems.Thm_Formalism_MainNotions_PlaneGram_hMat_mem

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
variable {K : Type} [Field K]
variable {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (F : MvPolynomial (L × Fin r) K)
    (h : ∀ α ∈ F.support, ∀ i a, α (i, a) ≠ 0 → i ∈ S → sg i = true) : 0 ≤ valS sg S F := by
  have key : subV sg S F ∈
      (MvPolynomial.map (σ := L × Fin r)
        (Polynomial.toLaurent : Polynomial (GenF K r) →+* LauF K r)).range := by
    refine substS_mem _ sg S _ _ _ ?_ F ?_
    · intro c
      refine ⟨MvPolynomial.C (Polynomial.C ((algebraMap (MvPolynomial (Fin r × Fin r) K) (GenF K r))
        (MvPolynomial.C c))), ?_⟩
      simp [lauι, Formalism.MainNotions.G.coefL]
    · intro α hα x hx
      unfold subX
      split_ifs with h1 h2
      · refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ?_ ⟨X (x.1, b), by simp⟩
        obtain ⟨q, hq⟩ := hMat_mem (K := K) r x.2 b
        exact ⟨MvPolynomial.C q, by simp [hq]⟩
      · exact absurd (h α hα x.1 x.2 (Finsupp.mem_support_iff.mp hx) h1) h2
      · exact ⟨X x, by simp⟩
  rw [le_valS_iff]
  intro β
  apply lord_nonneg_of_mem
  obtain ⟨q, hq⟩ := key
  rw [← hq, MvPolynomial.coeff_map]
  exact ⟨_, rfl⟩
end Formalism.MainNotions.PlaneGram
