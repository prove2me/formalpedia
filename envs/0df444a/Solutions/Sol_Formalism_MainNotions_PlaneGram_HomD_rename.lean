-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.HomD_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:30:30.263115+00:00
-- url     : https://prove2.me/submissions/309933ca-cb0b-4708-b23b-10af5ae220b0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ldeg_mapDomain

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
variable {K : Type} [Field K] {L L' : Type} {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution [Fintype L] [DecidableEq L] [DecidableEq L'] (f : L → L')
    (hf : Function.Injective f) (d : L → ℕ) (G : MvPolynomial (L × Fin r) K) (hG : HomD d G) :
    HomD (fun i' => ∑ l, if f l = i' then d l else 0) (rename (Prod.map f (id : Fin r → Fin r)) G) := by
  classical
  intro β hβ i'
  have hinj : Function.Injective (Prod.map f (id : Fin r → Fin r)) := by
    rintro ⟨a, b⟩ ⟨c, e⟩ hac
    simp only [Prod.map, id, Prod.mk.injEq] at hac
    exact Prod.ext (hf hac.1) hac.2
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hβ
  obtain ⟨β₀, h₀, rfl⟩ := hβ
  rw [ldeg_mapDomain]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hG β₀ h₀ l]
end Formalism.MainNotions.PlaneGram
