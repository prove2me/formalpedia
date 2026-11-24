-- Prove2me | solution 1 for Formalism.REAL.typesSplit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:16:03.48975+00:00
-- url     : https://prove2.me/submissions/e857185e-00aa-4e8e-a087-1285d4c0ad38

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_compact_span_zero_le
import Theorems.Thm_Formalism_REAL_isotypic_part_le_of_forall
import Theorems.Thm_Formalism_REAL_compact_span_le_isotypic_part
import Theorems.Thm_Formalism_REAL_root_injective_of_ne
import Theorems.Thm_Formalism_REAL_noncompact_arr_one_compact_stable
import Theorems.Thm_Formalism_REAL_noncompact_arr_finite_dimensional
import Theorems.Thm_Formalism_REAL_glRel_kRel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (hv : HVCoeff) (hi : KIsoSplit) (ha : ArrModule) : TypesSplit := by
  intro V _ _ n ε E Λ u hg hu hΛ hfd
  have hA := (ha V n ε E 1).1 hg
  have hKU := (ha V n ε E 1).2 hu
  have hKR := glRel_kRel ε _ hA.1
  have := noncompact_arr_finite_dimensional (j := 1) hfd
  obtain ⟨h1, h2⟩ := hi (Arr V n 1) n ε (arrE E 1) (arrV0 ε E u 1)
    {μ | ∃ a b, a < b ∧ ε a ≠ ε b ∧ μ = Λ + root a b} inferInstance hKR hKU noncompact_arr_one_compact_stable
  have heq : isoPart ε (arrE E 1) {μ | ∃ a b, a < b ∧ ε a ≠ ε b ∧ μ = Λ + root a b}ᶜ
      (arrV0 ε E u 1) = Vminus ε E Λ u := by
    apply le_antisymm
    · apply isotypic_part_le_of_forall
      intro y hy μ hμ hyh
      by_cases hy0 : y = 0
      · subst hy0; exact compact_span_zero_le _
      · obtain ⟨a, b, hne, rfl⟩ := hv V n ε E Λ μ u y hg hu hΛ hy hyh hy0
        apply compact_span_le_isotypic_part hy _ hyh
        have hab : a ≠ b := fun h => hne (h ▸ rfl)
        rcases lt_or_gt_of_ne hab with h | h
        · exact absurd ⟨a, b, h, hne, rfl⟩ hμ
        · exact ⟨a, b, h, hne, rfl⟩
    · apply isotypic_part_le_of_forall
      intro y hy μ hμ hyh
      apply compact_span_le_isotypic_part hy _ hyh
      rintro ⟨a', b', h', hne', heq'⟩
      obtain ⟨a, b, h, hne, rfl⟩ := hμ
      obtain ⟨e1, e2⟩ := root_injective_of_ne (ne_of_gt h) (add_left_cancel heq')
      subst e1; subst e2
      exact absurd h (not_lt.mpr h'.le)
  refine ⟨fun F hF G hG => h1 F hF G (heq ▸ hG), ?_⟩
  rw [← heq]
  exact h2
end Formalism.REAL
