-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.card_le_of_chars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:05.374101+00:00
-- url     : https://prove2.me/submissions/b7b97914-0fc4-42ed-bab0-f8a3d4bd2868

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_char_indep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {F A L : Type} [CommRing F] [CommRing A] [Algebra F A] [Field L] {ι' ι : Type} [Fintype ι'] [Fintype ι]
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution (χ : ι' → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) : Fintype.card ι' ≤ Fintype.card ι := by
  have hli : LinearIndependent L (fun j : ι' => fun i : ι => χ j (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := char_indep χ hχ φ hφ e he b hb g (fun i => by
      have h3 := congrFun hg i
      rw [Finset.sum_apply] at h3
      exact h3)
    intro j
    simp [h0]
  simpa using hli.fintype_card_le_finrank
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
