-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_serIn_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:41.571779+00:00
-- url     : https://prove2.me/submissions/2d15abfe-3436-4df7-aa0b-04c28480880d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {A : Set σ} {F G : MvPowerSeries σ K} (hF : rtjSerIn A F) (hG : rtjSerIn A G) :
    rtjSerIn A (F * G) := by
  unfold rtjSerIn at hF hG ⊢
  intro μ hμ
  rw [MvPowerSeries.coeff_mul] at hμ
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  subst hp
  have h1 := hF p.1 (left_ne_zero_of_mul hne)
  have h2 := hG p.2 (right_ne_zero_of_mul hne)
  intro i hi
  rcases Finset.mem_union.mp (Finsupp.support_add hi) with h | h
  · exact h1 h
  · exact h2 h
end Formalism.L2.FormalSeriesBounds
