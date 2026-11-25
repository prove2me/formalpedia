-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.wave_letters_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:55:09.532097+00:00
-- url     : https://prove2.me/submissions/bb38054e-5ce8-483a-92e3-b901496471ef

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdBelowOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx11
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : WaveLettersOne := by
  intro hPW R M _ _ _ _ _ _ Ξ L f pl dat y X X' κ Mx lv be hκ hsh hs hF
  have : Subsingleton (Fin (2 * 0 + 1)) := (inferInstance : Subsingleton (Fin 1))
  have h := hPW R M Ξ 0 L dat (fun a _ => y a) X X' hsh (fun a => Function.injective_of_subsingleton _)
  rw [Fintype.sum_subsingleton _ (fun _ => (0 : Fin (2 * 0 + 1)))] at h
  have hl : ∀ a : Fin L, F7.lagCo (fun _ : Fin (2 * 0 + 1) => y a) 0 = 1 := by
    intro a
    unfold F7.lagCo
    apply Finset.prod_eq_one
    intro i hi
    exact absurd (Subsingleton.elim _ _) (Finset.mem_erase.1 hi).1
  simp only [hl, Finset.prod_const_one, Complex.ofReal_one, one_mul] at h
  have hn : (∏ a, ‖(dat a).s‖) * ‖Ξ X X'‖ = ‖F7.Fw Ξ X X' (List.ofFn fun a => (dat a, y a)) 1 1‖ := by
    rw [← h, norm_mul, norm_prod]
  have h1 : (∏ a, ‖(dat a).s‖) = (∏ _a : Fin L, κ) * ∏ a, lv (pl a) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun a _ => hs a)
  have h2 : (∏ a, κ * be (pl a)) = (∏ _a : Fin L, κ) * ∏ a, be (pl a) := by
    rw [← Finset.prod_mul_distrib]
  have hP : 0 < ∏ _a : Fin L, κ := Finset.prod_pos (fun _ _ => hκ)
  rw [← hn, h1, h2, mul_assoc, mul_assoc] at hF
  exact le_of_mul_le_mul_left hF hP
end Formalism.FourierDecayAlt.P
