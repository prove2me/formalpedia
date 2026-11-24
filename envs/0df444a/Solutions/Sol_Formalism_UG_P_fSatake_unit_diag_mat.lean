-- Prove2me | solution 1 for Formalism.UG.P.fSatake_unit_diag_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:16.861641+00:00
-- url     : https://prove2.me/submissions/ea357f61-f267-4e57-a00b-32c94b6196be

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Theorems.Thm_Formalism_UG_P_fSatake_rev_iff
import Theorems.Thm_Formalism_UG_P_fSatake_cTJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution {M : Matrix (Fin n) (Fin n) L} (hb : ∀ i j : Fin n, j < i → M i j = 0)
    (hU : cT σ M * antiJ L n * M = antiJ L n) (i : Fin n) : σ (M i i) * M i.rev i.rev = 1 := by
  have h := congrFun (congrFun hU i) i.rev
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev] at h
  · rw [fSatake_cTJ, Fin.rev_rev,
      show antiJ L n i i.rev = 1 from if_pos ((fSatake_rev_iff i i.rev).2 (Fin.rev_rev i).symm)] at h
    exact h
  · intro l _ hl
    rw [fSatake_cTJ]
    rcases lt_or_gt_of_ne hl with h1 | h1
    · have h2 : i < l.rev := by
        simp only [Fin.lt_iff_val_lt_val, Fin.val_rev] at h1 ⊢
        omega
      rw [hb _ _ h2, map_zero, zero_mul]
    · rw [hb l i.rev h1, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.UG.P
