-- Prove2me | solution 1 for Formalism.UG.P.stdform_sig_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:08:19.730554+00:00
-- url     : https://prove2.me/submissions/b3681cf4-0531-46cb-83b9-ef3d243adb4b

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Theorems.Thm_Formalism_UG_P_stdform_sig_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {p : ℕ} (M : Matrix n n ℂ) (hs : HasSignature M p 0) (y : n → ℂ)
    (hy : y ≠ 0) : 0 < stdformQ M y := by
  obtain ⟨e, P, hP⟩ := hs
  obtain ⟨x, hx0, hQ⟩ := stdform_sig_diag M e P hP y
  rw [hQ]
  simp only [Fin.sum_univ_zero, sub_zero]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (hx0 hy)
  rcases k with i | i
  · exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩
  · exact Fin.elim0 i
end Formalism.UG.P
