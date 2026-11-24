-- Prove2me | solution 1 for Formalism.UG.P.stdform_sig_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:08:18.626265+00:00
-- url     : https://prove2.me/submissions/a67698b6-d802-482b-a719-860c0df870da

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
theorem _root_.solution {q : ℕ} (M : Matrix n n ℂ) (hs : HasSignature M 0 q) (y : n → ℂ)
    (hy : y ≠ 0) : stdformQ M y < 0 := by
  obtain ⟨e, P, hP⟩ := hs
  obtain ⟨x, hx0, hQ⟩ := stdform_sig_diag M e P hP y
  rw [hQ]
  simp only [Fin.sum_univ_zero, zero_sub, neg_lt_zero]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (hx0 hy)
  rcases k with i | i
  · exact Fin.elim0 i
  · exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩
end Formalism.UG.P
