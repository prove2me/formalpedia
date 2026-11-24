-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.FE_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:11.847804+00:00
-- url     : https://prove2.me/submissions/b18935e2-e5ed-48f5-80d6-ccb742e255df

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_F_S_mul
import Theorems.Thm_Formalism_GM_euler_e_of_biHom
import Theorems.Thm_Formalism_GM_euler_w_of_biHom
import Theorems.Thm_P2M_Formalism_GM_tieE_apply__373a5b0b31bc
import Theorems.Thm_P2M_Formalism_GM_tieF_apply__aa4421b36bb1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution {a b : ℕ} {g : MvPolynomial σ K} (hg : BiHom w e a b g) :
    tieF w e (tieE w e g) = tieE w e (tieF w e g) + ((a + b + r : ℕ) : K) • g := by
  rw [tieE_apply', tieF_apply', F_S_mul hw he hwe g a b (euler_w_of_biHom w e hg) (euler_e_of_biHom w e hg),
    ← tieF_apply', ← tieE_apply']
end Formalism.GM.leadingTermLemmas
