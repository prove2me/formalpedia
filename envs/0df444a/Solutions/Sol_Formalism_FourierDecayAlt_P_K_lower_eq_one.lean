-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.K.lower_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:29.402172+00:00
-- url     : https://prove2.me/submissions/cc689b58-e24d-423a-973a-34544a9eb29c

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_mulW_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_Wmul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.K
open Matrix Finset Real Formalism.FourierDecayAlt.K
variable {K : Type} [Field K] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.K
theorem _root_.solution {a c : Matrix (Fin n) (Fin n) K} {d : Fin n → K} (ha : IsUpUni a)
    (hc : IsUpUni c) (hd : ∀ x, d x ≠ 0)
    (h : a * (w0 n * diagonal d) = (w0 n * diagonal d) * c) : a = 1 := by
  ext i k
  rw [Matrix.one_apply]
  split_ifs with hik
  · subst hik
    exact ha.2 i
  · rcases lt_or_gt_of_ne hik with h' | h'
    · have e := congrFun (congrFun h i) (Fin.rev k)
      rw [mulW_apply, Wmul_apply, Fin.rev_rev] at e
      have hc0 : c (Fin.rev i) (Fin.rev k) = 0 := hc.1 (Fin.rev_lt_rev.mpr h')
      rw [hc0, mul_zero] at e
      exact (mul_eq_zero.mp e).resolve_right (hd _)
    · exact ha.1 h'
end Formalism.FourierDecayAlt.P.K
