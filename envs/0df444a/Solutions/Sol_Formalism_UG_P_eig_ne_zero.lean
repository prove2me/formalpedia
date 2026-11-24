-- Prove2me | solution 1 for Formalism.UG.P.eig_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:52.381248+00:00
-- url     : https://prove2.me/submissions/90f9955f-ef0f-4171-ad96-515933d628d2

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Matrix
namespace Formalism.UG.P
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hdet : IsUnit J.det) (i : n) : hJ.eigenvalues i ≠ 0 := by
  intro h0
  apply hdet.ne_zero
  rw [hJ.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])
end Formalism.UG.P
