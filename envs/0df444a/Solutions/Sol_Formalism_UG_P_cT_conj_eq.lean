-- Prove2me | solution 1 for Formalism.UG.P.cT_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:14.094813+00:00
-- url     : https://prove2.me/submissions/76d444fe-a4e5-4bea-9978-14950b32bf7b

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution {m k : Type} (M : Matrix m k ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply]
end Formalism.UG.P
