-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gg_index_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:07.710364+00:00
-- url     : https://prove2.me/submissions/e65ef708-2e7d-425f-b524-c1626f65482c

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {d : ℕ} (c : Composition d) (i : Fin d) (a : ℕ)
    (h1 : c.sizeUpTo a ≤ (i : ℕ)) (h2 : (i : ℕ) < c.sizeUpTo (a + 1)) : (c.index i : ℕ) = a := by
  have a1 := c.sizeUpTo_index_le i
  have a2 : (i : ℕ) < c.sizeUpTo ((c.index i : ℕ) + 1) := c.lt_sizeUpTo_index_succ i
  rcases lt_trichotomy (c.index i : ℕ) a with hlt | heq | hgt
  · have := c.monotone_sizeUpTo (show (c.index i : ℕ) + 1 ≤ a from hlt); omega
  · exact heq
  · have := c.monotone_sizeUpTo (show a + 1 ≤ (c.index i : ℕ) from hgt); omega
end Formalism.HermitianLatticeCounting.P
