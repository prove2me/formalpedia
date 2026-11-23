-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5bCons_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:26.82647+00:00
-- url     : https://prove2.me/submissions/3d258412-459e-4dc0-aec8-f55b46c56dcb

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R : Type*} {r : ℕ} (u : Fin (r + 1) → R) (Y : Matrix (Fin r) (Fin (r + 1)) R)
    (a : Fin r) (j : Fin (r + 1)) : consRowMatrix u Y a.succ j = Y a j := rfl
end Formalism.HermitianLatticeCounting.P
