-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.Icc_eq_Ico_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:16.684191+00:00
-- url     : https://prove2.me/submissions/9d12e9a1-5858-48f0-af68-397d0aa5c27c

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

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
theorem _root_.solution (a b : ℕ) : Finset.Icc a b = Finset.Ico a (b + 1) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  constructor <;> intro h <;> omega
end Formalism.HermitianLatticeCounting.P
