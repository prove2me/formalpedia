-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowTiePSplit.X_sub_mul_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:27.124614+00:00
-- url     : https://prove2.me/submissions/81107ffb-ed81-42bb-89a9-2446019b6e8f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePSplit
open Polynomial Matrix
variable {K : Type} [Field K] {n : ℕ}
namespace Formalism.L2.FormalSeriesBounds.RowTiePSplit
theorem _root_.solution {ι : Type} [DecidableEq ι] {s : Finset ι} {v : ι → K} {i : ι} (hi : i ∈ s) :
    (X - Polynomial.C (v i)) * Lagrange.basis s v i =
      Polynomial.C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by
  rw [Lagrange.nodal_eq_mul_nodal_erase hi]
  simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib, Lagrange.nodalWeight, Lagrange.nodal,
    map_prod]
  ring
end Formalism.L2.FormalSeriesBounds.RowTiePSplit
