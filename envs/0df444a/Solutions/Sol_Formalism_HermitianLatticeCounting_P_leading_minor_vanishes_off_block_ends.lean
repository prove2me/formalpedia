-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.leading_minor_vanishes_off_block_ends
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:31.01251+00:00
-- url     : https://prove2.me/submissions/2def7238-63a7-4268-80c8-dd66d4e07770

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gg_index_eq

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorVanishesOffBlockEnds := by
  intro R _ d c t q hq hne
  have hqd : q < d := lt_of_le_of_ne hq (by rw [← c.sizeUpTo_length]; exact hne _)
  set a : ℕ := (c.index ⟨q, hqd⟩ : ℕ) with ha
  have h1 : c.sizeUpTo a ≤ q := c.sizeUpTo_index_le ⟨q, hqd⟩
  have h2 : q < c.sizeUpTo (a + 1) := c.lt_sizeUpTo_index_succ ⟨q, hqd⟩
  have h1' : c.sizeUpTo a < q := lt_of_le_of_ne h1 (fun h => hne a h.symm)
  unfold leadingPrincipalMinor
  apply Matrix.det_eq_zero_of_row_eq_zero (⟨⟨c.sizeUpTo a, by omega⟩, h1'⟩ : {i : Fin d // (i : ℕ) < q})
  intro j
  have hj := j.2
  have hidx : (c.index ⟨c.sizeUpTo a, by omega⟩ : ℕ) = a :=
    gg_index_eq c _ a le_rfl (by simp; omega)
  simp only [Matrix.submatrix_apply, blockAntidiagonalMatrix]
  rw [if_neg]
  rintro ⟨-, h⟩
  rw [hidx] at h
  omega
end Formalism.HermitianLatticeCounting.P
