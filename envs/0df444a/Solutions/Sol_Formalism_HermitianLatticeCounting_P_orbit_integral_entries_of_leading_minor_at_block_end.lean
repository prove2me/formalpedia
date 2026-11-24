-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.orbit_integral_entries_of_leading_minor_at_block_end
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:51.609801+00:00
-- url     : https://prove2.me/submissions/3bd5ff25-4914-4f81-9013-a8d1f5758fcd

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gg_index_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_invariant_value_holds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_mixed_minor_vanishing
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_det_mem

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
theorem _root_.solution (hV : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorAtBlockEnd) : Formalism.HermitianLatticeCounting.ExpansionTerms.OrbitIntegralEntries := by
  intro K _ O d c t ht l u hl hu hO
  have hmem : ∀ q, leadingPrincipalMinor (blockAntidiagonalMatrix c t) q ∈ O := by
    intro q
    rw [← invariant_value_holds K d (blockAntidiagonalMatrix c t) l u q hl hu]
    unfold leadingPrincipalMinor
    exact gf_det_mem O _ fun i j => hO _ _
  have hne : ∀ p, leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo p) ≠ 0 := by
    intro p
    rw [hV K d c t p]
    exact Finset.prod_ne_zero_iff.mpr fun x _ =>
      mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ (ht x))
  refine ⟨fun p => ⟨hmem _, hne p⟩, fun a => ?_⟩
  have hlt : c.sizeUpTo (a : ℕ) < c.sizeUpTo ((a : ℕ) + 1) := c.sizeUpTo_strict_mono a.2
  have hle : c.sizeUpTo ((a : ℕ) + 1) ≤ d := c.sizeUpTo_le _
  let i : Fin d := ⟨c.sizeUpTo (a : ℕ), by omega⟩
  let j' : Fin d := ⟨c.sizeUpTo ((a : ℕ) + 1) - 1, by omega⟩
  have hi : (c.index i : ℕ) = a := gg_index_eq c i a le_rfl hlt
  have hj : (c.index j' : ℕ) = a := gg_index_eq c j' a
    (show c.sizeUpTo (a : ℕ) ≤ c.sizeUpTo ((a : ℕ) + 1) - 1 by omega)
    (show c.sizeUpTo ((a : ℕ) + 1) - 1 < c.sizeUpTo ((a : ℕ) + 1) by omega)
  have hia : c.index i = a := Fin.ext hi
  have hja : c.index j' = c.index i := Fin.ext (hj.trans hi.symm)
  have hmix := (mixed_minor_vanishing K d c t l u hl hu i j' (by rw [hi]) hja).2
    (show c.sizeUpTo ((a : ℕ) + 1) - 1 + 1 = c.sizeUpTo ((c.index i : ℕ) + 1) by rw [hi]; omega)
  rw [hia] at hmix
  have e : leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo (a : ℕ)) * t a = mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' := hmix.symm
  rw [e]
  unfold mixedMinor
  exact gf_det_mem O _ fun x y => hO _ _
end Formalism.HermitianLatticeCounting.P
