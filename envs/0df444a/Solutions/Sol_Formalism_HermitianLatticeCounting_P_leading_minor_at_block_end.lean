-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.leading_minor_at_block_end
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:14.874856+00:00
-- url     : https://prove2.me/submissions/eeb599b0-ddd8-4600-ac57-e488db82135f

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gg_index_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gg_step

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorAtBlockEnd := by
  intro R _ d c t p
  induction p with
  | zero =>
    have : IsEmpty {i : Fin d // (i : ℕ) < c.sizeUpTo 0} := ⟨fun i => by have := i.2; simp at this⟩
    simp [leadingPrincipalMinor]
  | succ p ih =>
    by_cases hp : p < c.length
    · have hs : c.sizeUpTo (p + 1) = c.sizeUpTo p + c.blocksFun ⟨p, hp⟩ := c.sizeUpTo_succ' ⟨p, hp⟩
      have hle : c.sizeUpTo p + c.blocksFun ⟨p, hp⟩ ≤ d := hs ▸ c.sizeUpTo_le _
      have hf : univ.filter (fun a : Fin c.length => (a : ℕ) < p + 1) =
          insert ⟨p, hp⟩ (univ.filter (fun a : Fin c.length => (a : ℕ) < p)) := by
        ext a
        simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
        omega
      rw [hf, Finset.prod_insert (by simp), ← ih, hs, mul_comm]
      apply gg_step _ _ _ _ hle
      · intro i j hi1 hi2 hj
        have hidx : (c.index i : ℕ) = p := gg_index_eq c i p hi1 (by omega)
        simp only [blockAntidiagonalMatrix]
        rw [if_neg]
        rintro ⟨h, -⟩
        have := c.sizeUpTo_index_le j
        rw [← h, hidx] at this
        omega
      · intro i j hi1 hi2 hj1 hj2
        have hidx : (c.index i : ℕ) = p := gg_index_eq c i p hi1 (by omega)
        have hjdx : (c.index j : ℕ) = p := gg_index_eq c j p hj1 (by omega)
        have hi' : c.index i = ⟨p, hp⟩ := Fin.ext hidx
        have hj' : c.index j = ⟨p, hp⟩ := Fin.ext hjdx
        simp only [blockAntidiagonalMatrix, hi', hj', true_and]
        congr 1
        exact propext ⟨fun h => by omega, fun h => by omega⟩
    · have hp' : c.length ≤ p := not_lt.mp hp
      have he : c.sizeUpTo (p + 1) = c.sizeUpTo p := by
        rw [c.sizeUpTo_ofLength_le (p + 1) (by omega), c.sizeUpTo_ofLength_le p hp']
      rw [he, ih]
      apply Finset.prod_congr _ (fun _ _ => rfl)
      ext a
      have := a.2
      simp only [mem_filter, mem_univ, true_and]
      omega
end Formalism.HermitianLatticeCounting.P
