-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_ff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:01.367843+00:00
-- url     : https://prove2.me/submissions/46871615-cbe0-45c5-aa71-e1e4f109f308

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
variable {S : Type*} [CommRing S] [HenselianLocalRing S]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {k : Type*} [Field k] [Finite k] (T N d : k)
    (hD : T ^ 2 - 4 * N ≠ 0) : ∃ a b : k, a ^ 2 + T * a * b + N * b ^ 2 = d := by
  classical
  have := Fintype.ofFinite k
  rcases Nat.mod_two_eq_zero_or_one (Fintype.card k) with h | h
  · obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (FiniteField.even_card_iff_char_two.2 h) d
    exact ⟨c, 0, by rw [hc]; ring⟩
  · have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero (fun hc => by
      rw [FiniteField.even_card_iff_char_two.1 hc] at h; exact absurd h (by decide))
    have hf : (X ^ 2 : k[X]).degree = 2 := by compute_degree!
    have hg : (C (-(T ^ 2 - 4 * N)) * X ^ 2 + C (-(4 * d)) : k[X]).degree = 2 := by
      compute_degree!
      intro h; exact hD (by linear_combination -h)
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg h
    simp at hxy
    refine ⟨(x - T * y) / 2, y, ?_⟩
    field_simp
    linear_combination hxy
end Formalism.HermitianLatticesTheory
