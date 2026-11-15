-- Prove2me | solution 1 for DiazModulus.fischler_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:32:24.255258+00:00
-- url     : https://prove2.me/submissions/89e162fd-4814-4546-bff8-1052e341ee8b

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fischler_prop_5_5
import Theorems.Thm_DiazModulus_fischler_commute_of_trace
import Theorems.Thm_DiazModulus_remond_commuting_subspaces

open Complex ComplexConjugate

/-! # Fischler's Theorem 1.2: the centraliser of a matrix with Q̄-free entries in ℒ̃

Suppose `2·dim C(M) ≥ n² + 2`. Roy's corollary, applied to `ad M` on trace-zero matrices in coordinates
(Fischler's Proposition 5.5), gives two subspaces `U`, `V` of `Mat_n(ℂ)`, each spanned by algebraic
matrices, with `dim U + dim V ≥ n² + 2` and `Tr(M(AB − BA)) = 0` for all `A ∈ U`, `B ∈ V`. As the `n²`
entries of `M` are linearly independent over `Q̄`, the vanishing of these traces forces `AB = BA` on
`U × V`. Rémond's lemma bounds the dimensions of two mutually commuting subspaces of `Mat_n(ℂ)` by
`dim U + dim V ≤ n² + 1`, a contradiction. Hence `2·dim C(M) ≤ n² + 1`, i.e. `dim C(M) ≤ (n² + 1)/2`. -/

namespace RC3_FC
end RC3_FC

open DiazModulus in
theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hfree : LinearIndependent (↥Qbar) (fun p : Fin n × Fin n => M p.1 p.2)) :
    2 * Module.finrank ℂ ↥(Subalgebra.centralizer ℂ ({M} : Set (Matrix (Fin n) (Fin n) ℂ))) ≤
      n ^ 2 + 1 := by
  by_contra h
  obtain ⟨U, V, hU, hV, hdim, htr⟩ := DiazModulus.fischler_prop_5_5 M hM (by omega)
  have hcomm := DiazModulus.fischler_commute_of_trace M hfree U V hU hV htr
  have hle := DiazModulus.remond_commuting_subspaces U V hcomm
  omega
