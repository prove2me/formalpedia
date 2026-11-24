-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace_zero_eq_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:41.380805+00:00
-- url     : https://prove2.me/submissions/2e741874-fc6b-4041-81d0-d0e93fb87cf0

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_besselSet_zero_iff_upper_triangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_besselChar_zero_eq_edge_sum
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_uniChar_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K] {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) K) V) (ψ₀ : AddChar K ℂ) :
    besselSpace ρ ψ₀ 0 0 = eqvSpace ρ (fun u : uniSub K N => (u : GL (Fin N) K))
      (fun u => ((uniChar ψ₀ N u : ℂˣ) : ℂ)) := by
  ext x
  constructor
  · intro h u
    have := h ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mpr u.2⟩
    show ρ (u : GL (Fin N) K) x = ((uniChar ψ₀ N u : ℂˣ) : ℂ) • x
    rw [uniChar_val, ← besselChar_zero_eq_edge_sum]
    exact this
  · intro h u
    have : ρ (u : GL (Fin N) K) x =
        ((uniChar ψ₀ N ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mp u.2⟩ : ℂˣ) : ℂ) • x :=
      h ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mp u.2⟩
    rw [uniChar_val, ← besselChar_zero_eq_edge_sum] at this
    exact this
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
