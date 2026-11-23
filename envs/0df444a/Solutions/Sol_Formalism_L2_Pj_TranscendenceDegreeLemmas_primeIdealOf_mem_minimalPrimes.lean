-- Prove2me | solution 1 for Formalism.L2.Pj.TranscendenceDegreeLemmas.primeIdealOf_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:21.920211+00:00
-- url     : https://prove2.me/submissions/d974ca30-28ef-4c9e-8163-cf24299932f5

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.TranscendenceDegreeLemmas
open AlgebraicGeometry CategoryTheory
namespace Formalism.L2.Pj.TranscendenceDegreeLemmas
theorem _root_.solution {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hx : hZ.1.genericPoint ∈ V) :
    (hV.primeIdealOf ⟨_, hx⟩).asIdeal ∈ minimalPrimes Γ(X, V) := by
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen : IsGenericPoint hZ.1.genericPoint Z := by
    have := hZ.1.isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  refine ⟨⟨(hV.primeIdealOf ⟨_, hx⟩).isPrime, bot_le⟩, fun q hq hle => ?_⟩
  let y : PrimeSpectrum Γ(X, V) := ⟨q, hq.1⟩
  have hsp : y ⤳ hV.primeIdealOf ⟨_, hx⟩ := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  have hsp' : hV.fromSpec y ⤳ hZ.1.genericPoint := by
    have := hsp.map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at this
  have hirr : IsIrreducible (closure {hV.fromSpec y}) := isIrreducible_singleton.closure
  have hZle : Z ⊆ closure {hV.fromSpec y} := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp')) isClosed_closure
  have heq : closure {hV.fromSpec y} = Z := (hZ.2 hirr hZle).antisymm hZle
  have hmem : hV.fromSpec y ∈ Z := heq ▸ subset_closure rfl
  have hxy : hV.fromSpec y = hZ.1.genericPoint := (hsp'.antisymm (hgen.specializes hmem)).eq
  have hy : y = hV.primeIdealOf ⟨_, hx⟩ :=
    hV.fromSpec.isOpenEmbedding.injective (hxy.trans (hV.fromSpec_primeIdealOf ⟨_, hx⟩).symm)
  have := congrArg PrimeSpectrum.asIdeal hy
  exact le_of_eq this.symm
end Formalism.L2.Pj.TranscendenceDegreeLemmas
