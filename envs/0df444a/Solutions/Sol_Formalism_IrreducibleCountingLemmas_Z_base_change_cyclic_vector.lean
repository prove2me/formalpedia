-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:46.357056+00:00
-- url     : https://prove2.me/submissions/367bc0c1-9663-40fc-a38a-350cdd6ce5b3

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_SchurOrthogonalityCompact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_exists_annihilator_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open scoped TensorProduct
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : BCCyclicVector := by
  unfold BCCyclicVector
  intro K V _ _ _ _ g hs
  classical
  obtain ⟨e, -, he⟩ := exists_annihilator_eq g hs g.charpoly dvd_rfl
  let φ : K[X] →ₗ[K] V :=
    { toFun := fun q => aeval g q e
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  let ψ : Polynomial.degreeLT K (Module.finrank K V) →ₗ[K] V :=
    φ.comp (Polynomial.degreeLT K (Module.finrank K V)).subtype
  have hdeg : g.charpoly.degree = (Module.finrank K V : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (LinearMap.charpoly_monic g).ne_zero,
      LinearMap.charpoly_natDegree]
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun x hx => ?_
    have hmem := Polynomial.mem_degreeLT.1 x.2
    have hd : g.charpoly ∣ x.1 := he x.1 hx
    exact Subtype.ext (Polynomial.eq_zero_of_dvd_of_degree_lt hd (by rw [hdeg]; exact hmem))
  haveI : FiniteDimensional K (Polynomial.degreeLT K (Module.finrank K V)) :=
    LinearEquiv.finiteDimensional (Polynomial.degreeLTEquiv K (Module.finrank K V)).symm
  have hfr : Module.finrank K (Polynomial.degreeLT K (Module.finrank K V)) = Module.finrank K V := by
    rw [(Polynomial.degreeLTEquiv K (Module.finrank K V)).finrank_eq]
    simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  refine ⟨e, fun v => ?_⟩
  obtain ⟨x, hx⟩ := hsurj v
  exact ⟨x.1, hx⟩
end Formalism.IrreducibleCountingLemmas.Z
