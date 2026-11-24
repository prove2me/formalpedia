-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.exists_ne_zero_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:52:50.302979+00:00
-- url     : https://prove2.me/submissions/933c7e89-a52a-419f-b1a9-03114e0c635d

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_SchurOrthogonalityCompact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero

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
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (p : K[X]) (hp : Irreducible p)
    (hdvd : p ∣ g.charpoly) : ∃ w : V, w ≠ 0 ∧ aeval g p w = 0 := by
  classical
  by_contra hcon
  have hinj : Function.Injective (aeval g p) := by
    refine (injective_iff_map_eq_zero (aeval g p)).2 fun w hw => ?_
    by_contra hw0
    exact hcon ⟨w, hw0, hw⟩
  haveI : Fact (Irreducible p) := ⟨hp⟩
  have hunit : IsUnit (aeval g p) := by
    first
      | exact (Module.End.isUnit_iff _).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
      | exact (LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj)
  have hunitL := hunit.map (Module.End.baseChangeHom K (AdjoinRoot p) V)
  have hE : Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p)
      = aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p))) := by
    rw [Polynomial.aeval_map_algebraMap, ← Polynomial.aeval_algHom_apply]
    rfl
  have hpr : Polynomial.eval (AdjoinRoot.root p) (p.map (algebraMap K (AdjoinRoot p))) = 0 := by
    rw [Polynomial.eval_map, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root p
  have hev : Module.End.HasEigenvalue (g.baseChange (AdjoinRoot p)) (AdjoinRoot.root p) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_baseChange]
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd _ hdvd) hpr
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have h0 : aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p))) v = 0 := by
    rw [Module.End.aeval_apply_of_hasEigenvector hv, hpr, zero_smul]
  rw [← hE] at h0
  have hbij : Function.Injective (Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p)) := by
    first
      | exact ((Module.End.isUnit_iff _).1 hunitL).1
      | exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hunitL)
  exact hv.2 (hbij (h0.trans (map_zero _).symm))
end Formalism.IrreducibleCountingLemmas.Z
