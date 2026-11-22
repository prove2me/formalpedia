-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.dualLattice_denom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:01.674311+00:00
-- url     : https://prove2.me/submissions/e69e3210-6af1-4497-bcee-051bcf010ac2

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {ι : Type*} [Fintype ι] (b : Basis ι K V) (L : Submodule R V)
    (hL : L.FG) : ∃ d : R, d ≠ 0 ∧ ∀ y ∈ L, d • y ∈ Submodule.span R (Set.range b) := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (Finset.image (fun p : V × ι => b.repr p.1 p.2) (S ×ˢ Finset.univ))
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  have key : ∀ v ∈ S, d • v ∈ Submodule.span R (Set.range b) := by
    intro v hv
    rw [← b.sum_repr v, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, hr⟩ := hint (b.repr v i) (Finset.mem_image.mpr ⟨(v, i), by simp [hv], rfl⟩)
    have hr' : algebraMap R K r = d • b.repr v i := hr
    rw [← smul_assoc, ← hr', algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)
  have hle : Submodule.span R (S : Set V) ≤
      (Submodule.span R (Set.range b)).comap (d • LinearMap.id : V →ₗ[R] V) := by
    rw [Submodule.span_le]
    intro v hv
    simpa using key v hv
  intro y hy
  rw [← hS] at hy
  simpa using hle hy
end Formalism.HermitianLatticesTheory
