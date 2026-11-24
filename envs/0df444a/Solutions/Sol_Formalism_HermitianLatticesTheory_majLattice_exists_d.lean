-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majLattice_exists_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:19.151993+00:00
-- url     : https://prove2.me/submissions/b2dc84c5-f9e3-4156-b22f-ede8cfd2ee32

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonMajorizingLattice
import Definitions.Def_Lemmata_GeneralBFactSecondRest_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_majLattice_common

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (b : Basis ι K V) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((d : K) * b.repr x i) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨d, hd, ht⟩ := majLattice_common (s.biUnion fun g => Finset.univ.image fun i => b.repr g i)
  refine ⟨d, hd, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    exact ht _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_coe.mp hg,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  | zero => intro i; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro i
    simp only [map_add, Finsupp.add_apply, mul_add]
    exact (hx i).add (hy i)
  | smul r x _ hx =>
    intro i
    have : b.repr (r • x) i = algebraMap (𝓞 K) K r * b.repr x i := by
      rw [← algebraMap_smul K r x, map_smul]; rfl
    rw [this, mul_left_comm]
    exact (RingOfIntegers.isIntegral_coe r).mul (hx i)
end Formalism.HermitianLatticesTheory
