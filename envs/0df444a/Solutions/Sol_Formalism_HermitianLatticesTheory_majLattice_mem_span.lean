-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majLattice_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:56.54072+00:00
-- url     : https://prove2.me/submissions/7b4fbae2-0ca0-4e90-ac0b-afa3b28feabd

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonMajorizingLattice
import Definitions.Def_Lemmata_GeneralBFactSecondRest_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_majLattice_realize_eq

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
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : ∀ i, IsIntegral ℤ (b.repr x i)) :
    realize b X x ∈ Submodule.span ℤ (Set.range (majLattice_B X hX)) := by
  refine ((majLattice_B X hX).mem_span_iff_repr_mem ℤ _).mpr fun k => ?_
  have hr : (majLattice_B X hX).repr (realize b X x) k =
      (latticeBasis K).repr (mixedEmbedding K (b.repr x k.1)) k.2 := by
    rw [majLattice_realize_eq, show majLattice_alt X (fun i => mixedEmbedding K (b.repr x i)) =
      LinearMap.linearEquivOfInjective (majLattice_alt X) (majLattice_T_injective X hX)
        majLattice_finrank (fun i => mixedEmbedding K (b.repr x i)) from rfl]
    simp only [majLattice_B, Basis.map_repr, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, Pi.basis_repr]
  rw [hr]
  have hmem : mixedEmbedding K (b.repr x k.1) ∈
      Submodule.span ℤ (Set.range (latticeBasis K)) := by
    rw [mem_span_latticeBasis]
    exact LinearMap.mem_range.mpr ⟨⟨_, hx k.1⟩, rfl⟩
  exact ((latticeBasis K).mem_span_iff_repr_mem ℤ _).mp hmem k.2
end Formalism.HermitianLatticesTheory
