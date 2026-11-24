-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:09.074967+00:00
-- url     : https://prove2.me/submissions/a46826e9-3545-4697-998c-917fab59f4ed

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonMajorizingLattice
import Definitions.Def_Lemmata_GeneralBFactSecondRest_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_majLattice_mem_span
import Theorems.Thm_Formalism_HermitianLatticesTheory_majLattice_B_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_majLattice_exists_c
import Theorems.Thm_Formalism_HermitianLatticesTheory_majLattice_exists_d
import Theorems.Thm_Formalism_HermitianLatticesTheory_majLattice_mem_zmap

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
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : MajLattice := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX L hL
  obtain ⟨d, hd, hdL⟩ := majLattice_exists_d b L hL.fg
  have hd' : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd
  constructor
  · have hmaps : Set.MapsTo (fun w => (d : ℝ) • w)
        (zmap (realize b X) L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))
        (Submodule.span ℤ (Set.range (majLattice_B X hX)) :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := (majLattice_mem_zmap b X L w).mp hw
      have h1 : (d : ℝ) • realize b X x = realize b X (d • x) := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      simp only [h1]
      apply majLattice_mem_span
      intro i
      have h2 : b.repr (d • x) i = (d : K) * b.repr x i := by
        rw [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]
      rw [h2]
      exact hdL x hx i
    have : DiscreteTopology (Submodule.span ℤ (Set.range (majLattice_B X hX)) :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) :=
      inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (majLattice_B X hX))))
    refine DiscreteTopology.of_continuous_injective
      ((continuous_const_smul (d : ℝ)).restrict hmaps) ?_
    intro p q hpq
    apply Subtype.ext
    have := congrArg Subtype.val hpq
    exact smul_right_injective _ hd' this
  · rw [eq_top_iff, ← (majLattice_B X hX).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨c, hc, hcL⟩ := majLattice_exists_c L hL.span_eq_top (b k.1)
    have hc' : (c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
    have hmem : (c : ℝ) • majLattice_B X hX k ∈ zmap (realize b X) L := by
      refine (majLattice_mem_zmap b X L _).mpr
        ⟨(RingOfIntegers.basis K k.2) • (c • b k.1), L.smul_mem _ hcL, ?_⟩
      rw [majLattice_B_apply b, integralBasis_apply, algebraMap_smul, smul_comm, map_zsmul,
        Int.cast_smul_eq_zsmul]
    have := Submodule.smul_mem (Submodule.span ℝ
      (zmap (realize b X) L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))
      (c : ℝ)⁻¹ (Submodule.subset_span hmem)
    rwa [inv_smul_smul₀ hc'] at this
end Formalism.HermitianLatticesTheory
