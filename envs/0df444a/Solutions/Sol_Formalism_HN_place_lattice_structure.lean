-- Prove2me | solution 1 for Formalism.HN.place_lattice_structure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:15.999356+00:00
-- url     : https://prove2.me/submissions/f465a640-bd1a-4750-bc9f-93582c8e2bcb

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_injective
import Theorems.Thm_Formalism_HN_PlaceLattice_linIndep_real
import Theorems.Thm_Formalism_HN_PlaceLattice_discrete_span_of_linIndep
import Theorems.Thm_Formalism_HN_PlaceLattice_zl_span_eq
import Theorems.Thm_Formalism_HN_PlaceLattice_rk_span_eq
import Theorems.Thm_Formalism_HN_PlaceLattice_exists_denom
import Theorems.Thm_Formalism_F_covol_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField
noncomputable section
namespace Formalism.HN
namespace PlaceLattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
end PlaceLattice
end Formalism.HN
namespace Formalism.HN
namespace PlaceLattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
end PlaceLattice
end Formalism.HN
namespace Formalism.HN
namespace PlaceLattice
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end PlaceLattice
end Formalism.HN
namespace Formalism.HN
private theorem place_lattice_structure_lemma {E : Type*} [NormedAddCommGroup E] {A B : Submodule ℤ E}
    (h : A ≤ B) [Module.Finite ℤ B] : Module.finrank ℤ A ≤ Module.finrank ℤ B :=
  LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion h) (Submodule.inclusion_injective h)
private theorem place_lattice_structure_lemma_2 {R : Type*} [Ring R] {V : Type*} [AddCommGroup V] [Module R V]
    {E : Type*} [NormedAddCommGroup E] (ρ : V →+ E) {N₁ N₂ : Submodule R V} (h : N₁ ≤ N₂) :
    zl ρ N₁ ≤ zl ρ N₂ := by
  intro x hx
  change x ∈ AddSubgroup.map ρ N₁.toAddSubgroup at hx
  change x ∈ AddSubgroup.map ρ N₂.toAddSubgroup
  obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.mp hx
  exact AddSubgroup.mem_map.mpr ⟨a, h ha, rfl⟩
end Formalism.HN
end
end

set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open PlaceLattice
namespace Formalism.HN
theorem _root_.solution : PlLat := by
  intro K V ι _ _ _ _ _ _ _ _ _ b X hX L hL
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  have hinj : Function.Injective ρ := realize_injective b X hX
  obtain ⟨y, hy0, hyL⟩ := exists_denom (K := K) (⇑b) L hL (fun x _ => by rw [b.span_eq]; trivial)
  have hyK : ((y : K))⁻¹ ≠ 0 := inv_ne_zero (Int.cast_ne_zero.mpr hy0)
  have hdM : DiscreteTopology (zl ρ (Submodule.span (𝓞 K) (Set.range fun a => ((y : K))⁻¹ • b a))) := by
    rw [zl_span_eq]
    exact discrete_span_of_linIndep (linIndep_real b X hX _ hyK)
  have hdL : DiscreteTopology (zl ρ L) :=
    DiscreteTopology.of_continuous_injective (continuous_inclusion (place_lattice_structure_lemma_2 ρ hyL))
      (Set.inclusion_injective (place_lattice_structure_lemma_2 ρ hyL))
  refine ⟨⟨hinj.injOn, hdL⟩, ?_, ?_⟩
  · obtain ⟨t, htL, hspan, hli⟩ := exists_linearIndependent K (L : Set V)
    haveI : Module.Finite K V := Module.Finite.of_basis b
    have htf : t.Finite := hli.setFinite
    haveI : Fintype t := htf.fintype
    have hcard : rkK L = Fintype.card t := by
      have hc := finrank_span_eq_card hli
      rw [Subtype.range_coe] at hc
      unfold rkK
      rw [← hspan]
      exact hc
    have hsub : ∀ x ∈ L, x ∈ Submodule.span K (Set.range ((↑) : t → V)) := by
      intro x hx
      rw [Subtype.range_coe, hspan]
      exact Submodule.subset_span hx
    obtain ⟨z, hz0, hzL⟩ := exists_denom (K := K) ((↑) : t → V) L hL hsub
    have hzK : ((z : K))⁻¹ ≠ 0 := inv_ne_zero (Int.cast_ne_zero.mpr hz0)
    have hli' : LinearIndependent K (fun a : t => ((z : K))⁻¹ • (a : V)) :=
      hli.units_smul (fun _ => Units.mk0 _ hzK)
    have hlow : Submodule.span (𝓞 K) (Set.range ((↑) : t → V)) ≤ L := by
      rw [Submodule.span_le, Subtype.range_coe]
      exact htL
    have h1 : rk ρ (Submodule.span (𝓞 K) (Set.range ((↑) : t → V))) = Module.finrank ℚ K * Fintype.card t :=
      (rk_span_eq ρ hinj _ hli).trans (congrArg _ (Fintype.card_congr (Equiv.refl _)))
    have h2 : rk ρ (Submodule.span (𝓞 K) (Set.range fun a : t => ((z : K))⁻¹ • (a : V))) =
        Module.finrank ℚ K * Fintype.card t :=
      (rk_span_eq ρ hinj _ hli').trans (congrArg _ (Fintype.card_congr (Equiv.refl _)))
    haveI : Module.Finite ℤ (zl ρ (Submodule.span (𝓞 K) (Set.range fun a : t => ((z : K))⁻¹ • (a : V)))) := by
      rw [zl_span_eq]
      exact Module.Finite.span_of_finite ℤ (Set.finite_range _)
    haveI : Module.Finite ℤ (zl ρ L) :=
      Module.Finite.of_injective (Submodule.inclusion (place_lattice_structure_lemma_2 ρ hzL))
        (Submodule.inclusion_injective _)
    have hA : Module.finrank ℤ (zl ρ (Submodule.span (𝓞 K) (Set.range ((↑) : t → V)))) ≤
        Module.finrank ℤ (zl ρ L) := place_lattice_structure_lemma (place_lattice_structure_lemma_2 ρ hlow)
    have hB : Module.finrank ℤ (zl ρ L) ≤
        Module.finrank ℤ (zl ρ (Submodule.span (𝓞 K) (Set.range fun a : t => ((z : K))⁻¹ • (a : V)))) :=
      place_lattice_structure_lemma (place_lattice_structure_lemma_2 ρ hzL)
    rw [hcard]
    exact le_antisymm (hB.trans h2.le) (h1.symm.le.trans hA)
  · unfold ht
    haveI := hdL
    have hd : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
    exact mul_pos (mul_pos (pow_pos two_pos _) (Real.rpow_pos_of_pos hd _)) (F.covol_pos _)
end Formalism.HN
