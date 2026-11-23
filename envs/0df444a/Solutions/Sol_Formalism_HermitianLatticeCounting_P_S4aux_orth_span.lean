-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.orth_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:57.362495+00:00
-- url     : https://prove2.me/submissions/05da7e05-767e-4801-9ff3-43b656e7bd92

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_gen
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_proj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_li
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {O : Type} [CommRing O] [StarRing O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
  (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution [Nontrivial O] {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i))) :
    Module.Free O (Submodule.span O (Set.range v)) ∧
    Module.finrank O (Submodule.span O (Set.range v)) = Fintype.card κ ∧
    (∀ x, ∃ t ∈ Submodule.span O (Set.range v), ∀ t' ∈ Submodule.span O (Set.range v),
      h (x - t) t' = 0) ∧
    (∀ φ : Submodule.span O (Set.range v) →ₗ[O] O, ∃ w ∈ Submodule.span O (Set.range v),
      ∀ x : Submodule.span O (Set.range v), φ x = h x w) := by
  have hli := orth_li h v horth hunit
  choose u hu using hunit
  have hmem : ∀ i, v i ∈ Submodule.span O (Set.range v) := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Module.Free.of_basis (Module.Basis.span hli), ?_, fun x => ?_, fun φ => ?_⟩
  · rw [finrank_span_eq_card hli]
  · refine ⟨∑ i, (h x (v i) * ((u i)⁻¹ : Oˣ)) • v i,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i), fun t' ht' => ?_⟩
    obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 ht'
    rw [orth_pair_gen]
    exact Finset.sum_eq_zero fun j _ => by rw [orth_proj h v horth u hu, mul_zero]
  · refine ⟨∑ i, star (φ ⟨v i, hmem i⟩ * ((u i)⁻¹ : Oˣ)) • v i,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i), fun x => ?_⟩
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 x.2
    have hx : x = ∑ j, w j • (⟨v j, hmem j⟩ : Submodule.span O (Set.range v)) := by
      apply Subtype.ext
      rw [← hw]
      simp
    rw [← hw, orth_pair_left]
    conv_lhs => rw [hx, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, orth_pair_right h v horth, star_star, ← hu, mul_assoc,
      Units.inv_mul, mul_one]
end Formalism.HermitianLatticeCounting.P.S4aux
