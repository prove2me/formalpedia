-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.relIndex_matL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:30:51.925668+00:00
-- url     : https://prove2.me/submissions/6717faaf-2848-4ffb-8d39-0d00b98dc309

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_unif_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_range_scal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_comap_scal
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_algebraMap_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_pK_anti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open NO
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {κ : Type} [Fintype κ] (f g : κ → κ → K) (hf : ∀ i j, f i j ∈ pK K 𝔭 0 ∧ f i j ≠ 0)
    (hg : ∀ i j, g i j ∈ pK K 𝔭 0 ∧ g i j ≠ 0) (k c : ℕ)
    (hle : matL 𝔭 (k + c) f g ≤ matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1)) :
    (matL 𝔭 (k + c) f g).relIndex (matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1)) *
        ∏ i, ∏ j, nO 𝔭 (f i j) =
      (∏ i, ∏ j, nO 𝔭 (g i j)) * Ideal.absNorm 𝔭 ^ (2 * Fintype.card κ ^ 2 * c) := by
  classical
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 : algebraMap F K (π : F) ≠ 0 := by
    rw [map_ne_zero]
    intro h
    apply hπ'
    rw [show π = 0 from RingOfIntegers.ext h]
    exact (𝔭 ^ 2).zero_mem
  set ϖ : K := algebraMap F K (π : F) with hϖ
  have hϖc : ϖ ^ c ∈ pK K 𝔭 0 :=
    pK_anti 𝔭 (Nat.zero_le c) ((mem_pK_iff_unif h𝔭 hπ hπ').2
      ⟨1, by simpa using algebraMap_mem_pK (K := K) 𝔭 1, (mul_one _).symm⟩)
  let d : κ → κ → K := fun i j => (f i j)⁻¹ * (g i j * ϖ ^ c)
  have hfd : ∀ i j, f i j * d i j = g i j * ϖ ^ c := fun i j =>
    mul_inv_cancel_left₀ (hf i j).2 _
  have hd : ∀ i j, d i j ∈ pK K 𝔭 0 := by
    intro i j
    have h1 : Matrix.single i j (ϖ ^ k * d i j) ∈ matL 𝔭 (k + c) f g := by
      intro i' j'
      by_cases h : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := h
        refine ⟨ϖ ^ (k + c) * 1, (mem_pK_iff_unif h𝔭 hπ hπ').2
          ⟨1, by simpa using algebraMap_mem_pK (K := K) 𝔭 1, rfl⟩, ?_⟩
        rw [Matrix.single_apply_same, mul_left_comm, hfd, pow_add]
        ring
      · refine ⟨0, (pK K 𝔭 (k + c)).zero_mem, ?_⟩
        rw [Matrix.single_apply, if_neg h, mul_zero, mul_zero]
    obtain ⟨w, hw, e⟩ := hle h1 i j
    rw [one_mul, one_mul, Matrix.single_apply_same] at e
    obtain ⟨b, hb, rfl⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 hw
    rw [mul_left_cancel₀ (pow_ne_zero k hπ0) e]
    exact hb
  have hn : ∀ i j, nO 𝔭 (d i j) * nO 𝔭 (f i j) = nO 𝔭 (g i j) * Ideal.absNorm 𝔭 ^ (2 * c) := by
    intro i j
    rw [mul_comm, ← nO_mul h𝔭 (hf i j).1 (hf i j).2 (hd i j), hfd,
      nO_mul h𝔭 (hg i j).1 (hg i j).2 hϖc, nO_unif_pow hK hF h𝔭 hπ hπ']
  have h1 : (matL 𝔭 (k + c) f g).relIndex (matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1)) =
      ∏ i, ∏ j, nO 𝔭 (d i j) := by
    rw [← range_scal h𝔭 hπ hπ' k, ← AddSubgroup.index_comap,
      comap_scal h𝔭 hπ hπ' hπ0 k c f g d (fun i j => (hf i j).2) hfd, AddSubgroup.index_pi,
      Fintype.prod_prod_type]
    rfl
  rw [h1]
  simp_rw [← Finset.prod_mul_distrib, hn, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← pow_mul]
  congr 2
  ring
end Formalism.HermitianLattices.Ext.L3.D2
