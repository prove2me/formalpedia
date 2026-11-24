-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_matrix_of_isom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:56.060698+00:00
-- url     : https://prove2.me/submissions/ad2cf7fc-a2fb-456d-a2ac-1d019761e6c4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsUnitaryNear
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_col
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_jK_inj
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_coe_eq_sum
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_form_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b))) (N : ℕ) :
    ∃ Y : Matrix κ κ (𝓞 K), (∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ N) ∧
      ∀ i, g (b i) - ∑ l, Y l i • b l ∈ (extP K 𝔭 ^ N • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  have := h𝔭.isPrime
  have hgb : ∀ i, g (b i) ∈ locF 𝔭 (spanO b) := by
    intro i
    have h1 : g (b i) ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 (spanO b)) :=
      ⟨b i, le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩), rfl⟩
    rwa [hg.2] at h1
  choose c hc hcL using fun i => exists_approx h𝔭 (spanO b) N (hgb i)
  have hsum : ∀ i, ∑ l, crd b ⟨_, hcL i⟩ l • b l = ι (c i) • g (b i) := by
    intro i
    have := coe_eq_sum b ⟨_, hcL i⟩
    exact (Finset.sum_congr rfl fun l _ => (algebraMap_smul K _ _).symm).trans this.symm
  refine ⟨Matrix.of fun l i => crd b ⟨_, hcL i⟩ l, fun i j => ?_, fun i => ?_⟩
  · have h1 := form_eq h b hH ⟨_, hcL i⟩ ⟨_, hcL j⟩
    have h2 : h (ι (c i) • g (b i)) (ι (c j) • g (b j)) = jK (ι (c i * c j) * H i j) := by
      rw [form_smul hF, hg.1, ← hH, ← map_mul]
    have h3 : (ι (c i * c j) * H i j) = ((Matrix.of fun l i => crd b ⟨_, hcL i⟩ l)ᴴ * H *
        (Matrix.of fun l i => crd b ⟨_, hcL i⟩ l)) i j := by
      rw [form_col]
      exact jK_inj (h2.symm.trans h1)
    rw [Matrix.sub_apply, ← h3]
    have h4 : ι (c i * c j) * H i j - H i j = ι (c i * c j - 1) * H i j := by
      rw [map_sub, map_one]; ring
    rw [h4]
    apply Ideal.mul_mem_right
    apply ι_mem_pow
    have : c i * c j - 1 = (c i - 1) * c j + (c j - 1) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ (hc i)) (hc j)
  · have h1 : ∑ l, (Matrix.of fun l i => crd b ⟨_, hcL i⟩ l) l i • b l = ι (c i) • g (b i) := hsum i
    rw [h1]
    have h2 : g (b i) - ι (c i) • g (b i) = ι (-(c i - 1)) • g (b i) := by
      rw [map_neg, map_sub, map_one, neg_smul, sub_smul, one_smul]; abel
    rw [h2]
    exact Submodule.smul_mem_smul (ι_mem_pow (neg_mem (hc i))) (hgb i)
end Formalism.HermitianLattices.Ext.L3.HU
