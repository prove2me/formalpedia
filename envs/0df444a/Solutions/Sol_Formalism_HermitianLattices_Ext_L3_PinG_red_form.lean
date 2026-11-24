-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinG.red_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:30.94857+00:00
-- url     : https://prove2.me/submissions/d3e2f69b-0d09-4518-9fca-ec3bc67d4a38

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RedEqOfSubMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinG_red_of_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinG_red_smul_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_mk_form
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinG
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.PinG
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (w w' : ↥(locF 𝔭 (spanO b))) {z : 𝓞 K} (hz : h (w : V) (w' : V) = algebraMap (𝓞 K) K z) :
    star (red b h𝔭 k w) ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ red b h𝔭 k w') =
      Ideal.Quotient.mk (extP K 𝔭 ^ k) z := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨c, hc, hcw⟩ := exists_approx h𝔭 (spanO b) k w.2
  obtain ⟨c', hc', hcw'⟩ := exists_approx h𝔭 (spanO b) k w'.2
  rw [← red_smul_one b h𝔭 k hc w, ← red_smul_one b h𝔭 k hc' w',
    red_of_mem b h𝔭 k (ι c • w) hcw, red_of_mem b h𝔭 k (ι c' • w') hcw', ← mk_form]
  have e1 := form_eq h b hH ⟨_, hcw⟩ ⟨_, hcw'⟩
  have e2 : h (ι c • (w : V)) (ι c' • (w' : V)) = algebraMap (𝓞 K) K (ι (c * c') * z) := by
    rw [form_smul hF, hz, map_mul (algebraMap (𝓞 K) K)]
  have e3 := FaithfulSMul.algebraMap_injective (𝓞 K) K (e1.symm.trans e2)
  have e4 : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (c * c')) = 1 := by
    rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq, ← map_one ι, ← map_sub]
    apply ι_mem_pow
    have : c * c' - 1 = (c - 1) * c' + (c' - 1) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ hc) hc'
  calc _ = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (c * c') * z) := congrArg _ e3
    _ = _ := by rw [map_mul, e4, one_mul]
end Formalism.HermitianLattices.Ext.L3.PinG
