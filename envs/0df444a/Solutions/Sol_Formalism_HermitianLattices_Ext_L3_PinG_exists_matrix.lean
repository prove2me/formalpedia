-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinG.exists_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:37.177713+00:00
-- url     : https://prove2.me/submissions/8de79683-219f-4332-ad6a-92c0adc041ac

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RedEqOfSubMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinG_red_bM
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinG_red_form
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinG_red_gM
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_mulVec
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_single


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
    (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b))) :
    ∃ G G' : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k),
      Gᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * G = H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) ∧
      G * G' = 1 ∧ ∀ w w' : ↥(locF 𝔭 (spanO b)), (w' : V) = g w →
        red b h𝔭 k w' = G *ᵥ red b h𝔭 k w := by
  have := h𝔭.isPrime
  have hg' : g⁻¹ ∈ autSub h (locF 𝔭 (spanO b)) := inv_mem hg
  refine ⟨gMat b h𝔭 k hg, gMat b h𝔭 k hg', ?_, ?_, ?_⟩
  · ext i j
    rw [← form_single (_ᴴ * _ * _) i j, ← form_mulVec, ← red_bM b h𝔭 k i, ← red_bM b h𝔭 k j,
      ← red_gM, ← red_gM, Matrix.map_apply]
    apply red_form h b hH h𝔭 k
    show h (g (b i)) (g (b j)) = _
    rw [hg.1 (b i) (b j), hH]
  · ext i j
    have h1 : (gMat b h𝔭 k hg * gMat b h𝔭 k hg') *ᵥ Pi.single j 1 = Pi.single j 1 := by
      rw [← mulVec_mulVec, ← red_bM b h𝔭 k j, ← red_gM, ← red_gM]
      congr 1
      apply Subtype.ext
      show g (g⁻¹ (b j)) = b j
      exact g.apply_symm_apply (b j)
    have h2 := congrFun h1 i
    rw [mulVec_single_one] at h2
    rw [Matrix.one_apply, ← Pi.single_apply]
    exact h2
  · intro w w' hww
    rw [← red_gM]
    congr 1
    apply Subtype.ext
    exact hww
end Formalism.HermitianLattices.Ext.L3.PinG
