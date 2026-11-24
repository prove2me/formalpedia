-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.integralBasisSpans.nkCount_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:21.283113+00:00
-- url     : https://prove2.me/submissions/7dbfb2d7-0498-4b9b-b76b-346e011678f9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_congrP_int
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_qE_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_mk_form
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.integralBasisSpans
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (n : 𝓞 F) :
    nkCount h (spanO b) 𝔭 k n = Nat.card {x : κ → 𝓞 K ⧸ extP K 𝔭 ^ k //
      star x ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ x) = Ideal.Quotient.mk _ (ι n)} := by
  unfold nkCount
  refine Nat.card_congr ((qE b (extP K 𝔭 ^ k)).toEquiv.subtypeEquiv fun x => ?_)
  have key : ∀ y : spanO b, CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ↔
      star (qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk y)) ⬝ᵥ
        (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ (qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk y))) =
        Ideal.Quotient.mk _ (ι n) := by
    intro y
    rw [form_eq h b hH, ← MeanB.algebraMap_comp, congrP_int h𝔭, mk_form, qE_mk]
  constructor
  · rintro ⟨y, rfl, hy⟩
    exact (key y).1 hy
  · intro hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨y, rfl, (key y).2 hx⟩
end Formalism.HermitianLattices.Ext.L3.integralBasisSpans
