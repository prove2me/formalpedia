-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.integralBasisSpans.akCount_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:31.140856+00:00
-- url     : https://prove2.me/submissions/cf44ca54-daf1-4387-ab51-700160d0e70f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_congrP_int
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_qE_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_mk_form
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_mulVec
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_single
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_qE_bO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_eM_mulVec

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
    (k : ℕ) :
    akCount h (spanO b) 𝔭 k = Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) //
      Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X = H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))} := by
  unfold akCount
  refine Nat.card_congr ((eM b (extP K 𝔭 ^ k)).subtypeEquiv fun X => ?_)
  have key : ∀ x y x' y' : spanO b, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
      (CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) ↔
        star (qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk x)) ⬝ᵥ
          (((eM b (extP K 𝔭 ^ k) X)ᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *
            eM b (extP K 𝔭 ^ k) X) *ᵥ qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk y)) =
        star (qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk x)) ⬝ᵥ
          (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ
            qE b (extP K 𝔭 ^ k) (Submodule.Quotient.mk y))) := by
    intro x y x' y' hx hy
    rw [form_eq h b hH, form_eq h b hH, congrP_int h𝔭, mk_form, mk_form, ← qE_mk, ← qE_mk, ← qE_mk,
      ← qE_mk, hx, hy, ← eM_mulVec, ← eM_mulVec, form_mulVec]
  constructor
  · intro hX
    ext i j
    obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _ (X (Submodule.Quotient.mk (bO b i)))
    obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective _ (X (Submodule.Quotient.mk (bO b j)))
    have := (key _ _ x' y' hx' hy').1 (hX _ _ x' y' hx' hy')
    rwa [qE_bO, qE_bO, form_single, form_single] at this
  · intro hX x y x' y' hx hy
    rw [key x y x' y' hx hy, hX]
end Formalism.HermitianLattices.Ext.L3.integralBasisSpans
