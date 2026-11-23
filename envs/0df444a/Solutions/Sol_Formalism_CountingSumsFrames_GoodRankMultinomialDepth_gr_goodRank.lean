-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GoodRankMultinomialDepth.gr_goodRank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:13.74488+00:00
-- url     : https://prove2.me/submissions/ea22c122-eca5-4799-88fc-997313b22bf5

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.GoodRankMultinomialDepth
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.CountingSumsFrames.GoodRankMultinomialDepth
theorem _root_.solution {A B ι : Type} [Fintype ι] [AddCommGroup A] [Module O A] [AddCommGroup B]
    [Module O B] {π : O} {f : A →ₗ[O] B} {D : ℕ} (h : GR ι π f D) :
    Formalism.G0.GoodRank π f (Fintype.card ι) D := by
  obtain ⟨u, v, huv⟩ := h
  let e : (Fin (Fintype.card ι) → O) ≃ₗ[O] (ι → O) :=
    LinearEquiv.funCongrLeft O O (Fintype.equivFin ι)
  refine ⟨u ∘ₗ e.toLinearMap, e.symm.toLinearMap ∘ₗ v, ?_⟩
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun huv (e x)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
  change e.symm (v (f (u (e x)))) = _
  rw [hx, map_smul, LinearEquiv.symm_apply_apply]
end Formalism.CountingSumsFrames.GoodRankMultinomialDepth
