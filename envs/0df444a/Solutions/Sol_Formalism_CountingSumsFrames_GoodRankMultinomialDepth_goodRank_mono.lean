-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GoodRankMultinomialDepth.goodRank_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:13.596454+00:00
-- url     : https://prove2.me/submissions/f7f8ba6a-d9c7-4eaf-a020-266016e41c4c

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
theorem _root_.solution {A B : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    {π : O} {f : A →ₗ[O] B} {n m D : ℕ} (h : Formalism.G0.GoodRank π f n D) (hmn : m ≤ n) :
    Formalism.G0.GoodRank π f m D := by
  classical
  obtain ⟨u, v, huv⟩ := h
  let i : (Fin m → O) →ₗ[O] (Fin n → O) :=
    LinearMap.pi (fun k => if hk : k.val < m then LinearMap.proj ⟨k.val, hk⟩ else 0)
  let p : (Fin n → O) →ₗ[O] (Fin m → O) := LinearMap.funLeft O O (Fin.castLE hmn)
  have hpi : ∀ x, p (i x) = x := by
    intro x
    funext k
    simp [p, i, LinearMap.funLeft_apply, Fin.castLE, k.isLt]
  refine ⟨u ∘ₗ i, p ∘ₗ v, ?_⟩
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun huv (i x)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
  rw [hx, map_smul, hpi]
end Formalism.CountingSumsFrames.GoodRankMultinomialDepth
