-- Prove2me | solution 1 for Formalism.IndefR.Rat.coord_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:33:31.691098+00:00
-- url     : https://prove2.me/submissions/2e407414-b1d8-44bf-bd05-c83015444b66

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_RationalAdjoints_CoordRat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Rat
open Matrix
namespace Formalism.IndefR.Rat
theorem _root_.solution {K : Type} [Field K] (σ : K →+* ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] {κ : Type} [Fintype κ]
    [DecidableEq κ] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : κ → Module.Dual ℂ E) (hψ : ∀ e, (∀ i, ψ i e = 0) → e = 0)
    (f : (ι → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f)
    (hfr : ∀ i l, ψ i (f (Pi.single l 1)) ∈ Set.range σ)
    (c : ι → ℂ) (hc : ∀ i, ψ i (f c) ∈ Set.range σ) : ∀ l, c l ∈ Set.range σ := by
  classical
  intro l

  choose A'' hA' using hfr
  choose b' hb' using hc
  set A' : Matrix κ ι K := Matrix.of A''
  have hfc : ∀ y : ι → ℂ, f y = ∑ m, y m • f (Pi.single m 1) := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => by
      rw [← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
  have hmul : ∀ y : ι → ℂ, ((A'.map σ) *ᵥ y) = fun i => ψ i (f y) := by
    intro y; funext i
    rw [hfc y, map_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, A', Matrix.of_apply, hA', map_smul,
      smul_eq_mul]
    exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  have hinj : Function.Injective (Matrix.toLin' A') := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (A'.map σ) *ᵥ (σ ∘ x) = 0 := by
      funext i
      rw [← RingHom.map_mulVec σ A' x i]
      have hx' : (A' *ᵥ x) i = 0 := by
        have := congrFun hx i; simpa using this
      simp [hx']
    rw [hmul] at h1
    have h2 : f (σ ∘ x) = 0 := hψ _ (fun i => congrFun h1 i)
    have h3 : (σ ∘ x) = 0 := hf (by rw [h2, map_zero])
    funext m
    have := congrFun h3 m
    simpa using this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A')
    (LinearMap.ker_eq_bot.mpr hinj)
  set L' : Matrix ι κ K := LinearMap.toMatrix' g
  have hLA : L' * A' = 1 := by
    have : LinearMap.toMatrix' (g.comp (Matrix.toLin' A')) = L' * A' := by
      rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
    rw [← this, hg, LinearMap.toMatrix'_id]
  have hLA' : (L'.map σ) * (A'.map σ) = 1 := by
    rw [← Matrix.map_mul, hLA, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hb : (A'.map σ) *ᵥ c = σ ∘ b' := by
    rw [hmul]; funext i; simp [hb']
  have hcL : c = (L'.map σ) *ᵥ (σ ∘ b') := by
    rw [← hb, Matrix.mulVec_mulVec, hLA', Matrix.one_mulVec]
  rw [hcL]
  exact ⟨(L' *ᵥ b') l, RingHom.map_mulVec σ L' b' l⟩
end Formalism.IndefR.Rat
