-- Prove2me | solution 1 for Formalism.L2.G.Cmp.map_of_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:08.435591+00:00
-- url     : https://prove2.me/submissions/a0e8d2f3-efe6-4140-85e4-17b75a6af425

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsHypA
import Theorems.Thm_Formalism_L2_G_Cmp_hform_fst
import Theorems.Thm_Formalism_L2_G_Cmp_hform_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
variable {T K : Type} [CommRing T] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
  (φ : T ≃+* K × K) (σ : T →+* T) (hσ : ∀ t, φ (σ t) = swapR K (φ t)) (Ov : Subring K) (S : Subring T)
  (hS : ∀ t, t ∈ S ↔ (φ t).1 ∈ Ov ∧ (φ t).2 ∈ Ov) (J : Matrix n n T) (Λ : Submodule S (n → T))
  (hΛ : ∀ y, y ∈ Λ ↔ ∀ z ∈ Λ, hform σ J z y ∈ S)
include hσ hS hΛ
namespace Formalism.L2.G.Cmp
theorem _root_.solution (x : GL n T) (hx : x ∈ UJ σ J)
    (h1 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ (((x : Matrix n n T) *ᵥ y) a)).1)
    (h2 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ ((((x⁻¹ : GL n T) : Matrix n n T) *ᵥ y) a)).1)
    (y : n → T) (hy : y ∈ Λ) : (x : Matrix n n T) *ᵥ y ∈ Λ := by
  have key : ∀ (K' : Matrix n n T) (a b : n → T), hform σ K' a b = (fun i => σ (a i)) ᵥ* K' ⬝ᵥ b := by
    intro K' a b
    simp only [hform, Matrix.vecMul, dotProduct, Finset.sum_mul]
    exact Finset.sum_comm
  have hgen : ∀ (M : Matrix n n T) (a b : n → T),
      hform σ J (M *ᵥ a) (M *ᵥ b) = hform σ (cT σ M * J * M) a b := by
    intro M a b
    have hmap : (fun i => σ ((M *ᵥ a) i)) = (M.map σ) *ᵥ (fun i => σ (a i)) := by
      funext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [key, key, hmap, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      Matrix.vecMul_vecMul]
    simp only [Matrix.mul_assoc]
    rfl
  have hU : cT σ (x : Matrix n n T) * J * (x : Matrix n n T) = J := hx
  have hz' : ∀ z : n → T, z = (x : Matrix n n T) *ᵥ (((x⁻¹ : GL n T) : Matrix n n T) *ᵥ z) := by
    intro z
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [hΛ]
  intro z hz
  rw [hS]
  have hinv : hform σ J z ((x : Matrix n n T) *ᵥ y) =
      hform σ J (((x⁻¹ : GL n T) : Matrix n n T) *ᵥ z) y := by
    nth_rewrite 1 [hz' z]
    rw [hgen, hU]
  refine ⟨?_, ?_⟩
  · obtain ⟨y', hy'Λ, hy'⟩ := h1 y hy
    have e : (φ (hform σ J z ((x : Matrix n n T) *ᵥ y))).1 = (φ (hform σ J z y')).1 := by
      rw [hform_fst φ σ hσ J, hform_fst φ σ hσ J]
      simp only [hy']
    rw [e]
    exact ((hS _).1 ((hΛ y').1 hy'Λ z hz)).1
  · obtain ⟨z', hz'Λ, hz'e⟩ := h2 z hz
    have e : (φ (hform σ J z ((x : Matrix n n T) *ᵥ y))).2 = (φ (hform σ J z' y)).2 := by
      rw [hinv, hform_snd φ σ hσ J, hform_snd φ σ hσ J]
      simp only [hz'e]
    rw [e]
    exact ((hS _).1 ((hΛ y).1 hy z' hz'Λ)).2
end Formalism.L2.G.Cmp
