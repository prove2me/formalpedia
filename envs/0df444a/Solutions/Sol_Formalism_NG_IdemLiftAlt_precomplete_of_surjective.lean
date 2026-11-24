-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.precomplete_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:09:42.962747+00:00
-- url     : https://prove2.me/submissions/5b0bac3a-917f-48d9-9560-a1ded33a9c9d

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
import Theorems.Thm_Formalism_NG_IdemLiftAlt_map_mem_smul_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]
namespace Formalism.NG.IdemLiftAlt
theorem _root_.solution (I : Ideal O) {M N : Type*} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] [IsPrecomplete I M] (π : M →ₗ[O] N)
    (hπ : Function.Surjective π) : IsPrecomplete I N := by
  refine ⟨fun f hf => ?_⟩
  have hmap : ∀ k, (I ^ k • (⊤ : Submodule O M)).map π = I ^ k • (⊤ : Submodule O N) := by
    intro k
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hπ]
  have hd : ∀ k, ∃ d ∈ I ^ k • (⊤ : Submodule O M), π d = f (k + 1) - f k := by
    intro k
    have h1 : f (k + 1) - f k ∈ I ^ k • (⊤ : Submodule O N) := by
      have := (SModEq.sub_mem).1 (hf (show k ≤ k + 1 by omega))
      have := Submodule.neg_mem _ this
      simpa using this
    rw [← hmap] at h1
    obtain ⟨d, hd, hd'⟩ := h1
    exact ⟨d, hd, hd'⟩
  choose d hdm hdπ using hd
  obtain ⟨g0, hg0⟩ := hπ (f 0)
  let g : ℕ → M := fun k => g0 + ∑ i ∈ Finset.range k, d i
  have hg : ∀ k, π (g k) = f k := by
    intro k
    induction k with
    | zero => simp [g, hg0]
    | succ k ih =>
      have e : g (k + 1) = g k + d k := by simp [g, Finset.sum_range_succ, add_assoc]
      rw [e, map_add, ih, hdπ]; abel
  have hgc : ∀ m k, m ≤ k → g m - g k ∈ I ^ m • (⊤ : Submodule O M) := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      have e : g m - g (k + 1) = (g m - g k) - d k := by
        simp only [g, Finset.sum_range_succ]; abel
      rw [e]
      exact Submodule.sub_mem _ ih
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmk) (hdm k))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹_› (f := g) (fun {m k} hmk => (SModEq.sub_mem).2 (hgc m k hmk))
  refine ⟨π L, fun k => ?_⟩
  rw [SModEq.sub_mem, ← hg k, ← map_sub]
  exact map_mem_smul_top _ π ((SModEq.sub_mem).1 (hL k))
end Formalism.NG.IdemLiftAlt
