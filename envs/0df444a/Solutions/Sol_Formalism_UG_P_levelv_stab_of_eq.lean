-- Prove2me | solution 1 for Formalism.UG.P.levelv_stab_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:26.692363+00:00
-- url     : https://prove2.me/submissions/ffa095fe-c922-4897-817a-a2889c810326

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Theorems.Thm_Formalism_UG_P_levelv_inv_mulVec
import Theorems.Thm_Formalism_UG_P_levelv_mulVec_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (Λ : Set (n → R)) (N : ℕ) (hinj : ∀ y y' : n → R, N • y = N • y' → y = y') (ga a b : GL n R)
    (hZ : (fun x => N • ((a : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x))) '' Λ =
      (fun x => N • ((b : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x))) '' Λ) (x : n → R) :
    x ∈ Λ ↔ ((ga⁻¹ * (a⁻¹ * b) * ga : GL n R) : Matrix n n R) *ᵥ x ∈ Λ := by
  have hk : ∀ y, ((ga⁻¹ * (a⁻¹ * b) * ga : GL n R) : Matrix n n R) *ᵥ y =
      ((ga⁻¹ : GL n R) : Matrix n n R) *ᵥ (((a⁻¹ : GL n R) : Matrix n n R) *ᵥ
        ((b : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ y))) := by
    intro y
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · intro hx
    have hmem : N • ((b : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x)) ∈
        (fun x => N • ((a : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x))) '' Λ := by
      rw [hZ]
      exact ⟨x, hx, rfl⟩
    obtain ⟨x', hx', he⟩ := hmem
    have he' := hinj _ _ he
    have hxx : x' = ((ga⁻¹ * (a⁻¹ * b) * ga : GL n R) : Matrix n n R) *ᵥ x := by
      rw [hk, ← he', levelv_inv_mulVec, levelv_inv_mulVec]
    rw [← hxx]
    exact hx'
  · intro hx
    have hmem : N • ((a : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ
        (((ga⁻¹ * (a⁻¹ * b) * ga : GL n R) : Matrix n n R) *ᵥ x))) ∈
        (fun x => N • ((b : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x))) '' Λ := by
      rw [← hZ]
      exact ⟨_, hx, rfl⟩
    obtain ⟨x', hx', he⟩ := hmem
    have he' := hinj _ _ he
    rw [hk, levelv_mulVec_inv, levelv_mulVec_inv] at he'
    have hxx : x' = x := by
      have h1 := congrArg (fun y => ((ga⁻¹ : GL n R) : Matrix n n R) *ᵥ
        (((b⁻¹ : GL n R) : Matrix n n R) *ᵥ y)) he'
      simpa only [levelv_inv_mulVec] using h1
    rw [← hxx]
    exact hx'
end Formalism.UG.P
