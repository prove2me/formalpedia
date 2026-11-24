-- Prove2me | solution 1 for Formalism.L2.G.Cmp.int_conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:58:09.335216+00:00
-- url     : https://prove2.me/submissions/30ab8d67-25ad-468c-bc5f-c30595dc313d

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsHypA

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
namespace Formalism.L2.G.Cmp
theorem _root_.solution {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n] (Ov : Subring K) (fr g : GL n K) :
    (∀ t : n → K, (∀ a, (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ t) a ∈ Ov) →
      ∀ a, (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((g : Matrix n n K) *ᵥ t)) a ∈ Ov) ↔
      ∀ a b, ((fr⁻¹ * g * fr : GL n K) : Matrix n n K) a b ∈ Ov := by
  have hmat : ∀ t : n → K, ((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((g : Matrix n n K) *ᵥ t) =
      ((fr⁻¹ * g * fr : GL n K) : Matrix n n K) *ᵥ (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ t) := by
    intro t
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  constructor
  · intro H a b
    have he : ((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((fr : Matrix n n K) *ᵥ Pi.single b 1) =
        Pi.single b 1 := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have h0 : ∀ c, (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((fr : Matrix n n K) *ᵥ Pi.single b 1)) c ∈ Ov := by
      intro c
      rw [he]
      by_cases hc : c = b
      · subst hc; simp
      · simp [Pi.single_apply, hc]
    have := H _ h0 a
    rw [hmat, he] at this
    simpa [Matrix.mulVec_single] using this
  · intro H t ht a
    rw [hmat]
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun b _ => mul_mem (H a b) (ht b)
end Formalism.L2.G.Cmp
