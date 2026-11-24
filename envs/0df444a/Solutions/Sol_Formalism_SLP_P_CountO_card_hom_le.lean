-- Prove2me | solution 1 for Formalism.SLP.P.CountO.card_hom_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:25.660315+00:00
-- url     : https://prove2.me/submissions/d791304b-2164-47d8-9b74-58ee72a3bdc4

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace Formalism.SLP.P.CountO
theorem _root_.solution (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)] {X : Type}
    [AddCommGroup X] [Module R X] (k : ℕ) (s : Finset X) (hsk : s.card ≤ k)
    (hs : Submodule.span R (s : Set X) ⊔ P • ⊤ = ⊤) :
    Finite (X →ₗ[R] R ⧸ P) ∧ Nat.card (X →ₗ[R] R ⧸ P) ≤ Nat.card (R ⧸ P) ^ k := by
  classical
  let F : (X →ₗ[R] R ⧸ P) → (s → R ⧸ P) := fun φ x => φ x
  have hF : Function.Injective F := by
    intro φ₁ φ₂ h
    have hle : Submodule.span R (s : Set X) ⊔ P • ⊤ ≤ LinearMap.ker (φ₁ - φ₂) := by
      refine sup_le ?_ ?_
      · rw [Submodule.span_le]
        intro x hx
        have := congrFun h ⟨x, hx⟩
        simp only [F] at this
        simp [this]
      · refine Submodule.smul_le.mpr fun r hr n _ => ?_
        rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
    rw [hs, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at hle
    exact hle
  have : Finite (X →ₗ[R] R ⧸ P) := Finite.of_injective F hF
  refine ⟨this, ?_⟩
  calc Nat.card (X →ₗ[R] R ⧸ P) ≤ Nat.card (s → R ⧸ P) := Nat.card_le_card_of_injective F hF
    _ = Nat.card (R ⧸ P) ^ s.card := by rw [Nat.card_fun]; simp
    _ ≤ Nat.card (R ⧸ P) ^ k := Nat.pow_le_pow_right Nat.card_pos hsk
end Formalism.SLP.P.CountO
