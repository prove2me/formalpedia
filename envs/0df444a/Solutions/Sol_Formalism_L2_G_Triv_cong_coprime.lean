-- Prove2me | solution 1 for Formalism.L2.G.Triv.cong_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:47:42.793527+00:00
-- url     : https://prove2.me/submissions/45e0553f-345d-4b44-8864-31e3e790dd92

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
import Theorems.Thm_Formalism_L2_G_Triv_one_add_pow_of_sq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {R : Type} [CommRing R] {k : ℕ}
namespace Formalism.L2.G.Triv
theorem _root_.solution (I : Ideal R) (hinf : (⨅ m : ℕ, I ^ m) = ⊥) (B : Matrix (Fin k) (Fin k) R)
    (hB : ∀ i j, (B - 1) i j ∈ I) (N : ℕ) (hN : IsUnit (N : R)) (hBN : B ^ N = 1) : B = 1 := by
  obtain ⟨c, hc⟩ := hN.exists_left_inv
  have step : ∀ m : ℕ, ∀ i j, (B - 1) i j ∈ I ^ (m + 1) := by
    intro m
    induction m with
    | zero => simpa using hB
    | succ m ih =>
      let φ := (Ideal.Quotient.mk (I ^ (m + 1 + 1))).mapMatrix (m := Fin k)
      have hXX : φ (B - 1) * φ (B - 1) = 0 := by
        rw [← map_mul]
        ext a b
        show Ideal.Quotient.mk _ (((B - 1) * (B - 1)) a b) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, Matrix.mul_apply]
        refine Ideal.sum_mem _ fun l _ => ?_
        have h1 : (B - 1) a l * (B - 1) l b ∈ I ^ (m + 1) * I ^ (m + 1) := Ideal.mul_mem_mul (ih a l) (ih l b)
        rw [← pow_add] at h1
        exact Ideal.pow_le_pow_right (by omega) h1
      have h2 : (1 + φ (B - 1)) ^ N = 1 := by
        have : 1 + φ (B - 1) = φ B := by rw [map_sub, map_one]; abel
        rw [this, ← map_pow, hBN, map_one]
      rw [one_add_pow_of_sq _ hXX] at h2
      have h3 : ((N : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I ^ (m + 1 + 1))) * φ (B - 1) = 0 := by
        simpa using h2
      intro i j
      have e : ((N : ℕ) : R ⧸ I ^ (m + 1 + 1)) * Ideal.Quotient.mk (I ^ (m + 1 + 1)) ((B - 1) i j) = 0 := by
        have h4 := congrFun (congrFun h3 i) j
        rw [← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul] at h4
        exact h4
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      calc Ideal.Quotient.mk (I ^ (m + 1 + 1)) ((B - 1) i j)
          = Ideal.Quotient.mk (I ^ (m + 1 + 1)) (c * (N : R)) * Ideal.Quotient.mk (I ^ (m + 1 + 1)) ((B - 1) i j) := by
            rw [hc, map_one, one_mul]
        _ = Ideal.Quotient.mk (I ^ (m + 1 + 1)) c *
            (((N : ℕ) : R ⧸ I ^ (m + 1 + 1)) * Ideal.Quotient.mk (I ^ (m + 1 + 1)) ((B - 1) i j)) := by
            rw [map_mul, map_natCast, mul_assoc]
        _ = 0 := by rw [e, mul_zero]
  have hz : B - 1 = 0 := by
    ext i j
    have : (B - 1) i j ∈ (⨅ m : ℕ, I ^ m) := by
      rw [Ideal.mem_iInf]
      intro m
      exact Ideal.pow_le_pow_right (Nat.le_succ m) (step m i j)
    rw [hinf] at this
    simpa using this
  exact sub_eq_zero.1 hz
end Formalism.L2.G.Triv
