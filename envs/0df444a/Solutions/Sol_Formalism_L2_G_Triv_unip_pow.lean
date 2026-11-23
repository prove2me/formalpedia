-- Prove2me | solution 1 for Formalism.L2.G.Triv.unip_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:26.131532+00:00
-- url     : https://prove2.me/submissions/634d94ee-b920-43c8-a207-af56d55f671c

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
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
theorem _root_.solution (I : Ideal R) (g : ℕ) (hg : g.Prime) (hgI : (g : R) ∈ I) (A : Matrix (Fin k) (Fin k) R)
    (hA : ∀ i j, j ≤ i → (A - 1) i j ∈ I) (s : ℕ) (hs : k ≤ g ^ s) (i j : Fin k) : (A ^ (g ^ s) - 1) i j ∈ I := by
  let π := Ideal.Quotient.mk I
  let φ := π.mapMatrix (m := Fin k)
  let N : Matrix (Fin k) (Fin k) (R ⧸ I) := φ (A - 1)
  have hN0 : ∀ i j : Fin k, j ≤ i → N i j = 0 := fun i j h =>
    Ideal.Quotient.eq_zero_iff_mem.2 (hA i j h)
  have hpow : ∀ m : ℕ, ∀ i j : Fin k, (j : ℕ) < i + m → (N ^ m) i j = 0 := by
    intro m
    induction m with
    | zero =>
      intro i j h
      rw [pow_zero, Matrix.one_apply, if_neg]
      rintro rfl
      omega
    | succ m ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : (l : ℕ) < i + m
      · rw [ih i l hl, zero_mul]
      · rw [hN0 l j (by rw [Fin.le_def]; omega), mul_zero]
  have hAm : φ A = N + 1 := by simp [N]
  have hg0 : ((g : ℕ) : R ⧸ I) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hgI
    simpa using this
  have key : (φ A) ^ (g ^ s) = 1 := by
    rw [hAm, (Commute.one_right N).add_pow, Finset.sum_eq_single 0]
    · simp
    · intro m hm hm0
      rw [Finset.mem_range] at hm
      by_cases hmm : m = g ^ s
      · have : N ^ m = 0 := by
          ext a b
          exact hpow m a b (by have := b.2; omega)
        rw [this]; simp
      · have hd : g ∣ (g ^ s).choose m := hg.dvd_choose_pow hm0 hmm
        obtain ⟨c, hc⟩ := hd
        have : (((g ^ s).choose m : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0 := by
          rw [hc, Nat.cast_mul]
          have : ((g : ℕ) : Matrix (Fin k) (Fin k) (R ⧸ I)) = 0 := by
            ext a b
            simp [Matrix.natCast_apply, hg0]
          rw [this, zero_mul]
        rw [this, mul_zero]
    · intro h; simp at h
  have : φ (A ^ (g ^ s) - 1) = 0 := by rw [map_sub, map_pow, key, map_one, sub_self]
  have h2 := congrFun (congrFun this i) j
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2
end Formalism.L2.G.Triv
