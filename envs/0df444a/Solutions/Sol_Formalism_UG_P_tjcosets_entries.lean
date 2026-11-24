-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:46.611808+00:00
-- url     : https://prove2.me/submissions/59c60cc3-ae9c-4d87-8307-23efae7fa3c8

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Theorems.Thm_Formalism_UG_P_tjcosets_bc_apply
import Theorems.Thm_Formalism_UG_P_tjcosets_mem_par


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L]
variable (O : Subring L) [IsLocalRing O]
variable {O}
namespace Formalism.UG.P
theorem _root_.solution (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0)
    (hmax : ∀ x : O, ϖ⁻¹ * (x : L) ∈ O ↔ IsLocalRing.residue O x = 0)
    [Finite (IsLocalRing.ResidueField O)] (h : GL (Fin n) O) (hϖO : ϖ ∈ O) :
    (∀ a b : Fin n, (if (a : ℕ) < j then ϖ⁻¹ else 1) *
        (((h : Matrix (Fin n) (Fin n) O) a b : O) : L) * (if (b : ℕ) < j then ϖ else 1) ∈ O) ↔
      bc (IsLocalRing.residue O) h ∈ tjcosets_par n j := by
  rw [tjcosets_mem_par]
  constructor
  · intro hall a b ha hb
    have h1 := hall a b
    rw [if_pos ha, if_neg (not_lt.2 hb), mul_one] at h1
    rw [tjcosets_bc_apply]
    exact (hmax _).1 h1
  · intro hpar a b
    by_cases ha : (a : ℕ) < j <;> by_cases hb : (b : ℕ) < j
    · rw [if_pos ha, if_pos hb, mul_comm ϖ⁻¹, mul_assoc, inv_mul_cancel₀ hϖ, mul_one]
      exact ((h : Matrix (Fin n) (Fin n) O) a b).2
    · rw [if_pos ha, if_neg hb, mul_one]
      apply (hmax _).2
      have := hpar a b ha (not_lt.1 hb)
      rw [tjcosets_bc_apply] at this
      exact this
    · rw [if_neg ha, if_pos hb, one_mul]
      exact O.mul_mem ((h : Matrix (Fin n) (Fin n) O) a b).2 hϖO
    · rw [if_neg ha, if_neg hb, one_mul, mul_one]
      exact ((h : Matrix (Fin n) (Fin n) O) a b).2
end Formalism.UG.P
