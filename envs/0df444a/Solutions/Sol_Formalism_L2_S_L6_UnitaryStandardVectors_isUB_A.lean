-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.isUB_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:36:53.157901+00:00
-- url     : https://prove2.me/submissions/659f5993-c31f-4ee7-917b-88f7c7f44e8a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_IsUB_inv
import Theorems.Thm_P2M_Formalism_L2_S_L6_UnitaryStandardVectors_Z_ne__2f739ef805d0
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_conj_apply

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
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {m : ℕ}
variable {blk : Fin m → ℕ} (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a)
  (hanti : ∀ a b, blk a = blk b → a < b → π b < π a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hblk hanti hZ
namespace Formalism.L2.S.L6.UnitaryStandardVectors
theorem _root_.solution {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUB blk C) : IsUB blk (Z * C⁻¹ * Z⁻¹)ᴴ := by
  have hD := hC.inv
  have hM : ∀ j i, (Z * C⁻¹ * Z⁻¹) j i = Z j (π j) * C⁻¹ (π j) (π i) * (Z i (π i))⁻¹ :=
    fun j i => conj_apply π hπ Z hZ _ j i
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [conjTranspose_apply, hM, hD.1, mul_one, mul_inv_cancel₀ (Z_ne' π hπ Z hZ i),
      star_one]
  · rw [conjTranspose_apply, hM] at hij
    have h1 : C⁻¹ (π j) (π i) ≠ 0 := by
      intro h0
      apply hij
      rw [h0]
      simp
    obtain ⟨hle, hb⟩ := hD.2 _ _ h1
    refine ⟨?_, by simpa [hblk] using hb.symm⟩
    rcases hle.lt_or_eq with hlt | heq
    · have h2 := hanti _ _ hb hlt
      rw [hπ, hπ] at h2
      exact h2.le
    · have h2 := congrArg π heq
      rw [hπ, hπ] at h2
      exact h2.symm.le
end Formalism.L2.S.L6.UnitaryStandardVectors
