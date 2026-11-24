-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FixedPointsGramVector.Hpk_fix_of_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:13:48.202601+00:00
-- url     : https://prove2.me/submissions/ab6ec9ad-8ae3-428b-944f-a563b0509138

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FixedPointsGramVector
open C2x5 C2x6 C2x7 HermitianProjections
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FixedPointsGramVector
theorem _root_.solution (y : Fin (2 * r + k + 1) → ℂ) (hy : phiL k r y = 0) : Hpk k r *ᵥ y = y := by
  have hsw : ∀ a : Fin r, y (eI k r a) = y (esI k r a) := by
    intro a
    have h := congrFun hy ⟨a.val, by omega⟩
    simp only [phiL, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, a.isLt, dif_pos] at h
    exact sub_eq_zero.1 h
  have hw : y ⟨r + k, by omega⟩ = 0 := by
    have h := congrFun hy ⟨r, by omega⟩
    simpa [phiL] using h
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rcases Nat.lt_or_ge i.val r with hi | hi
  · rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · have e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        simp only [Hpk]
        rw [if_pos ⟨hi, by show (i : ℕ) + (2 * r + k - i) = 2 * r + k; omega⟩]
      rw [e, one_mul]
      have := hsw ⟨i.val, hi⟩
      simp only [eI, esI] at this
      rw [← this]
    · intro b _ hb
      have hb' : b.val ≠ 2 * r + k - i.val := fun h => hb (Fin.ext h)
      simp only [Hpk]
      split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff] <;> omega
    · intro h; exact absurd (Finset.mem_univ _) h
  rcases Nat.lt_or_ge i.val (r + k) with hi2 | hi2
  · rw [Finset.sum_eq_single i]
    · have e : Hpk k r i i = 1 := by
        simp only [Hpk]
        rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hi, by omega, trivial⟩, if_neg (by omega)]
      rw [e, one_mul]
    · intro b _ hb
      simp only [Hpk]
      split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff] <;> omega
    · intro h; exact absurd (Finset.mem_univ _) h
  rcases eq_or_lt_of_le hi2 with hi3 | hi3
  · have hi4 : i = ⟨r + k, by omega⟩ := Fin.ext hi3.symm
    rw [hi4, hw, Finset.sum_eq_single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1))]
    · rw [hw, mul_zero]
    · intro b _ hb
      have hb' : b.val ≠ r + k := fun h => hb (Fin.ext h)
      simp only [Hpk, Fin.ext_iff, Fin.val_mk]
      split_ifs with h1 h2 h3 <;> first | omega | simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hlt : 2 * r + k - i.val < r := by omega
    rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · have e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        simp only [Hpk]
        rw [if_neg (by omega), if_pos ⟨hlt, by show (i : ℕ) + (2 * r + k - i) = 2 * r + k; omega⟩]
      rw [e, one_mul]
      have := hsw ⟨2 * r + k - i.val, hlt⟩
      simp only [eI, esI] at this
      rw [this]
      congr 1
      ext
      show 2 * r + k - (2 * r + k - i.val) = i.val
      omega
    · intro b _ hb
      have hb' : b.val ≠ 2 * r + k - i.val := fun h => hb (Fin.ext h)
      simp only [Hpk]
      split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff] <;> omega
    · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.FixedPointsGramVector
