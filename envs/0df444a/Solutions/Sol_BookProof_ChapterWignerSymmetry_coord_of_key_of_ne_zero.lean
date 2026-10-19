-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.coord_of_key_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:58:40.940475+00:00
-- url     : https://prove2.me/submissions/96e0e253-3c62-4fba-bf6a-2b4566dd88bc

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.coord_of_key_of_ne_zero
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
import Definitions.Def_ChapterWignerSymmetryInfinite
open BookProof.ChapterWignerSymmetry



open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {T : E → E}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

set_option maxHeartbeats 1000000 in
theorem solution (hS : WignerCoord S o) (κ : ℂ →+* ℂ) (hκn : ∀ z, ‖κ z‖ = ‖z‖)
    (hκc : ∀ z, κ (conj z) = conj (κ z))
    (hkey : ∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = κ (conj (v o) * v i))
    {v : ι → ℂ} (hv : v o ≠ 0) : ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v k = lam * κ (v k) := by

  have hκvo : κ (v o) ≠ 0 := by
    intro h
    apply hv
    have := hκn (v o)
    rw [h] at this
    simpa [eq_comm] using this.symm
  refine ⟨S v o / κ (v o), ?_, ?_⟩
  · rw [norm_div, hS.coord_norm v o, hκn]
    exact div_self (by simpa using hv)
  · intro k
    have hlam : S v o = (S v o / κ (v o)) * κ (v o) := by field_simp
    have hlamnorm : (S v o / κ (v o)) * conj (S v o / κ (v o)) = 1 := by
      rw [Complex.mul_conj]
      have hsq : Complex.normSq (S v o / κ (v o)) = ‖S v o / κ (v o)‖ ^ 2 := by rw [Complex.sq_norm]
      rw [hsq, norm_div, hS.coord_norm v o, hκn, div_self (by simpa using hv)]
      norm_num
    by_cases hk : k = o
    · subst hk; exact hlam
    · have h := hkey k hk v
      rw [map_mul, hκc] at h
      -- `conj (S v o) * S v k = conj (κ (v o)) * κ (v k)`
      have hconj : conj (S v o) = conj (S v o / κ (v o)) * conj (κ (v o)) := by
        rw [← map_mul, ← hlam]
      rw [hconj] at h
      have hne : conj (κ (v o)) ≠ 0 := by simpa using hκvo
      have hcancel : conj (S v o / κ (v o)) * S v k = κ (v k) := by
        refine mul_left_cancel₀ hne ?_
        calc conj (κ (v o)) * (conj (S v o / κ (v o)) * S v k)
            = conj (S v o / κ (v o)) * conj (κ (v o)) * S v k := by ring
          _ = conj (κ (v o)) * κ (v k) := h
      calc S v k = ((S v o / κ (v o)) * conj (S v o / κ (v o))) * S v k := by rw [hlamnorm]; ring
        _ = (S v o / κ (v o)) * (conj (S v o / κ (v o)) * S v k) := by ring
        _ = (S v o / κ (v o)) * κ (v k) := by rw [hcancel]
