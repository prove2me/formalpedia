-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.mixed_minor_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:37.288492+00:00
-- url     : https://prove2.me/submissions/cd4571ea-5ebd-48a2-b265-adb2fb804b60

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_lower_sub
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_lower_det
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_invariant_value_holds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_lead_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_one_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.MixedMinorVanishing := by
  intro R _ d c t l u hl hu i j' hi hj'
  have hid : (i : ℕ) + 1 ≤ d := Nat.succ_le_of_lt i.isLt
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin ((i : ℕ) + 1) → Fin d, ρ = fun a => Fin.castLE hid a := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin ((i : ℕ) + 1) → Fin d,
      κ = fun b : Fin ((i : ℕ) + 1) => if (b : ℕ) < (i : ℕ) then Fin.castLE hid b else j' := ⟨_, rfl⟩
  have hmono : StrictMono ρ := by subst hρ; exact fun a b h => h
  have hdown : ∀ a x, x ≤ ρ a → ∃ b, ρ b = x := by
    subst hρ
    exact fun a x hx => ⟨⟨x.1, lt_of_le_of_lt hx a.2⟩, rfl⟩
  have key : mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' = ((blockAntidiagonalMatrix c t * u).submatrix ρ κ).det := by
    have h0 : mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' = ((l * (blockAntidiagonalMatrix c t * u)).submatrix ρ κ).det := by
      subst hρ hκ
      rw [← Matrix.mul_assoc]
      rfl
    rw [h0, gf_lower_sub ρ hmono.injective hdown l hl, Matrix.det_mul, gf_lower_det ρ hmono l hl,
      one_mul]
  have hend : (i : ℕ) < c.sizeUpTo ((c.index i : ℕ) + 1) := c.lt_sizeUpTo_index_succ i
  have hrow : ∀ y : Fin d, (y : ℕ) + 1 < c.sizeUpTo ((c.index i : ℕ) + 1) →
      (blockAntidiagonalMatrix c t * u) i y = 0 := by
    intro y hy
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    unfold blockAntidiagonalMatrix
    split_ifs with h
    · have h1 : y < x := by
        rw [Fin.lt_def]; omega
      rw [hu.2 _ _ h1, mul_zero]
    · rw [zero_mul]
  have hlast : ρ (Fin.last (i : ℕ)) = i := by subst hρ; exact Fin.ext rfl
  have hκlt : ∀ b : Fin ((i : ℕ) + 1), (b : ℕ) < (i : ℕ) → ((κ b : Fin d) : ℕ) = (b : ℕ) := by
    intro b hb; subst hκ; simp [hb]
  have hκlast : κ (Fin.last (i : ℕ)) = j' := by subst hκ; simp
  have hrow0 : ∀ b : Fin ((i : ℕ) + 1), b ≠ Fin.last (i : ℕ) →
      ((blockAntidiagonalMatrix c t * u).submatrix ρ κ) (Fin.last (i : ℕ)) b = 0 := by
    intro b hb
    have hb' : (b : ℕ) < (i : ℕ) := Fin.val_lt_last hb
    rw [Matrix.submatrix_apply, hlast]
    apply hrow
    rw [hκlt b hb']; omega
  constructor
  · intro hj
    rw [key]
    apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last (i : ℕ))
    intro b
    by_cases hb : b = Fin.last (i : ℕ)
    · rw [hb, Matrix.submatrix_apply, hlast, hκlast]
      exact hrow j' hj
    · exact hrow0 b hb
  · intro hj
    rw [key, Matrix.det_succ_row _ (Fin.last (i : ℕ)), Finset.sum_eq_single (Fin.last (i : ℕ))]
    · have h1 : ((blockAntidiagonalMatrix c t * u).submatrix ρ κ) (Fin.last (i : ℕ)) (Fin.last (i : ℕ)) =
          t (c.index i) := by
        rw [Matrix.submatrix_apply, hlast, hκlast, Matrix.mul_apply, Finset.sum_eq_single j']
        · rw [hu.1, mul_one]
          unfold blockAntidiagonalMatrix
          rw [if_pos]
          exact ⟨hj'.symm, by omega⟩
        · intro x _ hx
          unfold blockAntidiagonalMatrix
          rw [if_neg, zero_mul]
          rintro ⟨_, h2⟩
          apply hx
          apply Fin.ext
          omega
        · intro h; exact absurd (Finset.mem_univ _) h
      have h2 : ((blockAntidiagonalMatrix c t * u).submatrix ρ κ).submatrix (Fin.last (i : ℕ)).succAbove
          (Fin.last (i : ℕ)).succAbove =
          (blockAntidiagonalMatrix c t * u).submatrix (Fin.castLE (le_of_lt i.isLt)) (Fin.castLE (le_of_lt i.isLt)) := by
        ext a b
        simp only [Matrix.submatrix_apply, Fin.succAbove_last]
        have ha : ρ a.castSucc = Fin.castLE (le_of_lt i.isLt) a := by subst hρ; exact Fin.ext rfl
        have hb : κ b.castSucc = Fin.castLE (le_of_lt i.isLt) b := by
          apply Fin.ext
          rw [hκlt _ (by simp)]
          rfl
        rw [ha, hb]
      have h3 : leadingPrincipalMinor (blockAntidiagonalMatrix c t * u) (i : ℕ) = leadingPrincipalMinor (blockAntidiagonalMatrix c t) (i : ℕ) := by
        have := invariant_value_holds R d (blockAntidiagonalMatrix c t) 1 u (i : ℕ) gf_one_lower hu
        rwa [Matrix.one_mul] at this
      rw [h1, h2, ← gf_lead_eq, h3]
      have h4 : ((-1 : R)) ^ (((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ) +
          ((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ)) = 1 := Even.neg_one_pow ⟨_, rfl⟩
      rw [h4, one_mul, mul_comm]
    · intro b _ hb
      rw [hrow0 b hb, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.HermitianLatticeCounting.P
