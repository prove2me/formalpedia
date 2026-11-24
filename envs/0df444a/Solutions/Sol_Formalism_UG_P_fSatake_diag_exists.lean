-- Prove2me | solution 1 for Formalism.UG.P.fSatake_diag_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:09.151135+00:00
-- url     : https://prove2.me/submissions/c49c254e-9876-4d24-bd08-72eec31f2ed8

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Theorems.Thm_Formalism_UG_P_fSatake_rev_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (e : Fin n → L) (he : ∀ i, σ (e i) * e i.rev = 1) :
    ∃ d : GU σ n, (((d : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e ∧
      (((d⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        Matrix.diagonal (fun i => (e i)⁻¹) := by
  have hne : ∀ i, e i ≠ 0 := fun i h => by
    have := he i.rev
    rw [Fin.rev_rev, h, mul_zero] at this
    exact zero_ne_one this
  let g : GL (Fin n) L := ⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹),
    by simp [Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (hne _)],
    by simp [Matrix.diagonal_mul_diagonal, inv_mul_cancel₀ (hne _)]⟩
  have hc : cT σ (Matrix.diagonal e) = Matrix.diagonal (fun i => σ (e i)) := by
    ext a c
    by_cases h : a = c
    · subst h
      simp [cT]
    · simp [cT, Matrix.diagonal_apply, h, Ne.symm h]
  have hg : g ∈ GU σ n := by
    show cT σ (Matrix.diagonal e) * antiJ L n * Matrix.diagonal e = antiJ L n
    ext i l
    rw [hc, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [antiJ]
    split_ifs with h
    · have hl : l = i.rev := (fSatake_rev_iff l i).1 (by omega)
      subst hl
      simp [he i]
    · simp
  exact ⟨⟨g, hg⟩, rfl, rfl⟩
end Formalism.UG.P
