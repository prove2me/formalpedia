-- Prove2me | solution 1 for BookProof.SmCar.fermi_mass_gap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:10.05959+00:00
-- url     : https://prove2.me/submissions/ef90582f-7940-49b4-bdb1-6e775b32989f

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.fermi_mass_gap
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Theorems.Thm_BookProof_SmCar_normSq_eq_sum
import Theorems.Thm_BookProof_SmCar_fermiEnergy_quadForm
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {m : Fin n → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (hm : ∀ i, mu ≤ m i)
    (ψ : FermiFock n) (hvac : ψ ∅ = 0) :
    mu * ‖ψ‖ ^ 2 ≤ (inner ℂ ψ (fermiEnergy m ψ) : ℂ).re := by

  have hre : (inner ℂ ψ (fermiEnergy m ψ) : ℂ).re
      = ∑ S : Finset (Fin n), (∑ i ∈ S, m i) * ‖ψ S‖ ^ 2 := by
    rw [fermiEnergy_quadForm]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre, normSq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ => ?_
  rcases eq_or_ne S ∅ with rfl | hS
  · simp [hvac]
  · have hne : S.Nonempty := Finset.nonempty_of_ne_empty hS
    obtain ⟨i0, hi0⟩ := hne
    have hge : mu ≤ ∑ i ∈ S, m i := by
      have hsum : ∑ i ∈ S, mu ≤ ∑ i ∈ S, m i :=
        Finset.sum_le_sum fun i _ => hm i
      have hcard : (S.card : ℝ) * mu ≤ ∑ i ∈ S, m i := by
        simpa [Finset.sum_const, nsmul_eq_mul] using hsum
      have h1 : (1:ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨i0, hi0⟩
      nlinarith
    have hnn : (0:ℝ) ≤ ‖ψ S‖ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hge hnn
