-- Prove2me | solution 1 for Formalism.L2.Th1.D.KernelCokernelKilling.gLog_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:45.827367+00:00
-- url     : https://prove2.me/submissions/f6a642df-42fb-409f-8616-cb77b93c1ca0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_pow_inj
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_coeff_gLog_single
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_coeff_gLog_zero
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_map_gLog
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_of_not_dvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral letterLog entLog)
open Formalism.InvariantFactorPaths.G7 (frobVar frobVar_eq_expand UnrOK)
open Formalism.L2.Th1.D.KernelCokernelKilling
open MvPowerSeries
variable {K : Type} [Field K] {τ : Type} [DecidableEq τ] {l d : ℕ}
namespace Formalism.L2.Th1.D.KernelCokernelKilling
theorem _root_.solution [CharZero K] (hl : l.Prime) (ρ : K →+* K) (φ : ZMod d → τ) (s : ZMod d) :
    gLog K l φ s - C ((l : K)⁻¹) * frobVar (l ^ 2) (map ρ (gLog K l φ (s - 2))) = X (φ s) := by
  have hl2 : 2 ≤ l := hl.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hstep : ∀ e : ℕ, s - 2 * ((e + 1 : ℕ) : ZMod d) = s - 2 - 2 * (e : ZMod d) := by
    intro e
    push_cast
    ring
  rw [map_gLog]
  ext n
  rw [map_sub, coeff_C_mul, coeff_X]
  by_cases hn : ∃ e : ℕ, n = Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)
  · obtain ⟨e, rfl⟩ := hn
    rw [coeff_gLog_single hl2]
    cases e with
    | zero =>
      have hnd : ¬ l ^ 2 ∣ (Finsupp.single (φ (s - 2 * ((0 : ℕ) : ZMod d))) ((l ^ 2) ^ 0))
          (φ (s - 2 * ((0 : ℕ) : ZMod d))) := by
        rw [Finsupp.single_eq_same, pow_zero, Nat.dvd_one]
        intro h
        nlinarith
      rw [Formalism.InvariantFactorPaths.G7.coeff_frobVar_of_not_dvd hq _ hnd]
      simp
    | succ e =>
      have hne : Finsupp.single (φ (s - 2 * ((e + 1 : ℕ) : ZMod d))) ((l ^ 2) ^ (e + 1)) ≠
          Finsupp.single (φ s) 1 := by
        intro h
        rw [Finsupp.single_eq_single_iff] at h
        rcases h with ⟨_, h2⟩ | ⟨h2, _⟩
        · have : (l ^ 2) ^ 0 = (l ^ 2) ^ (e + 1) := by rw [pow_zero]; exact h2.symm
          exact absurd (pow_inj hl2 this) (by omega)
        · exact pow_ne_zero _ hq h2
      rw [if_neg hne]
      have hsm : Finsupp.single (φ (s - 2 * ((e + 1 : ℕ) : ZMod d))) ((l ^ 2) ^ (e + 1)) =
          (l ^ 2) • Finsupp.single (φ (s - 2 - 2 * (e : ZMod d))) ((l ^ 2) ^ e) := by
        rw [hstep, Finsupp.smul_single, smul_eq_mul, ← pow_succ']
      rw [hsm, Formalism.InvariantFactorPaths.G7.coeff_frobVar_smul hq, coeff_gLog_single hl2, pow_succ, mul_inv]
      ring
  · simp only [not_exists] at hn
    rw [coeff_gLog_zero φ s n hn]
    have hX : n ≠ Finsupp.single (φ s) 1 := by
      intro h
      apply hn 0
      rw [h]
      simp
    rw [if_neg hX]
    have hfz : coeff n (frobVar (l ^ 2) (gLog K l φ (s - 2))) = 0 := by
      by_contra hne
      obtain ⟨m, hm, hm0⟩ := Formalism.InvariantFactorPaths.G7.coeff_frobVar_ne_zero hq hne
      by_cases hm' : ∃ e : ℕ, m = Finsupp.single (φ (s - 2 - 2 * (e : ZMod d))) ((l ^ 2) ^ e)
      · obtain ⟨e, rfl⟩ := hm'
        apply hn (e + 1)
        rw [hm, hstep, Finsupp.smul_single, smul_eq_mul, ← pow_succ']
      · simp only [not_exists] at hm'
        exact hm0 (coeff_gLog_zero φ (s - 2) m hm')
    rw [hfz]
    simp
end Formalism.L2.Th1.D.KernelCokernelKilling
