-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.projection_property
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:06:02.286786+00:00
-- url     : https://prove2.me/submissions/621ae240-5ce6-4bb4-9eb1-138d67552d3b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_cs

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.ProjClaim := by
  intro n H P U c hH hH2 hpos hPU horth hc hPn v hv
  have hE : ∀ x : Fin n → ℂ, star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
    intro x
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  have hEnn : ∀ x : Fin n → ℂ, 0 ≤ ∑ i, Complex.normSq (x i) :=
    fun x => Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hHv : ∀ u : Fin n → ℂ, herm H (H *ᵥ v) u = star u ⬝ᵥ v := by
    intro u; simp only [herm, Matrix.mulVec_mulVec, hH2, Matrix.one_mulVec]
  set w := P *ᵥ (H *ᵥ v) with hw
  have hwU : w ∈ U := hPU _
  have hwu : ∀ u ∈ U, herm H w u = star u ⬝ᵥ v := by
    intro u hu
    have := horth (H *ᵥ v) u hu
    simp only [herm, Matrix.mulVec_sub, dotProduct_sub, sub_eq_zero] at this
    rw [← hHv u]; simp only [herm]; exact this.symm

  have hEH : ∑ i, Complex.normSq ((H *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
    have h1 := hE (H *ᵥ v)
    have h2 := hE v
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hH, hH2, Matrix.one_mulVec, h2] at h1
    exact_mod_cast h1.symm
  set Ev := ∑ i, Complex.normSq (v i) with hEv
  set Ew := ∑ i, Complex.normSq (w i) with hEw
  have hw2 : Ew ≤ c ^ 2 * Ev := by rw [← hEH]; exact hPn _

  have hcsU := c2x3_cs H hH U hpos w v hwU hv
  rw [hwu v hv, hE v, Complex.normSq_ofReal] at hcsU

  have hpos1 : ∀ x ∈ (⊤ : Submodule ℂ (Fin n → ℂ)), x ≠ 0 → 0 < (herm 1 x x).re := by
    intro x _ hx0
    simp only [herm, Matrix.one_mulVec, hE, Complex.ofReal_re]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
      (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i))
  have hcs1 := c2x3_cs 1 (by simp) ⊤ hpos1 v w Submodule.mem_top Submodule.mem_top
  simp only [herm, Matrix.one_mulVec, hE, Complex.ofReal_re] at hcs1

  set ρ := (herm H w w).re with hρ
  have hρ2 : ρ ^ 2 ≤ (c * Ev) ^ 2 := by
    have h1 : ρ ^ 2 ≤ Complex.normSq (herm H w w) := by
      rw [hρ, Complex.normSq_apply]; nlinarith [sq_nonneg (herm H w w).im]
    rw [hwu w hwU] at h1
    have h2 : Complex.normSq (star w ⬝ᵥ v) ≤ Ev * Ew := hcs1
    have h3 : Ev * Ew ≤ Ev * (c ^ 2 * Ev) := mul_le_mul_of_nonneg_left hw2 (hEnn v)
    nlinarith
  have hcE : 0 ≤ c * Ev := mul_nonneg hc (hEnn v)
  have hρle : ρ ≤ c * Ev := by nlinarith
  have hvv := hcsU
  have hhv : 0 ≤ (herm H v v).re := by
    by_cases h0 : v = 0
    · subst h0; simp [herm]
    · exact le_of_lt (hpos v hv h0)
  by_cases hE0 : Ev = 0
  · rw [hE0]; exact mul_nonneg hc hhv
  · have hEpos : 0 < Ev := lt_of_le_of_ne (hEnn v) (Ne.symm hE0)
    have : Ev * Ev ≤ c * Ev * (herm H v v).re := by nlinarith
    nlinarith
end Formalism.FourierDecayAlt.P
