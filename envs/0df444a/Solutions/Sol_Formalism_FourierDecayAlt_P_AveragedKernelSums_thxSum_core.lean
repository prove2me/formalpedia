-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.thxSum_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:01.02627+00:00
-- url     : https://prove2.me/submissions/63ffb54c-727b-4d0f-9e26-586b70fdfc1f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_psi_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_card_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_orth
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_R_le_perp
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_card_eq
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
open Classical
namespace Formalism.FourierDecayAlt.P.AveragedKernelSums
theorem _root_.solution (hL : LocalDatum K R ψ) {L₁ : AddSubgroup K} (hle : L₁ ≤ R.toAddSubgroup)
    (A B : Finset K) (hB : IsReps B R.toAddSubgroup L₁) (hpp : perp ψ (perp ψ L₁) = L₁)
    (hfin : R.toAddSubgroup.relIndex (perp ψ L₁) ≠ 0)
    (hvol : volL R L₁ * volL R (perp ψ L₁) = 1) (m : ℕ) (τ : K → Kˣ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (h h' : Point K) :
    ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (Quotient.out x : K) ∈ perp ψ L₁ then
        thx R ψ m cr A B τ (Quotient.out x) h h' else 0) =
      ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ ρ ∈ A, ∑ b ∈ B,
        uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b)) := by
  classical
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => psi_R hL hr
  have hRP := R_le_perp hL hle
  have hcardT := card_alt hRP
  have hTfin : {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ perp ψ L₁}.Finite := by
    have : Finite {x : K ⧸ R.toAddSubgroup | Quotient.out x ∈ perp ψ L₁} :=
      Nat.finite_of_card_ne_zero (by rw [hcardT]; exact hfin)
    exact Set.toFinite _
  set Tf := hTfin.toFinset with hTfdef
  have hTf : ∀ x, x ∈ Tf ↔ Quotient.out x ∈ perp ψ L₁ := by
    intro x; rw [hTfdef, Set.Finite.mem_toFinset]; rfl
  have hTcard : Tf.card = B.card := by
    rw [← card_eq hL hle B hB hvol, ← hcardT, Nat.card_eq_card_finite_toFinset hTfin]
  have hB0 : (B.card : ℂ) ≠ 0 := by
    rw [← hTcard, ← Nat.card_eq_card_finite_toFinset hTfin, hcardT]
    exact_mod_cast hfin

  have hO : ∀ b ∈ B, ∀ b' ∈ B, ∑ x ∈ Tf,
      ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) =
        if b = b' then (B.card : ℂ) else 0 := by
    intro b hb b' hb'
    have e : ∀ x : K ⧸ R.toAddSubgroup,
        ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) =
          ψ (Quotient.out x * (b' - b)) := by
      intro x
      rw [hL.unitary, ← AddChar.map_add_eq_mul]
      congr 1; ring
    simp only [e]
    by_cases hbb : b = b'
    · subst hbb
      rw [if_pos rfl]
      simp [hTcard]
    · rw [if_neg hbb]
      have hc : b' - b ∈ R := R.sub_mem (hB.1 b' hb') (hB.1 b hb)
      have hnot : b' - b ∉ perp ψ (perp ψ L₁) := by
        rw [hpp]
        intro hmem
        obtain ⟨a, _, ha⟩ := hB.2 b' (hB.1 b' hb')
        have e1 : b = a := ha b ⟨hb, hmem⟩
        have e2 : b' = a := ha b' ⟨hb', by rw [sub_self]; exact L₁.zero_mem⟩
        exact hbb (e1.trans e2.symm)
      have : ∃ z₀ ∈ perp ψ L₁, ψ ((b' - b) * z₀) ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hnot hcon
      obtain ⟨z₀, hz₀, hne⟩ := this
      rw [mul_comm] at hne
      exact orth hψ hRP Tf hTf hc hz₀ hne
  have hS : ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (Quotient.out x : K) ∈ perp ψ L₁ then
        thx R ψ m cr A B τ (Quotient.out x) h h' else 0) =
      ∑ x ∈ Tf, thx R ψ m cr A B τ (Quotient.out x) h h' := by
    rw [finsum_eq_sum_of_support_subset (s := Tf)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [if_pos ((hTf x).mp hx)]
    · intro x hx
      rw [Finset.mem_coe, hTf]
      by_contra hcon
      exact hx (if_neg hcon)
  rw [hS]
  unfold thx
  rw [← Finset.mul_sum, Finset.sum_comm, mul_inv, mul_assoc, Finset.mul_sum (a := (B.card : ℂ)⁻¹)]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h1 : ∀ b ∈ B, ∑ x ∈ Tf, ∑ b' ∈ B,
      ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) *
        uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) =
      (B.card : ℂ) * uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b)) := by
    intro b hb
    rw [Finset.sum_comm]
    have h2 : ∀ b' ∈ B, ∑ x ∈ Tf,
        ψ (-(Quotient.out x * b)) * conj (ψ (-(Quotient.out x * b'))) *
          uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) =
        if b = b' then (B.card : ℂ) * uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b'))
          else 0 := by
      intro b' hb'
      rw [← Finset.sum_mul, hO b hb b' hb']
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq, if_pos hb]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← mul_assoc]
  congr 1
  field_simp
end Formalism.FourierDecayAlt.P.AveragedKernelSums
