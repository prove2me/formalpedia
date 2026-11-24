-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stationaryPhaseOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:35.106582+00:00
-- url     : https://prove2.me/submissions/167c3516-f8ed-41d5-a65f-f4dd436163e6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals
import Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_fin_supp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_intK_eq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_root_piece
import Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_ball_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism.FourierDecayAlt.P.HessianScalingIntegrals
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.StationaryAssemble := by
  intro hNS hMorse hRef hMod hRF _ _ _ _ _ hRS hSM hGA _ K _ _ _ R ψ hD hn m hm γ hγ L₀ Λ₁ Q hL₀ hΛ₁
    hQ hQu
  obtain ⟨VM, hVM, hM⟩ := hMorse K R ψ hD hn m hm Q hQ hQu
  obtain ⟨VS, hVS, hS⟩ := hRS K R ψ hD hn (m + 1) (by omega) Q hQ hQu
  have hΛ₁n : (Λ₁ : Set K) ∈ 𝓝 (0 : K) := hΛ₁.1.mem_nhds Λ₁.zero_mem
  obtain ⟨B, hB, hBV⟩ := hSM K R ψ hD hn (VM ∩ VS ∩ (Λ₁ : Set K))
    (inter_mem (inter_mem hVM hVS) hΛ₁n)
  obtain ⟨VN, hVN, hN⟩ := hNS K R ψ hD hn m hm L₀ Λ₁ B.toAddSubgroup Q hL₀ hΛ₁ hB hQ hQu
  obtain ⟨VG, hVG, hG⟩ := hGA K R ψ hD hn m B.toAddSubgroup Q hB hQ hQu
  refine ⟨VN ∩ VG, inter_mem hVN hVG, ?_⟩
  intro t D' A ht hD' hA Λ hΛ hF

  have hΛn : (Λ : Set K) ∈ 𝓝 (0 : K) := hΛ.1.mem_nhds Λ.zero_mem
  have hBn : (B : Set K) ∈ 𝓝 (0 : K) := hB.1.mem_nhds B.zero_mem
  obtain ⟨Λ', hΛ', hΛ'V⟩ := hSM K R ψ hD hn ((Λ : Set K) ∩ (B : Set K)) (inter_mem hΛn hBn)
  have hΛ'Λ : Λ'.toAddSubgroup ≤ Λ := fun x hx => (hΛ'V hx).1
  have hΛ'B : Λ' ≤ B := fun x hx => (hΛ'V hx).2
  set F : (Fin m → K) → ℂ := fun x => A x * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)) with hFdef
  have hFsupp : ∀ x, F x ≠ 0 → ∀ i, x i ∈ L₀ := fun x hx i =>
    (hA.1 x (left_ne_zero_of_mul hx) i).1
  have hF' : LatInvN Λ'.toAddSubgroup F := fun x l hl => hF x l fun i => hΛ'Λ (hl i)
  rw [← hRef K R ψ hD Λ Λ'.toAddSubgroup L₀ m F hΛ hΛ' hL₀ hΛ'Λ hFsupp hF]

  have hfin : {z : Kˣ | z ^ (m + 1) = D'}.Finite :=
    @hRF K _ hD.artin hD.red (m + 1) (by omega) D'
  have hzQ : ∀ z : Kˣ, z ^ (m + 1) = D' → (z : K) ^ (m + 1) = (D' : K) := fun z hz => by
    rw [← hz, Units.val_pow_eq_pow_val]
  have hsep : ∀ z z' : Kˣ, z ^ (m + 1) = D' → z' ^ (m + 1) = D' → ∀ x : Fin m → K,
      (∀ k, x k - (z : K) ∈ B) → (∀ k, x k - (z' : K) ∈ B) → z = z' := by
    intro z z' hz hz' x hx hx'
    refine hS z z' (by rw [hzQ z hz]; exact hD') (hz.trans hz'.symm) ?_
    have h1 := B.sub_mem (hx' ⟨0, hm⟩) (hx ⟨0, hm⟩)
    have h2 : (z : K) - (z' : K) = x ⟨0, hm⟩ - (z' : K) - (x ⟨0, hm⟩ - (z : K)) := by ring
    rw [h2]
    exact (hBV h1).1.2
  set Foff : (Fin m → K) → ℂ := fun x =>
    if ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup then 0 else F x with hFoff
  set Fz : Kˣ → (Fin m → K) → ℂ := fun z x => if ∀ k, x k - (z : K) ∈ B then F x else 0 with hFz
  have hdec : ∀ x, F x = Foff x + ∑ z ∈ hfin.toFinset, Fz z x := by
    intro x
    by_cases h : ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup
    · obtain ⟨z0, hz0, hx0⟩ := h
      have h1 : Foff x = 0 := if_pos ⟨z0, hz0, hx0⟩
      rw [h1, zero_add, Finset.sum_eq_single z0]
      · exact (if_pos hx0).symm
      · intro z hz hne
        refine if_neg fun hx => hne ?_
        exact hsep z z0 (by simpa using hz) hz0 x hx hx0
      · intro hz
        exact absurd (by simpa using hz0) hz
    · have h1 : Foff x = F x := if_neg h
      rw [h1, Finset.sum_eq_zero, add_zero]
      intro z hz
      exact if_neg fun hx => h ⟨z, by simpa using hz, hx⟩
  have hFoffInv : LatInvN Λ'.toAddSubgroup Foff := by
    intro x l hl
    have h1 : (∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, (x + l) k - (z : K) ∈ B.toAddSubgroup) ↔
        ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup :=
      exists_congr fun z => and_congr_right fun _ =>
        ball_iff B.toAddSubgroup x l z fun k => hΛ'B (hl k)
    simp only [hFoff]
    rw [if_congr h1 rfl (hF' x l hl)]
  have hFzInv : ∀ z : Kˣ, LatInvN Λ'.toAddSubgroup (Fz z) := by
    intro z x l hl
    have h1 : (∀ k, (x + l) k - (z : K) ∈ B) ↔ ∀ k, x k - (z : K) ∈ B :=
      ball_iff B.toAddSubgroup x l z fun k => hΛ'B (hl k)
    simp only [hFz]
    rw [if_congr h1 (hF' x l hl) rfl]
  have hFoffSupp : ∀ x, Foff x ≠ 0 → ∀ i, x i ∈ L₀ := by
    intro x hx
    apply hFsupp
    intro h0
    apply hx
    simp only [hFoff, h0, ite_self]
  have hFzSupp : ∀ z x, Fz z x ≠ 0 → ∀ i, x i ∈ L₀ := by
    intro z x hx
    apply hFsupp
    intro h0
    apply hx
    simp only [hFz, h0, ite_self]
  have hS0 := fin_supp Λ'.toAddSubgroup L₀ hΛ'.1 hL₀.2 m
  have hsplit : intK R Λ'.toAddSubgroup m F = intK R Λ'.toAddSubgroup m Foff +
      ∑ z ∈ hfin.toFinset, intK R Λ'.toAddSubgroup m (Fz z) := by
    rw [intK_eq_sum R _ L₀ m hS0 F hFsupp, intK_eq_sum R _ L₀ m hS0 Foff hFoffSupp]
    simp_rw [fun z => intK_eq_sum R _ L₀ m hS0 (Fz z) (hFzSupp z)]
    rw [← Finset.mul_sum, ← mul_add, Finset.sum_comm, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun y _ => hdec _
  have hoff : intK R Λ'.toAddSubgroup m Foff = 0 :=
    hN t D' A ht.1 hD' hA Λ'.toAddSubgroup hΛ' hFoffInv
  rw [hsplit, hoff, zero_add]
  have hrhs : (∑ᶠ z : Kˣ, if z ^ (m + 1) = D' then
          γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
            modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K)) else 0) =
      ∑ z ∈ hfin.toFinset, γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
            modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K)) := by
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · refine Finset.sum_congr rfl fun z hz => if_pos (by simpa using hz)
    · intro z hz
      simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
      by_contra h
      exact hz (if_neg h)
  rw [hrhs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz' : z ^ (m + 1) = D' := by simpa using hz
  have hzq : (z : K) ^ (m + 1) ∈ Q := by rw [hzQ z hz']; exact hD'
  exact root_piece R ψ m γ hγ Λ₁ B Λ' hB hΛ' hΛ'B (fun b hb => (hBV hb).2) A hA.2 t z (D' : K)
    (hzQ z hz') ⟨(hMod K R ψ hD z t).1, (hMod K R ψ hD t z).1, (hMod K R ψ hD z t).2⟩
    (hG t z ht.2 hzq) (hM B hB (fun b hb => (hBV hb).1.1) z hzq) (hFzInv z)
end Formalism.FourierDecayAlt.P
