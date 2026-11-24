-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.thetaOnDomainOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:39.187104+00:00
-- url     : https://prove2.me/submissions/5abb89d9-e894-4e36-a74a-442414fa81c3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanPositiveSemidefinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_psd_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_psd_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_finite_classes
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_finsum_ite_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_mean_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_reps_card_ne_zero

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
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.ThOmAssemble := by
  intro hGI hADE hLC hKH hMLC hLCh hLF hSU hSmU hUG hUNB hCP hUB hCSA hMM hKG hKBD hGRC hAB hPG hPD
    hPL hCM hCNE hTL hTB hTS hA2 hN1 K _ _ _ R ψ hD hch m hm hA13 n₀ F Lc Om hF hCut hOm
  classical
  obtain ⟨hLo, hLcpt, hRL, hNs0⟩ := hCut
  obtain ⟨D⟩ := hADE hLC hKH hMLC hLCh hLF K R ψ hD hch (m + 1) F Om (Lc : Set K) (by omega) hOm
    hLcpt
  obtain ⟨V₁, hV₁, hLow⟩ := hTL hGI hA2.2 hUG hN1 hCSA hMM hCP hKG hGRC hAB hCNE hCM hPL K R ψ hD hch
    m hm n₀ F Om (Lc : Set K) hF hOm D
  obtain ⟨V₂, hV₂, hSh⟩ := hSU K R ψ hD hch ((D.A ×ˢ D.B).image (fun p => p.1 + p.2))
  obtain ⟨t, ht⟩ := hSmU K R ψ hD hch (V₁ ∩ V₂) (Filter.inter_mem hV₁ hV₂)

  let τ : K → Kˣ := fun σ =>
    if h : IsUnit (((t⁻¹ : Kˣ) : K) + σ) then h.unit⁻¹ else 1
  have hmem : ∀ ρ ∈ D.A, ∀ b ∈ D.B, ρ + b ∈ (D.A ×ˢ D.B).image (fun p => p.1 + p.2) := by
    intro ρ hρ b hb
    exact Finset.mem_image.2 ⟨(ρ, b), Finset.mem_product.2 ⟨hρ, hb⟩, rfl⟩
  have hτ : ∀ ρ ∈ D.A, ∀ b ∈ D.B, IsShift t (τ (ρ + b)) (ρ + b) := by
    intro ρ hρ b hb
    have hu := (hSh t ht.2 _ (hmem ρ hρ b hb)).1
    simp only [IsShift, τ, dif_pos hu, inv_inv, IsUnit.unit_spec]
  have hτmod : ∀ ρ ∈ D.A, ∀ b ∈ D.B,
      modK R (τ (ρ + b) : K) * modK R ((t⁻¹ : Kˣ) : K) = modK R 1 := by
    intro ρ hρ b hb
    have h1 := (hSh t ht.2 _ (hmem ρ hρ b hb)).2
    have h2 := (hMM K R ψ hD (τ (ρ + b)) (τ (ρ + b))⁻¹).2
    rw [hτ ρ hρ b hb] at h2
    rw [← h1, ← h2, ← hτ ρ hρ b hb, Units.mul_inv]
  have htpos : 0 < modK R ((t⁻¹ : Kˣ) : K) := (hMM K R ψ hD t⁻¹ 1).1

  have hcrex : ∀ x : K ⧸ R.toAddSubgroup, ∃ u : Kˣ, ((u : K) : K ⧸ R.toAddSubgroup) = x := by
    intro x
    obtain ⟨r, hr, hu⟩ := hD.unitRep (Quotient.out x)
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec, QuotientAddGroup.mk_add, QuotientAddGroup.out_eq',
      (QuotientAddGroup.eq_zero_iff r).2 hr, add_zero]
  choose cr hcr using hcrex
  have hcr' : IsCr R cr := hcr
  have hBR : ∀ b ∈ D.B, b ∈ R := fun b hb => D.repsB.1 b hb
  obtain ⟨hper, hpsd⟩ := hTB hCP hKG hN1 hMM K R ψ hD m n₀ F D.A D.B τ cr hF hcr' hBR
  obtain ⟨Θm, hΘm⟩ := hA13 n₀ F hF
  refine ⟨fun z h h' => if z ∈ Lc then thx R ψ m cr D.A D.B τ z h h' else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x r hr
    have hiff : x + r ∈ Lc ↔ x ∈ Lc := by
      constructor
      · intro h
        have := Lc.sub_mem h (hRL r hr)
        simpa using this
      · intro h; exact Lc.add_mem h (hRL r hr)
    funext h h'
    simp only [hiff, hper x r hr]
  ·
    intro x
    by_cases hx : x ∈ Lc
    · simpa only [hx, if_true] using hpsd x
    · simpa only [hx, if_false] using psd_zero F
  ·
    intro x hx h _ h' _
    simp only [hx, if_false]
  ·
    intro t' ht'
    by_cases hx : (t' : K) ∈ Lc
    · have := hLow t τ cr ht.1 hcr' hτ (t' : K) ht'
      refine psd_congr ?_ this
      intro h _ h' _
      have hu : IsUnit (t' : K) := t'.isUnit
      have hu' : hu.unit = t' := Units.ext rfl
      simp only [hx, if_true, NsK, dif_pos hu, hu']
    · refine psd_congr ?_ (psd_zero F)
      intro h hh h' hh'
      simp only [hx, if_false, hNs0 t' hx h hh h' hh', sub_zero]
  ·
    have hPlat := (hPL K R ψ hD hch D.L₁ D.lat₁).1
    have hRlat : IsLat R.toAddSubgroup := ⟨hD.isOpen, hD.isCompact⟩
    have hfin := finite_classes R.toAddSubgroup (perp ψ D.L₁)
      (hLF K (perp ψ D.L₁) R.toAddSubgroup hPlat hRlat)
    have hS : ∀ x : K ⧸ R.toAddSubgroup, (Quotient.out x : K) ∈ perp ψ D.L₁ → x ∈ hfin.toFinset :=
      fun x hx => hfin.mem_toFinset.2 hx
    have hAc := reps_card_ne_zero D.repsA
    have hBc := reps_card_ne_zero D.repsB
    have hp1 : IsPSD F (fun h h' => ∑ ρ ∈ D.A, ∑ b ∈ D.B,
        ((((D.A.card : ℝ) * (D.B.card : ℝ))⁻¹ : ℝ) : ℂ) *
          (((cSize R h ^ (m + 1) * cSize R h' ^ (m + 1) : ℝ) : ℂ) * N0 R ψ h h' -
            uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b)))) := by
      refine psd_sum D.A fun ρ _ => psd_sum D.B fun b _ => psd_smul _ (by positivity) ?_
      exact hUNB hUG hN1 hCSA hMM hLF K R ψ hD m n₀ F Θm hF hΘm (τ (ρ + b)) cr hcr'
    have hp2 : IsPSD F (fun h h' => ∑ x ∈ hfin.toFinset,
        if (Quotient.out x : K) ∈ Lc then 0 else thx R ψ m cr D.A D.B τ (Quotient.out x) h h') := by
      refine psd_sum _ fun x _ => ?_
      by_cases hx : (Quotient.out x : K) ∈ Lc
      · simpa only [hx, if_true] using psd_zero F
      · simpa only [hx, if_false] using hpsd _
    refine psd_congr ?_ (psd_add hp1 hp2)
    intro h hh h' hh'
    have hsum := hTS hPG hPD hPL hLF hGRC hCP hKG hN1 hMM K R ψ hD hch m (m + 1) n₀ F Om (Lc : Set K) D
      τ cr hF hcr' h hh h' hh'
    rw [← mean_sub D.A D.B hAc hBc, ← hsum]
    rw [finsum_ite_eq hfin.toFinset (fun x : K ⧸ R.toAddSubgroup => (Quotient.out x : K) ∈ perp ψ D.L₁)
      (fun x => thx R ψ m cr D.A D.B τ (Quotient.out x) h h') hS]
    rw [finsum_ite_eq hfin.toFinset (fun x : K ⧸ R.toAddSubgroup => (Quotient.out x : K) ∈ Lc)
      (fun x => thx R ψ m cr D.A D.B τ (Quotient.out x) h h')
      (fun x hx => hS x (D.cutPerp _ hx))]
    rw [sub_add, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxP : (Quotient.out x : K) ∈ perp ψ D.L₁ := hfin.mem_toFinset.1 hx
    by_cases hxL : (Quotient.out x : K) ∈ Lc
    · simp only [hxP, hxL, if_true, sub_zero]
    · simp only [hxP, hxL, if_true, if_false, sub_self]
  ·
    intro x h _ h' _ hne
    by_cases hx : x ∈ Lc
    · simp only [hx, if_true, thx]
      have hz : ∀ ρ ∈ D.A, ∀ b ∈ D.B, ∀ b' ∈ D.B,
          uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) = 0 := by
        intro ρ hρ b hb b' hb'
        refine hUB hKBD hCSA hMM K R ψ hD m cr Set.univ h h' _ _ ?_ hne
        exact mul_right_cancel₀ htpos.ne' ((hτmod ρ hρ b hb).trans (hτmod ρ hρ b' hb').symm)
      have : ∑ ρ ∈ D.A, ((D.B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ D.B, ∑ b' ∈ D.B,
          ψ (-(x * b)) * conj (ψ (-(x * b'))) *
            uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) = 0 := by
        refine Finset.sum_eq_zero fun ρ hρ => ?_
        rw [Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun b' hb' => by
          rw [hz ρ hρ b hb b' hb', mul_zero], mul_zero]
      rw [this, mul_zero]
    · simp only [hx, if_false]
end Formalism.FourierDecayAlt.P
