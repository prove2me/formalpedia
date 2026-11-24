-- Prove2me | solution 1 for Formalism.HN.shiftInvariance_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:17.863488+00:00
-- url     : https://prove2.me/submissions/08780adc-f9e8-41f1-b147-6260c4573810

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Theorems.Thm_Formalism_HN_shiftInv_isSat_iff
import Theorems.Thm_Formalism_HN_shiftInv_mu
import Theorems.Thm_Formalism_HN_shiftInv_sum
import Theorems.Thm_Formalism_HN_saturation_basic_properties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
universe u v w w₂
private theorem lt_card_filter_le_iff_of_antitone {n : ℕ} {s : Fin n → ℝ} (hs : Antitone s) (j : Fin n) (θ : ℝ) :
    (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ s i)).card ↔ θ ≤ s j := by
  constructor
  · intro h
    by_contra hlt
    replace hlt := not_le.mp hlt
    have h2 : Finset.univ.filter (fun i => θ ≤ s i) ⊆ Finset.Iio j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Iio]
      by_contra hji
      replace hji := not_lt.mp hji
      have := hs hji
      linarith
    have c2 := Finset.card_le_card h2
    rw [Fin.card_Iio] at c2
    omega
  · intro h
    have h1 : Finset.Iic j ⊆ Finset.univ.filter (fun i => θ ≤ s i) := by
      intro i hi
      simp only [Finset.mem_Iic] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.trans (hs hi)
    have c1 := Finset.card_le_card h1
    rw [Fin.card_Iic] at c1
    omega
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w w₂
namespace Formalism.HN
theorem _root_.solution (h1 : MuChar.{u, v, w}) (h1' : MuChar.{u, v, w₂})
    (h4 : HNSlopes.{u, v, w}) : ShiftInvariance.{u, v, w, w₂} := by
  intro R V E E₂ _ _ _ _ _ _ _ _ _ ρ ρ₂ L c hL hL₂ hsh
  have hBL := saturation_basic_properties R V E ρ L hL
  have hBL₂ := saturation_basic_properties R V E₂ ρ₂ L hL₂
  have hfilt : ∀ θ : ℝ, hnStep ρ₂ L (θ + c) = hnStep ρ L θ := by
    intro θ
    unfold hnStep
    congr 1
    ext N
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hNL, hN0, hθ⟩
      have hm := (shiftInv_mu h1 h1' ρ ρ₂ N c (hBL.1 N hNL) (hBL₂.1 N hNL)
        (fun N' hN' => hsh N' (hN'.trans hNL)) hN0).2
      exact ⟨hNL, hN0, by linarith⟩
    · rintro ⟨hNL, hN0, hθ⟩
      have hm := (shiftInv_mu h1 h1' ρ ρ₂ N c (hBL.1 N hNL) (hBL₂.1 N hNL)
        (fun N' hN' => hsh N' (hN'.trans hNL)) hN0).2
      exact ⟨hNL, hN0, by linarith⟩
  have hfiltle : ∀ θ : ℝ, hnStep ρ L θ ≤ L := fun θ => sSup_le fun N hN => hN.1
  have hS := h4 R V E ρ L hL
  have hslope : ∀ (j : ℕ) (hj₂ : j < rk ρ₂ L) (hj : j < rk ρ L),
      slopeList ρ₂ L ⟨j, hj₂⟩ = slopeList ρ L ⟨j, hj⟩ + c := by
    intro j hj₂ hj
    have hset : {θ : ℝ | j < rk ρ₂ (hnStep ρ₂ L θ)} = Set.Iic (slopeList ρ L ⟨j, hj⟩ + c) := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_Iic]
      have hf : hnStep ρ₂ L θ = hnStep ρ L (θ - c) := by
        have := hfilt (θ - c)
        rwa [sub_add_cancel] at this
      rw [hf, (hsh _ (hfiltle (θ - c))).1, ← hS.2.1 (θ - c)]
      refine (lt_card_filter_le_iff_of_antitone hS.1 ⟨j, hj⟩ (θ - c)).trans ?_
      constructor <;> intro h <;> linarith
    show sSup {θ : ℝ | j < rk ρ₂ (hnStep ρ₂ L θ)} = slopeList ρ L ⟨j, hj⟩ + c
    rw [hset, csSup_Iic]
  refine ⟨fun N => ?_, fun hL0 => shiftInv_mu h1 h1' ρ ρ₂ L c hL hL₂ hsh hL0,
    hfilt, fun k => ?_⟩
  · rw [shiftInv_isSat_iff ρ₂ hL₂, shiftInv_isSat_iff ρ hL]
    constructor
    · rintro ⟨hNL, hm⟩
      refine ⟨hNL, fun N' hNN' hN'L hr => hm N' hNN' hN'L ?_⟩
      rwa [(hsh N' hN'L).1, (hsh N hNL).1]
    · rintro ⟨hNL, hm⟩
      refine ⟨hNL, fun N' hNN' hN'L hr => hm N' hNN' hN'L ?_⟩
      rwa [(hsh N' hN'L).1, (hsh N hNL).1] at hr
  · exact shiftInv_sum (hsh L le_rfl).1 (slopeList ρ L) (slopeList ρ₂ L) c k hslope
end Formalism.HN
