-- Prove2me | solution 1 for Formalism.HN.sizeMu_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:20:55.214092+00:00
-- url     : https://prove2.me/submissions/82cfe5d3-3c6b-4734-b9f2-1066b4dfe5db

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Theorems.Thm_Formalism_HN_sizeMu_rpow_eq
import Theorems.Thm_Formalism_HN_sizeMu_finrank_eq
import Theorems.Thm_Formalism_F_covolAntiSameRank
import Theorems.Thm_Formalism_F_covol_pos
import Theorems.Thm_Formalism_F_degQuot
import Theorems.Thm_Formalism_HN_muChar_zl_mono
import Theorems.Thm_Formalism_HN_saturation_basic_properties
import Theorems.Thm_Formalism_HN_slope_characterization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField NumberField.InfinitePlace
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution (h1 : PlLat) : SizeMu := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX L hLfg hL0 c
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  have hnf := sizeMu_finrank_eq K
  have hd : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)
  obtain ⟨hlat, hrkL, hhtL⟩ := h1 K V ι b X hX L hLfg
  have hSB := saturation_basic_properties (𝓞 K) V _ ρ L hlat

  have hrk_pos : ∀ N : Submodule (𝓞 K) V, N.FG → N ≠ ⊥ →
      0 < (nPl K : ℝ) ∧ 0 < (rkK N : ℝ) := by
    intro N hN hN0
    obtain ⟨hlN, hrkN, -⟩ := h1 K V ι b X hX N hN
    have h0 : rk ρ N ≠ 0 := fun h =>
      hN0 (((saturation_basic_properties (𝓞 K) V _ ρ N hlN).2.2.2.1 N le_rfl).1 h)
    rw [hrkN, hnf] at h0
    constructor
    · have : nPl K ≠ 0 := fun h => h0 (by simp [h])
      exact_mod_cast Nat.pos_of_ne_zero this
    · have : rkK N ≠ 0 := fun h => h0 (by simp [h])
      exact_mod_cast Nat.pos_of_ne_zero this

  have hsize : ∀ N : Submodule (𝓞 K) V, N.FG → N ≠ ⊥ →
      size b X N = Real.exp (c - slope ρ N) := by
    intro N hN hN0
    obtain ⟨hf, hj⟩ := hrk_pos N hN hN0
    obtain ⟨hlN, hrkN, -⟩ := h1 K V ι b X hX N hN
    have hC : 0 < Formalism.F.covol (zl ρ N) := by
      have := hlN.2
      exact Formalism.F.covol_pos _
    unfold size ht
    rw [show (2 : ℝ) ^ (nPl K * rkK N) = (2 : ℝ) ^ ((nPl K : ℝ) * (rkK N : ℝ)) by
      rw [← Real.rpow_natCast]; push_cast; rfl]
    rw [sizeMu_rpow_eq _ _ _ _ hf hj hC hd]
    congr 1
    have hr : (Formalism.F.rk (zl ρ N) : ℝ) = 2 * (nPl K : ℝ) * rkK N := by
      have : Formalism.F.rk (zl ρ N) = 2 * nPl K * rkK N := by
        rw [← hnf]; exact hrkN
      rw [this]; push_cast; ring
    simp only [c, slope, Formalism.F.slope, Formalism.F.deg, logDisc, hr, hnf]
    push_cast
    ring

  have hlt_of : ∀ S : Submodule (𝓞 K) V, IsSat ρ L S → S ≠ L → rk ρ S < rk ρ L := by
    intro S hS hSL
    obtain ⟨-, hSle, -⟩ := hSB.2.2.2.2.2.2.2 S hS
    rcases lt_or_eq_of_le hSle with h | h
    · exact h
    · exact absurd (hSB.2.2.1 S L hS hS.1 le_rfl h.symm).symm hSL

  have hsizeQ : ∀ S : Submodule (𝓞 K) V, IsSat ρ L S → S ≠ L →
      sizeQ b X L S = Real.exp (c - Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ S))) := by
    intro S hS hSL
    have hSfg : S.FG := Submodule.FG.of_le hLfg hS.1
    obtain ⟨-, hrkS, -⟩ := h1 K V ι b X hX S hSfg
    obtain ⟨hqrk, hSle, -⟩ := hSB.2.2.2.2.2.2.2 S hS
    have hlt := hlt_of S hS hSL
    have hf := (hrk_pos L hLfg hL0).1
    have hjlt : (rkK S : ℝ) < rkK L := by
      rw [hrkS, hrkL, hnf] at hlt
      have : rkK S < rkK L := Nat.lt_of_mul_lt_mul_left hlt
      exact_mod_cast this
    have hJ : 0 < (rkK L : ℝ) - rkK S := by linarith
    have hCq : 0 < Formalism.F.covol (Formalism.F.quot (zl ρ L) (zl ρ S)) := by
      have := (Formalism.F.degQuot _ (zl ρ L) (zl ρ S) hlat.2 hS.2).1
      exact Formalism.F.covol_pos _
    unfold sizeQ htQ
    rw [sizeMu_rpow_eq _ _ _ _ hf hJ hCq hd]
    congr 1
    have hr : (Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ S)) : ℝ) =
        2 * (nPl K : ℝ) * ((rkK L : ℝ) - rkK S) := by
      rw [hqrk, Nat.cast_sub hSle, hrkS, hrkL, hnf]
      push_cast; ring
    simp only [c, Formalism.F.slope, Formalism.F.deg, logDisc, hr, hnf]
    push_cast
    ring
  have hMC := slope_characterization (𝓞 K) V _ ρ L hlat hL0
  refine ⟨hsize L hLfg hL0, ?_, hsizeQ, ?_, ?_, ?_⟩
  ·
    rw [hsize L hLfg hL0, Real.log_exp]
    simp only [muDef, c]
    ring
  ·
    obtain ⟨N, hNs, hN0, hNslope⟩ := hMC.2.2.1
    have hbound : ∀ R : Submodule (𝓞 K) V, R ≤ L → R ≠ ⊥ → slope ρ R ≤ muMax ρ L := by
      intro R hRL hR0
      have h := (hMC.1 (muMax ρ L)).1 le_rfl R hRL
      have hRfg : R.FG := Submodule.FG.of_le hLfg hRL
      obtain ⟨hf, hj⟩ := hrk_pos R hRfg hR0
      obtain ⟨-, hrkR, -⟩ := h1 K V ι b X hX R hRfg
      have hpos : (0 : ℝ) < rk ρ R := by rw [hrkR, hnf]; push_cast; positivity
      show deg ρ R / (rk ρ R : ℝ) ≤ _
      rw [div_le_iff₀ hpos]
      exact h
    unfold leastSize
    apply IsLeast.csInf_eq
    refine ⟨⟨N, hNs.1, hN0, ?_⟩, ?_⟩
    · rw [hsize N (Submodule.FG.of_le hLfg hNs.1) hN0, hNslope]
    · rintro t ⟨R, hRL, hR0, rfl⟩
      rw [hsize R (Submodule.FG.of_le hLfg hRL) hR0]
      exact Real.exp_le_exp.2 (by linarith [hbound R hRL hR0])
  ·
    unfold largestSize
    have hset : {t | ∃ S : Submodule (𝓞 K) V, IsSat ρ L S ∧ S ≠ L ∧ sizeQ b X L S = t} =
        (fun s => Real.exp (c - s)) '' {t | ∃ N : Submodule (𝓞 K) V, IsSat ρ L N ∧ N ≠ L ∧
          Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ N)) = t} := by
      ext t
      constructor
      · rintro ⟨S, hS, hSL, rfl⟩
        exact ⟨_, ⟨S, hS, hSL, rfl⟩, (hsizeQ S hS hSL).symm⟩
      · rintro ⟨s, ⟨S, hS, hSL, rfl⟩, rfl⟩
        exact ⟨S, hS, hSL, hsizeQ S hS hSL⟩
    rw [hset]
    refine (Antitone.map_csInf_of_continuousAt (f := fun s => Real.exp (c - s)) ?_ ?_ ?_ ?_).symm
    · exact (Real.continuous_exp.comp (continuous_const.sub continuous_id)).continuousAt
    · intro a a' haa
      exact Real.exp_le_exp.2 (by linarith)
    · exact ⟨_, ⊥, hSB.2.2.2.2.2.1, fun h => hL0 h.symm, rfl⟩
    · refine ⟨muMin ρ L, ?_⟩
      rintro t ⟨S, hS, hSL, rfl⟩
      have h := (hMC.2.1 (muMin ρ L)).1 le_rfl S hS.1
      obtain ⟨hqrk, hSle, hqdeg⟩ := hSB.2.2.2.2.2.2.2 S hS
      have hlt : (rk ρ S : ℝ) < rk ρ L := by exact_mod_cast hlt_of S hS hSL
      show _ ≤ Formalism.F.deg _ / (Formalism.F.rk _ : ℝ)
      rw [hqrk, hqdeg, Nat.cast_sub hSle, le_div_iff₀ (by linarith)]
      exact h
  ·
    intro L' hLL' hL'fg hrk'
    obtain ⟨hlat', hrkL', -⟩ := h1 K V ι b X hX L' hL'fg
    unfold ht
    rw [hrk']
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Formalism.F.covolAntiSameRank _ (zl ρ L) (zl ρ L') hlat'.2 (muChar_zl_mono ρ hLL')
      (by show rk ρ L = rk ρ L'; rw [hrkL, hrkL', hrk'])
end Formalism.HN
