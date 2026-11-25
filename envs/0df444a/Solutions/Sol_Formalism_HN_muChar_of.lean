-- Prove2me | solution 1 for Formalism.HN.muChar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:03:53.835805+00:00
-- url     : https://prove2.me/submissions/1a1e1ac7-ca81-46eb-a8fe-b7899fb5ceec

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Theorems.Thm_Formalism_HN_muChar_zl_mono
import Theorems.Thm_Formalism_F_saturProps
import Theorems.Thm_Formalism_F_slopesBdd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w
namespace Formalism.HN
theorem _root_.solution (h1 : SatR.{u, v, w}) (h2 : SatBasic.{u, v, w}) (h3 : RatioMax.{u, v, w}) :
    MuChar.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L hL hL0
  obtain ⟨-, P2, P3, P4, P5, P6, -, P8⟩ := h2 R V E ρ L hL
  have hdisc : DiscreteTopology (zl ρ L) := hL.2
  have hrk0 : rk ρ (⊥ : Submodule R V) = 0 := (P4 ⊥ bot_le).2 rfl
  have hrkpos : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → (0 : ℝ) < rk ρ N := by
    intro N hN hN0
    have : rk ρ N ≠ 0 := fun h => hN0 ((P4 N hN).1 h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hslope : ∀ N : Submodule R V, slope ρ N = deg ρ N / rk ρ N := fun N => rfl
  have hzlne : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → zl ρ N ≠ ⊥ := by
    intro N hN hN0 h
    apply hN0
    apply (P4 N hN).1
    show Formalism.F.rk (zl ρ N) = 0
    rw [h]
    simp [Formalism.F.rk]
  obtain ⟨c, hc⟩ := Formalism.F.slopesBdd E (zl ρ L) hdisc
  have hsc : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → slope ρ N ≤ c := fun N hN hN0 =>
    hc ⟨zl ρ N, muChar_zl_mono ρ hN, hzlne N hN hN0, rfl⟩
  have hdegbd : ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ max c 0 * rk ρ L := by
    intro N hN
    by_cases hN0 : N = ⊥
    · subst hN0
      rw [P5]
      exact mul_nonneg (le_max_right c 0) (Nat.cast_nonneg _)
    · have hpos := hrkpos N hN hN0
      have hs := hsc N hN hN0
      rw [hslope, div_le_iff₀ hpos] at hs
      have hr : (rk ρ N : ℝ) ≤ rk ρ L := by exact_mod_cast (P2 N L hN le_rfl).1
      have e1 : c * (rk ρ N : ℝ) ≤ max c 0 * rk ρ N :=
        mul_le_mul_of_nonneg_right (le_max_left c 0) (Nat.cast_nonneg _)
      have e2 : max c 0 * (rk ρ N : ℝ) ≤ max c 0 * rk ρ L :=
        mul_le_mul_of_nonneg_left hr (le_max_right c 0)
      linarith

  set T : Set ℝ := {t | ∃ N : Submodule R V, N ≤ L ∧ N ≠ ⊥ ∧ slope ρ N = t} with hT
  have hmuMax : muMax ρ L = sSup T := rfl
  have hTne : T.Nonempty := ⟨_, L, le_rfl, hL0, rfl⟩
  have hTbdd : BddAbove T := by
    refine ⟨c, ?_⟩
    rintro t ⟨N, hN, hN0, rfl⟩
    exact hsc N hN hN0
  have part1 : ∀ θ : ℝ, muMax ρ L ≤ θ ↔
      ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ θ * rk ρ N := by
    intro θ
    rw [hmuMax]
    constructor
    · intro h N hN
      by_cases hN0 : N = ⊥
      · subst hN0
        rw [P5, hrk0]
        simp
      · have h1 : slope ρ N ≤ θ := (le_csSup hTbdd ⟨N, hN, hN0, rfl⟩).trans h
        rw [hslope, div_le_iff₀ (hrkpos N hN hN0)] at h1
        exact h1
    · intro h
      refine csSup_le hTne ?_
      rintro t ⟨N, hN, hN0, rfl⟩
      rw [hslope, div_le_iff₀ (hrkpos N hN hN0)]
      exact h N hN

  have hsatlt : ∀ S : Submodule R V, IsSat ρ L S → S ≠ L → rk ρ S < rk ρ L := by
    intro S hS hSL
    have hle := (P8 S hS).2.1
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (P3 S L hS hS.1 le_rfl h.symm).symm hSL
  have hdpos : ∀ S : Submodule R V, IsSat ρ L S → S ≠ L →
      (1 : ℝ) ≤ (rk ρ L : ℝ) - rk ρ S := by
    intro S hS hSL
    have h' : rk ρ S + 1 ≤ rk ρ L := hsatlt S hS hSL
    have : (rk ρ S : ℝ) + 1 ≤ rk ρ L := by exact_mod_cast h'
    linarith
  have hqslope : ∀ S : Submodule R V, IsSat ρ L S →
      Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ S)) =
        (deg ρ L - deg ρ S) / ((rk ρ L : ℝ) - rk ρ S) := by
    intro S hS
    obtain ⟨hr, hle, hd⟩ := P8 S hS
    show Formalism.F.deg _ / (Formalism.F.rk _ : ℝ) = _
    rw [hr, hd, Nat.cast_sub hle]
  set U : Set ℝ := {t | ∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ L ∧
    Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ N)) = t} with hU
  have hmuMin : muMin ρ L = sInf U := rfl
  have hUne : U.Nonempty := ⟨_, ⊥, P6, hL0.symm, rfl⟩
  have hUbdd : BddBelow U := by
    refine ⟨min (deg ρ L - max c 0 * rk ρ L) 0, ?_⟩
    rintro t ⟨N, hN, hNL, rfl⟩
    rw [hqslope N hN]
    have hd := hdpos N hN hNL
    rw [le_div_iff₀ (by linarith)]
    have hb := hdegbd N hN.1
    have m1 := min_le_left (deg ρ L - max c 0 * rk ρ L) 0
    have m2 := min_le_right (deg ρ L - max c 0 * rk ρ L) 0
    have m3 := mul_le_mul_of_nonpos_left hd m2
    linarith
  have part2 : ∀ θ : ℝ, θ ≤ muMin ρ L ↔
      ∀ N : Submodule R V, N ≤ L → θ * ((rk ρ L : ℝ) - rk ρ N) ≤ deg ρ L - deg ρ N := by
    intro θ
    rw [hmuMin]
    constructor
    · intro h N hN
      obtain ⟨N', hNN', hN'L, hzl⟩ := h1 R V E ρ L N hL hN
      obtain ⟨hsat, -, hrkeq⟩ :=
        Formalism.F.saturProps E (zl ρ L) (zl ρ N) hdisc (muChar_zl_mono ρ hN)
      have hN'sat : IsSat ρ L N' := ⟨hN'L, by rw [hzl]; exact hsat⟩
      have hrk' : rk ρ N' = rk ρ N := by
        show Formalism.F.rk (zl ρ N') = Formalism.F.rk (zl ρ N)
        rw [hzl]
        exact hrkeq
      have hdeg' : deg ρ N ≤ deg ρ N' := (P2 N N' hNN' hN'L).2 hrk'.symm
      by_cases hN'L' : N' = L
      · have hr : rk ρ N = rk ρ L := by rw [← hrk', hN'L']
        have hdg : deg ρ N ≤ deg ρ L := hN'L' ▸ hdeg'
        rw [hr, sub_self, mul_zero]
        linarith
      · have ht := h.trans (csInf_le hUbdd ⟨N', hN'sat, hN'L', rfl⟩)
        rw [hqslope N' hN'sat] at ht
        have hd := hdpos N' hN'sat hN'L'
        rw [le_div_iff₀ (by linarith)] at ht
        rw [← hrk']
        linarith
    · intro h
      refine le_csInf hUne ?_
      rintro t ⟨N, hN, hNL, rfl⟩
      rw [hqslope N hN]
      have hd := hdpos N hN hNL
      rw [le_div_iff₀ (by linarith)]
      exact h N hN.1
  have part3 : ∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ ⊥ ∧ slope ρ N = muMax ρ L := by
    obtain ⟨N, hbN, hNsat, hmax⟩ := h3 R V E ρ L ⊥ hL P6 hL0.symm
    have hN0 : N ≠ ⊥ := hbN.ne'
    refine ⟨N, hNsat, hN0, ?_⟩
    rw [hmuMax]
    refine (IsGreatest.csSup_eq ⟨(show slope ρ N ∈ T from ⟨N, hNsat.1, hN0, rfl⟩), ?_⟩).symm
    rintro t ⟨N', hN', hN'0, rfl⟩
    have hm := hmax N' (bot_lt_iff_ne_bot.2 hN'0) hN'
    rw [P5, hrk0] at hm
    simp only [sub_zero, Nat.cast_zero] at hm
    rw [hslope, hslope, div_le_div_iff₀ (hrkpos N' hN' hN'0) (hrkpos N hNsat.1 hN0)]
    linarith
  have hquotbot : Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ (⊥ : Submodule R V))) = slope ρ L := by
    rw [hqslope ⊥ P6, P5, hrk0, hslope]
    simp
  refine ⟨part1, part2, part3, ?_, ?_⟩
  · rw [hmuMin, ← hquotbot]
    exact csInf_le hUbdd
      (show Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ (⊥ : Submodule R V))) ∈ U from ⟨⊥, P6, hL0.symm, rfl⟩)
  · rw [hmuMax]
    exact le_csSup hTbdd (show slope ρ L ∈ T from ⟨L, le_rfl, hL0, rfl⟩)
end Formalism.HN
