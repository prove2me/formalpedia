-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.theorem_A_monomial_of_lemmas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:19:30.916915+00:00
-- url     : https://prove2.me/submissions/f968d265-35ef-490c-8e68-e4464f8a244b

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAOneMonomialLogLoss
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TheoremAMonomialOfLemmas
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_logb_max_one_nat
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_pureMon
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_single
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dualRadiiInequalities
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_bipower
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_collapse
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_rowRad_ge
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_rowRad_nonneg
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_rowRad_spec
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_rowRad_top
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_IncomingBounds_lemmaFa
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
universe u
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution (hS : LemmaS.{u}) (hR : LemmaRA.{u, 0}) (hA : ThmAAssembly7)
    (hFP : FramePure.{u}) : ThmAJet7.{u} := by
  intro K _ _ _ l d N0 N1 _ hl hl3 hd hde hpi h0 K0 hK0 ζ hζ be hbe x hx g hg0 hg U hU ε hε
    TT nu1 nu2 size hnu21 hnu1s spec κ hκtop hκD hspec hcap hrow hkill
  classical
  have hodd : Odd l := hl.odd_of_ne_two (by omega)
  have hl2 : 2 ≤ l := hl.two_le
  have hlpos : 0 < l := by omega
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  obtain ⟨⟨sig, hsigD, hsigA, hFn⟩, -⟩ := lemmaFa l d hl3 hd hde
    (fun s => (Dl d TT nu1 size s : ℝ)) (fun s => Nat.cast_nonneg _)
  have hsig0 : ∀ s, 0 ≤ sig s := fun s => (hsigD.1 s).1
  have hnotop : ∀ (s : ZMod d) (k : Fin N0), (s ∈ TT ∧ k.val = 0) → spec (s, k) = none := by
    intro s k hsk
    rcases h : spec (s, k) with _ | ⟨s0, j⟩
    · rfl
    · exact absurd hsk (hspec s k s0 j h).2.2.2.1
  obtain ⟨eps, heps0, hepsT, hmain⟩ := hA l d hl3 hd hde TT nu1 nu2 size hnu21 hnu1s sig
    ⟨hsigD, hFn⟩ (ZV d N0 N1) (fun y => y.1) (frameTop TT) (fun y => spec (y.1, y.2.1))
    (fun y => κ y)
    (by
      intro i hi
      have hi' := of_decide_eq_true hi
      exact ⟨hi'.1, hnotop _ _ hi'⟩)
    (by
      intro s hs
      have hset : Finset.univ.filter (fun i : ZV d N0 N1 => i.1 = s ∧ frameTop TT i = true) =
          Finset.univ.image (fun b : Fin N1 => ((s, ⟨0, h0⟩, b) : ZV d N0 N1)) := by
        ext ⟨s', k, b⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, frameTop,
          decide_eq_true_eq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, -, hk⟩
          exact ⟨b, rfl, Fin.ext hk.symm, rfl⟩
        · rintro ⟨b', rfl, rfl, rfl⟩
          exact ⟨rfl, hs, rfl⟩
      rw [hset, Finset.sum_image (fun b _ b' _ h => by simpa using h)]
      exact_mod_cast hκtop s hs)
    (by intro s; exact_mod_cast hκD s)
    (by
      intro i s0 j h
      obtain ⟨h1, h2, h3, -, h5, h6⟩ := hspec i.1 i.2.1 s0 j h
      exact ⟨h1, h2, h3, h5, h6⟩)
    (by intro s0 j; exact_mod_cast hcap s0 j)
  have R := dualRadiiInequalities l d hl3 hd hde TT sig eps hsigA hsig0 heps0 hepsT
  obtain ⟨hS1, hS2⟩ := hS K l d hl hodd hd hde hpi K0 hK0 ζ hζ be hbe
  have hM1 : ∀ (z i : ZV d N0 N1), ‖frameM (N1 := N1) x z i‖ ≤ 1 := by
    intro z i
    unfold frameM
    split_ifs
    · exact hx _
    · simp
  have hMlt : ∀ (z i : ZV d N0 N1), frameM (N1 := N1) x z i ≠ 0 → i.1 = z.1 := by
    intro z i h
    unfold frameM at h
    split_ifs at h with h'
    · exact h'.1
    · exact absurd rfl h

  have hsmall : ∀ (i j : ZV d N0 N1) (α β : ℕ),
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      i.1 ≠ j.1 ∧ i.1 + (α : ZMod d) = j.1 + (β : ZMod d) ∧ Odd (α + β) := by
    intro i j α β hnot
    apply jet_bipower hde hl2
    by_contra hnb
    apply hnot
    have hc := jet_collapse (fun y : ZV d N0 N1 => y.1) (frameM (N1 := N1) x) hM1 hMlt be
      (pureMon l i j α β)
    have hmd : (pureMon l i j α β).mapDomain (fun y : ZV d N0 N1 => y.1) =
        Finsupp.single i.1 (l ^ α) + Finsupp.single j.1 (l ^ β) := by
      simp [pureMon, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    rw [hmd] at hc
    have h2 := hS2 _ hnb
    rw [monoWtGe_iff] at h2 ⊢
    refine hc.trans (h2.trans_eq ?_)
    congr 2
    rw [asmR_dot_pureMon, dot_add, asmR_dot_single, asmR_dot_single]
    push_cast
    ring

  have key : ∀ (i j : ZV d N0 N1) (α β : ℕ), pureMon l i j α β ≤ κ →
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      frameTop TT i = true → frameTop TT j = false →
      1 ≤ (l : ℝ) ^ α * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) i +
        (l : ℝ) ^ β * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) j := by
    rintro ⟨s0, k0, b⟩ ⟨s, k, b'⟩ α β hle hnot hti htj
    obtain ⟨hne, heq, hab⟩ := hsmall _ _ α β hnot
    simp only at hne heq
    have hti' : s0 ∈ TT ∧ k0.val = 0 := of_decide_eq_true hti
    have htj' : ¬ (s ∈ TT ∧ k.val = 0) := of_decide_eq_false htj
    obtain rfl : k0 = ⟨0, h0⟩ := Fin.ext hti'.2
    rw [jet_rowRad_top l sig eps _ _ _ _ hti]
    obtain ⟨hz, hw⟩ := hFP K l d N0 N1 hl hpi h0 x hx be hS1 s0 s hne k b b' α β
    have hbb : b = b' := by
      by_contra hbb
      apply hnot
      rw [hz hbb, monoWtGe_iff, norm_zero]
      exact Real.rpow_nonneg hpi0.le _
    subst hbb
    have hij : ((s0, ⟨0, h0⟩, b) : ZV d N0 N1) ≠ (s, k, b) := fun h => hne (congrArg Prod.fst h)
    have hκi : l ^ α ≤ κ (s0, ⟨0, h0⟩, b) := by
      have := hle (s0, ⟨0, h0⟩, b)
      simpa [pureMon, Finsupp.single_apply, hij, Ne.symm hij] using this
    have hκj : l ^ β ≤ κ (s, k, b) := by
      have := hle (s, k, b)
      simpa [pureMon, Finsupp.single_apply, hij, Ne.symm hij] using this
    have hnu : κ (s0, ⟨0, h0⟩, b) ≤ nu1 s0 := by
      rw [← hκtop s0 hti'.1]
      exact Finset.single_le_sum (f := fun b => κ (s0, ⟨0, h0⟩, b)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    have hsz : κ (s, k, b) ≤ Dl d TT nu1 size s := by
      rw [← hκD s]
      exact Finset.single_le_sum (f := fun y => κ y) (fun _ _ => Nat.zero_le _)
        (by simp [htj])
    obtain ⟨j0, hj0⟩ : ∃ j0 : ℤ, j0 = (α : ℤ) - β := ⟨_, rfl⟩
    have hsj : s = s0 + (j0 : ZMod d) := by
      rw [hj0]
      push_cast
      linear_combination (-1 : ZMod d) * heq
    have hjodd : Odd j0 := by
      obtain ⟨c, hc⟩ := hab
      exact ⟨(c : ℤ) - β, by omega⟩
    have hlev1 : 0 < j0 → l ^ j0.toNat ≤ nu1 s0 := by
      intro hj
      have : j0.toNat = α - β := by omega
      rw [this]
      exact (Nat.pow_le_pow_right hlpos (Nat.sub_le α β)).trans (hκi.trans hnu)
    have hlev2 : j0 < 0 → l ^ (-j0).toNat ≤ Dl d TT nu1 size s := by
      intro hj
      have : (-j0).toNat = β - α := by omega
      rw [this]
      exact (Nat.pow_le_pow_right hlpos (Nat.sub_le β α)).trans (hκj.trans hsz)
    by_cases hsp : spec (s, k) = some (s0, j0)
    · rw [jet_rowRad_spec l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
        (fun y => spec (y.1, y.2.1)) (s, k, b) htj hsp]
      rcases lt_trichotomy α β with hαβ | hαβ | hαβ
      · rw [if_neg (by omega)]
        have ht : (-j0).toNat = β - α := by omega
        rw [ht]
        have := R.2.2.1 s0 α (β - α) (max (sig s) ((l : ℝ) ^ (β - α))⁻¹) (by omega)
          (le_max_right _ _)
        rwa [Nat.add_sub_cancel' hαβ.le] at this
      · subst hαβ
        exfalso
        obtain ⟨c, hc⟩ := hab
        omega
      · rw [if_pos (by omega)]
        have ht : j0.toNat = α - β := by omega
        rw [ht]
        have := R.2.1 s0 β (α - β) (max (sig s) (1 - (l : ℝ) ^ (α - β) * eps s0)) (by omega)
          (le_max_right _ _)
        rwa [Nat.add_sub_cancel' hαβ.le] at this
    · exfalso
      apply hnot
      apply hw
      have hk := hkill s0 hti'.1 s k j0 htj' hjodd hsj hlev1 hlev2 hsp
      by_cases hβα : β ≤ α
      · rw [if_pos hβα]
        rw [if_pos (by omega : (0 : ℤ) ≤ j0)] at hk
        have ht : j0.toNat = α - β := by omega
        rwa [ht] at hk
      · rw [if_neg hβα]
        rw [if_neg (by omega : ¬ (0 : ℤ) ≤ j0)] at hk
        have ht : (-j0).toNat = β - α := by omega
        rwa [ht] at hk
  have hpure : ∀ (i j : ZV d N0 N1) (α β : ℕ), pureMon l i j α β ≤ κ →
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      1 ≤ (l : ℝ) ^ α * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) i +
        (l : ℝ) ^ β * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) j := by
    intro i j α β hle hnot
    obtain ⟨hne, heq, hab⟩ := hsmall i j α β hnot
    have hsw : pureMon l j i β α = pureMon l i j α β := by
      unfold pureMon; exact add_comm _ _
    cases hti : frameTop TT i <;> cases htj : frameTop TT j
    · exact R.1 i.1 j.1 α β _ _ (jet_rowRad_ge l sig eps _ _ _ i hti)
        (jet_rowRad_ge l sig eps _ _ _ j htj) hab heq
    · have h := key j i β α (by rw [hsw]; exact hle) (by rw [hsw]; exact hnot) htj hti
      linarith
    · exact key i j α β hle hnot hti htj
    · rw [jet_rowRad_top l sig eps _ _ _ _ hti, jet_rowRad_top l sig eps _ _ _ _ htj]
      exact R.2.2.2 i.1 (of_decide_eq_true hti).1 j.1 (of_decide_eq_true htj).1 α β hab heq

  have hκa : ∀ y : ZV d N0 N1, κ y ≤ max 1 (kaMaxOneLetter d TT nu1 nu2) := by
    rintro ⟨s, k, b⟩
    refine le_trans ?_ (le_max_right _ _)
    cases hty : frameTop TT ((s, k, b) : ZV d N0 N1)
    · have hty' : ¬ (s ∈ TT ∧ k.val = 0) := of_decide_eq_false hty
      have h1 : κ (s, k, b) ≤ ∑ b : Fin N1, κ (s, k, b) :=
        Finset.single_le_sum (f := fun b => κ (s, k, b)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ b)
      have h2 : capL d TT nu1 nu2 s ≤ Finset.univ.sup (capL d TT nu1 nu2) :=
        Finset.le_sup (f := capL d TT nu1 nu2) (Finset.mem_univ s)
      exact h1.trans ((hrow s k hty').trans (h2.trans (le_max_right _ _)))
    · have hty' : s ∈ TT ∧ k.val = 0 := of_decide_eq_true hty
      obtain rfl : k = ⟨0, h0⟩ := Fin.ext hty'.2
      have h1 : κ (s, ⟨0, h0⟩, b) ≤ nu1 s := by
        rw [← hκtop s hty'.1]
        exact Finset.single_le_sum (f := fun b => κ (s, ⟨0, h0⟩, b)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ b)
      have h2 : nu1 s ≤ TT.sup nu1 := Finset.le_sup (f := nu1) hty'.1
      exact h1.trans (h2.trans (le_max_left _ _))
  have hLR := hR K l d N0 N1 hl hodd hd hde hpi K0 hK0 ζ hζ be hbe (ZV d N0 N1)
    (fun y => y.1) (frameM (N1 := N1) x) hM1 hMlt g hg0 hg U hU ε hε
    (rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT) (fun y => spec (y.1, y.2.1)))
    (jet_rowRad_nonneg l sig eps _ _ _ hsig0 heps0) κ (max 1 (kaMaxOneLetter d TT nu1 nu2)) (le_max_left _ _) hκa hpure
  have hcard : (Fintype.card (ZV d N0 N1) : ℝ) = (d : ℝ) * N0 * N1 := by
    simp only [ZV, Fintype.card_prod, ZMod.card, Fintype.card_fin]
    push_cast
    ring
  rw [hcard, logb_max_one_nat] at hLR
  refine hLR.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hpi.le ?_)
  linarith [hmain]
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
