-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EGauss.struct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:20.077061+00:00
-- url     : https://prove2.me/submissions/7aa82c86-b121-481b-8bba-2a084c0ba9fc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_minorAt_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_entry_exists
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_sum_sub_sigma
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.EGauss
variable {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν]
namespace Formalism.InvariantFactorPaths.G7.EGauss
theorem _root_.solution (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1)
    (Y : ZMod (2 * ν) × Fin r0 × Fin r0 → K) :
    ∃ (C : ℕ) (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
      (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
      (I' : ∀ c, Fin (l c) → Fin r1),
      (∏ s : ZMod (2 * ν), minorProd
        (fun (i : Fin r0) (b : Fin r1) =>
          (∑ a : Fin r0, MvPolynomial.C (Y (s, i, a)) * MvPolynomial.X (s, a, b) :
            MvPolynomial (ZV ν r0 r1) K)) (hts s) (hp s) (I s)) = entryOp ξ e l sf T I' ∧
      (∀ s a, ∃ y, ξ s a = Y y) ∧ (∀ c i a, ∃ y, T c i a = Y y) ∧
      alN e = alG TT colN hts ∧ capN sf = capG TT colN hts ∧ lsN l sf = lsG TT colN hts ∧
      ∀ (J : Finset (Fin r1)) (i : ℕ), 1 ≤ i →
        (∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
            then e x else 0) +
          ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I' c)) ∩ J).card else 0)) ≤
        ∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
          (if s.val % 2 = 0 then min (hts s c) i - ((univ.image (I s c)) ∩ J).card
          else ((univ.image (I s c)) ∩ J).card) := by
  classical
  let A := Σ s, Fin (colN s)
  let top : A → Prop := fun x => x.1 ∈ TT ∧ hts x.1 x.2 = 1
  let ξ : ZMod (2 * ν) → Fin r0 → K := fun s a => Y (s, ⟨0, a.pos⟩, a)
  let fac : A → MvPolynomial (ZV ν r0 r1) K := fun x =>
    minorAt x.1 (fun i a => Y (x.1, ⟨i.val, lt_of_lt_of_le i.isLt (hp x.1 x.2)⟩, a)) (I x.1 x.2)
  let g : {x : A // top x} → TpV ν r1 := fun x =>
    (x.1.1, I x.1.1 x.1.2 ⟨0, by rw [x.2.2]; exact one_pos⟩)
  obtain ⟨C, e, l, sf, T, I', hop, he, hl, hT⟩ := entry_exists ξ g
    (fun x : {x : A // ¬ top x} => x.1.1) (fun x => hts x.1.1 x.1.2)
    (fun x i a => Y (x.1.1, ⟨i.val, lt_of_lt_of_le i.isLt (hp x.1.1 x.1.2)⟩, a))
    (fun x => I x.1.1 x.1.2)
  have hal : ∀ s, alN e s = ∑ c : Fin (colN s), if top ⟨s, c⟩ then 1 else 0 := by
    intro s
    rw [← sum_sub_sigma colN top (fun _ => 1) s]
    have h := he (fun y => if y.1 = s then 1 else 0)
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s (by intro s' _ h; simp [h]) (by simp)] at h
    simpa [alN] using h
  have hcap : ∀ s, capN sf s = ∑ c : Fin (colN s), if ¬ top ⟨s, c⟩ then 1 else 0 := by
    intro s
    rw [← sum_sub_sigma colN (fun x => ¬ top x) (fun _ => 1) s,
      ← hl (fun s' _ _ => if s' = s then 1 else 0)]
    unfold capN
    rw [Finset.card_filter]
  have hls : ∀ s, lsN l sf s = ∑ c : Fin (colN s), if ¬ top ⟨s, c⟩ then hts s c else 0 := by
    intro s
    rw [← sum_sub_sigma colN (fun x => ¬ top x) (fun x => hts x.1 x.2) s,
      ← hl (fun s' h _ => if s' = s then h else 0)]
    simp [lsN, Finset.sum_filter]
  have halG : ∀ s, (∑ c : Fin (colN s), if top ⟨s, c⟩ then 1 else 0) = alG TT colN hts s := by
    intro s
    unfold alG
    by_cases hs : s ∈ TT
    · rw [if_pos hs, Finset.card_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [top, hs, true_and]
    · simp [top, hs]
  refine ⟨C, ξ, e, l, sf, T, I', ?_, fun s a => ⟨_, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hop]
    have h1 : ∀ x : {x : A // top x}, topForm ξ (g x) = fac x.1 := by
      intro x
      simp only [fac]
      rw [minorAt_one x.1.1 x.2.2]
      rfl
    rw [Finset.prod_congr rfl (fun x _ => h1 x)]
    have h2 := Fintype.prod_subtype_mul_prod_subtype top fac
    rw [Fintype.prod_sigma] at h2
    exact h2.symm
  · intro c i a
    obtain ⟨x, i', h⟩ := hT c i a
    exact ⟨_, h⟩
  · funext s
    rw [hal, halG]
  · funext s
    have h : (∑ c : Fin (colN s), if top ⟨s, c⟩ then 1 else 0) +
        (∑ c : Fin (colN s), if ¬ top ⟨s, c⟩ then 1 else 0) = colN s := by
      rw [← Finset.sum_add_distrib]
      trans ∑ _c : Fin (colN s), 1
      · refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> rfl
      · simp
    rw [halG] at h
    rw [hcap]
    unfold capG
    omega
  · funext s
    have h : (∑ c : Fin (colN s), if top ⟨s, c⟩ then 1 else 0) +
        (∑ c : Fin (colN s), if ¬ top ⟨s, c⟩ then hts s c else 0) = ∑ c, hts s c := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : top ⟨s, c⟩
      · simp [hc, hc.2]
      · simp [hc]
    rw [halG] at h
    rw [hls]
    unfold lsG
    omega
  · intro J i hi
    have e1 : ∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
        then e x else 0) = ∑ x : {x : A // top x},
          if ((g x).1.val % 2 = 0 ∧ (g x).2 ∉ J) ∨ ((g x).1.val % 2 = 1 ∧ (g x).2 ∈ J)
            then 1 else 0 := by
      rw [← he (fun y => if (y.1.val % 2 = 0 ∧ y.2 ∉ J) ∨ (y.1.val % 2 = 1 ∧ y.2 ∈ J)
        then 1 else 0)]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> simp
    rw [e1, hl (fun s _ Ih => if s.val % 2 = 1 then ((univ.image Ih) ∩ J).card else 0)]
    let W : A → ℕ := fun x =>
      if x.1.val % 2 = 0 then min (hts x.1 x.2) i - ((univ.image (I x.1 x.2)) ∩ J).card
      else ((univ.image (I x.1 x.2)) ∩ J).card
    have e2 := Fintype.sum_subtype_add_sum_subtype top W
    rw [Fintype.sum_sigma] at e2
    refine le_trans ?_ (le_of_eq e2)
    refine add_le_add (Finset.sum_le_sum fun x _ => ?_) (Finset.sum_le_sum fun x _ => ?_)
    · obtain ⟨⟨s, c⟩, hs, hc⟩ := x
      have hc' : hts s c = 1 := hc
      have him : univ.image (I s c) = {I s c ⟨0, by rw [hc']; exact one_pos⟩} := by
        ext b
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨j, rfl⟩
          congr 1
          apply Fin.ext
          have := j.isLt
          simp only
          omega
        · rintro rfl
          exact ⟨_, rfl⟩
      have hmin : min 1 i = 1 := min_eq_left hi
      simp only [W, g, him, hc', hmin]
      by_cases hb : I s c ⟨0, by rw [hc']; exact one_pos⟩ ∈ J
      · rw [Finset.singleton_inter_of_mem hb]
        rcases Nat.mod_two_eq_zero_or_one s.val with h | h <;> simp [h, hb]
      · rw [Finset.singleton_inter_of_notMem hb]
        rcases Nat.mod_two_eq_zero_or_one s.val with h | h <;> simp [h, hb]
    · simp only [W]
      rcases Nat.mod_two_eq_zero_or_one x.1.1.val with h | h <;> simp [h]
end Formalism.InvariantFactorPaths.G7.EGauss
