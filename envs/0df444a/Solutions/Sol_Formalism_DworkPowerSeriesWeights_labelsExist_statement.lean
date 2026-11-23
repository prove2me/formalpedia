-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.labelsExist_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:00.257737+00:00
-- url     : https://prove2.me/submissions/3a92f765-1f39-46f9-b91a-8331cf323ee2

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_oddExponentCount


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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : LabelsExist := by
  classical
  intro l d N0 _ hl TT nu1 size a ha hnu hsize hN
  let S : ZMod d → Finset ℤ := fun s =>
    (Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ s - (j : ZMod d) ∈ TT ∧
      (0 < j → l ^ j.toNat ≤ nu1 (s - (j : ZMod d))) ∧ (j < 0 → l ^ (-j).toNat ≤ size s))

  have hpow : ∀ (s : ZMod d) (j : ℤ), Odd j →
      (0 < j → l ^ j.toNat ≤ nu1 (s - (j : ZMod d))) → (j < 0 → l ^ (-j).toNat ≤ size s) →
      l ^ j.natAbs ≤ a := by
    intro s j hj h1 h2
    rcases lt_trichotomy j 0 with h | h | h
    · have : (-j).toNat = j.natAbs := by omega
      rw [← this]
      exact (h2 h).trans (hsize s)
    · subst h
      exact absurd hj (by decide)
    · have : j.toNat = j.natAbs := by omega
      rw [← this]
      exact (h1 h).trans (hnu _)
  have hIcc : ∀ j : ℤ, l ^ j.natAbs ≤ a → j ∈ Finset.Icc (-(a : ℤ)) a := by
    intro j hj
    have h1 : j.natAbs < l ^ j.natAbs := Nat.lt_pow_self hl
    rw [Finset.mem_Icc]
    omega
  have hcard : ∀ s, ((S s).card : ℝ) ≤ 2 * Real.logb l a + 1 := by
    intro s
    refine le_trans ?_ (oddExponentCount l a hl ha)
    exact_mod_cast Finset.card_le_card (by
      intro j hj
      simp only [S, Finset.mem_filter] at hj
      rw [Finset.mem_filter]
      exact ⟨hj.1, hj.2.1, hpow s j hj.2.1 hj.2.2.2.1 hj.2.2.2.2⟩)
  refine ⟨fun s => (S s).card,
    fun s i => (s - ((((S s).equivFin.symm i : S s) : ℤ) : ZMod d), (((S s).equivFin.symm i : S s) : ℤ)),
    a, ?_, ?_, ?_, ?_⟩
  · intro s i i' hii
    have h2 := congrArg Prod.snd hii
    simp only at h2
    exact (S s).equivFin.symm.injective (Subtype.ext h2)
  · intro s s0 j
    constructor
    · rintro ⟨i, hi⟩
      have hm := ((S s).equivFin.symm i).2
      have h1 := congrArg Prod.fst hi
      have h2 := congrArg Prod.snd hi
      simp only at h1 h2
      rw [h2] at h1 hm
      simp only [S, Finset.mem_filter] at hm
      rw [h1] at hm
      exact ⟨hm.2.2.1, hm.2.1, by rw [← h1]; ring, hm.2.2.2.1, hm.2.2.2.2⟩
    · rintro ⟨hT, hodd, hs, hp, hn⟩
      have hs0 : s - (j : ZMod d) = s0 := by rw [hs]; ring
      have hm : j ∈ S s := by
        simp only [S, Finset.mem_filter]
        rw [hs0]
        exact ⟨hIcc j (hpow s j hodd (by rw [hs0]; exact hp) hn), hodd, hT, hp, hn⟩
      refine ⟨(S s).equivFin ⟨j, hm⟩, ?_⟩
      simp only [Equiv.symm_apply_apply, hs0]
  · intro s
    have h1 := hcard s
    have h2 : ((S s).card : ℝ) + 1 ≤ (N0 : ℝ) := by linarith
    have h3 : (S s).card + 1 ≤ N0 := by exact_mod_cast h2
    show (S s).card + _ ≤ N0
    split_ifs <;> omega
  · intro s i
    show (-(((S s).equivFin.symm i : S s) : ℤ)).toNat ≤ a
    obtain ⟨j, hm⟩ := (S s).equivFin.symm i
    have hm' := (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
    show (-j).toNat ≤ a
    omega
end Formalism.DworkPowerSeriesWeights
