-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.gauss7_labels
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:56.504806+00:00
-- url     : https://prove2.me/submissions/dd840c54-3146-4c2c-9dd9-01f98020ca99

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementF
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CapLeOddShiftBound
import Definitions.Def_Formalism_GaussJetBounds_ThmAEntryFull
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TwoFormsOfTheoremA
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_letter_labels_finite
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (TT : Finset (ZMod d))
    (nu1 size : ZMod d → ℕ) :
    ∃ (lab : ∀ s, Fin (JnumOneLetter l d TT nu1 size s) → ZMod d × ℤ) (m : ℕ),
      (∀ s, Function.Injective (lab s)) ∧
      (∀ (s s0 : ZMod d) (j : ℤ), (∃ i, lab s i = (s0, j)) ↔
        (s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
          (j < 0 → l ^ (-j).toNat ≤ Dl d TT nu1 size s))) ∧
      ∀ s i, (-(lab s i).2).toNat ≤ m := by
  classical
  have hex : ∀ s, ∃ f : Fin (JnumOneLetter l d TT nu1 size s) → ZMod d × ℤ, Function.Injective f ∧
      ∀ q : ZMod d × ℤ, (∃ i, f i = q) ↔ IsLabOneLetter l d TT nu1 size s q.1 q.2 := by
    intro s
    have hfin := letter_labels_finite l d hl TT nu1 size s
    have hcard : hfin.toFinset.card = JnumOneLetter l d TT nu1 size s :=
      (Set.ncard_eq_toFinset_card _ hfin).symm
    refine ⟨fun i => ((Finset.equivFinOfCardEq hcard).symm i).1, ?_, fun q => ⟨?_, fun hq => ?_⟩⟩
    · intro i i' h
      exact (Finset.equivFinOfCardEq hcard).symm.injective (Subtype.ext h)
    · rintro ⟨i, rfl⟩
      have h := ((Finset.equivFinOfCardEq hcard).symm i).2
      rw [Set.Finite.mem_toFinset] at h
      exact h
    · refine ⟨Finset.equivFinOfCardEq hcard ⟨q, ?_⟩, ?_⟩
      · rw [Set.Finite.mem_toFinset]
        exact hq
      · simp
  choose lab hinj hlab using hex
  refine ⟨lab, ∑ s, ∑ i, (-(lab s i).2).toNat, hinj, fun s s0 j => hlab s (s0, j), fun s i => ?_⟩
  calc (-(lab s i).2).toNat ≤ ∑ i, (-(lab s i).2).toNat :=
        Finset.single_le_sum (f := fun i => (-(lab s i).2).toNat) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun s => ∑ i, (-(lab s i).2).toNat)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
