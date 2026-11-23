-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jet_bipower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:31.456108+00:00
-- url     : https://prove2.me/submissions/448b27a5-58fe-49aa-b825-c5fb74de3a77

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameCoeffMulLin
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAJet
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_parity
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {d : ℕ} [NeZero d] (hde : Even d) {l : ℕ} (hl : 2 ≤ l) {t1 t2 : ZMod d}
    {α β : ℕ} (h : IsBiPower l (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β))) :
    t1 ≠ t2 ∧ t1 + (α : ZMod d) = t2 + (β : ZMod d) ∧ Odd (α + β) := by
  classical
  obtain ⟨s, s', α', β', hs, hs', -, heq, hn⟩ := h
  have hss : s ≠ s' := by rintro rfl; omega
  have hpar := jet_parity hde hs hs' heq
  have hpos : ∀ k : ℕ, l ^ k ≠ 0 := fun k => pow_ne_zero _ (by omega)
  have hinj : ∀ a b : ℕ, l ^ a = l ^ b → a = b := fun a b hab =>
    Nat.pow_right_injective hl hab
  have F1 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) s = l ^ α' := by
    rw [hn]; simp [hss]
  have F2 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) s' = l ^ β' := by
    rw [hn]; simp [Ne.symm hss]
  have F3 : ∀ t, (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t ≠ 0 →
      t = s ∨ t = s' := by
    intro t ht
    rw [hn] at ht
    by_contra hc
    simp only [not_or] at hc
    apply ht
    simp [Ne.symm hc.1, Ne.symm hc.2]
  have G3 : ∀ t, (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t ≠ 0 →
      t = t1 ∨ t = t2 := by
    intro t ht
    by_contra hc
    simp only [not_or] at hc
    apply ht
    simp [Ne.symm hc.1, Ne.symm hc.2]
  have ht12 : t1 ≠ t2 := by
    rintro rfl
    have a := G3 s (by rw [F1]; exact hpos _)
    have b := G3 s' (by rw [F2]; exact hpos _)
    simp only [or_self] at a b
    exact hss (a.trans b.symm)
  have H1 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t1 = l ^ α := by
    simp [ht12]
  have H2 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t2 = l ^ β := by
    simp [Ne.symm ht12]
  refine ⟨ht12, ?_⟩
  rcases F3 t1 (by rw [H1]; exact hpos _) with h1 | h1 <;>
    rcases F3 t2 (by rw [H2]; exact hpos _) with h2 | h2
  · exact absurd (h1.trans h2.symm) ht12
  · subst h1 h2
    have e1 := hinj _ _ (H1.symm.trans F1)
    have e2 := hinj _ _ (H2.symm.trans F2)
    subst e1 e2
    exact ⟨heq, hpar⟩
  · subst h1 h2
    have e1 := hinj _ _ (H1.symm.trans F2)
    have e2 := hinj _ _ (H2.symm.trans F1)
    subst e1 e2
    exact ⟨heq.symm, by rwa [add_comm]⟩
  · exact absurd (h1.trans h2.symm) ht12
end Formalism.DworkPowerSeriesWeights
