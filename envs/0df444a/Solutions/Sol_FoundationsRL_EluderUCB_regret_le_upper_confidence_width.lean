-- Prove2me | solution 1 for FoundationsRL.EluderUCB.regret_le_upper_confidence_width
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:06:35.297961+00:00
-- url     : https://prove2.me/submissions/c90d9f82-d54b-4250-b5be-6697bafd7948

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_regret
import Definitions.Def_FoundationsRL_EluderUCB_IsGeneralizedUCBRun

open FoundationsRL.EluderUCB in
theorem solution {Act : Type*} (F : Set (Act → ℝ)) (hfin : F.Finite)
    (β : ℝ) (fstar : Act → ℝ) (T : ℕ) (π : ℕ → Act) (r : ℕ → ℝ) (fhat : ℕ → Act → ℝ)
    (hrun : IsGeneralizedUCBRun F β T π r fhat)
    (hmem : ∀ t ∈ Finset.Icc 1 T, fstar ∈ confidenceSet F β π r t (fhat t)) :
    regret fstar T π ≤
      ∑ t ∈ Finset.Icc 1 T, (ucbIndex F β π r t (fhat t) (π t) - fstar (π t)) := by
  haveI : Nonempty Act := ⟨π 0⟩
  unfold regret
  apply Finset.sum_le_sum
  intro t ht
  have hle : ∀ p, fstar p ≤ ucbIndex F β π r t (fhat t) p := by
    intro p
    unfold ucbIndex
    have hsub : confidenceSet F β π r t (fhat t) ⊆ F := fun f hf => hf.1
    have hfin' : ((fun f : Act → ℝ => f p) '' confidenceSet F β π r t (fhat t)).Finite :=
      (hfin.subset hsub).image _
    exact le_csSup hfin'.bddAbove ⟨fstar, hmem t ht, rfl⟩
  have hsup : (⨆ p, fstar p) ≤ ucbIndex F β π r t (fhat t) (π t) :=
    ciSup_le (fun p => (hle p).trans ((hrun t ht).2 p))
  linarith
