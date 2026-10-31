-- Prove2me | solution 1 for FuzzyExtractors.ImprovedJS.rec_correct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:00:17.523584+00:00
-- url     : https://prove2.me/submissions/2e3ff13d-c0a7-4d03-9a51-799af81631a2

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJS_Basic
import Theorems.Thm_FuzzyExtractors_ImprovedJS_intersection_bound
import Theorems.Thm_FuzzyExtractors_ImprovedJS_pLow_unique

open Polynomial FuzzyExtractors.ImprovedJS

lemma charPoly_roots_toFinset {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] (w : Finset 𝔽) :
    (charPoly w).roots.toFinset = w := by
  classical
  induction w using Finset.induction_on with
  | empty =>
    simp [charPoly]
  | @insert a s ha ih =>
    have h1 : charPoly (insert a s) = (X - C a) * charPoly s := by
      simp [charPoly, Finset.prod_insert ha]
    have h2 : (X - C a : 𝔽[X]) * charPoly s ≠ 0 := by
      rw [← h1]
      unfold charPoly
      exact Finset.prod_ne_zero_iff.mpr (fun x _ => Polynomial.X_sub_C_ne_zero x)
    rw [h1, Polynomial.roots_mul h2, Polynomial.roots_X_sub_C, Multiset.toFinset_add,
        Multiset.toFinset_singleton, ih, Finset.singleton_union]

/-- Construction 5 analysis (p. 21): Rec recovers w from w′ and SS(w) whenever dis(w, w′) ≤ t,
i.e. Construction 5 satisfies the correctness property of a secure sketch on SDif_s(𝔽). -/
theorem solution {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s) :
    FuzzyExtractors.Hamming.SketchCorrect (sdifDist (𝓤 := 𝔽) (s := s)) t (sketch s t) (recover s t) := by
  intro w w' hd coeffs hcoeffs
  simp only [sketch, PMF.support_pure, Set.mem_singleton_iff] at hcoeffs
  subst hcoeffs
  have hint := (intersection_bound s t hts w.1 w'.1 w.2 w'.2 hd).2
  have hex : ∃ pLow, Step3Cond s t (sketchCoeffs s t w.1) w'.1 pLow := ⟨_, hint⟩
  have hchoose : Step3Cond s t (sketchCoeffs s t w.1) w'.1 (Classical.choose hex) :=
    Classical.choose_spec hex
  have huniq : Classical.choose hex = -(charPoly w.1 - pHigh s t (sketchCoeffs s t w.1)) :=
    pLow_unique s t hts w'.1 w'.2 (fun x => (pHigh s t (sketchCoeffs s t w.1)).eval x)
      (Classical.choose hex) (-(charPoly w.1 - pHigh s t (sketchCoeffs s t w.1)))
      hchoose.1 hint.1 hchoose.2 hint.2
  have hsub : pHigh s t (sketchCoeffs s t w.1) - Classical.choose hex = charPoly w.1 := by
    rw [huniq]
    ring
  have hroots : (pHigh s t (sketchCoeffs s t w.1) - Classical.choose hex).roots.toFinset = w.1 := by
    rw [hsub, charPoly_roots_toFinset]
  have hcard : (pHigh s t (sketchCoeffs s t w.1) - Classical.choose hex).roots.toFinset.card = s := by
    rw [hroots, w.2]
  unfold recover
  rw [dif_pos hex, dif_pos hcard]
  congr 1
  ext1
  exact hroots
