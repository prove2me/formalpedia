-- Prove2me | solution 1 for BookProof.ChapterSirkGramCutoff.sirk_end_to_end_truncated_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:36:30.189218+00:00
-- url     : https://prove2.me/submissions/ddae0fd5-aff1-41e4-a408-81e090ec36e0

-- Generated from ChapterSirkGramCutoff.lean — solution of BookProof.ChapterSirkGramCutoff.sirk_end_to_end_truncated_cutoff
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_defect_le_sqrt_cutoff
import Theorems.Thm_BookProof_ChapterSirkGramWhitening_sirk_end_to_end_truncated_gram
open BookProof.ChapterSirkGramCutoff










noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (heig : IsGramEigen w u lam) {tol : ℝ}
    (R : Finset (Fin m)) (hcut : ∀ k ∉ R, lam k ≤ tol)
    {d : ℕ} (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E)
    (rX : E →L[ℂ] E) (rB : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (flow psiX : E →L[ℂ] E) (psiB : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (C Dmin hrate : ℝ) (k : ℕ)
    (hV : (adjoint V).comp V = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)))
    (hmem : ∀ j ∈ R, ∃ z, V z = synthesis w (u j))
    (hViso : ∀ x : EuclideanSpace ℂ (Fin d), ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖adjoint V v‖ ≤ ‖v‖)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - rX‖ ≤ C * (Real.exp (-(hrate * k)) * Dmin))
    (hcx2 : ‖psiB - rB‖ ≤ C * (Real.exp (-(hrate * k)) * Dmin))
    (c : EuclideanSpace ℂ (Fin m))
    (hexact : rX (V (adjoint V (synthesis w c)))
      = V (rB (adjoint V (V (adjoint V (synthesis w c))))))
    (hproj : adjoint V (V (adjoint V (synthesis w c))) = adjoint V (synthesis w c)) :
    ‖flow (synthesis w c)
        - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB (synthesis w c)‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin hrate ‖synthesis w c‖ k
        + ‖rX‖ * (Real.sqrt tol * (Real.sqrt m * ‖c‖)) :=
  sirk_end_to_end_truncated_gram w V rX rB flow psiX psiB C Dmin hrate k hViso hVadj
      hflow hcx1 hcx2 (defect_le_sqrt_cutoff heig R hcut V hV hmem) c hexact hproj
