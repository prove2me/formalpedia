-- Prove2me | solution 2 for DiaconisStroock.OddPaths.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T01:42:31.965386+00:00
-- url     : https://prove2.me/submissions/20e47636-44a8-46e9-b70d-4031feb171ea

import Mathlib
import Definitions.Def_DiaconisStroock_OddPaths_Iota
import Definitions.Def_mm_spectral
import Definitions.Def_DiaconisStroock_Poincare_Paths
import Definitions.Def_mm_basic
import Theorems.Thm_DiaconisStroock_OddPaths_eigenvalue_ge

-- carved verbatim out of submission f2196187-2ec7-4b13-a48c-4afd8c626dc9, lines 304-343

section
set_option autoImplicit false
open scoped BigOperators
open MarkovMixing
open DiaconisStroock.Poincare
open MarkovMixing DiaconisStroock.Poincare DiaconisStroock.OddPaths
open MarkovMixing DiaconisStroock.OddPaths

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (haper : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (S : V → List V) (hS : IsOddPathSystem P π S) :
    -1 + 2 / iota P π S ≤ betaMin P := by
  have hx : ∃ x, 0 < π x := by
    by_contra hn
    push_neg at hn
    have hs := Finset.sum_nonpos (s := Finset.univ) (fun x _ => hn x)
    have hm := hπ.1.2
    linarith
  obtain ⟨x, hx⟩ := hx
  have h1 : IsEigenvalue P 1 := by
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro hz
      have hc := congrFun hz x
      norm_num at hc
    · ext y
      change (∑ z, P y z*1) = 1*1
      simpa using hP.2 y
  apply le_csInf (show Set.Nonempty {β : ℝ | IsEigenvalue P β} from ⟨1, h1⟩)
  intro β hβ
  exact DiaconisStroock.OddPaths.eigenvalue_ge P hP hirr π hπ hrev S hS β hβ

end
