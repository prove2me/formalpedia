-- Prove2me | solution 1 for CompactnessConjecture.quantitativeCompactnessCounterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/628ab4ae-5b10-4947-92ff-6cc164e68393

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_compactnessSharpHostPowerConstant_pos
import Theorems.Thm_CompactnessConjecture_checkedManuscriptCounterexample

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution :
    ∃ (family : Finset FiniteGraph) (c C : ℝ),
      family.Nonempty ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      0 < c ∧
      0 < C ∧
      UniformMemberLower family c ∧
      (∀ (n : ℕ) (host : SimpleGraph (Fin n)),
        FamilyFree family host →
          (host.edgeFinset.card : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (∀ n : ℕ,
        (familyExtremal family n : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (0 : ℝ) < 1 / 48 ∧
      (21 : ℝ) / 16 = (4 : ℝ) / 3 - 1 / 48 ∧
      ¬ IsCompactFamily family ∧
      ¬ CompactnessConjectureStatement := by
  obtain ⟨hnonempty, hgeometry, hlower_pos, hlower, hhost, hfamily,
    hgap_pos, hexponents, hnot_compact, hconjecture⟩ :=
    checkedManuscriptCounterexample
  refine ⟨proposedFamily, manuscriptLowerConstant,
    compactnessHostPowerConstant, hnonempty, hgeometry, hlower_pos, ?_,
    hlower, hhost, hfamily, hgap_pos, hexponents, hnot_compact,
    hconjecture⟩
  simpa [compactnessSharpHostPowerConstant] using
    compactnessSharpHostPowerConstant_pos
end CompactnessConjecture
