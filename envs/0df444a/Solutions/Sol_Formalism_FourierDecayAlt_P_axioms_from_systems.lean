-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.axioms_from_systems
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:42:28.476304+00:00
-- url     : https://prove2.me/submissions/e53a2dc0-b370-4d29-846d-087901aee332

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : AxiomsFromSystems := by
  intro E W _ D hOk he hTh htop
  classical
  constructor
  · intro i s hs hsi hi h h' t t' hl hl' ht ht' hne hK
    have ok := hOk i s hs hsi hi {h, h'} (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
    refine ⟨?_, ok.1 t t' ht ht' h (by simp) h' (by simp) hK⟩
    rintro ⟨rfl, rfl⟩
    exact hK (htop h h' t t' (by simpa using hl) (by simpa using hl') ht ht' hne)
  · intro i s hs hsi hi
    refine ⟨he i (by omega) hi, ?_, ?_, ?_⟩
    · intro t ht Y hY
      exact (hOk i s hs hsi hi Y hY).2.2.2.2.1 t ht
    · intro t t' htt
      funext h h'
      by_cases hl : TB.level h = i - s ∧ TB.level h' = i - s
      · have ok := hOk i s hs hsi hi {h, h'} (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hl.1
          · exact hl.2)
        exact ok.2.2.1 t t' htt h (by simp) h' (by simp)
      · rw [hTh i s t h h' hl, hTh i s t' h h' hl]
    · intro S hS Y hY
      exact (hOk i s hs hsi hi Y hY).2.2.2.2.2 S hS
end Formalism.FourierDecayAlt.P
