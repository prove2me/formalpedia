-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.axioms_from_families
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:20.095574+00:00
-- url     : https://prove2.me/submissions/7a5aec4c-405a-4824-a181-049095ee54c0

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_tb_zero

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
theorem _root_.solution : AxiomsFromFamilies := by
  classical
  intro hU hA E W _ D hyp he htop
  have key : ∀ i s, ∃ Th : E → TB.Pt E → TB.Pt E → ℂ,
      ((1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1) → ∀ F : Finset (TB.Pt E), (∀ h ∈ F, TB.level h = i - s) →
        (LocSys.mk (sysOf D i s).N Th (sysOf D i s).B (sysOf D i s).L (sysOf D i s).L').Ok F) ∧
      (∀ t h h', ¬ (TB.level h = i - s ∧ TB.level h' = i - s) → Th t h h' = 0) ∧
      ∀ t (F : Finset (TB.Pt E)), TB.PSDOn F (Th t) := by
    intro i s
    by_cases hr : 1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1
    · obtain ⟨Th, h1, h2, h3⟩ := hU E (TB.Pt E) {h | TB.level h = i - s} (sysOf D i s).N
        (sysOf D i s).B (sysOf D i s).L (sysOf D i s).L'
        (fun F hF => hyp i s hr.1 hr.2.1 hr.2.2 F hF)
      exact ⟨Th, fun _ => h1, h2, h3⟩
    · exact ⟨fun _ _ _ => 0, fun h => absurd h hr, fun _ _ _ _ => rfl, fun _ _ => Jx9.tb_zero⟩
  choose Th h1 h2 h3 using key
  refine ⟨Th, ?_⟩
  have := hA E W (withTh D Th) (fun i s hs hsi hi Y hY => h1 i s ⟨hs, hsi, hi⟩ Y hY) he
    (fun i s t h h' hn => h2 i s t h h' hn) htop
  exact ⟨this.1, this.2, fun i s t Y => h3 i s t Y⟩
end Formalism.FourierDecayAlt.P
