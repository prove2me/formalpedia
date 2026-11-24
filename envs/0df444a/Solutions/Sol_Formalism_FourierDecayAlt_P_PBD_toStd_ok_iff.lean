-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.toStd_ok_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:08.0333+00:00
-- url     : https://prove2.me/submissions/547c25d0-4e48-4f53-bf90-1f5d81ce084f

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (r : ℕ) (g : ℝ) (hg : 0 < g) : ∀ (p : C.LPt) (b : ℕ),
    (∀ x ∈ D.toStd r g b p, 1 ≤ x.1 ∧ x.2 ≠ 0) ↔ ∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ≠ 0
  | [], _ => by simp [D.toStd]
  | (s, t) :: rest, b => by
    have ih := solution r g hg rest (b + s)
    have hne : ((((g / (2 * Real.pi)) ^ S6.nuBlock r b s : ℝ) : ℂ) * Complex.I ^ (s - 1)) ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ Complex.I_ne_zero)
      have : 0 < (g / (2 * Real.pi)) ^ S6.nuBlock r b s := zpow_pos (by positivity) _
      exact_mod_cast this.ne'
    simp only [D.toStd, List.mem_cons, forall_eq_or_imp]
    rw [ih]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, fun ht => h2 (by rw [ht, mul_zero])⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, mul_ne_zero hne h2⟩, h3⟩
end Formalism.FourierDecayAlt.P.PBD
