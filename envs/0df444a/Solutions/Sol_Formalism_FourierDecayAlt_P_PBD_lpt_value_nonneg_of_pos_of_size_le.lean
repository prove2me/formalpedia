-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:36:11.003388+00:00
-- url     : https://prove2.me/submissions/d755d64b-5abe-43da-b422-86730cc60106

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 < fr b s) :
    ∀ (p : C.LPt) (b : ℕ), 1 ≤ b → b + D.ptSize p ≤ r + 1 → 0 ≤ C.nAux k r GG fr b p
  | [], _, _, _ => by simp [C.nAux]
  | (s, t) :: rest, b, hb, hs => by
    simp only [D.ptSize, List.map_cons, List.sum_cons] at hs
    have ih := solution k r GG fr hfr rest (b + s) (by omega) (by simp only [D.ptSize]; omega)
    simp only [C.nAux]
    refine mul_nonneg ?_ ih
    have : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by
      rintro ⟨h1, h2⟩
      have : 0 ≤ (rest.map Prod.fst).sum := Nat.zero_le _
      omega
    rw [if_neg this]
    exact zpow_nonneg (mul_nonneg (hfr b s).le (norm_nonneg _)) _
end Formalism.FourierDecayAlt.P.PBD
