-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.gamLev_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:03.051018+00:00
-- url     : https://prove2.me/submissions/0dc82462-28d8-4ff8-bf0d-d0dbf2e3ecf4

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
theorem _root_.solution (k r : ℕ) (κ de : ℝ) (j : ℕ) (hj : j ≤ r) :
    D.GamLev k r κ de j =
      κ ^ (-(4 * ((r : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * (C.Mlev k r (j + 1) - 1))) / de * D.GamLev k r κ de (j + 1) := by
  unfold D.GamLev
  have : Finset.Ioc j (r + 1) = insert (j + 1) (Finset.Ioc (j + 1) (r + 1)) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
  rw [this, Finset.prod_insert (by simp)]
end Formalism.FourierDecayAlt.P.PBD
