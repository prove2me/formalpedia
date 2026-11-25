-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.isIU_of_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:06:10.230023+00:00
-- url     : https://prove2.me/submissions/2fea2fee-0f1b-4f69-a934-d39933c4a156

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {U f : MvPowerSeries τ C} (hi : IntS V U) (he : U = mvExp f) : IsIU V U := by
  refine ⟨hi, ?_⟩
  subst he
  unfold mvExp
  have h1 : (MvPowerSeries.constantCoeff fun m : τ →₀ ℕ =>
      ∑ k ∈ Finset.range (Finsupp.degree m + 1), (MvPowerSeries.coeff m) (f ^ k) / (k.factorial : C)) = 1 := by
    show (∑ k ∈ Finset.range (Finsupp.degree (0 : τ →₀ ℕ) + 1),
      (MvPowerSeries.coeff (0 : τ →₀ ℕ)) (f ^ k) / (k.factorial : C)) = 1
    simp
  rw [h1]
  first
    | simp
    | exact map_one _
    | rfl
    | (simp [VF.v]; done)
end Formalism.L2.FormalSeriesBounds.VP
