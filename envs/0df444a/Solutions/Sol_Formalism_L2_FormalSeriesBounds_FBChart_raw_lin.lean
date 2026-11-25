-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.raw_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:19:59.996339+00:00
-- url     : https://prove2.me/submissions/3f59b1ea-952c-4730-9435-2c2f441ff81a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)
namespace Formalism.L2.FormalSeriesBounds
namespace FBChart
theorem _root_.solution (i : Fin dd) (μ : Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ ((Y.raw p).lg i) =
      MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ ?_, ← uncurry_X i]
  · rfl
  · have hd : ∀ ν : Fin dd →₀ ℕ, (ν.mapDomain fun x : Fin dd => ((0 : Fin 1), x)).degree = ν.degree := by
      intro ν
      refine Finsupp.induction_linear ν ?_ ?_ ?_
      · simp
      · intro f g hf hg
        rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg]
      · intro a b
        rw [Finsupp.mapDomain_single]
        simp
    rw [hd]
    exact hμ
end FBChart
end Formalism.L2.FormalSeriesBounds
