-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.dmap_zePart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:24.085741+00:00
-- url     : https://prove2.me/submissions/e1f8d34e-c2f0-43c7-a3d3-58685a949b77

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (ε : Pt C 1 dd) (s : Orb × Fin 2) (m : Fin dd) :
    ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ε m) • zePart Y p s j =
      ∑ c : I s.1 s.2, linAct ε ((p s.1).u s.2 c) m •
        (MvPowerSeries.X (⟨s.1, ⟨s.2, c⟩⟩ : WVO I) : MvPowerSeries (WVO I) C) := by
  unfold zePart
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Finset.sum_smul]
  congr 1
end Formalism.L2.FormalSeriesBounds
