-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.jet_orb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:59:58.740514+00:00
-- url     : https://prove2.me/submissions/e5832c0a-8122-44d6-abc5-3fd435509d53

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_rename
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_rename
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rename_supported
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_serIn_rename


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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
variable {n : ℕ}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (Po : ∀ o, MvPolynomial (Fin n × WV (I o)) C) (Φ : ∀ o, MvPowerSeries (Fin n × WV (I o)) C) :
    jetAt0 (∏ o, toAll o (Po o)) (∏ o, MvPowerSeries.rename (eAll n o) (Φ o)) = ∏ o, jetAt0 (Po o) (Φ o) := by
  have hA : ∀ o ∈ (Finset.univ : Finset Orb), ∀ o' ∈ (Finset.univ : Finset Orb), o ≠ o' →
      Disjoint (Set.range (eAll (I := I) n o)) (Set.range (eAll (I := I) n o')) := by
    intro o _ o' _ h
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact h (congrArg (fun z : Fin n × WVO I => z.2.1) hy).symm
  have hT : ∀ o, toAll o (Po o) = MvPolynomial.rename (eAll n o) (Po o) := fun o => rfl
  exact (rtj_jet_prod (fun o => Set.range (eAll (I := I) n o)) Finset.univ hA
    (fun o => toAll o (Po o)) (fun o => MvPowerSeries.rename (eAll n o) (Φ o))
    (fun o _ => by rw [hT]; exact rtj_rename_supported _ _)
    (fun o _ => rtj_serIn_rename _ _)).trans
    (Finset.prod_congr rfl fun o _ => by rw [hT]; exact rtj_jet_rename _ _ _)
end Formalism.L2.FormalSeriesBounds.VP
