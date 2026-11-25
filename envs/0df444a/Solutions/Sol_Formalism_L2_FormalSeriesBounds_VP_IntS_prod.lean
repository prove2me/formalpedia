-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.IntS_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:04:38.366645+00:00
-- url     : https://prove2.me/submissions/92222657-a976-4564-94ec-f3a299eb9d92

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSProd

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
variable {C : Type} [Field C] {V : VF C} {σ : Type}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {ι : Type} (s : Finset ι) {F : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS V (F i)) :
    IntS V (∏ i ∈ s, F i) := by
  classical
  have hge : ∀ c : C, (c = 0 ∨ c = 1) → V.Ge 0 c := by
    rintro c (rfl | rfl)
    · simp [VF.Ge]
    · simp [VF.Ge]
  have hone : IntS V (1 : MvPowerSeries σ C) := by
    intro μ
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · exact hge 1 (Or.inr rfl)
    · exact hge 0 (Or.inl rfl)
  have hmul : ∀ F G : MvPowerSeries σ C, IntS V F → IntS V G → IntS V (F * G) := by
    intro F G hF hG μ
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_induction _ (V.Ge 0) (fun a b ha hb => ?_) (hge 0 (Or.inl rfl)) (fun q _ => ?_)
    · exact le_trans (le_min ha hb) (V.v.map_add a b)
    · have h1 := add_le_add (hF q.1) (hG q.2)
      unfold VF.Ge
      rw [AddValuation.map_mul]
      simpa using h1
  induction s using Finset.induction_on with
  | empty => simpa using hone
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hmul _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end Formalism.L2.FormalSeriesBounds.VP
