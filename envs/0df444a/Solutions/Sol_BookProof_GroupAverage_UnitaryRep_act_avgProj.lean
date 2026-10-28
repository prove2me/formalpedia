-- Prove2me | solution 1 for BookProof.GroupAverage.UnitaryRep.act_avgProj
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:30:11.307002+00:00
-- url     : https://prove2.me/submissions/5d5ae029-461f-462c-9f19-59185cbd6c95

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterWignerOrbitClassification
open BookProof.GroupAverage BookProof.ReducedEsa

namespace A3S48GA
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]

lemma inner_left (rep : UnitaryRep G F) (g : G) (x y : F) :
    (inner ℂ (rep.act g x) y : ℂ) = inner ℂ x (rep.act g⁻¹ y) := by
  conv_lhs => rw [show y = rep.act g (rep.act g⁻¹ y) by rw [← rep.act_mul, mul_inv_cancel, rep.act_one]]
  exact rep.act_inner _ _ _

lemma avg_apply (rep : UnitaryRep G F) (x : F) :
    rep.avgProj x = ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, rep.act g x := by
  simp [UnitaryRep.avgProj, LinearMap.sum_apply]

lemma act_avg (rep : UnitaryRep G F) (h : G) (x : F) : rep.act h (rep.avgProj x) = rep.avgProj x := by
  rw [avg_apply, map_smul, map_sum]
  congr 1
  simp_rw [← rep.act_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => rfl)

lemma avg_inv (rep : UnitaryRep G F) {x : F} (hx : ∀ g : G, rep.act g x = x) : rep.avgProj x = x := by
  rw [avg_apply]
  simp_rw [hx]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]

lemma red (rep : UnitaryRep G F) : IsReducingProjection rep.avgProj := by
  refine ⟨fun x => avg_inv rep (fun g => act_avg rep g x), fun x y => ?_⟩
  rw [avg_apply, avg_apply, inner_smul_left, inner_smul_right, sum_inner, inner_sum]
  simp only [map_inv₀, map_natCast]
  congr 1
  simp_rw [inner_left rep]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => rfl)
end A3S48GA
open A3S48GA

theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] (G : Type*) [Group G] [Fintype G]
    (rep : UnitaryRep G F) (h : G) (x : F) : rep.act h (rep.avgProj x) = rep.avgProj x := act_avg rep h x
