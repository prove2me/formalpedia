-- Prove2me | solution 1 for BookProof.GroupAverage.UnitaryRep.mem_range_avgProj_iff
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:42:01.977518+00:00
-- url     : https://prove2.me/submissions/652de706-39ae-4ce9-9dfe-59ee3ecff35b

import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
open BookProof.GroupAverage
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]
variable (rep : UnitaryRep G F)

private lemma average_invariant (x : F) (g : G) :
    rep.act g (rep.avgProj x) = rep.avgProj x := by
  classical
  simp only [UnitaryRep.avgProj, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, ← rep.act_mul]
  congr 1
  exact Fintype.sum_bijective (fun h : G => g * h) (Group.mulLeft_bijective g)
    (fun h => rep.act (g * h) x) (fun h => rep.act h x) (fun h => rfl)

private lemma average_fixed {x : F} (hx : ∀ g : G, rep.act g x = x) :
    rep.avgProj x = x := by
  classical
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [UnitaryRep.avgProj, LinearMap.smul_apply, LinearMap.sum_apply, hx,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem solution {x : F} :
    x ∈ LinearMap.range rep.avgProj ↔ ∀ g : G, rep.act g x = x := by
  constructor
  · rintro ⟨y, rfl⟩ g
    exact average_invariant rep y g
  · intro hx
    exact ⟨x, average_fixed rep hx⟩

#print axioms solution
