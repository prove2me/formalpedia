-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctions.l_optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T06:45:33.597145+00:00
-- url     : https://prove2.me/submissions/2f6cfe81-67a8-4bad-9ffa-8d7a87648a91

import Theorems.Thm_DiscreteConvex_LConvexFunctions_l_proximity_theorem
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ

open DiscreteConvex.LConvexFunctions
namespace LProximityOptimality
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma unit_shift_of_base_equality (g : (V → ℤ) → WithTop ℝ) (ht : TRF g)
    (p : V → ℤ) (hp : g p ≠ ⊤) (he : g p = g (fun v => p v+1)) :
    ∀ q : V → ℤ, g (fun v => q v+1) = g q := by
  obtain ⟨r,hr⟩ := ht
  have hz : (r : WithTop ℝ) = 0 := by
    apply (add_right_inj_of_ne_top hp).mp
    calc
      g p + (r : WithTop ℝ) = g (p+1) := (hr p).symm
      _ = g p := he.symm
      _ = g p+0 := by simp
  intro q
  have hfun : (q+1 : V → ℤ) = (fun v => q v+1) := by funext v; rfl
  simpa only [hfun,hz,add_zero] using hr q

lemma unit_equality_of_minimum (g : (V → ℤ) → WithTop ℝ) (ht : TRF g)
    (p : V → ℤ) (hmin : ∀ q, g p ≤ g q) : g p = g (fun v => p v+1) := by
  obtain ⟨r,hr⟩ := ht
  have hback : g (fun v => p v-1) + (r : WithTop ℝ) = g p := by
    have he : ((fun v => p v-1) + 1 : V → ℤ) = p := by
      funext v
      simp
    simpa only [he] using (hr (fun v => p v-1)).symm
  apply le_antisymm (hmin _)
  change g (p+1) ≤ g p
  rw [hr]
  exact (add_le_add (hmin (fun v => p v-1)) le_rfl).trans_eq hback

theorem criterion :
    (∀ g : (V → ℤ) → WithTop ℝ, SBF g → TRF g → ∀ p ∈ DomZ g,
      (∀ q, g p ≤ g q) ↔
        ((∀ Y : Finset V, g p ≤ g (fun v => p v + IndicatorVec Y v)) ∧
          g p = g (fun v => p v + 1))) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, LNaturalConvex g → ∀ p ∈ DomZ g,
      (∀ q, g p ≤ g q) ↔
        (∀ Y : Finset V, g p ≤ g (fun v => p v + IndicatorVec Y v) ∧
          g p ≤ g (fun v => p v - IndicatorVec Y v))) := by
  constructor
  · intro g hs ht p hp
    constructor
    · intro hmin
      exact ⟨fun Y => hmin _,unit_equality_of_minimum g ht p hmin⟩
    · rintro ⟨hloc,heq⟩
      have hunit := unit_shift_of_base_equality g ht p hp heq
      obtain ⟨_,r,hr,hbounds⟩ :=
        (DiscreteConvex.LConvexFunctions.l_proximity_theorem (V := V) 1 (by norm_num)).1
          g hs ht hunit p hp (by simpa only [one_mul] using hloc)
      have he : r = p := by
        funext v
        have hb := hbounds v
        simp only [sub_self,mul_zero,add_zero] at hb
        exact le_antisymm hb.2 hb.1
      simpa only [he,ArgMin,Set.mem_setOf_eq] using hr
  · intro g hL p hp
    constructor
    · intro hmin Y
      exact ⟨hmin _,hmin _⟩
    · intro hloc
      obtain ⟨_,r,hr,hbounds⟩ :=
        (DiscreteConvex.LConvexFunctions.l_proximity_theorem (V := V) 1 (by norm_num)).2
          g hL p hp (by simpa only [one_mul] using hloc)
      have he : r = p := by
        funext v
        have hb := hbounds v
        simp only [sub_self,mul_zero,add_zero,sub_zero] at hb
        exact le_antisymm hb.2 hb.1
      simpa only [he,ArgMin,Set.mem_setOf_eq] using hr

end LProximityOptimality
#print axioms LProximityOptimality.unit_shift_of_base_equality
#print axioms LProximityOptimality.criterion


theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ g : (V → ℤ) → WithTop ℝ, SBF g → TRF g → ∀ p ∈ DomZ g,
      (∀ q, g p ≤ g q) ↔
        ((∀ Y : Finset V, g p ≤ g (fun v => p v + IndicatorVec Y v)) ∧
          g p = g (fun v => p v + 1))) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, LNaturalConvex g → ∀ p ∈ DomZ g,
      (∀ q, g p ≤ g q) ↔
        (∀ Y : Finset V, g p ≤ g (fun v => p v + IndicatorVec Y v) ∧
          g p ≤ g (fun v => p v - IndicatorVec Y v))) := LProximityOptimality.criterion (V := V)

#print axioms solution
