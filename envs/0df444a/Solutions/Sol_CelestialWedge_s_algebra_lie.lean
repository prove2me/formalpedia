-- Prove2me | solution 1 for CelestialWedge.s_algebra_lie
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T15:24:30.273983+00:00
-- url     : https://prove2.me/submissions/bfbe394c-ad46-4122-8306-4209549fdb11

import Mathlib
import Definitions.Def_celestial_wedge_algebra
import Definitions.Def_celestial_gluon_s_algebra

set_option autoImplicit false

universe u

namespace CelestialWedgeSAux

open CelestialWedge Complex

lemma inWedge_add (x y : WedgeIndex) : InWedge (x.1.1 + y.1.1 - 1) (x.1.2 + y.1.2) := by
  obtain ⟨a, b, ha, hb⟩ := x.2
  obtain ⟨c, d, hc, hd⟩ := y.2
  exact ⟨a + c, b + d, by push_cast; linarith, by push_cast; linarith⟩

noncomputable def wadd (x y : WedgeIndex) : WedgeIndex :=
  ⟨(x.1.1 + y.1.1 - 1, x.1.2 + y.1.2), inWedge_add x y⟩

lemma wadd_comm (x y : WedgeIndex) : wadd x y = wadd y x := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_ <;> simp only [wadd] <;> ring

lemma wadd_assoc (x y z : WedgeIndex) : wadd x (wadd y z) = wadd (wadd x y) z := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_ <;> simp only [wadd] <;> ring

lemma wadd_left_comm (x y z : WedgeIndex) : wadd y (wadd x z) = wadd (wadd x y) z := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_ <;> simp only [wadd] <;> ring

variable {ι : Type u} [Fintype ι] (f : ι → ι → ι → ℂ)

lemma gen_eq (x y : WedgeIndex × ι) :
    sBracketGen f x y = ∑ c, (-I * f x.2 y.2 c) • Finsupp.single (wadd x.1 y.1, c) (1 : ℂ) := by
  unfold sBracketGen
  rw [dif_pos (inWedge_add x.1 y.1)]
  rfl

lemma br_single (x y : WedgeIndex × ι) :
    sBracket f (Finsupp.single x 1) (Finsupp.single y 1) = sBracketGen f x y := by
  simp [sBracket, Finsupp.linearCombination_single]

lemma antisymm_basis (hf : IsLieStructureConstants f) (x y : WedgeIndex × ι) :
    sBracket f (Finsupp.single x 1) (Finsupp.single y 1) =
      -sBracket f (Finsupp.single y 1) (Finsupp.single x 1) := by
  rw [br_single, br_single, gen_eq, gen_eq, wadd_comm x.1 y.1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hf.1 x.2 y.2 c, ← neg_smul]
  congr 1
  ring

lemma antisymm (hf : IsLieStructureConstants f) (X Y : SSpace ι) :
    sBracket f X Y = -sBracket f Y X := by
  induction X using Finsupp.induction_linear with
  | zero => simp
  | add X1 X2 h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2, neg_add]
  | single x r =>
    induction Y using Finsupp.induction_linear with
    | zero => simp
    | add Y1 Y2 h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2, neg_add]
    | single y s =>
      rw [← Finsupp.smul_single_one x r, ← Finsupp.smul_single_one y s]
      simp only [map_smul, LinearMap.smul_apply]
      rw [antisymm_basis f hf x y, smul_neg, smul_neg, smul_comm r s]

lemma coef_id (hf : IsLieStructureConstants f) (a b e d : ι) :
    ∑ c, (-I * f b e c) * (-I * f a c d) =
      ∑ c, (-I * f a b c) * (-I * f c e d) + ∑ c, (-I * f a e c) * (-I * f b c d) := by
  have J := hf.2 a b e d
  have h1 : ∀ c, f c a d = -f a c d := fun c => hf.1 c a d
  have h2 : ∀ c, f e a c = -f a e c := fun c => hf.1 e a c
  have h3 : ∀ c, f c b d = -f b c d := fun c => hf.1 c b d
  simp only [h1, h2, h3] at J
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at J
  have hII : ∀ x y : ℂ, (-I * x) * (-I * y) = -(x * y) := by
    intro x y
    have : I * I = -1 := I_mul_I
    linear_combination (x * y) * this
  simp only [hII, Finset.sum_neg_distrib]
  have k1 : ∑ c, f b e c * -f a c d = -∑ c, f b e c * f a c d := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun c _ => by ring
  have k2 : ∑ c, -f a e c * -f b c d = ∑ c, f a e c * f b c d := by
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [k1, k2] at J
  linear_combination J

lemma jac_basis (hf : IsLieStructureConstants f) (x y z : WedgeIndex × ι) :
    sBracket f (Finsupp.single x 1) (sBracket f (Finsupp.single y 1) (Finsupp.single z 1)) =
      sBracket f (sBracket f (Finsupp.single x 1) (Finsupp.single y 1)) (Finsupp.single z 1) +
        sBracket f (Finsupp.single y 1)
          (sBracket f (Finsupp.single x 1) (Finsupp.single z 1)) := by
  have hL : sBracket f (Finsupp.single x 1)
      (sBracket f (Finsupp.single y 1) (Finsupp.single z 1)) =
      ∑ d, (∑ c, (-I * f y.2 z.2 c) * (-I * f x.2 c d)) •
        Finsupp.single (wadd (wadd x.1 y.1) z.1, d) (1 : ℂ) := by
    rw [br_single, gen_eq, map_sum]
    simp only [map_smul, br_single, gen_eq, Finset.smul_sum, smul_smul, wadd_assoc]
    rw [Finset.sum_comm]
    simp only [Finset.sum_smul]
  have hR1 : sBracket f (sBracket f (Finsupp.single x 1) (Finsupp.single y 1))
      (Finsupp.single z 1) =
      ∑ d, (∑ c, (-I * f x.2 y.2 c) * (-I * f c z.2 d)) •
        Finsupp.single (wadd (wadd x.1 y.1) z.1, d) (1 : ℂ) := by
    rw [br_single, gen_eq, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, br_single, gen_eq, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_smul]
  have hR2 : sBracket f (Finsupp.single y 1)
      (sBracket f (Finsupp.single x 1) (Finsupp.single z 1)) =
      ∑ d, (∑ c, (-I * f x.2 z.2 c) * (-I * f y.2 c d)) •
        Finsupp.single (wadd (wadd x.1 y.1) z.1, d) (1 : ℂ) := by
    rw [br_single, gen_eq, map_sum]
    simp only [map_smul, br_single, gen_eq, Finset.smul_sum, smul_smul, wadd_left_comm]
    rw [Finset.sum_comm]
    simp only [Finset.sum_smul]
  rw [hL, hR1, hR2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← add_smul, coef_id f hf]

lemma jacobi (hf : IsLieStructureConstants f) (X Y Z : SSpace ι) :
    sBracket f X (sBracket f Y Z) =
      sBracket f (sBracket f X Y) Z + sBracket f Y (sBracket f X Z) := by
  induction X using Finsupp.induction_linear with
  | zero => simp
  | add X1 X2 h1 h2 =>
    simp only [map_add, LinearMap.add_apply, h1, h2]
    abel
  | single x r =>
    induction Y using Finsupp.induction_linear with
    | zero => simp
    | add Y1 Y2 h1 h2 =>
      simp only [map_add, LinearMap.add_apply, h1, h2]
      abel
    | single y s =>
      induction Z using Finsupp.induction_linear with
      | zero => simp
      | add Z1 Z2 h1 h2 =>
        simp only [map_add, LinearMap.add_apply, h1, h2]
        abel
      | single z t =>
        rw [← Finsupp.smul_single_one x r, ← Finsupp.smul_single_one y s,
          ← Finsupp.smul_single_one z t]
        simp only [map_smul, LinearMap.smul_apply]
        rw [jac_basis f hf x y z]
        simp only [smul_add, smul_smul]
        congr 1 <;> congr 1 <;> ring

end CelestialWedgeSAux

open CelestialWedge Complex in
theorem solution {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ)
    (hf : IsLieStructureConstants f) :
    (∀ X : SSpace ι, sBracket f X X = 0) ∧
    (∀ X Y Z : SSpace ι,
      sBracket f X (sBracket f Y Z) =
        sBracket f (sBracket f X Y) Z + sBracket f Y (sBracket f X Z)) := by
  refine ⟨fun X => ?_, fun X Y Z => CelestialWedgeSAux.jacobi f hf X Y Z⟩
  have h := CelestialWedgeSAux.antisymm f hf X X
  have h2 : (2 : ℂ) • sBracket f X X = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  rcases smul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact h3
