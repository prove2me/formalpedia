-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsD.polyhedral_mnat_operations
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:44:58.344318+00:00
-- url     : https://prove2.me/submissions/67dc462c-4542-45d4-ae0d-7324034dd816

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MNaturalConvexR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosScalarMul
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsConvexUniv
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SeparablePerturbR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ProjectionR

open scoped Pointwise
open Classical
open DiscreteConvex.MConvexFunctionsD

namespace Counterexample650

noncomputable def c0 : ℝ :=
  (sInf (Set.range (fun r : ℝ => (r : WithTop ℝ)))).untopD 0

def D (x : Bool → ℝ) : Prop := (x false ≠ 0 ∧ x false ≠ 1) ∨ c0 - 2 < x true

noncomputable def f (x : Bool → ℝ) : WithTop ℝ :=
  if D x then ((x true : ℝ) : WithTop ℝ) else ⊤

noncomputable def rad (x : Bool → ℝ) : ℝ :=
  if x false = 0 ∨ x false = 1 then (x true - (c0 - 2)) / 2
  else min (|x false| / 2) (|x false - 1| / 2)

lemma rad_pos {x : Bool → ℝ} (hx : D x) : 0 < rad x := by
  unfold rad
  split_ifs with h01
  · rcases hx with ⟨hne0, hne1⟩ | hgt
    · rcases h01 with h0 | h1
      · exact absurd h0 hne0
      · exact absurd h1 hne1
    · linarith
  · push_neg at h01
    refine lt_min (div_pos (abs_pos.mpr h01.1) zero_lt_two)
      (div_pos (abs_pos.mpr (sub_ne_zero.mpr h01.2)) zero_lt_two)

lemma D_of_dist {x x' : Bool → ℝ} (hx : D x)
    (hf : |x' false - x false| ≤ rad x) (ht : |x' true - x true| ≤ rad x) : D x' := by
  unfold rad at hf ht
  by_cases h01 : x false = 0 ∨ x false = 1
  · rw [if_pos h01] at hf ht
    have hgt : c0 - 2 < x true := by
      rcases hx with ⟨hne0, hne1⟩ | hgt
      · rcases h01 with h0 | h1
        · exact absurd h0 hne0
        · exact absurd h1 hne1
      · exact hgt
    right
    have := (abs_le.mp ht).1
    linarith
  · rw [if_neg h01] at hf
    push_neg at h01
    have hf0 : |x' false - x false| ≤ |x false| / 2 := hf.trans (min_le_left _ _)
    have hf1 : |x' false - x false| ≤ |x false - 1| / 2 := hf.trans (min_le_right _ _)
    left
    refine ⟨?_, ?_⟩
    · rcases lt_or_gt_of_ne h01.1 with hneg | hgt
      · rw [abs_of_neg hneg] at hf0
        have := (abs_le.mp hf0).2; linarith
      · rw [abs_of_pos hgt] at hf0
        have := (abs_le.mp hf0).1; linarith
    · rcases lt_or_gt_of_ne h01.2 with hneg | hgt
      · have hsub : x false - 1 < 0 := by linarith
        rw [abs_of_neg hsub] at hf1
        have := (abs_le.mp hf1).2; linarith
      · have hsub : 0 < x false - 1 := by linarith
        rw [abs_of_pos hsub] at hf1
        have := (abs_le.mp hf1).1; linarith

lemma charVec_abs_le (u v w : Option Bool) {α : ℝ} (h0 : 0 ≤ α) :
    |α * ((CharVec u w : ℝ) - (CharVec v w : ℝ))| ≤ α := by
  have h1 : |(CharVec u w : ℝ) - (CharVec v w : ℝ)| ≤ 1 := by
    unfold CharVec
    split_ifs <;> norm_num
  calc |α * ((CharVec u w : ℝ) - (CharVec v w : ℝ))|
      = α * |(CharVec u w : ℝ) - (CharVec v w : ℝ)| := by rw [abs_mul, abs_of_nonneg h0]
    _ ≤ α * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = α := mul_one α

lemma sum_option_bool (x : Option Bool → ℝ) :
    (∑ w : Option Bool, x w) = x none + x (some false) + x (some true) := by
  simp [Fintype.sum_option]; ring

lemma charVec_sum_option_bool (u : Option Bool) :
    (∑ w : Option Bool, (CharVec u w : ℝ)) = 1 := by
  fin_cases u <;> simp [CharVec]

lemma hf_mnat : MNaturalConvexR f := by
  intro x hx y hy u hu
  simp only [DomR, Set.mem_ofPred_eq, LiftedFunctionR, f] at hx hy
  split_ifs at hx with hxs hxd <;> try contradiction
  split_ifs at hy with hys hyd <;> try contradiction
  have hsum_x : (∑ w : Option Bool, x w) = 0 := by
    rw [sum_option_bool, hxs]; simp
  have hsum_y : (∑ w : Option Bool, y w) = 0 := by
    rw [sum_option_bool, hys]; simp
  have hex_v : ∃ v ∈ SuppNegR x y, True := by
    by_contra! hno
    have hle : ∀ w : Option Bool, y w ≤ x w := fun w => le_of_not_gt (fun hlt => hno w hlt)
    have hlt : y u < x u := hu
    have hsum_lt : (∑ w : Option Bool, y w) < ∑ w : Option Bool, x w :=
      Finset.sum_lt_sum (fun w _ => hle w) ⟨u, Finset.mem_univ u, hlt⟩
    linarith
  obtain ⟨v, hv, -⟩ := hex_v
  let xb : Bool → ℝ := fun b => x (some b)
  let yb : Bool → ℝ := fun b => y (some b)
  let α0 : ℝ := min (rad xb) (rad yb)
  have hα0 : 0 < α0 := lt_min (rad_pos hxd) (rad_pos hyd)
  refine ⟨v, hv, α0, hα0, fun α h0 hle => ?_⟩
  have hαx : α ≤ rad xb := hle.trans (min_le_left _ _)
  have hαy : α ≤ rad yb := hle.trans (min_le_right _ _)
  set x' : Option Bool → ℝ := fun w => x w - α * ((CharVec u w : ℝ) - (CharVec v w : ℝ))
  set y' : Option Bool → ℝ := fun w => y w + α * ((CharVec u w : ℝ) - (CharVec v w : ℝ))
  have hx's : x' none = -(∑ b : Bool, x' (some b)) := by
    have hsum : (∑ w : Option Bool, x' w) = 0 := by
      simp only [x', sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum, charVec_sum_option_bool, hsum_x]
      ring
    rw [sum_option_bool] at hsum
    simp; linarith
  have hy's : y' none = -(∑ b : Bool, y' (some b)) := by
    have hsum : (∑ w : Option Bool, y' w) = 0 := by
      simp only [y', Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        charVec_sum_option_bool, hsum_y]
      ring
    rw [sum_option_bool] at hsum
    simp; linarith
  have hx'd : D (fun b => x' (some b)) := by
    apply D_of_dist hxd
    · simpa [x', xb] using (charVec_abs_le u v (some false) h0).trans hαx
    · simpa [x', xb] using (charVec_abs_le u v (some true) h0).trans hαx
  have hy'd : D (fun b => y' (some b)) := by
    apply D_of_dist hyd
    · simpa [y', yb] using (charVec_abs_le u v (some false) h0).trans hαy
    · simpa [y', yb] using (charVec_abs_le u v (some true) h0).trans hαy
  simp only [LiftedFunctionR, f, hxs, hxd, hx's, hx'd, hys, hyd, hy's, hy'd, ↓reduceIte,
    ge_iff_le, ← WithTop.coe_add, WithTop.coe_le_coe]
  dsimp [x', y']
  linarith

lemma proj_interior {y : Bool → ℝ} (hy0 : y false ≠ 0) (hy1 : y false ≠ 1) :
    ProjectionR f {false} y = sInf (Set.range (fun r : ℝ => (r : WithTop ℝ))) := by
  unfold ProjectionR
  congr 1
  ext L
  simp only [Finset.mem_singleton, forall_eq, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hdz : D z := Or.inl ⟨by rwa [hz], by rwa [hz]⟩
    exact ⟨z true, by simp [f, hdz]⟩
  · rintro ⟨r, rfl⟩
    let z : Bool → ℝ := fun b => if b = false then y false else r
    have hz : z false = y false := by simp [z]
    have hdz : D z := Or.inl ⟨by rwa [hz], by rwa [hz]⟩
    exact ⟨z, hz, by simp [f, hdz, z]⟩

lemma proj_zero_le :
    ProjectionR f {false} (fun _ => 0) ≤ ((c0 - 1 : ℝ) : WithTop ℝ) := by
  unfold ProjectionR
  apply csInf_le
  · refine ⟨((c0 - 2 : ℝ) : WithTop ℝ), ?_⟩
    rintro L ⟨z, hz, rfl⟩
    simp only [Finset.mem_singleton, forall_eq] at hz
    unfold f
    split_ifs with hdz
    · rw [WithTop.coe_le_coe]
      rcases hdz with ⟨hne0, _⟩ | hgt
      · exact absurd hz hne0
      · exact hgt.le
    · exact le_top
  · refine ⟨fun b => if b = false then 0 else c0 - 1, by simp, ?_⟩
    have hdz : D (fun b => if b = false then (0 : ℝ) else c0 - 1) := Or.inr (by norm_num)
    simp [f, hdz]

lemma proj_one_le :
    ProjectionR f {false} (fun b => if b = false then 1 else 0) ≤ ((c0 - 1 : ℝ) : WithTop ℝ) := by
  unfold ProjectionR
  apply csInf_le
  · refine ⟨((c0 - 2 : ℝ) : WithTop ℝ), ?_⟩
    rintro L ⟨z, hz, rfl⟩
    simp only [Finset.mem_singleton, forall_eq, ↓reduceIte] at hz
    unfold f
    split_ifs with hdz
    · rw [WithTop.coe_le_coe]
      rcases hdz with ⟨_, hne1⟩ | hgt
      · exact absurd hz hne1
      · exact hgt.le
    · exact le_top
  · refine ⟨fun b => if b = false then 1 else c0 - 1, by simp, ?_⟩
    have hdz : D (fun b => if b = false then (1 : ℝ) else c0 - 1) := Or.inr (by norm_num)
    simp [f, hdz]

end Counterexample650

open Counterexample650 in
theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
      (f : (V → ℝ) → WithTop ℝ) (_hf : MNaturalConvexR f),
      (∀ lam : ℝ, 0 < lam → MNaturalConvexR (fun x => PosScalarMul lam (f x))) ∧
      (∀ (a : V → ℝ) (beta : ℝ), beta ≠ 0 → MNaturalConvexR (fun x => f (fun v => a v + beta * x v))) ∧
      (∀ p : V → ℝ, MNaturalConvexR (LinearWeightR f p)) ∧
      (∀ phi : V → ℝ → WithTop ℝ, (∀ v, IsConvexUniv (phi v)) →
        (DomR (SeparablePerturbR f phi)).Nonempty → MNaturalConvexR (SeparablePerturbR f phi)) ∧
      (∀ U : Finset V, (DomR (ProjectionR f U)).Nonempty → MNaturalConvexR (ProjectionR f U))) := by
  intro H
  have hdom : (DomR (ProjectionR f {false})).Nonempty := by
    refine ⟨fun _ => 0, ?_⟩
    simp only [DomR, Set.mem_ofPred_eq]
    exact ne_top_of_le_ne_top WithTop.coe_ne_top proj_zero_le
  have hproj := (H f hf_mnat).2.2.2.2 {false} hdom
  let x : Option Bool → ℝ := fun _ => 0
  let y : Option Bool → ℝ := fun o =>
    match o with
    | none => -1
    | some false => 1
    | some true => 0
  have hx_sum : x none = -(∑ b : Bool, x (some b)) := by simp [x]
  have hy_sum : y none = -(∑ b : Bool, y (some b)) := by simp [y]
  have hx_val : LiftedFunctionR (ProjectionR f {false}) x ≤ ((c0 - 1 : ℝ) : WithTop ℝ) := by
    simp only [LiftedFunctionR, hx_sum, ↓reduceIte]
    exact proj_zero_le
  have hy_val : LiftedFunctionR (ProjectionR f {false}) y ≤ ((c0 - 1 : ℝ) : WithTop ℝ) := by
    simp only [LiftedFunctionR, hy_sum, ↓reduceIte]
    have heq : (fun v : Bool => y (some v)) = (fun b => if b = false then 1 else 0) := by
      ext b; cases b <;> rfl
    rw [heq]
    exact proj_one_le
  have hx_dom : x ∈ DomR (LiftedFunctionR (ProjectionR f {false})) := by
    simp only [DomR, Set.mem_ofPred_eq]
    exact ne_top_of_le_ne_top WithTop.coe_ne_top hx_val
  have hy_dom : y ∈ DomR (LiftedFunctionR (ProjectionR f {false})) := by
    simp only [DomR, Set.mem_ofPred_eq]
    exact ne_top_of_le_ne_top WithTop.coe_ne_top hy_val
  have hu : (none : Option Bool) ∈ SuppPosR x y := by
    simp [SuppPosR, x, y]
  obtain ⟨v, hv, α0, hα0, Hα⟩ := hproj x hx_dom y hy_dom none hu
  have hv_eq : v = some false := by
    simp only [SuppNegR, Set.mem_ofPred_eq] at hv
    rcases v with _ | b
    · simp [x, y] at hv; norm_num at hv
    · cases b
      · rfl
      · simp [x, y] at hv
  subst hv_eq
  let α : ℝ := min α0 (1 / 2)
  have hα_pos : 0 < α := lt_min hα0 (by norm_num)
  have hα_le : α ≤ α0 := min_le_left _ _
  have hα_half : α ≤ 1 / 2 := min_le_right _ _
  have hle := Hα α hα_pos.le hα_le
  set x' : Option Bool → ℝ := fun w =>
    x w - α * ((CharVec (none : Option Bool) w : ℝ) - (CharVec (some false) w : ℝ))
  set y' : Option Bool → ℝ := fun w =>
    y w + α * ((CharVec (none : Option Bool) w : ℝ) - (CharVec (some false) w : ℝ))
  have hx'_sum : x' none = -(∑ b : Bool, x' (some b)) := by
    simp [x', x, CharVec]
  have hy'_sum : y' none = -(∑ b : Bool, y' (some b)) := by
    simp [y', y, CharVec]; ring
  set S_univ := sInf (Set.range (fun r : ℝ => (r : WithTop ℝ)))
  have hx'_val : LiftedFunctionR (ProjectionR f {false}) x' = S_univ := by
    simp only [LiftedFunctionR, hx'_sum, ↓reduceIte]
    apply proj_interior
    · simp [x', x, CharVec, hα_pos.ne']
    · intro h
      have h1 : x' (some false) = α := by simp [x', x, CharVec]
      linarith
  have hy'_val : LiftedFunctionR (ProjectionR f {false}) y' = S_univ := by
    simp only [LiftedFunctionR, hy'_sum, ↓reduceIte]
    apply proj_interior
    · intro h
      have h1 : y' (some false) = 1 - α := by simp [y', y, CharVec]; ring
      linarith
    · intro h
      have h1 : y' (some false) = 1 - α := by simp [y', y, CharVec]; ring
      linarith
  rw [ge_iff_le, hx'_val, hy'_val] at hle
  have hbad : S_univ + S_univ ≤ ((c0 - 1 : ℝ) : WithTop ℝ) + ((c0 - 1 : ℝ) : WithTop ℝ) :=
    hle.trans (add_le_add hx_val hy_val)
  cases hc : S_univ with
  | top =>
    rw [hc, top_add, ← WithTop.coe_add, top_le_iff] at hbad
    exact WithTop.coe_ne_top hbad
  | coe r =>
    have hc0 : c0 = r := by simp [c0, S_univ, hc]
    rw [hc, hc0, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hbad
    linarith
