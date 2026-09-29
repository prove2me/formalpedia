-- Prove2me | solution 2 for Erdos9796Mission.problem96
-- status  : ACCEPTED   (disprove)
-- author  : @mysticflounder
-- created : 2026-09-13T22:58:39.702365+00:00
-- url     : https://prove2.me/submissions/d9629b77-2ade-4d49-a684-b8af3636a0b7

/-
Prove2Me disproof adapter, prepared by Adam McKenna, 2026-09-13.
Construction and proof: Liam Kruer, Jensen Kohlmeyer, Liam Price.
Upstream commit: 0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2.
Upstream proof declarations are unchanged; its final custom audit command is omitted.
-/
import Definitions.Def_Erdos9796Mission

import Mathlib

/-!
# Unit distances in convex polygons: complete formalisation

Single-file formalisation of 96-97.tex by Liam Kruer, Jensen Kohlmeyer, and
Liam Price. All construction lemmas, quantitative results, corollaries, and
the disproofs of Erdos problems 96, 97, and the general fixed-k conjecture
are included below. The only import is Mathlib.

Main entry points in namespace Proof:
* main_theorem and main_quantitative (explicit absolute constant C = 7)
* finite_construction_plane and threshold_configuration_plane
* convex_unit_distances_omega and eventual_minimum_degree
* bounded_size_minimum_degree and explicit_erdos_97_counterexample
* erdos_96_false, erdos_97_false, and erdos_97_general_false

The final section checks the transitive axiom dependencies of 33 results,
permitting only propext, Classical.choice, and Quot.sound.

Checked with Lean v4.33.1 and the Mathlib version used by this project.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

/- The following compatibility definitions reproduce the relevant geometry
interfaces of FormalConjecturesForMathlib.Geometry.Metric and Geometry.2d.
Those sources are Copyright 2025 The Formal Conjectures Authors and licensed
under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0
They are included here so this file requires no Formal Conjectures imports. -/

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

noncomputable def unitDistNum {X : Type*} [MetricSpace X] (s : Finset X) : ℕ := by
  classical
  exact (s.sym2.filter fun p => dist p.out.1 p.out.2 = 1).card

namespace EuclideanGeometry
open scoped EuclideanGeometry

def ConvexIndep (S : Set ℝ²) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

end EuclideanGeometry

/-! ## Source: Definitions.lean -/

section Combined_Definitions

/-!
Definitions used by the Formal Conjectures statements of Erdős problems 96 and 97.
The definitions below reproduce the relevant definitions from those problem files;
no conjecture declaration or unproved theorem is imported.
-/

open EuclideanGeometry
open scoped EuclideanGeometry

namespace Erdos96

noncomputable def convexUnitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistNum points | (points : Finset ℝ²) (_ : points.card = n) (_ : ConvexIndep points)}

noncomputable def maxConvexUnitDistances (n : ℕ) : ℕ :=
  sSup (convexUnitDistanceCounts n)

end Erdos96

namespace Erdos97

def HasNEquidistantPointsAt (n : ℕ) (A : Finset ℝ²) (p : ℝ²) : Prop :=
  ∃ r : ℝ, r > 0 ∧ (A.filter fun q ↦ dist p q = r).card ≥ n

def HasNEquidistantPointsOn (n : ℕ) (A B : Finset ℝ²) : Prop :=
  ∀ p ∈ B, HasNEquidistantPointsAt n A p

def HasNEquidistantProperty (n : ℕ) (A : Finset ℝ²) : Prop :=
  HasNEquidistantPointsOn n A A

def HasNUnitDistancePointsAt (n : ℕ) (A : Finset ℝ²) (p : ℝ²) : Prop :=
  (A.filter fun q ↦ dist p q = 1).card ≥ n

def HasNUnitDistancePointsOn (n : ℕ) (A B : Finset ℝ²) : Prop :=
  ∀ p ∈ B, HasNUnitDistancePointsAt n A p

def HasNUnitDistanceProperty (n : ℕ) (A : Finset ℝ²) : Prop :=
  HasNUnitDistancePointsOn n A A

end Erdos97

end Combined_Definitions

/-! ## Source: Erdos96.lean -/

section Combined_Erdos96

/-!
# Superlinearly many unit distances in convex position
Authors: Liam Kruer <kruerl@purdue.edu>
         Jensen Kohlmeyer <jenwin@purdue.edu>

OpenAI Codex provided substantial assistance with the mathematical exploration,
construction, proofs, formalization, verification, and manuscript preparation.
The authors are responsible for the content.

Proof of the original counterexample and the negation of Erdős problem 96.
The conjectures' definitions above do not import unproved statements.
-/

open _root_.Erdos96

/- ## Angle -/

section OriginalAngle

/- Calculus of the angle subtended by a unit chord at the origin. -/

namespace Proof


noncomputable def chordCos (r s : ℝ) : ℝ := (r ^ 2 + s ^ 2 - 1) / (2 * r * s)
noncomputable def chordCosLeft (r s : ℝ) : ℝ := (r ^ 2 - s ^ 2 + 1) / (2 * r ^ 2 * s)
noncomputable def chordCosMixed (r s : ℝ) : ℝ := -(r ^ 2 + s ^ 2 + 1) / (2 * r ^ 2 * s ^ 2)
noncomputable def chordAngle (r s : ℝ) : ℝ := Real.arccos (chordCos r s)

theorem chordCos_comm (r s : ℝ) : chordCos r s = chordCos s r := by
  unfold chordCos
  congr 1 <;> ring

theorem hasDerivAt_chordCos_left {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) :
    HasDerivAt (fun x => chordCos x s) (chordCosLeft r s) r := by
  have hnum := (((hasDerivAt_id r).pow 2).add_const (s ^ 2)).sub_const 1
  have hden := ((hasDerivAt_id r).const_mul 2).mul_const s
  convert! hnum.div hden (mul_ne_zero (mul_ne_zero two_ne_zero hr) hs) using 1
  dsimp only [id_eq, Pi.pow_apply]
  unfold chordCosLeft
  field_simp [hr, hs]
  ring

theorem hasDerivAt_chordCos_right {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) :
    HasDerivAt (chordCos r) (chordCosLeft s r) s := by
  simpa only [chordCos_comm] using hasDerivAt_chordCos_left hs hr

theorem hasDerivAt_chordCosLeft_right {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) :
    HasDerivAt (chordCosLeft r) (chordCosMixed r s) s := by
  have hnum := (((hasDerivAt_id s).pow 2).const_sub (r ^ 2)).add_const 1
  have hden := (hasDerivAt_id s).const_mul (2 * r ^ 2)
  convert! hnum.div hden (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hr)) hs) using 1
  dsimp only [id_eq, Pi.pow_apply]
  unfold chordCosMixed
  field_simp [hr, hs]
  ring

theorem chordCos_mixed_identity {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) :
    -(chordCosMixed r s * (1 - chordCos r s ^ 2) +
      chordCos r s * chordCosLeft r s * chordCosLeft s r) = 1 / (r ^ 2 * s ^ 2) := by
  unfold chordCosMixed chordCos chordCosLeft
  field_simp [hr, hs]
  ring

noncomputable def chordAngleLeft (r s : ℝ) : ℝ :=
  -chordCosLeft r s / Real.sqrt (1 - chordCos r s ^ 2)

theorem chord_discriminant_pos {r s : ℝ}
    (hl : -1 < chordCos r s) (hu : chordCos r s < 1) :
    0 < 1 - chordCos r s ^ 2 := by
  nlinarith

theorem hasDerivAt_chordAngle_left {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    (hl : -1 < chordCos r s) (hu : chordCos r s < 1) :
    HasDerivAt (fun x => chordAngle x s) (chordAngleLeft r s) r := by
  convert! (Real.hasDerivAt_arccos (ne_of_gt hl) (ne_of_lt hu)).comp r
    (hasDerivAt_chordCos_left hr hs) using 1
  unfold chordAngleLeft
  ring

theorem hasDerivAt_chordAngleLeft_right {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    (hl : -1 < chordCos r s) (hu : chordCos r s < 1) :
    HasDerivAt (chordAngleLeft r)
      (1 / (r ^ 2 * s ^ 2 * Real.sqrt (1 - chordCos r s ^ 2) ^ 3)) s := by
  have hq := chord_discriminant_pos hl hu
  have hsqrt : Real.sqrt (1 - chordCos r s ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hsquare := Real.sq_sqrt hq.le
  have hnum := (hasDerivAt_chordCosLeft_right hr hs).neg
  have hden := (((hasDerivAt_chordCos_right hr hs).pow 2).const_sub 1).sqrt (ne_of_gt hq)
  convert! hnum.div hden hsqrt using 1
  have hid := chordCos_mixed_identity hr hs
  dsimp only [id_eq, Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul, mul_one]
  field_simp [hr, hs, hsqrt] at hid ⊢
  rw [hsquare]
  linear_combination -hid

theorem chordAngle_mixed_positive {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    (hl : -1 < chordCos r s) (hu : chordCos r s < 1) :
    0 < deriv (chordAngleLeft r) s := by
  rw [(hasDerivAt_chordAngleLeft_right hr hs hl hu).deriv]
  have := Real.sqrt_pos.mpr (chord_discriminant_pos hl hu)
  positivity

end Proof

end OriginalAngle

/- ## GenericAngles -/

section OriginalGenericAngles

/- Local separation of finite linear combinations of edge angles. -/

namespace Proof

open Set Filter
open scoped Topology


def ChordFeasible (r s : ℝ) : Prop :=
  r ≠ 0 ∧ s ≠ 0 ∧ -1 < chordCos r s ∧ chordCos r s < 1

theorem chordAngle_rectangle_strict {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hf : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, ChordFeasible x y) :
    0 < chordAngle b d - chordAngle a d - chordAngle b c + chordAngle a c := by
  have hm : ∀ x ∈ Icc a b, chordAngleLeft x c < chordAngleLeft x d := by
    intro x hx
    have hmono : StrictMonoOn (chordAngleLeft x) (Icc c d) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc c d)
      · intro y hy
        obtain ⟨hr, hs, hl, hu⟩ := hf x hx y hy
        exact (hasDerivAt_chordAngleLeft_right hr hs hl hu).continuousAt.continuousWithinAt
      · intro y hy
        obtain ⟨hr, hs, hl, hu⟩ := hf x hx y (interior_subset hy)
        exact chordAngle_mixed_positive hr hs hl hu
    exact hmono ⟨le_rfl, hcd.le⟩ ⟨hcd.le, le_rfl⟩ hcd
  have hder : ∀ x ∈ Icc a b,
      HasDerivAt (fun t => chordAngle t d - chordAngle t c)
        (chordAngleLeft x d - chordAngleLeft x c) x := by
    intro x hx
    obtain ⟨hrd, hsd, hld, hud⟩ := hf x hx d ⟨hcd.le, le_rfl⟩
    obtain ⟨hrc, hsc, hlc, huc⟩ := hf x hx c ⟨le_rfl, hcd.le⟩
    exact (hasDerivAt_chordAngle_left hrd hsd hld hud).sub
      (hasDerivAt_chordAngle_left hrc hsc hlc huc)
  have hmono : StrictMonoOn (fun t => chordAngle t d - chordAngle t c) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    · intro x hx
      exact (hder x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hder x (interior_subset hx)).deriv]
      exact sub_pos.mpr (hm x (interior_subset hx))
  have hh := hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  linarith

noncomputable def matrixSum {L P : Type*} [Fintype L] [Fintype P]
    (f : L → P → ℝ → ℝ → ℝ) (r : L → ℝ) (s : P → ℝ) : ℝ :=
  ∑ i, ∑ j, f i j (r i) (s j)

theorem matrix_rectangle {L P : Type*} [Fintype L] [Fintype P]
    [DecidableEq L] [DecidableEq P] (f : L → P → ℝ → ℝ → ℝ)
    (r : L → ℝ) (s : P → ℝ) (i : L) (j : P) (x y : ℝ) :
    matrixSum f (Function.update r i x) (Function.update s j y) -
      matrixSum f r (Function.update s j y) -
      matrixSum f (Function.update r i x) s + matrixSum f r s =
    f i j x y - f i j (r i) y - f i j x (s j) + f i j (r i) (s j) := by
  let g := fun a b => f a b (Function.update r i x a) (Function.update s j y b) -
    f a b (r a) (Function.update s j y b) -
    f a b (Function.update r i x a) (s b) + f a b (r a) (s b)
  have he : matrixSum f (Function.update r i x) (Function.update s j y) -
      matrixSum f r (Function.update s j y) -
      matrixSum f (Function.update r i x) s + matrixSum f r s = ∑ a, ∑ b, g a b := by
    simp only [matrixSum, g, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [he, Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [g]
    · intro b _ hbj
      simp [g, Function.update_of_ne hbj]
    · simp
  · intro a _ hai
    apply Finset.sum_eq_zero
    intro b _
    simp [g, Function.update_of_ne hai]
  · simp

theorem finite_avoidance {X K Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] [Zero Y]
    (f : K → X → Y) (U : Set X) (hU : IsOpen U) (hne : U.Nonempty)
    (hc : ∀ k, ContinuousOn (f k) U)
    (hnc : ∀ k, ∀ V : Set X, V ⊆ U → IsOpen V → V.Nonempty → ∃ x ∈ V, f k x ≠ 0)
    (s : Finset K) : ∃ x ∈ U, ∀ k ∈ s, f k x ≠ 0 := by
  classical
  suffices ∃ V : Set X, V ⊆ U ∧ IsOpen V ∧ V.Nonempty ∧
      ∀ x ∈ V, ∀ k ∈ s, f k x ≠ 0 by
    obtain ⟨V, hVU, hVo, ⟨x, hx⟩, hv⟩ := this
    exact ⟨x, hVU hx, hv x hx⟩
  induction s using Finset.induction_on with
  | empty => exact ⟨U, subset_rfl, hU, hne, by simp⟩
  | @insert k s hks ih =>
    obtain ⟨V, hVU, hVo, hVne, hV⟩ := ih
    obtain ⟨x, hx, hkx⟩ := hnc k V hVU hVo hVne
    refine ⟨V ∩ (f k) ⁻¹' ({0}ᶜ), inter_subset_left.trans hVU,
      (hc k |>.mono hVU).isOpen_inter_preimage hVo isClosed_singleton.isOpen_compl,
      ⟨x, hx, hkx⟩, ?_⟩
    intro y hy j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hy.2
    · exact hV y hy.1 j hj

theorem coordinate_rectangle {L P : Type*} [DecidableEq L] [DecidableEq P]
    {U : Set ((L → ℝ) × (P → ℝ))} (hU : IsOpen U) {z : (L → ℝ) × (P → ℝ)}
    (hz : z ∈ U) (i : L) (j : P) :
    ∃ b d : ℝ, z.1 i < b ∧ z.2 j < d ∧
      ∀ x ∈ Icc (z.1 i) b, ∀ y ∈ Icc (z.2 j) d,
        (Function.update z.1 i x, Function.update z.2 j y) ∈ U := by
  let F := fun xy : ℝ × ℝ => (Function.update z.1 i xy.1, Function.update z.2 j xy.2)
  have hF : Continuous F := by unfold F; fun_prop
  have hmem : (z.1 i, z.2 j) ∈ F ⁻¹' U := by simpa [F] using hz
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp ((hU.preimage hF).mem_nhds hmem)
  obtain ⟨a, b, hab, hAsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hA
  obtain ⟨c, d, hcd, hBsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hB
  refine ⟨(z.1 i + b) / 2, (z.2 j + d) / 2, by linarith [hab.2], by linarith [hcd.2], ?_⟩
  intro x hx y hy
  change (x, y) ∈ F ⁻¹' U
  apply hAB
  constructor
  · apply hAsub
    constructor <;> linarith [hab.1, hab.2, hx.1, hx.2]
  · apply hBsub
    constructor <;> linarith [hcd.1, hcd.2, hy.1, hy.2]

theorem angle_sum_not_constant {L P : Type*} [Fintype L] [Fintype P]
    [DecidableEq L] [DecidableEq P] (c : L → P → ℝ) (i : L) (j : P) (hc : c i j ≠ 0)
    (U : Set ((L → ℝ) × (P → ℝ))) (hU : IsOpen U) (hne : U.Nonempty)
    (hf : ∀ z ∈ U, ChordFeasible (z.1 i) (z.2 j)) (k : ℝ) :
    ∃ z ∈ U, matrixSum (fun a b x y => c a b * chordAngle x y) z.1 z.2 ≠ k := by
  by_contra hnone
  push Not at hnone
  obtain ⟨z, hz⟩ := hne
  obtain ⟨b, d, hb, hd, hrect⟩ := coordinate_rectangle hU hz i j
  have hfeas : ∀ x ∈ Icc (z.1 i) b, ∀ y ∈ Icc (z.2 j) d, ChordFeasible x y := by
    intro x hx y hy
    simpa using hf _ (hrect x hx y hy)
  have hpositive := chordAngle_rectangle_strict hb hd hfeas
  have h00 := hnone z hz
  have h11 := hnone _ (hrect b ⟨hb.le, le_rfl⟩ d ⟨hd.le, le_rfl⟩)
  have h01 := hnone _ (hrect (z.1 i) ⟨le_rfl, hb.le⟩ d ⟨hd.le, le_rfl⟩)
  have h10 := hnone _ (hrect b ⟨hb.le, le_rfl⟩ (z.2 j) ⟨le_rfl, hd.le⟩)
  simp only [Function.update_eq_self] at h01 h10
  have hid := matrix_rectangle (fun a b x y => c a b * chordAngle x y) z.1 z.2 i j b d
  rw [h00, h11, h01, h10] at hid
  have hzero : c i j * (chordAngle b d - chordAngle (z.1 i) d -
      chordAngle b (z.2 j) + chordAngle (z.1 i) (z.2 j)) = 0 := by linear_combination -hid
  exact (mul_ne_zero hc (ne_of_gt hpositive)) hzero

theorem weighted_angles_continuousAt {L P : Type*} [Fintype L] [Fintype P]
    (c : L → P → ℝ) (z : (L → ℝ) × (P → ℝ))
    (hr : ∀ i, z.1 i ≠ 0) (hs : ∀ j, z.2 j ≠ 0) :
    ContinuousAt (fun u => matrixSum (fun i j x y => c i j * chordAngle x y) u.1 u.2) z := by
  unfold matrixSum chordAngle chordCos
  fun_prop (disch := aesop)

theorem finite_angle_avoidance {L P K : Type*} [Fintype L] [Fintype P]
    [DecidableEq L] [DecidableEq P]
    (c : K → L → P → ℝ) (offset : K → ℝ) (U : Set ((L → ℝ) × (P → ℝ)))
    (hU : IsOpen U) (hne : U.Nonempty)
    (hnz : ∀ z ∈ U, (∀ i, z.1 i ≠ 0) ∧ (∀ j, z.2 j ≠ 0))
    (hc : ∀ k, ∃ i j, c k i j ≠ 0)
    (hfeas : ∀ k i j, c k i j ≠ 0 → ∀ z ∈ U, ChordFeasible (z.1 i) (z.2 j))
    (s : Finset K) : ∃ z ∈ U, ∀ k ∈ s,
      matrixSum (fun i j x y => c k i j * chordAngle x y) z.1 z.2 ≠ offset k := by
  let f := fun (k : K) (z : (L → ℝ) × (P → ℝ)) =>
    matrixSum (fun i j x y => c k i j * chordAngle x y) z.1 z.2 - offset k
  have hcont : ∀ k, ContinuousOn (f k) U := by
    intro k z hz
    exact ((weighted_angles_continuousAt (c k) z (hnz z hz).1 (hnz z hz).2).sub
      continuousAt_const).continuousWithinAt
  have hnc : ∀ k, ∀ V : Set ((L → ℝ) × (P → ℝ)),
      V ⊆ U → IsOpen V → V.Nonempty → ∃ z ∈ V, f k z ≠ 0 := by
    intro k V hVU hVo hVne
    obtain ⟨i, j, hij⟩ := hc k
    obtain ⟨z, hz, hh⟩ := angle_sum_not_constant (c k) i j hij V hVo hVne
      (fun z hz => hfeas k i j hij z (hVU hz)) (offset k)
    exact ⟨z, hz, sub_ne_zero.mpr hh⟩
  obtain ⟨z, hz, hh⟩ := finite_avoidance f U hU hne hcont hnc s
  exact ⟨z, hz, fun k hk => sub_ne_zero.mp (hh k hk)⟩

end Proof

end OriginalGenericAngles

/- ## SeedAlgebra -/

section OriginalSeedAlgebra

/- Polynomial identities for the two classes of incidence seeds. -/

namespace Proof

noncomputable section

def lineC (x t : ℝ) : ℝ := x ^ 2 + t / 2
def pointD (x t : ℝ) : ℝ := -x ^ 2 + t / 2

def lineSeed (ε x t : ℝ) : ℂ := ⟨ε * x, -1 / 2 + ε ^ 2 * lineC x t⟩
def pointSeed (ε x t : ℝ) : ℂ := ⟨-ε * x, 1 / 2 + ε ^ 2 * pointD x t⟩

def support (a b : ℂ) : ℝ := a.re * (b.re - a.re) + a.im * (b.im - a.im)

theorem line_support_identity (ε x t y u : ℝ) :
    support (lineSeed ε x t) (lineSeed ε y u) =
      ε ^ 2 * (-(y - x) ^ 2 / 2 - (u - t) / 4) +
      ε ^ 4 * lineC x t * (lineC y u - lineC x t) := by
  simp only [support, lineSeed, lineC]
  ring

theorem point_support_identity (ε x t y u : ℝ) :
    support (pointSeed ε x t) (pointSeed ε y u) =
      ε ^ 2 * (-(y - x) ^ 2 / 2 + (u - t) / 4) +
      ε ^ 4 * pointD x t * (pointD y u - pointD x t) := by
  simp only [support, pointSeed, pointD]
  ring

theorem line_normSq (ε x t : ℝ) :
    Complex.normSq (lineSeed ε x t) =
      1 / 4 - ε ^ 2 * t / 2 + ε ^ 4 * (lineC x t) ^ 2 := by
  simp only [Complex.normSq_apply, lineSeed, lineC]
  ring

theorem point_normSq (ε x t : ℝ) :
    Complex.normSq (pointSeed ε x t) =
      1 / 4 + ε ^ 2 * t / 2 + ε ^ 4 * (pointD x t) ^ 2 := by
  simp only [Complex.normSq_apply, pointSeed, pointD]
  ring

theorem incidence_distance_identity (ε x t y u : ℝ)
    (h : u - t = (y - x) ^ 2) :
    Complex.normSq (pointSeed ε y u - lineSeed ε x t) =
      1 + ε ^ 4 * (pointD y u - lineC x t) ^ 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    pointSeed, lineSeed, pointD, lineC]
  linear_combination ε ^ 2 * h

theorem signed_digit_margin {x t : ℝ}
    (h : |t| < (50 / 27 : ℝ) * x ^ 2) :
    -x ^ 2 / 2 - t / 4 < -x ^ 2 / 27 ∧
      -x ^ 2 / 2 + t / 4 < -x ^ 2 / 27 := by
  rcases abs_lt.mp h with ⟨hl, hu⟩
  constructor <;> linarith

end
end Proof

end OriginalSeedAlgebra

/- ## RadialGeometry -/

section OriginalRadialGeometry

/- Strict radial support, rotations, and their convexity consequences. -/

namespace Proof

open scoped InnerProductSpace

theorem support_eq_inner (a b : ℂ) : support a b = ⟪a, b - a⟫_ℝ := by
  simp only [support, Complex.inner, Complex.mul_re, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem support_eq_normSq (a b : ℂ) :
    2 * support a b = Complex.normSq b - Complex.normSq a - Complex.normSq (b - a) := by
  simp only [support, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem support_negative_of_equal_norm {a b : ℂ} (hne : a ≠ b)
    (hnorm : ‖a‖ = ‖b‖) : support a b < 0 := by
  have heq : Complex.normSq a = Complex.normSq b := by
    simpa only [Complex.normSq_eq_norm_sq] using congrArg (fun r : ℝ => r ^ 2) hnorm
  have hp : 0 < Complex.normSq (b - a) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hne.symm)
  have := support_eq_normSq a b
  linarith

theorem convexIndependent_of_support {ι : Type*} (p : ι → ℂ)
    (h : ∀ i j, i ≠ j → support (p i) (p j) < 0) : ConvexIndependent ℝ p := by
  intro s i hi
  by_contra hnot
  have hs : p '' s ⊆ {z : ℂ | ⟪p i, z⟫_ℝ < ⟪p i, p i⟫_ℝ} := by
    rintro z ⟨j, hj, rfl⟩
    have hij : i ≠ j := fun he => hnot (he.symm ▸ hj)
    have hh := h i j hij
    rw [support_eq_inner, inner_sub_right] at hh
    exact sub_neg.mp hh
  have hc : Convex ℝ {z : ℂ | ⟪p i, z⟫_ℝ < ⟪p i, p i⟫_ℝ} :=
    convex_halfSpace_lt ((innerₗ ℂ) (p i)).isLinear _
  have hz := (convexHull_min hs hc) hi
  exact lt_irrefl _ (show ⟪p i, p i⟫_ℝ < ⟪p i, p i⟫_ℝ from hz)

theorem support_mul (a b w : ℂ) :
    support (a * w) (b * w) = Complex.normSq w * support a b := by
  simp only [support, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem norm_subset_prod {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (hw : ∀ i ∈ s, ‖w i‖ = 1) : ‖∏ i ∈ s, w i‖ = 1 := by
  rw [norm_prod]
  exact Finset.prod_eq_one hw

theorem norm_prod_sub_one_le {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    ‖(∏ i ∈ s, w i) - 1‖ ≤ ∑ i ∈ s, ‖w i - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hwi := hw i (Finset.mem_insert_self i s)
    have hws : ∀ j ∈ s, ‖w j‖ = 1 := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    calc
      ‖w i * (∏ j ∈ s, w j) - 1‖ =
          ‖w i * ((∏ j ∈ s, w j) - 1) + (w i - 1)‖ := by congr 1; ring
      _ ≤ ‖w i * ((∏ j ∈ s, w j) - 1)‖ + ‖w i - 1‖ := norm_add_le _ _
      _ = ‖(∏ j ∈ s, w j) - 1‖ + ‖w i - 1‖ := by rw [norm_mul, hwi, one_mul]
      _ ≤ ‖w i - 1‖ + ∑ j ∈ s, ‖w j - 1‖ := by linarith [ih hws]

theorem support_change_same_norm (a b a' b' : ℂ) (hn : ‖a'‖ = ‖a‖) :
    |support a' b' - support a b| ≤
      ‖a' - a‖ * ‖b'‖ + ‖a‖ * ‖b' - b‖ := by
  have he : support a' b' - support a b =
      ⟪a' - a, b'⟫_ℝ + ⟪a, b' - b⟫_ℝ := by
    simp only [support_eq_inner, inner_sub_left, inner_sub_right,
      real_inner_self_eq_norm_sq, hn]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))

theorem rotated_support_bound {a b u v : ℂ} {H : ℝ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hU : ‖u - 1‖ ≤ H) (hV : ‖v - 1‖ ≤ H) :
    support (a * u) (b * v) ≤ support a b + 2 * H := by
  have hH : 0 ≤ H := (norm_nonneg _).trans hU
  have hau : ‖a * u‖ = ‖a‖ := by rw [norm_mul, hu, mul_one]
  have hbv : ‖b * v‖ = ‖b‖ := by rw [norm_mul, hv, mul_one]
  have hdiffa : ‖a * u - a‖ ≤ H := by
    rw [← mul_sub_one, norm_mul]
    exact (mul_le_mul ha hU (norm_nonneg _) (by norm_num)).trans_eq (one_mul H)
  have hdiffb : ‖b * v - b‖ ≤ H := by
    rw [← mul_sub_one, norm_mul]
    exact (mul_le_mul hb hV (norm_nonneg _) (by norm_num)).trans_eq (one_mul H)
  have hh := support_change_same_norm a b (a * u) (b * v) hau
  rw [hbv] at hh
  have h1 : ‖a * u - a‖ * ‖b‖ ≤ H := by
    exact (mul_le_mul hdiffa hb (norm_nonneg _) hH).trans_eq (mul_one H)
  have h2 : ‖a‖ * ‖b * v - b‖ ≤ H := by
    exact (mul_le_mul ha hdiffb (norm_nonneg _) (by norm_num)).trans_eq (one_mul H)
  have := le_abs_self (support (a * u) (b * v) - support a b)
  linarith

end Proof

end OriginalRadialGeometry

/- ## Amplification -/

section OriginalAmplification

/- Amplification by products of unit complex numbers. -/

namespace Proof

noncomputable section

def subsetProduct {E : Type*} (w : E → ℂ) (S : Finset E) : ℂ := ∏ e ∈ S, w e

def rotatedCopy {I E : Type*} (b : I → ℂ) (w : E → ℂ) (x : I × Finset E) : ℂ :=
  b x.1 * subsetProduct w x.2

theorem subsetProduct_norm {E : Type*} (w : E → ℂ) (hw : ∀ e, ‖w e‖ = 1)
    (S : Finset E) : ‖subsetProduct w S‖ = 1 :=
  norm_subset_prod S w (fun e _ => hw e)

theorem subsetProduct_close {E : Type*} [Fintype E] (w : E → ℂ)
    (hw : ∀ e, ‖w e‖ = 1) (S : Finset E) :
    ‖subsetProduct w S - 1‖ ≤ ∑ e, ‖w e - 1‖ := by
  classical
  refine (norm_prod_sub_one_le S w (fun e _ => hw e)).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun e _ _ => norm_nonneg (w e - 1))

theorem rotatedCopy_injective {I E : Type*} (b : I → ℂ) (w : E → ℂ)
    (hb : ∀ i, b i ≠ 0) (hn : Function.Injective (fun i => ‖b i‖))
    (hw : ∀ e, ‖w e‖ = 1) (hprod : Function.Injective (subsetProduct w)) :
    Function.Injective (rotatedCopy b w) := by
  rintro ⟨i, S⟩ ⟨j, T⟩ he
  have hnorm := congrArg norm he
  simp only [rotatedCopy, norm_mul, subsetProduct_norm w hw, mul_one] at hnorm
  have hij := hn hnorm
  subst j
  have hST := hprod (mul_left_cancel₀ (hb i) he)
  exact Prod.ext rfl hST

theorem rotatedCopy_convexIndependent {I E : Type*} [Fintype E]
    (b : I → ℂ) (w : E → ℂ) (hb : ∀ i, b i ≠ 0)
    (hn : Function.Injective (fun i => ‖b i‖)) (hb1 : ∀ i, ‖b i‖ ≤ 1)
    (hw : ∀ e, ‖w e‖ = 1) (hprod : Function.Injective (subsetProduct w))
    (hsupport : ∀ i j, i ≠ j → support (b i) (b j) < -2 * ∑ e, ‖w e - 1‖) :
    ConvexIndependent ℝ (rotatedCopy b w) := by
  apply convexIndependent_of_support
  rintro ⟨i, S⟩ ⟨j, T⟩ hne
  by_cases hij : i = j
  · subst j
    apply support_negative_of_equal_norm
    · exact fun h => hne (rotatedCopy_injective b w hb hn hw hprod h)
    · simp only [rotatedCopy, norm_mul, subsetProduct_norm w hw]
  · have hbound := rotated_support_bound (hb1 i) (hb1 j)
      (subsetProduct_norm w hw S) (subsetProduct_norm w hw T)
      (subsetProduct_close w hw S) (subsetProduct_close w hw T)
    dsimp [rotatedCopy]
    linarith [hsupport i j hij]

theorem rotatedCopy_unit_edge {I E : Type*} [DecidableEq E]
    (b : I → ℂ) (w : E → ℂ) (hw : ∀ e, ‖w e‖ = 1)
    (i j : I) (e : E) (he : ‖b i - b j * w e‖ = 1)
    (S : Finset E) (hS : e ∉ S) :
    dist (rotatedCopy b w (i, S)) (rotatedCopy b w (j, insert e S)) = 1 := by
  simp only [rotatedCopy, subsetProduct, Finset.prod_insert hS, dist_eq_norm]
  rw [show b i * (∏ f ∈ S, w f) - b j * (w e * ∏ f ∈ S, w f) =
    (b i - b j * w e) * ∏ f ∈ S, w f by ring]
  rw [norm_mul, he, norm_subset_prod S w (fun f _ => hw f), one_mul]

end
end Proof

end OriginalAmplification

/- ## GenericRotations -/

section OriginalGenericRotations

/- Distinct subset products of correction rotations in every feasible open radius set. -/

namespace Proof

open Set Filter
open scoped Topology


noncomputable section

def edgeAngleSum {L P E : Type*} [Fintype E] (l : E → L) (p : E → P)
    (a : E → ℝ) (z : (L → ℝ) × (P → ℝ)) : ℝ :=
  ∑ e, a e * chordAngle (z.1 (l e)) (z.2 (p e))

theorem edge_angle_rectangle {L P E : Type*} [Fintype E]
    [DecidableEq L] [DecidableEq P] [DecidableEq E]
    (l : E → L) (p : E → P) (hij : Function.Injective (fun e => (l e, p e)))
    (a : E → ℝ) (r : L → ℝ) (s : P → ℝ) (e : E) (x y : ℝ) :
    edgeAngleSum l p a (Function.update r (l e) x, Function.update s (p e) y) -
      edgeAngleSum l p a (r, Function.update s (p e) y) -
      edgeAngleSum l p a (Function.update r (l e) x, s) + edgeAngleSum l p a (r, s) =
    a e * (chordAngle x y - chordAngle (r (l e)) y - chordAngle x (s (p e)) +
      chordAngle (r (l e)) (s (p e))) := by
  let g := fun f => a f * (chordAngle (Function.update r (l e) x (l f)) (Function.update s (p e) y (p f)) -
    chordAngle (r (l f)) (Function.update s (p e) y (p f)) -
    chordAngle (Function.update r (l e) x (l f)) (s (p f)) + chordAngle (r (l f)) (s (p f)))
  have he : edgeAngleSum l p a (Function.update r (l e) x, Function.update s (p e) y) -
      edgeAngleSum l p a (r, Function.update s (p e) y) -
      edgeAngleSum l p a (Function.update r (l e) x, s) + edgeAngleSum l p a (r, s) = ∑ f, g f := by
    simp only [g, edgeAngleSum, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [he, Finset.sum_eq_single e]
  · simp [g]
  · intro f _ hfe
    by_cases hl : l f = l e
    · have hp : p f ≠ p e := fun hh => hfe (hij (Prod.ext hl hh))
      simp [g, Function.update_of_ne hp]
    · simp [g, Function.update_of_ne hl]
  · simp

theorem edge_angle_sum_not_constant {L P E : Type*} [Fintype E]
    [DecidableEq L] [DecidableEq P] [DecidableEq E]
    (l : E → L) (p : E → P) (hij : Function.Injective (fun e => (l e, p e)))
    (a : E → ℝ) (e : E) (ha : a e ≠ 0)
    (U : Set ((L → ℝ) × (P → ℝ))) (hU : IsOpen U) (hne : U.Nonempty)
    (hf : ∀ z ∈ U, ChordFeasible (z.1 (l e)) (z.2 (p e))) (k : ℝ) :
    ∃ z ∈ U, edgeAngleSum l p a z ≠ k := by
  by_contra hnone
  push Not at hnone
  obtain ⟨z, hz⟩ := hne
  obtain ⟨b, d, hb, hd, hrect⟩ := coordinate_rectangle hU hz (l e) (p e)
  have hfeas : ∀ x ∈ Icc (z.1 (l e)) b, ∀ y ∈ Icc (z.2 (p e)) d, ChordFeasible x y := by
    intro x hx y hy
    simpa using hf _ (hrect x hx y hy)
  have hpositive := chordAngle_rectangle_strict hb hd hfeas
  have h00 := hnone z hz
  have h11 := hnone _ (hrect b ⟨hb.le, le_rfl⟩ d ⟨hd.le, le_rfl⟩)
  have h01 := hnone _ (hrect (z.1 (l e)) ⟨le_rfl, hb.le⟩ d ⟨hd.le, le_rfl⟩)
  have h10 := hnone _ (hrect b ⟨hb.le, le_rfl⟩ (z.2 (p e)) ⟨le_rfl, hd.le⟩)
  simp only [Function.update_eq_self] at h01 h10
  have hid := edge_angle_rectangle l p hij a z.1 z.2 e b d
  rw [h00, h11, h01, h10] at hid
  have hzero : a e * (chordAngle b d - chordAngle (z.1 (l e)) d -
      chordAngle b (z.2 (p e)) + chordAngle (z.1 (l e)) (z.2 (p e))) = 0 := by linarith
  exact mul_ne_zero ha (ne_of_gt hpositive) hzero

theorem edge_angles_continuousAt {L P E : Type*} [Fintype E]
    (l : E → L) (p : E → P) (a : E → ℝ) (z : (L → ℝ) × (P → ℝ))
    (hr : ∀ i, z.1 i ≠ 0) (hs : ∀ j, z.2 j ≠ 0) : ContinuousAt (edgeAngleSum l p a) z := by
  unfold edgeAngleSum chordAngle chordCos
  fun_prop (disch := aesop)

def subsetDifference {E : Type*} [DecidableEq E] (S T : Finset E) (e : E) : ℝ :=
  (if e ∈ S then 1 else 0) - (if e ∈ T then 1 else 0)

theorem subsetDifference_sum {E : Type*} [Fintype E] [DecidableEq E]
    (S T : Finset E) (f : E → ℝ) :
    ∑ e, subsetDifference S T e * f e = (∑ e ∈ S, f e) - ∑ e ∈ T, f e := by
  simp [subsetDifference, sub_mul, ite_mul, Finset.sum_sub_distrib]

theorem subsetDifference_nonzero {E : Type*} [DecidableEq E]
    {S T : Finset E} (hne : S ≠ T) : ∃ e, subsetDifference S T e ≠ 0 := by
  by_contra hh
  push Not at hh
  apply hne
  ext e
  have he := hh e
  by_cases hS : e ∈ S <;> by_cases hT : e ∈ T <;> simp_all [subsetDifference]

def phaseRotations {L P E : Type*} (l : E → L) (p : E → P) (θ : E → ℝ)
    (z : (L → ℝ) × (P → ℝ)) (e : E) : ℂ :=
  Complex.exp (((θ e - chordAngle (z.1 (l e)) (z.2 (p e)) : ℝ) : ℂ) * Complex.I)

theorem phaseRotations_norm {L P E : Type*} (l : E → L) (p : E → P) (θ : E → ℝ)
    (z : (L → ℝ) × (P → ℝ)) (e : E) : ‖phaseRotations l p θ z e‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem exp_phase_small_injective {x y : ℝ} (hsmall : |x - y| < Real.pi)
    (he : Complex.exp ((x : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I)) : x = y := by
  have hexp : Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) = Complex.exp 0 := by
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, he, div_self (Complex.exp_ne_zero _), Complex.exp_zero]
  have hxy := abs_lt.mp hsmall
  have hh := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := ((x - y : ℝ) : ℂ) * Complex.I) (y := 0)
    (by simpa using hxy.1) (by simpa using hxy.2.le)
    (by simpa using neg_neg_of_pos Real.pi_pos) (by simpa using Real.pi_pos.le) hexp
  have := congrArg Complex.im hh
  exact sub_eq_zero.mp (by simpa using this)

theorem subsetProduct_phase {L P E : Type*} (l : E → L) (p : E → P) (θ : E → ℝ)
    (z : (L → ℝ) × (P → ℝ)) (S : Finset E) :
    subsetProduct (phaseRotations l p θ z) S =
      Complex.exp (((∑ e ∈ S, (θ e - chordAngle (z.1 (l e)) (z.2 (p e))) : ℝ) : ℂ) * Complex.I) := by
  unfold subsetProduct phaseRotations
  rw [← Complex.exp_sum]
  congr 1
  simp [Complex.ofReal_sum, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]

def relationPhase {L P E : Type*} (l : E → L) (p : E → P) (θ : E → ℝ)
    (S T : Finset E) (z : (L → ℝ) × (P → ℝ)) : ℝ :=
  (∑ e ∈ S, (θ e - chordAngle (z.1 (l e)) (z.2 (p e)))) -
    ∑ e ∈ T, (θ e - chordAngle (z.1 (l e)) (z.2 (p e)))

theorem relationPhase_eq {L P E : Type*} [Fintype E] [DecidableEq E]
    (l : E → L) (p : E → P) (θ : E → ℝ) (S T : Finset E) (z : (L → ℝ) × (P → ℝ)) :
    relationPhase l p θ S T z =
      (∑ e, subsetDifference S T e * θ e) - edgeAngleSum l p (subsetDifference S T) z := by
  unfold relationPhase edgeAngleSum
  rw [← Finset.sum_sub_distrib, ← subsetDifference_sum S T]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem relationPhase_exp {L P E : Type*} (l : E → L) (p : E → P) (θ : E → ℝ)
    (S T : Finset E) (z : (L → ℝ) × (P → ℝ))
    (he : subsetProduct (phaseRotations l p θ z) S = subsetProduct (phaseRotations l p θ z) T) :
    Complex.exp (((relationPhase l p θ S T z : ℝ) : ℂ) * Complex.I) = 1 := by
  unfold relationPhase
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub,
    ← subsetProduct_phase l p θ z S, ← subsetProduct_phase l p θ z T, he]
  apply div_self
  rw [subsetProduct_phase]
  exact Complex.exp_ne_zero _

theorem phaseRotations_continuousAt {L P E : Type*} (l : E → L) (p : E → P) (θ : E → ℝ)
    (z : (L → ℝ) × (P → ℝ)) (hr : ∀ i, z.1 i ≠ 0) (hs : ∀ j, z.2 j ≠ 0) (e : E) :
    ContinuousAt (fun u => phaseRotations l p θ u e) z := by
  unfold phaseRotations chordAngle chordCos
  fun_prop (disch := aesop)

theorem subset_products_separate {L P E : Type*} [Fintype E]
    [DecidableEq L] [DecidableEq P] [DecidableEq E]
    (l : E → L) (p : E → P) (hij : Function.Injective (fun e => (l e, p e)))
    (θ : E → ℝ) (U : Set ((L → ℝ) × (P → ℝ))) (hU : IsOpen U) (hne : U.Nonempty)
    (hnz : ∀ z ∈ U, (∀ i, z.1 i ≠ 0) ∧ (∀ j, z.2 j ≠ 0))
    (hf : ∀ e, ∀ z ∈ U, ChordFeasible (z.1 (l e)) (z.2 (p e)))
    (S T : Finset E) (hST : S ≠ T) :
    ∃ z ∈ U, subsetProduct (phaseRotations l p θ z) S ≠ subsetProduct (phaseRotations l p θ z) T := by
  by_contra hnone
  push Not at hnone
  obtain ⟨e, he⟩ := subsetDifference_nonzero hST
  obtain ⟨z₀, hz₀⟩ := hne
  let φ := relationPhase l p θ S T
  have hc : ContinuousOn φ U := by
    intro z hz
    have hh : ContinuousAt (fun u => (∑ e, subsetDifference S T e * θ e) -
        edgeAngleSum l p (subsetDifference S T) u) z :=
      continuousAt_const.sub (edge_angles_continuousAt l p (subsetDifference S T) z (hnz z hz).1 (hnz z hz).2)
    change ContinuousWithinAt φ U z
    rw [show φ = fun u => (∑ e, subsetDifference S T e * θ e) -
      edgeAngleSum l p (subsetDifference S T) u by funext u; exact relationPhase_eq l p θ S T u]
    exact hh.continuousWithinAt
  let V := U ∩ (fun z => |φ z - φ z₀|) ⁻¹' Iio Real.pi
  have hVo : IsOpen V :=
    (hc.sub continuousOn_const).abs.isOpen_inter_preimage hU isOpen_Iio
  have hVne : V.Nonempty := ⟨z₀, hz₀, by simpa using Real.pi_pos⟩
  have hVU : V ⊆ U := inter_subset_left
  have hconstant : ∀ z ∈ V, edgeAngleSum l p (subsetDifference S T) z =
      (∑ e, subsetDifference S T e * θ e) - φ z₀ := by
    intro z hz
    have h1 := relationPhase_exp l p θ S T z (hnone z (hVU hz))
    have h0 := relationPhase_exp l p θ S T z₀ (hnone z₀ hz₀)
    have hphase : φ z = φ z₀ := exp_phase_small_injective hz.2 (h1.trans h0.symm)
    rw [show φ z = (∑ e, subsetDifference S T e * θ e) -
        edgeAngleSum l p (subsetDifference S T) z from relationPhase_eq l p θ S T z] at hphase
    linarith
  obtain ⟨z, hz, hh⟩ := edge_angle_sum_not_constant l p hij (subsetDifference S T) e he V hVo hVne
    (fun z hz => hf e z (hVU hz)) ((∑ e, subsetDifference S T e * θ e) - φ z₀)
  exact hh (hconstant z hz)

theorem exists_injective_subsetProducts {L P E : Type*} [Fintype E]
    [DecidableEq L] [DecidableEq P] [DecidableEq E]
    (l : E → L) (p : E → P) (hij : Function.Injective (fun e => (l e, p e)))
    (θ : E → ℝ) (U : Set ((L → ℝ) × (P → ℝ))) (hU : IsOpen U) (hne : U.Nonempty)
    (hnz : ∀ z ∈ U, (∀ i, z.1 i ≠ 0) ∧ (∀ j, z.2 j ≠ 0))
    (hf : ∀ e, ∀ z ∈ U, ChordFeasible (z.1 (l e)) (z.2 (p e))) :
    ∃ z ∈ U, Function.Injective (subsetProduct (phaseRotations l p θ z)) := by
  classical
  let K := {st : Finset E × Finset E // st.1 ≠ st.2}
  let f := fun (k : K) (z : (L → ℝ) × (P → ℝ)) =>
    subsetProduct (phaseRotations l p θ z) k.val.1 - subsetProduct (phaseRotations l p θ z) k.val.2
  have hc : ∀ k, ContinuousOn (f k) U := by
    intro k z hz
    have hrot := phaseRotations_continuousAt l p θ z (hnz z hz).1 (hnz z hz).2
    apply ContinuousAt.continuousWithinAt
    unfold f subsetProduct
    fun_prop
  have hnc : ∀ k, ∀ V : Set ((L → ℝ) × (P → ℝ)),
      V ⊆ U → IsOpen V → V.Nonempty → ∃ z ∈ V, f k z ≠ 0 := by
    intro k V hVU hVo hVne
    obtain ⟨z, hz, hh⟩ := subset_products_separate l p hij θ V hVo hVne
      (fun z hz => hnz z (hVU hz)) (fun e z hz => hf e z (hVU hz)) k.val.1 k.val.2 k.property
    exact ⟨z, hz, sub_ne_zero.mpr hh⟩
  obtain ⟨z, hz, hh⟩ := finite_avoidance f U hU hne hc hnc Finset.univ
  refine ⟨z, hz, ?_⟩
  intro S T heq
  by_contra hST
  exact hh (⟨(S, T), hST⟩ : K) (Finset.mem_univ _) (sub_eq_zero.mpr heq)

end
end Proof

end OriginalGenericRotations

/- ## CorrectionAlgebra -/

section OriginalCorrectionAlgebra

/- Exact algebraic correction of a fourth-order error in a unit distance. -/

namespace Proof

noncomputable section

def correctionRadicand (ε t M q : ℝ) : ℝ :=
  t ^ 2 - ε ^ 2 * M ^ 2 * q - ε ^ 6 * M ^ 4 / 4

def chordNumerator (ε t M : ℝ) (q : ℂ) : ℂ :=
  ⟨q.re + ε ^ 4 * M ^ 2 / 2, -ε * Real.sqrt (correctionRadicand ε t M q.re)⟩

def correction (ε t M : ℝ) (q : ℂ) : ℂ := chordNumerator ε t M q / q

def correctionCoefficient (ε t M : ℝ) (q : ℂ) : ℂ :=
  (⟨ε * M ^ 2 / 2,
    M ^ 2 * (q.re + ε ^ 4 * M ^ 2 / 4) /
      (Real.sqrt (correctionRadicand ε t M q.re) - t)⟩ : ℂ) / q

theorem chordNumerator_normSq (ε t M : ℝ) (q : ℂ)
    (him : q.im = ε * t) (hF : 0 ≤ correctionRadicand ε t M q.re) :
    Complex.normSq (chordNumerator ε t M q) = Complex.normSq q := by
  have hs := Real.sq_sqrt hF
  simp only [chordNumerator, Complex.normSq_apply]
  rw [him]
  dsimp [correctionRadicand] at hs ⊢
  linear_combination ε ^ 2 * hs

theorem correction_norm (ε t M : ℝ) (q : ℂ) (hq : q ≠ 0)
    (him : q.im = ε * t) (hF : 0 ≤ correctionRadicand ε t M q.re) :
    ‖correction ε t M q‖ = 1 := by
  have hh : Complex.normSq (correction ε t M q) = 1 := by
    rw [correction, Complex.normSq_div, chordNumerator_normSq ε t M q him hF]
    exact div_self (ne_of_gt (Complex.normSq_pos.mpr hq))
  rw [Complex.normSq_eq_norm_sq] at hh
  nlinarith [norm_nonneg (correction ε t M q)]

theorem correction_cubic_identity (ε t M : ℝ) (q : ℂ) (hq : q ≠ 0)
    (him : q.im = ε * t) (hF : 0 ≤ correctionRadicand ε t M q.re)
    (hden : Real.sqrt (correctionRadicand ε t M q.re) - t ≠ 0) :
    correction ε t M q - 1 = (ε : ℂ) ^ 3 * correctionCoefficient ε t M q := by
  have hs := Real.sq_sqrt hF
  have he : chordNumerator ε t M q - q = (ε : ℂ) ^ 3 *
      (⟨ε * M ^ 2 / 2,
        M ^ 2 * (q.re + ε ^ 4 * M ^ 2 / 4) /
          (Real.sqrt (correctionRadicand ε t M q.re) - t)⟩ : ℂ) := by
    apply Complex.ext
    · simp only [chordNumerator, Complex.sub_re, Complex.mul_re, ← Complex.ofReal_pow,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    · simp only [chordNumerator, Complex.sub_im, Complex.mul_im,
        ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      rw [him]
      rw [← mul_div_assoc]
      apply (eq_div_iff hden).mpr
      dsimp [correctionRadicand] at hs ⊢
      linear_combination -ε * hs
  unfold correction correctionCoefficient
  rw [← div_self hq, ← sub_div, he, mul_div_assoc]

theorem correction_unit_distance (a b : ℂ) (ε t M : ℝ)
    (hq : starRingEnd ℂ a * b ≠ 0)
    (him : (starRingEnd ℂ a * b).im = ε * t)
    (hF : 0 ≤ correctionRadicand ε t M (starRingEnd ℂ a * b).re)
    (hdist : Complex.normSq (b - a) = 1 + ε ^ 4 * M ^ 2) :
    ‖a - b * correction ε t M (starRingEnd ℂ a * b)‖ = 1 := by
  let q := starRingEnd ℂ a * b
  let w := correction ε t M q
  have hw : ‖w‖ = 1 := correction_norm ε t M q hq him hF
  have hz : starRingEnd ℂ a * (b * w) = chordNumerator ε t M q := by
    change starRingEnd ℂ a * (b * (chordNumerator ε t M q / q)) = _
    rw [← mul_assoc]
    exact mul_div_cancel₀ _ hq
  have hreal : (a * starRingEnd ℂ (b * w)).re = q.re + ε ^ 4 * M ^ 2 / 2 := by
    have hh := congrArg Complex.re hz
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      chordNumerator] at hh ⊢
    linarith
  have hbase : Complex.normSq a + Complex.normSq b - 2 * q.re = 1 + ε ^ 4 * M ^ 2 := by
    simpa [Complex.normSq_sub, q, mul_comm, add_comm] using hdist
  have hns : Complex.normSq (a - b * w) = 1 := by
    rw [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_eq_norm_sq w, hw, one_pow, mul_one,
      hreal]
    linarith
  rw [Complex.normSq_eq_norm_sq] at hns
  nlinarith [norm_nonneg (a - b * w)]

end
end Proof

end OriginalCorrectionAlgebra

/- ## SeedGerms -/

section OriginalSeedGerms

/- Continuous formulas for the small correction rotations at a seed. -/

namespace Proof

open Filter
open scoped Topology

noncomputable section

def seedTangent (ε x t y u : ℝ) : ℝ :=
  (x - y) / 2 + ε ^ 2 * (x * pointD y u + y * lineC x t)

def seedProduct (ε x t y u : ℝ) : ℂ :=
  starRingEnd ℂ (lineSeed ε x t) * pointSeed ε y u

def seedCoefficient (ε x t y u : ℝ) : ℂ :=
  correctionCoefficient ε (seedTangent ε x t y u) (pointD y u - lineC x t)
    (seedProduct ε x t y u)

def seedCorrection (ε x t y u : ℝ) : ℂ :=
  correction ε (seedTangent ε x t y u) (pointD y u - lineC x t)
    (seedProduct ε x t y u)

theorem seedProduct_im (ε x t y u : ℝ) :
    (seedProduct ε x t y u).im = ε * seedTangent ε x t y u := by
  simp [seedProduct, seedTangent, lineSeed, pointSeed, Complex.mul_im]
  ring

theorem seedProduct_zero (x t y u : ℝ) : seedProduct 0 x t y u = (-1 / 4 : ℂ) := by
  apply Complex.ext <;> norm_num [seedProduct, lineSeed, pointSeed, Complex.mul_re, Complex.mul_im]

theorem continuous_lineSeed (x t : ℝ) : Continuous (fun ε => lineSeed ε x t) := by
  unfold lineSeed
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop

theorem continuous_pointSeed (x t : ℝ) : Continuous (fun ε => pointSeed ε x t) := by
  unfold pointSeed
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop

theorem continuous_seedProduct (x t y u : ℝ) : Continuous (fun ε => seedProduct ε x t y u) := by
  exact ((continuous_lineSeed x t).star).mul (continuous_pointSeed y u)

theorem continuous_seedTangent (x t y u : ℝ) : Continuous (fun ε => seedTangent ε x t y u) := by
  unfold seedTangent
  fun_prop

theorem seed_radicand_zero (x t y u : ℝ) :
    correctionRadicand 0 (seedTangent 0 x t y u) (pointD y u - lineC x t)
      (seedProduct 0 x t y u).re = ((x - y) / 2) ^ 2 := by
  simp [correctionRadicand, seedTangent]

theorem seed_denominator_pos (x t y u : ℝ) (hxy : x < y) :
    0 < Real.sqrt (correctionRadicand 0 (seedTangent 0 x t y u)
      (pointD y u - lineC x t) (seedProduct 0 x t y u).re) - seedTangent 0 x t y u := by
  rw [seed_radicand_zero]
  simp only [seedTangent, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero]
  rw [Real.sqrt_sq_eq_abs, abs_of_neg (by linarith : (x - y) / 2 < 0)]
  linarith

theorem continuousAt_seedCoefficient (x t y u : ℝ) (hxy : x < y) :
    ContinuousAt (fun ε => seedCoefficient ε x t y u) 0 := by
  have hq : seedProduct 0 x t y u ≠ 0 := by rw [seedProduct_zero]; norm_num
  have hden := ne_of_gt (seed_denominator_pos x t y u hxy)
  have hcq := (continuous_seedProduct x t y u).continuousAt (x := 0)
  have hct := (continuous_seedTangent x t y u).continuousAt (x := 0)
  unfold seedCoefficient correctionCoefficient
  apply ContinuousAt.div _ hcq hq
  simp only [Complex.mk_eq_add_mul_I]
  have hreal : ContinuousAt (fun ε =>
      (pointD y u - lineC x t) ^ 2 *
      ((seedProduct ε x t y u).re + ε ^ 4 * (pointD y u - lineC x t) ^ 2 / 4) /
      (Real.sqrt (correctionRadicand ε (seedTangent ε x t y u)
        (pointD y u - lineC x t) (seedProduct ε x t y u).re) - seedTangent ε x t y u)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · unfold correctionRadicand
      fun_prop
    · exact hden
  fun_prop

theorem seedCorrection_properties (x t y u : ℝ) (hxy : x < y)
    (hinc : u - t = (y - x) ^ 2) :
    ∀ᶠ ε in 𝓝 (0 : ℝ),
      ‖seedCorrection ε x t y u‖ = 1 ∧
      ‖lineSeed ε x t - pointSeed ε y u * seedCorrection ε x t y u‖ = 1 ∧
      seedCorrection ε x t y u - 1 = (ε : ℂ) ^ 3 * seedCoefficient ε x t y u := by
  have hq : ∀ᶠ ε in 𝓝 (0 : ℝ), seedProduct ε x t y u ≠ 0 :=
    (continuous_seedProduct x t y u).continuousAt.eventually_ne (by rw [seedProduct_zero]; norm_num)
  have hFcont : Continuous (fun ε => correctionRadicand ε (seedTangent ε x t y u)
      (pointD y u - lineC x t) (seedProduct ε x t y u).re) := by
    unfold correctionRadicand
    have ht := continuous_seedTangent x t y u
    have hq := continuous_seedProduct x t y u
    fun_prop
  have hF : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < correctionRadicand ε (seedTangent ε x t y u)
      (pointD y u - lineC x t) (seedProduct ε x t y u).re := by
    apply continuousAt_const.eventually_lt hFcont.continuousAt
    rw [seed_radicand_zero]
    exact sq_pos_of_ne_zero (by linarith)
  have hdc : Continuous (fun ε => Real.sqrt (correctionRadicand ε (seedTangent ε x t y u)
      (pointD y u - lineC x t) (seedProduct ε x t y u).re) - seedTangent ε x t y u) :=
    hFcont.sqrt.sub (continuous_seedTangent x t y u)
  have hd := hdc.continuousAt.eventually_ne (ne_of_gt (seed_denominator_pos x t y u hxy))
  filter_upwards [hq, hF, hd] with ε hq hF hd
  exact ⟨correction_norm _ _ _ _ hq (seedProduct_im ε x t y u) hF.le,
    correction_unit_distance _ _ _ _ _ hq (seedProduct_im ε x t y u) hF.le
      (incidence_distance_identity ε x t y u hinc),
    correction_cubic_identity _ _ _ _ hq (seedProduct_im ε x t y u) hF.le hd⟩

theorem seedCorrection_im_negative (x t y u : ℝ) (hxy : x < y) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (seedProduct ε x t y u * seedCorrection ε x t y u).im < 0 := by
  have hq : ∀ᶠ ε in 𝓝 (0 : ℝ), seedProduct ε x t y u ≠ 0 :=
    (continuous_seedProduct x t y u).continuousAt.eventually_ne (by rw [seedProduct_zero]; norm_num)
  have hFcont : Continuous (fun ε => correctionRadicand ε (seedTangent ε x t y u)
      (pointD y u - lineC x t) (seedProduct ε x t y u).re) := by
    unfold correctionRadicand
    have ht := continuous_seedTangent x t y u
    have hq := continuous_seedProduct x t y u
    fun_prop
  have hF : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < correctionRadicand ε (seedTangent ε x t y u)
      (pointD y u - lineC x t) (seedProduct ε x t y u).re := by
    apply continuousAt_const.eventually_lt hFcont.continuousAt
    rw [seed_radicand_zero]
    exact sq_pos_of_ne_zero (by linarith)
  filter_upwards [hq.filter_mono nhdsWithin_le_nhds, hF.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with ε hq hF (hε : 0 < ε)
  change (seedProduct ε x t y u * (chordNumerator ε (seedTangent ε x t y u)
    (pointD y u - lineC x t) (seedProduct ε x t y u) / seedProduct ε x t y u)).im < 0
  rw [mul_div_cancel₀ _ hq]
  change -ε * Real.sqrt (correctionRadicand ε (seedTangent ε x t y u)
    (pointD y u - lineC x t) (seedProduct ε x t y u).re) < 0
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hε) (Real.sqrt_pos.mpr hF)

end
end Proof

end OriginalSeedGerms

/- ## SeedLimits -/

section OriginalSeedLimits

/- Choosing one sufficiently small positive parameter for finitely many seed inequalities. -/

namespace Proof

open Filter
open scoped Topology

noncomputable section

theorem eventually_scaled_ne (a b : ℝ → ℂ) (F : ℝ → ℝ)
    (hF : ContinuousAt F 0) (hF0 : F 0 ≠ 0)
    (hid : ∀ ε, Complex.normSq (a ε) - Complex.normSq (b ε) = ε ^ 2 * F ε) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖a ε‖ ≠ ‖b ε‖ := by
  have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε ≠ 0 :=
    (hF.eventually_ne hF0).filter_mono nhdsWithin_le_nhds
  filter_upwards [he, self_mem_nhdsWithin] with ε hFε (hε : 0 < ε)
  intro hn
  have hs : Complex.normSq (a ε) = Complex.normSq (b ε) := by
    simp only [Complex.normSq_eq_norm_sq, hn]
  have hz := hid ε
  rw [hs, sub_self] at hz
  exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt hε)) hFε hz.symm

theorem eventually_scaled_support (a b : ℝ → ℂ) (A F : ℝ → ℝ)
    (hF : ContinuousAt F 0) (hF0 : F 0 < 0)
    (hid : ∀ ε, support (a ε) (b ε) + ε ^ 3 * A ε = ε ^ 2 * F ε) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), support (a ε) (b ε) < -ε ^ 3 * A ε := by
  have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε < 0 :=
    (hF.eventually_lt continuousAt_const hF0).filter_mono nhdsWithin_le_nhds
  filter_upwards [he, self_mem_nhdsWithin] with ε hFε (hε : 0 < ε)
  have hh : ε ^ 2 * F ε < 0 := mul_neg_of_pos_of_neg (pow_pos hε 2) hFε
  linarith [hid ε]

theorem eventually_line_support (x t y u : ℝ) (A : ℝ → ℝ)
    (hA : ContinuousAt A 0) (hm : -(y - x) ^ 2 / 2 - (u - t) / 4 < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), support (lineSeed ε x t) (lineSeed ε y u) < -ε ^ 3 * A ε := by
  let F := fun ε => -(y - x) ^ 2 / 2 - (u - t) / 4 +
    ε ^ 2 * lineC x t * (lineC y u - lineC x t) + ε * A ε
  apply eventually_scaled_support _ _ A F
  · unfold F; fun_prop
  · simpa [F] using hm
  · intro ε
    rw [line_support_identity]
    dsimp [F]
    ring

theorem eventually_point_support (x t y u : ℝ) (A : ℝ → ℝ)
    (hA : ContinuousAt A 0) (hm : -(y - x) ^ 2 / 2 + (u - t) / 4 < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), support (pointSeed ε x t) (pointSeed ε y u) < -ε ^ 3 * A ε := by
  let F := fun ε => -(y - x) ^ 2 / 2 + (u - t) / 4 +
    ε ^ 2 * pointD x t * (pointD y u - pointD x t) + ε * A ε
  apply eventually_scaled_support _ _ A F
  · unfold F; fun_prop
  · simpa [F] using hm
  · intro ε
    rw [point_support_identity]
    dsimp [F]
    ring

theorem eventually_cross_support (x t y u : ℝ) (A : ℝ → ℝ) (hA : ContinuousAt A 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      support (lineSeed ε x t) (pointSeed ε y u) < -ε ^ 3 * A ε ∧
      support (pointSeed ε y u) (lineSeed ε x t) < -ε ^ 3 * A ε := by
  have hc₁ : ContinuousAt (fun ε => support (lineSeed ε x t) (pointSeed ε y u) + ε ^ 3 * A ε) 0 := by
    unfold support lineSeed pointSeed; fun_prop
  have hc₂ : ContinuousAt (fun ε => support (pointSeed ε y u) (lineSeed ε x t) + ε ^ 3 * A ε) 0 := by
    unfold support lineSeed pointSeed; fun_prop
  have h₁ : ∀ᶠ ε in 𝓝 (0 : ℝ), support (lineSeed ε x t) (pointSeed ε y u) + ε ^ 3 * A ε < 0 :=
    hc₁.eventually_lt continuousAt_const (by norm_num [support, lineSeed, pointSeed])
  have h₂ : ∀ᶠ ε in 𝓝 (0 : ℝ), support (pointSeed ε y u) (lineSeed ε x t) + ε ^ 3 * A ε < 0 :=
    hc₂.eventually_lt continuousAt_const (by norm_num [support, lineSeed, pointSeed])
  filter_upwards [h₁.filter_mono nhdsWithin_le_nhds, h₂.filter_mono nhdsWithin_le_nhds] with ε h₁ h₂
  constructor <;> linarith

theorem eventually_line_norm_ne (x t y u : ℝ) (htu : t ≠ u) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖lineSeed ε x t‖ ≠ ‖lineSeed ε y u‖ := by
  apply eventually_scaled_ne _ _ (fun ε => -(t - u) / 2 + ε ^ 2 * ((lineC x t) ^ 2 - (lineC y u) ^ 2))
  · fun_prop
  · simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero]
    exact div_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr htu)) (by norm_num)
  · intro ε
    rw [line_normSq, line_normSq]
    ring

theorem eventually_point_norm_ne (x t y u : ℝ) (htu : t ≠ u) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖pointSeed ε x t‖ ≠ ‖pointSeed ε y u‖ := by
  apply eventually_scaled_ne _ _ (fun ε => (t - u) / 2 + ε ^ 2 * ((pointD x t) ^ 2 - (pointD y u) ^ 2))
  · fun_prop
  · simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero]
    exact div_ne_zero (sub_ne_zero.mpr htu) (by norm_num)
  · intro ε
    rw [point_normSq, point_normSq]
    ring

theorem eventually_cross_norm_ne (x t y u : ℝ) (ht : 0 < t) (hu : 0 < u) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖lineSeed ε x t‖ ≠ ‖pointSeed ε y u‖ := by
  apply eventually_scaled_ne _ _ (fun ε => -(t + u) / 2 + ε ^ 2 * ((lineC x t) ^ 2 - (pointD y u) ^ 2))
  · fun_prop
  · simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero]
    linarith
  · intro ε
    rw [line_normSq, point_normSq]
    ring

end
end Proof

end OriginalSeedLimits

/- ## Incidence -/

section OriginalIncidence

/- The coordinate incidence graph used in the construction. -/

namespace Proof

abbrev PointLabel (d : ℕ) := Fin d → Fin d
abbrev LineLabel (d : ℕ) := (i : Fin d) × ({j : Fin d // j ≠ i} → Fin d)
abbrev EdgeLabel (d : ℕ) := PointLabel d × Fin d

def edgePoint {d : ℕ} (e : EdgeLabel d) : PointLabel d := e.1
def edgeLine {d : ℕ} (e : EdgeLabel d) : LineLabel d := ⟨e.2, fun j => e.1 j⟩

theorem edge_endpoints_injective (d : ℕ) :
    Function.Injective (fun e : EdgeLabel d => (edgeLine e, edgePoint e)) := by
  intro e f h
  have hpoint : e.1 = f.1 := congrArg Prod.snd h
  have hline : e.2 = f.2 := congrArg (fun p => p.1.1) h
  exact Prod.ext hpoint hline

theorem pointLabel_card (d : ℕ) : Fintype.card (PointLabel d) = d ^ d := by
  simp [PointLabel]

theorem puncturedFin_card {d : ℕ} (i : Fin d) :
    Fintype.card {j : Fin d // j ≠ i} = d - 1 := by
  simp

theorem lineLabel_card (d : ℕ) : Fintype.card (LineLabel d) = d * d ^ (d - 1) := by
  simp [LineLabel, Fintype.card_sigma]

theorem edgeLabel_card (d : ℕ) : Fintype.card (EdgeLabel d) = d ^ (d + 1) := by
  simp [EdgeLabel, pow_succ]

theorem vertexLabel_card {d : ℕ} (hd : 1 ≤ d) :
    Fintype.card (LineLabel d ⊕ PointLabel d) = 2 * d ^ d := by
  rw [Fintype.card_sum, lineLabel_card, pointLabel_card]
  have hpow : d * d ^ (d - 1) = d ^ d := by
    rw [← pow_succ', Nat.sub_add_cancel hd]
  omega

end Proof

end OriginalIncidence

/- ## Digits -/

section OriginalDigits

/- Separation of distinct finite sums of powers of five. -/

namespace Proof

noncomputable section

def digitSum (q : ℝ) (s : Finset ℕ) : ℝ := ∑ i ∈ s, q ^ i

theorem geometric_five (n : ℕ) :
    4 * (∑ i ∈ Finset.range n, (5 : ℝ) ^ i) = (5 : ℝ) ^ n - 1 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; linarith

theorem geometric_twentyfive (n : ℕ) :
    24 * (∑ i ∈ Finset.range n, (25 : ℝ) ^ i) = (25 : ℝ) ^ n - 1 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; linarith

theorem dominant_digit_bounds {q : ℝ} (hq : 0 ≤ q) {A B : Finset ℕ} {h : ℕ}
    (hdis : Disjoint A B) (hmem : h ∈ A) (hmax : ∀ j ∈ A ∪ B, j ≤ h) :
    q ^ h - (∑ i ∈ Finset.range h, q ^ i) ≤ digitSum q A - digitSum q B ∧
    digitSum q A - digitSum q B ≤ q ^ h + (∑ i ∈ Finset.range h, q ^ i) := by
  have hsubB : B ⊆ Finset.range h := by
    intro j hj
    have hle := hmax j (Finset.mem_union_right A hj)
    have hne : j ≠ h := by
      intro he
      exact (Finset.disjoint_left.mp hdis hmem) (he ▸ hj)
    exact Finset.mem_range.mpr (lt_of_le_of_ne hle hne)
  have hsubA : A ⊆ Finset.range (h + 1) := by
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hmax j (Finset.mem_union_left B hj)))
  have hAlo : q ^ h ≤ digitSum q A :=
    Finset.single_le_sum (fun j _ => pow_nonneg hq j) hmem
  have hBlo : 0 ≤ digitSum q B := Finset.sum_nonneg (fun j _ => pow_nonneg hq j)
  have hAhi : digitSum q A ≤ ∑ i ∈ Finset.range (h + 1), q ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubA (fun j _ _ => pow_nonneg hq j)
  have hBhi : digitSum q B ≤ ∑ i ∈ Finset.range h, q ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubB (fun j _ _ => pow_nonneg hq j)
  rw [Finset.sum_range_succ] at hAhi
  constructor <;> linarith

theorem dominant_five_separation {A B : Finset ℕ} {h : ℕ}
    (hdis : Disjoint A B) (hmem : h ∈ A) (hmax : ∀ j ∈ A ∪ B, j ≤ h) :
    0 < digitSum 5 A - digitSum 5 B ∧
    0 < digitSum 25 A - digitSum 25 B ∧
    digitSum 25 A - digitSum 25 B <
      (50 / 27 : ℝ) * (digitSum 5 A - digitSum 5 B) ^ 2 := by
  obtain ⟨h5lo, h5hi⟩ := dominant_digit_bounds (q := 5) (by norm_num) hdis hmem hmax
  obtain ⟨h25lo, h25hi⟩ := dominant_digit_bounds (q := 25) (by norm_num) hdis hmem hmax
  have g5 := geometric_five h
  have g25 := geometric_twentyfive h
  have hp5 : 0 < (5 : ℝ) ^ h := by positivity
  have hp25 : 0 < (25 : ℝ) ^ h := by positivity
  have hx : 3 / 4 * (5 : ℝ) ^ h < digitSum 5 A - digitSum 5 B := by linarith
  have ht : digitSum 25 A - digitSum 25 B < 25 / 24 * (25 : ℝ) ^ h := by linarith
  have hp : (25 : ℝ) ^ h = ((5 : ℝ) ^ h) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hsq := mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ 3 / 4 * 5 ^ h) hx
  refine ⟨by linarith, by linarith, ?_⟩
  rw [hp] at ht
  nlinarith

theorem digit_separation {s t : Finset ℕ} (hne : s ≠ t) :
    digitSum 5 s ≠ digitSum 5 t ∧ digitSum 25 s ≠ digitSum 25 t ∧
    |digitSum 25 s - digitSum 25 t| <
      (50 / 27 : ℝ) * (digitSum 5 s - digitSum 5 t) ^ 2 := by
  let A := s \ t
  let B := t \ s
  have hdis : Disjoint A B := by
    simp only [A, B, Finset.disjoint_left, Finset.mem_sdiff]
    aesop
  have hneAB : (A ∪ B).Nonempty := by
    by_contra hc
    have he : A ∪ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
    apply hne
    ext i
    have hi : i ∉ A ∪ B := by rw [he]; simp
    simp only [A, B, Finset.mem_union, Finset.mem_sdiff] at hi
    tauto
  let h := (A ∪ B).max' hneAB
  have hh : h ∈ A ∪ B := Finset.max'_mem _ _
  have hmax : ∀ j ∈ A ∪ B, j ≤ h := fun j hj => Finset.le_max' _ j hj
  have he5 : digitSum 5 s - digitSum 5 t = digitSum 5 A - digitSum 5 B := by
    exact (Finset.sum_sdiff_sub_sum_sdiff (s₁ := t) (s₂ := s) (f := fun i => (5 : ℝ) ^ i)).symm
  have he25 : digitSum 25 s - digitSum 25 t = digitSum 25 A - digitSum 25 B := by
    exact (Finset.sum_sdiff_sub_sum_sdiff (s₁ := t) (s₂ := s) (f := fun i => (25 : ℝ) ^ i)).symm
  rcases Finset.mem_union.mp hh with hh | hh
  · obtain ⟨hx, ht, hbound⟩ := dominant_five_separation hdis hh hmax
    refine ⟨?_, ?_, ?_⟩
    · intro he; rw [he, sub_self] at he5; linarith
    · intro he; rw [he, sub_self] at he25; linarith
    · rw [he5, he25, abs_of_pos ht]; exact hbound
  · have hmax' : ∀ j ∈ B ∪ A, j ≤ h := by simpa [Finset.union_comm] using hmax
    obtain ⟨hx, ht, hbound⟩ := dominant_five_separation hdis.symm hh hmax'
    refine ⟨?_, ?_, ?_⟩
    · intro he; rw [he, sub_self] at he5; linarith
    · intro he; rw [he, sub_self] at he25; linarith
    · rw [he5, he25, abs_of_neg (by linarith : digitSum 25 A - digitSum 25 B < 0)]
      nlinarith

end
end Proof

end OriginalDigits

/- ## LabelDigits -/

section OriginalLabelDigits

/- An injective assignment of lacunary digits to coordinate incidence labels. -/

namespace Proof

noncomputable section

def pointCells {d : ℕ} (p : PointLabel d) : Finset (Fin d × Fin d) :=
  Finset.univ.image (fun i => (i, p i))

def lineCells {d : ℕ} (l : LineLabel d) : Finset (Fin d × Fin d) :=
  Finset.univ.image (fun i : {j : Fin d // j ≠ l.1} => (i.val, l.2 i))

theorem mem_pointCells {d : ℕ} (p : PointLabel d) (i j : Fin d) :
    (i, j) ∈ pointCells p ↔ p i = j := by
  simp [pointCells]

theorem mem_lineCells {d : ℕ} (l : LineLabel d) (i j : Fin d) :
    (i, j) ∈ lineCells l ↔ ∃ h : i ≠ l.1, l.2 ⟨i, h⟩ = j := by
  simp [lineCells]

theorem pointCells_injective (d : ℕ) : Function.Injective (@pointCells d) := by
  intro p q he
  funext i
  have hi : (i, p i) ∈ pointCells q := by rw [← he, mem_pointCells]
  exact (mem_pointCells q i (p i)).mp hi |>.symm

theorem lineCells_injective (d : ℕ) : Function.Injective (@lineCells d) := by
  rintro ⟨i, f⟩ ⟨j, g⟩ he
  have hij : i = j := by
    by_contra hne
    have hj : (i, g ⟨i, hne⟩) ∈ lineCells ⟨j, g⟩ := by
      rw [mem_lineCells]
      exact ⟨hne, rfl⟩
    rw [← he, mem_lineCells] at hj
    obtain ⟨hbad, _⟩ := hj
    exact hbad rfl
  subst j
  have hfg : f = g := by
    funext k
    have hk : (k.val, f k) ∈ lineCells ⟨i, g⟩ := by
      rw [← he, mem_lineCells]
      exact ⟨k.property, rfl⟩
    obtain ⟨_, hh⟩ := (mem_lineCells _ _ _).mp hk
    exact hh.symm
  subst g
  rfl

theorem incidence_cells {d : ℕ} (e : EdgeLabel d) :
    pointCells (edgePoint e) = insert (e.2, e.1 e.2) (lineCells (edgeLine e)) := by
  ext ⟨i, j⟩
  simp only [Finset.mem_insert, mem_pointCells, mem_lineCells, edgePoint, edgeLine,
    Prod.mk.injEq]
  by_cases hi : i = e.2
  · subst i
    simp [eq_comm]
  · simp [hi]

theorem completing_cell_absent {d : ℕ} (e : EdgeLabel d) :
    (e.2, e.1 e.2) ∉ lineCells (edgeLine e) := by
  simp [mem_lineCells, edgeLine]

def digitIndex (d : ℕ) : (Fin d × Fin d) ↪ ℕ :=
  (Fintype.equivFin (Fin d × Fin d)).toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩

def pointDigits {d : ℕ} (p : PointLabel d) : Finset ℕ := (pointCells p).map (digitIndex d)
def lineDigits {d : ℕ} (l : LineLabel d) : Finset ℕ := (lineCells l).map (digitIndex d)

theorem pointDigits_injective (d : ℕ) : Function.Injective (@pointDigits d) := by
  intro p q he
  exact pointCells_injective d (Finset.map_injective (digitIndex d) he)

theorem lineDigits_injective (d : ℕ) : Function.Injective (@lineDigits d) := by
  intro p q he
  exact lineCells_injective d (Finset.map_injective (digitIndex d) he)

def pointX {d : ℕ} (p : PointLabel d) : ℝ := digitSum 5 (pointDigits p)
def lineX {d : ℕ} (l : LineLabel d) : ℝ := digitSum 5 (lineDigits l)
def pointT {d : ℕ} (p : PointLabel d) : ℝ := 1 + digitSum 25 (pointDigits p)
def lineT {d : ℕ} (l : LineLabel d) : ℝ := 1 + digitSum 25 (lineDigits l)

theorem incidence_digit_identity {d : ℕ} (e : EdgeLabel d) :
    let z : ℝ := 5 ^ (digitIndex d (e.2, e.1 e.2))
    0 < z ∧ pointX (edgePoint e) - lineX (edgeLine e) = z ∧
      pointT (edgePoint e) - lineT (edgeLine e) = z ^ 2 := by
  have hnew : digitIndex d (e.2, e.1 e.2) ∉ lineDigits (edgeLine e) := by
    simp [lineDigits, completing_cell_absent]
  have hcells : pointDigits (edgePoint e) =
      insert (digitIndex d (e.2, e.1 e.2)) (lineDigits (edgeLine e)) := by
    simp only [pointDigits, lineDigits, incidence_cells, Finset.map_insert]
  dsimp only
  refine ⟨by positivity, ?_, ?_⟩
  · simp [pointX, lineX, digitSum, hcells, Finset.sum_insert hnew]
  · simp only [pointT, lineT, hcells, digitSum, Finset.sum_insert hnew]
    have hp : (25 : ℝ) ^ (digitIndex d (e.2, e.1 e.2)) =
        ((5 : ℝ) ^ (digitIndex d (e.2, e.1 e.2))) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    linarith

end
end Proof

end OriginalLabelDigits

/- ## SeedPattern -/

section OriginalSeedPattern

/- Abstract hypotheses on a finite incidence pattern and its lacunary realization. -/

namespace Proof

open Filter
open scoped Topology

noncomputable section

structure SeedPattern (L P E : Type*) where
  line : E → L
  point : E → P
  endpoints_injective : Function.Injective (fun e => (line e, point e))
  LX : L → ℝ
  LT : L → ℝ
  PX : P → ℝ
  PT : P → ℝ
  LT_pos : ∀ l, 0 < LT l
  PT_pos : ∀ p, 0 < PT p
  LT_injective : Function.Injective LT
  PT_injective : Function.Injective PT
  line_margin : ∀ l k, l ≠ k → -(LX k - LX l) ^ 2 / 2 - (LT k - LT l) / 4 < 0
  point_margin : ∀ p q, p ≠ q → -(PX q - PX p) ^ 2 / 2 + (PT q - PT p) / 4 < 0
  edge_positive : ∀ e, LX (line e) < PX (point e)
  edge_identity : ∀ e, PT (point e) - LT (line e) = (PX (point e) - LX (line e)) ^ 2

def coordinatePattern (d : ℕ) : SeedPattern (LineLabel d) (PointLabel d) (EdgeLabel d) where
  line := edgeLine
  point := edgePoint
  endpoints_injective := edge_endpoints_injective d
  LX := lineX
  LT := lineT
  PX := pointX
  PT := pointT
  LT_pos l := by
    have hh : 0 ≤ digitSum 25 (lineDigits l) := Finset.sum_nonneg (fun _ _ => by positivity)
    dsimp [lineT]; linarith
  PT_pos p := by
    have hh : 0 ≤ digitSum 25 (pointDigits p) := Finset.sum_nonneg (fun _ _ => by positivity)
    dsimp [pointT]; linarith
  LT_injective := by
    intro l k he
    by_contra hne
    have hh := (digit_separation ((lineDigits_injective d).ne hne)).2.1
    apply hh
    dsimp [lineT] at he
    linarith
  PT_injective := by
    intro p q he
    by_contra hne
    have hh := (digit_separation ((pointDigits_injective d).ne hne)).2.1
    apply hh
    dsimp [pointT] at he
    linarith
  line_margin := by
    intro l k hne
    obtain ⟨hX, _, hsep⟩ := digit_separation ((lineDigits_injective d).ne hne.symm)
    have hm := (signed_digit_margin hsep).1
    have hsq : 0 < (digitSum 5 (lineDigits k) - digitSum 5 (lineDigits l)) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hX)
    dsimp [lineX, lineT]
    have he : 1 + digitSum 25 (lineDigits k) - (1 + digitSum 25 (lineDigits l)) =
        digitSum 25 (lineDigits k) - digitSum 25 (lineDigits l) := by ring
    rw [he]
    linarith
  point_margin := by
    intro p q hne
    obtain ⟨hX, _, hsep⟩ := digit_separation ((pointDigits_injective d).ne hne.symm)
    have hm := (signed_digit_margin hsep).2
    have hsq : 0 < (digitSum 5 (pointDigits q) - digitSum 5 (pointDigits p)) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hX)
    dsimp [pointX, pointT]
    have he : 1 + digitSum 25 (pointDigits q) - (1 + digitSum 25 (pointDigits p)) =
        digitSum 25 (pointDigits q) - digitSum 25 (pointDigits p) := by ring
    rw [he]
    linarith
  edge_positive e := by
    obtain ⟨hz, hx, ht⟩ := incidence_digit_identity e
    linarith
  edge_identity e := by
    obtain ⟨hz, hx, ht⟩ := incidence_digit_identity e
    rw [hx, ht]

def SeedPattern.base {L P E : Type*} (S : SeedPattern L P E) (ε : ℝ) : L ⊕ P → ℂ :=
  Sum.elim (fun l => lineSeed ε (S.LX l) (S.LT l)) (fun p => pointSeed ε (S.PX p) (S.PT p))

def SeedPattern.rot {L P E : Type*} (S : SeedPattern L P E) (ε : ℝ) (e : E) : ℂ :=
  seedCorrection ε (S.LX (S.line e)) (S.LT (S.line e)) (S.PX (S.point e)) (S.PT (S.point e))

def SeedPattern.coeff {L P E : Type*} (S : SeedPattern L P E) (ε : ℝ) (e : E) : ℂ :=
  seedCoefficient ε (S.LX (S.line e)) (S.LT (S.line e)) (S.PX (S.point e)) (S.PT (S.point e))

theorem SeedPattern.coeff_continuous {L P E : Type*} (S : SeedPattern L P E) (e : E) :
    ContinuousAt (fun ε => S.coeff ε e) 0 :=
  continuousAt_seedCoefficient _ _ _ _ (S.edge_positive e)

end
end Proof

end OriginalSeedPattern

/- ## PreparedSeed -/

section OriginalPreparedSeed

/- Existence of a finite seed with exact unit corrections and a strict support margin. -/

namespace Proof

open Filter
open scoped Topology

noncomputable section

structure PreparedSeed {L P E : Type*} [Fintype E] (l : E → L) (p : E → P) where
  base : L ⊕ P → ℂ
  rotation : E → ℂ
  base_ne_zero : ∀ i, base i ≠ 0
  base_norm_lt : ∀ i, ‖base i‖ < 1
  radii_injective : Function.Injective (fun i => ‖base i‖)
  rotation_norm : ∀ e, ‖rotation e‖ = 1
  unit_edge : ∀ e, ‖base (Sum.inl (l e)) - base (Sum.inr (p e)) * rotation e‖ = 1
  support_margin : ∀ i j, i ≠ j →
    support (base i) (base j) < -2 * ∑ e, ‖rotation e - 1‖
  chord_im_negative : ∀ e,
    (starRingEnd ℂ (base (Sum.inl (l e))) * base (Sum.inr (p e)) * rotation e).im < 0

theorem SeedPattern.exists_prepared {L P E : Type*} [Fintype L] [Fintype P] [Fintype E]
    (S : SeedPattern L P E) : Nonempty (PreparedSeed S.line S.point) := by
  let A := fun ε : ℝ => 2 * ∑ e, ‖S.coeff ε e‖
  have hcoeff : ∀ e, ContinuousAt (fun ε => S.coeff ε e) 0 := S.coeff_continuous
  have hA : ContinuousAt A 0 := by unfold A; fun_prop
  have hbase : ∀ i, Continuous (fun ε => S.base ε i) := by
    intro i
    cases i with
    | inl l => exact continuous_lineSeed _ _
    | inr p => exact continuous_pointSeed _ _
  have hbase0 : ∀ i, ‖S.base 0 i‖ = 1 / 2 := by
    intro i
    cases i <;> norm_num [SeedPattern.base, lineSeed, pointSeed, Complex.norm_def, Complex.normSq_apply]
  have hbounds : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.base ε i ≠ 0 ∧ ‖S.base ε i‖ < 1 := by
    intro i
    have hlo : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < ‖S.base ε i‖ :=
      continuousAt_const.eventually_lt (hbase i).norm.continuousAt (by rw [hbase0]; norm_num)
    have hhi : ∀ᶠ ε in 𝓝 (0 : ℝ), ‖S.base ε i‖ < 1 :=
      (hbase i).norm.continuousAt.eventually_lt continuousAt_const (by rw [hbase0]; norm_num)
    filter_upwards [hlo.filter_mono nhdsWithin_le_nhds, hhi.filter_mono nhdsWithin_le_nhds] with ε hlo hhi
    exact ⟨norm_pos_iff.mp hlo, hhi⟩
  have hnorms : ∀ i j, ∀ᶠ ε in 𝓝[>] (0 : ℝ), i ≠ j → ‖S.base ε i‖ ≠ ‖S.base ε j‖ := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    cases i with
    | inl l =>
      cases j with
      | inl k =>
        have hk : l ≠ k := fun h => hij (congrArg Sum.inl h)
        exact (eventually_line_norm_ne _ _ _ _ (S.LT_injective.ne hk)).mono (fun _ h _ => h)
      | inr p =>
        exact (eventually_cross_norm_ne _ _ _ _ (S.LT_pos l) (S.PT_pos p)).mono (fun _ h _ => h)
    | inr p =>
      cases j with
      | inl l =>
        exact (eventually_cross_norm_ne _ _ _ _ (S.LT_pos l) (S.PT_pos p)).mono (fun _ h _ => h.symm)
      | inr q =>
        have hq : p ≠ q := fun h => hij (congrArg Sum.inr h)
        exact (eventually_point_norm_ne _ _ _ _ (S.PT_injective.ne hq)).mono (fun _ h _ => h)
  have hsupports : ∀ i j, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      i ≠ j → support (S.base ε i) (S.base ε j) < -ε ^ 3 * A ε := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    cases i with
    | inl l =>
      cases j with
      | inl k =>
        have hk : l ≠ k := fun h => hij (congrArg Sum.inl h)
        exact (eventually_line_support _ _ _ _ A hA (S.line_margin l k hk)).mono (fun _ h _ => h)
      | inr p =>
        exact (eventually_cross_support _ _ _ _ A hA).mono (fun _ h _ => h.1)
    | inr p =>
      cases j with
      | inl l =>
        exact (eventually_cross_support _ _ _ _ A hA).mono (fun _ h _ => h.2)
      | inr q =>
        have hq : p ≠ q := fun h => hij (congrArg Sum.inr h)
        exact (eventually_point_support _ _ _ _ A hA (S.point_margin p q hq)).mono (fun _ h _ => h)
  have hedges : ∀ e, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖S.rot ε e‖ = 1 ∧
      ‖S.base ε (Sum.inl (S.line e)) - S.base ε (Sum.inr (S.point e)) * S.rot ε e‖ = 1 ∧
      S.rot ε e - 1 = (ε : ℂ) ^ 3 * S.coeff ε e := fun e =>
    (seedCorrection_properties _ _ _ _ (S.edge_positive e) (S.edge_identity e)).filter_mono
      nhdsWithin_le_nhds
  have him : ∀ e, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (starRingEnd ℂ (S.base ε (Sum.inl (S.line e))) *
        S.base ε (Sum.inr (S.point e)) * S.rot ε e).im < 0 := fun e =>
    seedCorrection_im_negative _ _ _ _ (S.edge_positive e)
  have hbAll : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, S.base ε i ≠ 0 ∧ ‖S.base ε i‖ < 1 := by
    simpa only [eventually_all] using hbounds
  have hnAll : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j, i ≠ j → ‖S.base ε i‖ ≠ ‖S.base ε j‖ := by
    simpa only [eventually_all] using hnorms
  have hsAll : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j, i ≠ j →
      support (S.base ε i) (S.base ε j) < -ε ^ 3 * A ε := by
    simpa only [eventually_all] using hsupports
  have heAll : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ e,
      ‖S.rot ε e‖ = 1 ∧
      ‖S.base ε (Sum.inl (S.line e)) - S.base ε (Sum.inr (S.point e)) * S.rot ε e‖ = 1 ∧
      S.rot ε e - 1 = (ε : ℂ) ^ 3 * S.coeff ε e := by
    simpa only [eventually_all] using hedges
  have hiAll : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ e,
      (starRingEnd ℂ (S.base ε (Sum.inl (S.line e))) *
        S.base ε (Sum.inr (S.point e)) * S.rot ε e).im < 0 := by
    simpa only [eventually_all] using him
  have hall := hbAll.and (hnAll.and (hsAll.and (heAll.and (hiAll.and self_mem_nhdsWithin))))
  obtain ⟨ε, hb, hn, hs, he, hi, hε⟩ := hall.exists
  have hε : 0 < ε := hε
  have hsum : 2 * ∑ e, ‖S.rot ε e - 1‖ = ε ^ 3 * A ε := by
    simp_rw [fun e => (he e).2.2, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε]
    rw [← Finset.mul_sum]
    dsimp [A]
    ring
  refine ⟨{
    base := S.base ε
    rotation := S.rot ε
    base_ne_zero := fun i => (hb i).1
    base_norm_lt := fun i => (hb i).2
    radii_injective := fun i j hh => by_contra fun hij => hn i j hij hh
    rotation_norm := fun e => (he e).1
    unit_edge := fun e => (he e).2.1
    support_margin := ?_
    chord_im_negative := hi }⟩
  intro i j hij
  have hh := hs i j hij
  linarith [hsum]

end
end Proof

end OriginalPreparedSeed

/- ## PhaseGeometry -/

section OriginalPhaseGeometry

/- Unit chords and radial changes with the directions held fixed. -/

namespace Proof

noncomputable section

def unitChord (r s : ℝ) : ℂ := Complex.exp (((-chordAngle r s : ℝ) : ℂ) * Complex.I)

theorem unitChord_norm (r s : ℝ) : ‖unitChord r s‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem unitChord_re {r s : ℝ} (hf : ChordFeasible r s) : (unitChord r s).re = chordCos r s := by
  simp [unitChord, Complex.exp_re, chordAngle, Real.cos_arccos hf.2.2.1.le hf.2.2.2.le]

theorem unitChord_im (r s : ℝ) : (unitChord r s).im = -Real.sqrt (1 - chordCos r s ^ 2) := by
  simp [unitChord, Complex.exp_im, chordAngle, Real.sin_arccos]

theorem unitChord_im_neg {r s : ℝ} (hf : ChordFeasible r s) : (unitChord r s).im < 0 := by
  rw [unitChord_im]
  exact neg_neg_of_pos (Real.sqrt_pos.mpr (chord_discriminant_pos hf.2.2.1 hf.2.2.2))

theorem unitChord_distance {r s : ℝ} (hf : ChordFeasible r s) :
    ‖(r : ℂ) - (s : ℂ) * unitChord r s‖ = 1 := by
  have hs : Complex.normSq ((r : ℂ) - (s : ℂ) * unitChord r s) = 1 := by
    rw [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_eq_norm_sq (unitChord r s),
      unitChord_norm, one_pow, mul_one]
    simp only [Complex.normSq_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.conj_re, unitChord_re hf]
    unfold chordCos
    field_simp [hf.1, hf.2.1]
    ring
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg ((r : ℂ) - (s : ℂ) * unitChord r s)]

theorem normSq_sub_mul (a b w : ℂ) :
    Complex.normSq (a - b * w) = Complex.normSq a + Complex.normSq b * Complex.normSq w -
      2 * (starRingEnd ℂ a * b * w).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem lower_half_unique {z w : ℂ} (hn : ‖z‖ = ‖w‖) (hr : z.re = w.re)
    (hz : z.im < 0) (hw : w.im < 0) : z = w := by
  have hsq : Complex.normSq z = Complex.normSq w := by
    simp only [Complex.normSq_eq_norm_sq, hn]
  apply Complex.ext hr
  simp only [Complex.normSq_apply] at hsq
  rw [hr] at hsq
  nlinarith

theorem corrected_chord {a b w : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hw : ‖w‖ = 1)
    (he : ‖a - b * w‖ = 1) (him : (starRingEnd ℂ a * b * w).im < 0) :
    ChordFeasible ‖a‖ ‖b‖ ∧
      starRingEnd ℂ a * b * w = ((‖a‖ * ‖b‖ : ℝ) : ℂ) * unitChord ‖a‖ ‖b‖ := by
  let q := starRingEnd ℂ a * b * w
  have hr : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hs : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hprod : 0 < ‖a‖ * ‖b‖ := mul_pos hr hs
  have hqnorm : ‖q‖ = ‖a‖ * ‖b‖ := by simp [q, hw]
  have hqnormSq : q.re ^ 2 + q.im ^ 2 = (‖a‖ * ‖b‖) ^ 2 := by
    have h := Complex.normSq_eq_norm_sq q
    rw [hqnorm] at h
    simpa [Complex.normSq_apply, pow_two] using h
  have hqre : q.re = (‖a‖ ^ 2 + ‖b‖ ^ 2 - 1) / 2 := by
    have h := normSq_sub_mul a b w
    simp only [Complex.normSq_eq_norm_sq, he, hw, one_pow, mul_one] at h
    change _ = _ - 2 * q.re at h
    linarith
  have hratio : q.re / (‖a‖ * ‖b‖) = chordCos ‖a‖ ‖b‖ := by
    rw [hqre]
    unfold chordCos
    ring
  have hqim : q.im < 0 := him
  have hsqim : 0 < q.im ^ 2 := sq_pos_of_ne_zero (ne_of_lt hqim)
  have hlo : -(‖a‖ * ‖b‖) < q.re := by nlinarith
  have hhi : q.re < ‖a‖ * ‖b‖ := by nlinarith
  have hf : ChordFeasible ‖a‖ ‖b‖ := by
    refine ⟨ne_of_gt hr, ne_of_gt hs, ?_, ?_⟩
    · rw [← hratio]
      exact (lt_div_iff₀ hprod).mpr (by linarith)
    · rw [← hratio]
      exact (div_lt_iff₀ hprod).mpr (by linarith)
  refine ⟨hf, ?_⟩
  apply lower_half_unique
  · calc
      ‖q‖ = ‖a‖ * ‖b‖ := hqnorm
      _ = ‖((‖a‖ * ‖b‖ : ℝ) : ℂ) * unitChord ‖a‖ ‖b‖‖ := by
        rw [norm_mul, unitChord_norm, Complex.norm_of_nonneg hprod.le, mul_one]
  · calc
      q.re = (‖a‖ * ‖b‖) * chordCos ‖a‖ ‖b‖ := by rw [← hratio]; field_simp
      _ = (((‖a‖ * ‖b‖ : ℝ) : ℂ) * unitChord ‖a‖ ‖b‖).re := by simp [unitChord_re hf]
  · exact him
  · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, add_zero] using
      mul_neg_of_pos_of_neg hprod (unitChord_im_neg hf)

def radialBase {I : Type*} (b : I → ℂ) (r : I → ℝ) (i : I) : ℂ :=
  (r i : ℂ) * (b i / (‖b i‖ : ℂ))

theorem radialBase_at_norm {I : Type*} (b : I → ℂ) (hb : ∀ i, b i ≠ 0) :
    radialBase b (fun i => ‖b i‖) = b := by
  funext i
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hb i)))

theorem normalized_norm {b : ℂ} (hb : b ≠ 0) : ‖b / (‖b‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr hb)

theorem radialBase_norm {I : Type*} (b : I → ℂ) (hb : ∀ i, b i ≠ 0)
    (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) (i : I) : ‖radialBase b r i‖ = r i := by
  rw [radialBase, norm_mul, normalized_norm (hb i), mul_one, Complex.norm_of_nonneg (hr i)]

def directionRatio (a b : ℂ) : ℂ := (a / (‖a‖ : ℂ)) / (b / (‖b‖ : ℂ))

theorem directionRatio_norm {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) : ‖directionRatio a b‖ = 1 := by
  rw [directionRatio, norm_div, normalized_norm ha, normalized_norm hb, div_self (by norm_num : (1 : ℝ) ≠ 0)]

theorem directionRatio_cancel {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    starRingEnd ℂ a * b * directionRatio a b = ((‖a‖ * ‖b‖ : ℝ) : ℂ) := by
  have hra : (‖a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)
  have hrb : (‖b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb)
  have hnorm : starRingEnd ℂ a * a = (‖a‖ : ℂ) ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  unfold directionRatio
  calc
    starRingEnd ℂ a * b * ((a / (‖a‖ : ℂ)) / (b / (‖b‖ : ℂ))) =
        (starRingEnd ℂ a * a) * (‖b‖ : ℂ) / (‖a‖ : ℂ) := by field_simp [hra, hrb, hb]
    _ = ((‖a‖ * ‖b‖ : ℝ) : ℂ) := by rw [hnorm, Complex.ofReal_mul]; field_simp [hra]

theorem phaseRotations_factor {L P E : Type*} (l : E → L) (p : E → P) (θ : E → ℝ)
    (σ : E → ℂ) (hσ : ∀ e, Complex.exp ((θ e : ℂ) * Complex.I) = σ e)
    (z : (L → ℝ) × (P → ℝ)) (e : E) :
    phaseRotations l p θ z e = σ e * unitChord (z.1 (l e)) (z.2 (p e)) := by
  simp only [phaseRotations, unitChord, Complex.ofReal_sub, Complex.ofReal_neg, sub_mul, neg_mul,
    Complex.exp_sub, Complex.exp_neg, hσ, div_eq_mul_inv]

theorem radial_unit_distance {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    {r s : ℝ} (hf : ChordFeasible r s) :
    ‖(r : ℂ) * (a / (‖a‖ : ℂ)) - (s : ℂ) * (b / (‖b‖ : ℂ)) *
      (directionRatio a b * unitChord r s)‖ = 1 := by
  have hbn : b / (‖b‖ : ℂ) ≠ 0 :=
    div_ne_zero hb (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb))
  have hra : (‖a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)
  have hrb : (‖b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb)
  have he : (r : ℂ) * (a / (‖a‖ : ℂ)) - (s : ℂ) * (b / (‖b‖ : ℂ)) *
      (directionRatio a b * unitChord r s) =
      (a / (‖a‖ : ℂ)) * ((r : ℂ) - (s : ℂ) * unitChord r s) := by
    unfold directionRatio
    field_simp [hbn, hra, hrb, hb]
  rw [he, norm_mul, normalized_norm ha, unitChord_distance hf, one_mul]

def PreparedSeed.angles {L P E : Type*} [Fintype E] {l : E → L} {p : E → P}
    (Q : PreparedSeed l p) (e : E) : ℝ :=
  Complex.arg (directionRatio (Q.base (Sum.inl (l e))) (Q.base (Sum.inr (p e))))

def PreparedSeed.radii {L P E : Type*} [Fintype E] {l : E → L} {p : E → P}
    (Q : PreparedSeed l p) : (L → ℝ) × (P → ℝ) :=
  (fun i => ‖Q.base (Sum.inl i)‖, fun j => ‖Q.base (Sum.inr j)‖)

theorem PreparedSeed.angles_exp {L P E : Type*} [Fintype E] {l : E → L} {p : E → P}
    (Q : PreparedSeed l p) (e : E) :
    Complex.exp ((Q.angles e : ℂ) * Complex.I) =
      directionRatio (Q.base (Sum.inl (l e))) (Q.base (Sum.inr (p e))) := by
  have hnorm := directionRatio_norm (Q.base_ne_zero (Sum.inl (l e))) (Q.base_ne_zero (Sum.inr (p e)))
  have hh := Complex.norm_mul_exp_arg_mul_I (directionRatio (Q.base (Sum.inl (l e))) (Q.base (Sum.inr (p e))))
  simpa only [PreparedSeed.angles, hnorm, Complex.ofReal_one, one_mul] using hh

theorem PreparedSeed.feasible {L P E : Type*} [Fintype E] {l : E → L} {p : E → P}
    (Q : PreparedSeed l p) (e : E) : ChordFeasible (Q.radii.1 (l e)) (Q.radii.2 (p e)) :=
  (corrected_chord (Q.base_ne_zero _) (Q.base_ne_zero _) (Q.rotation_norm e)
    (Q.unit_edge e) (Q.chord_im_negative e)).1

theorem PreparedSeed.phase_at_radii {L P E : Type*} [Fintype E] {l : E → L} {p : E → P}
    (Q : PreparedSeed l p) : phaseRotations l p Q.angles Q.radii = Q.rotation := by
  funext e
  have ha := Q.base_ne_zero (Sum.inl (l e))
  have hb := Q.base_ne_zero (Sum.inr (p e))
  have he := (corrected_chord ha hb (Q.rotation_norm e) (Q.unit_edge e) (Q.chord_im_negative e)).2
  apply mul_left_cancel₀ (mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr ha) hb)
  rw [phaseRotations_factor l p Q.angles _ Q.angles_exp, ← mul_assoc, directionRatio_cancel ha hb]
  exact he.symm

end
end Proof

end OriginalPhaseGeometry

/- ## Perturbation -/

section OriginalPerturbation

/- A simultaneous radius perturbation preserving support and separating every subset product. -/

namespace Proof

open Set Filter
open scoped Topology

noncomputable section


def joinedRadii {L P : Type*} (z : (L → ℝ) × (P → ℝ)) : L ⊕ P → ℝ := Sum.elim z.1 z.2

def PreparedSeed.varBase {L P E : Type*} [Fintype E] {l : E → L} {p : E → P}
    (Q : PreparedSeed l p) (z : (L → ℝ) × (P → ℝ)) : L ⊕ P → ℂ := radialBase Q.base (joinedRadii z)

theorem PreparedSeed.varBase_at_radii {L P E : Type*} [Fintype E] {l : E → L} {p : E → P}
    (Q : PreparedSeed l p) : Q.varBase Q.radii = Q.base := by
  have hh : joinedRadii Q.radii = fun i => ‖Q.base i‖ := by funext i; cases i <;> rfl
  unfold PreparedSeed.varBase
  rw [hh]
  exact radialBase_at_norm Q.base Q.base_ne_zero

theorem PreparedSeed.varBase_continuous {L P E : Type*} [Fintype E] {l : E → L} {p : E → P}
    (Q : PreparedSeed l p) (i : L ⊕ P) : Continuous (fun z => Q.varBase z i) := by
  cases i <;> simp only [PreparedSeed.varBase, radialBase, joinedRadii, Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem joinedRadii_continuous {L P : Type*} (i : L ⊕ P) :
    Continuous (fun z : (L → ℝ) × (P → ℝ) => joinedRadii z i) := by
  cases i <;> simp only [joinedRadii, Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem PreparedSeed.varBase_unit_edge {L P E : Type*} [Fintype E] {l : E → L} {p : E → P}
    (Q : PreparedSeed l p) (z : (L → ℝ) × (P → ℝ)) (e : E)
    (hf : ChordFeasible (z.1 (l e)) (z.2 (p e))) :
    ‖Q.varBase z (Sum.inl (l e)) - Q.varBase z (Sum.inr (p e)) * phaseRotations l p Q.angles z e‖ = 1 := by
  rw [phaseRotations_factor l p Q.angles _ Q.angles_exp]
  exact radial_unit_distance (Q.base_ne_zero _) (Q.base_ne_zero _) hf

structure SeparatedSeed {L P E : Type*} [Fintype E] (l : E → L) (p : E → P) where
  base : L ⊕ P → ℂ
  rotation : E → ℂ
  base_ne_zero : ∀ i, base i ≠ 0
  base_norm_lt : ∀ i, ‖base i‖ < 1
  radii_injective : Function.Injective (fun i => ‖base i‖)
  rotation_norm : ∀ e, ‖rotation e‖ = 1
  unit_edge : ∀ e, ‖base (Sum.inl (l e)) - base (Sum.inr (p e)) * rotation e‖ = 1
  support_margin : ∀ i j, i ≠ j → support (base i) (base j) < -2 * ∑ e, ‖rotation e - 1‖
  products_injective : Function.Injective (subsetProduct rotation)

def GoodRadii {L P E : Type*} [Fintype E] {l : E → L} {p : E → P}
    (Q : PreparedSeed l p) (z : (L → ℝ) × (P → ℝ)) : Prop :=
  (∀ i, 0 < joinedRadii z i) ∧ (∀ i, ‖Q.varBase z i‖ < 1) ∧
  Function.Injective (joinedRadii z) ∧
  (∀ e, ChordFeasible (z.1 (l e)) (z.2 (p e))) ∧
  ∀ i j, i ≠ j → support (Q.varBase z i) (Q.varBase z j) <
    -2 * ∑ e, ‖phaseRotations l p Q.angles z e - 1‖

theorem PreparedSeed.goodRadii_nhds {L P E : Type*} [Fintype L] [Fintype P] [Fintype E]
    {l : E → L} {p : E → P} (Q : PreparedSeed l p) :
    ∀ᶠ z in 𝓝 Q.radii, GoodRadii Q z := by
  have hjoined : ∀ i, joinedRadii Q.radii i = ‖Q.base i‖ := by intro i; cases i <;> rfl
  have hr : ∀ i, Q.radii.1 i ≠ 0 := fun i => norm_ne_zero_iff.mpr (Q.base_ne_zero _)
  have hs : ∀ j, Q.radii.2 j ≠ 0 := fun j => norm_ne_zero_iff.mpr (Q.base_ne_zero _)
  have hrot : ∀ e, ContinuousAt (fun z => phaseRotations l p Q.angles z e) Q.radii :=
    phaseRotations_continuousAt l p Q.angles Q.radii hr hs
  have hbase : ∀ i, ContinuousAt (fun z => Q.varBase z i) Q.radii :=
    fun i => (Q.varBase_continuous i).continuousAt
  have hpos : ∀ i, ∀ᶠ z in 𝓝 Q.radii, 0 < joinedRadii z i := by
    intro i
    apply continuousAt_const.eventually_lt (joinedRadii_continuous i).continuousAt
    rw [hjoined]
    exact norm_pos_iff.mpr (Q.base_ne_zero i)
  have hnorm : ∀ i, ∀ᶠ z in 𝓝 Q.radii, ‖Q.varBase z i‖ < 1 := by
    intro i
    apply (hbase i).norm.eventually_lt continuousAt_const
    rw [Q.varBase_at_radii]
    exact Q.base_norm_lt i
  have hinj : ∀ i j, ∀ᶠ z in 𝓝 Q.radii, i ≠ j → joinedRadii z i ≠ joinedRadii z j := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    have hdiff : ContinuousAt (fun z => joinedRadii z i - joinedRadii z j) Q.radii :=
      (joinedRadii_continuous i).continuousAt.sub (joinedRadii_continuous j).continuousAt
    have hdiff0 : joinedRadii Q.radii i - joinedRadii Q.radii j ≠ 0 := by
      rw [hjoined, hjoined]
      exact sub_ne_zero.mpr (Q.radii_injective.ne hij)
    exact (hdiff.eventually_ne hdiff0).mono (fun _ hh _ => sub_ne_zero.mp hh)
  have hfeas : ∀ e, ∀ᶠ z in 𝓝 Q.radii, ChordFeasible (z.1 (l e)) (z.2 (p e)) := by
    intro e
    have hcos : ContinuousAt (fun z : (L → ℝ) × (P → ℝ) => chordCos (z.1 (l e)) (z.2 (p e))) Q.radii := by
      unfold chordCos
      fun_prop (disch := aesop)
    have hl : ∀ᶠ z in 𝓝 Q.radii, -1 < chordCos (z.1 (l e)) (z.2 (p e)) :=
      continuousAt_const.eventually_lt hcos (Q.feasible e).2.2.1
    have hu : ∀ᶠ z in 𝓝 Q.radii, chordCos (z.1 (l e)) (z.2 (p e)) < 1 :=
      hcos.eventually_lt continuousAt_const (Q.feasible e).2.2.2
    filter_upwards [hpos (Sum.inl (l e)), hpos (Sum.inr (p e)), hl, hu] with z hr hs hl hu
    exact ⟨ne_of_gt hr, ne_of_gt hs, hl, hu⟩
  have hmargin : ∀ i j, ∀ᶠ z in 𝓝 Q.radii, i ≠ j →
      support (Q.varBase z i) (Q.varBase z j) < -2 * ∑ e, ‖phaseRotations l p Q.angles z e - 1‖ := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    have hc : ContinuousAt (fun z => support (Q.varBase z i) (Q.varBase z j) +
        2 * ∑ e, ‖phaseRotations l p Q.angles z e - 1‖) Q.radii := by
      have hri := Complex.continuous_re.continuousAt.comp (hbase i)
      have hrj := Complex.continuous_re.continuousAt.comp (hbase j)
      have hii := Complex.continuous_im.continuousAt.comp (hbase i)
      have hij := Complex.continuous_im.continuousAt.comp (hbase j)
      unfold support
      exact ((hri.mul (hrj.sub hri)).add (hii.mul (hij.sub hii))).add
        (continuousAt_const.mul
          (tendsto_finsetSum Finset.univ (fun e _ =>
            ((hrot e).sub continuousAt_const).norm)))
    have hvalue : support (Q.varBase Q.radii i) (Q.varBase Q.radii j) +
        2 * ∑ e, ‖phaseRotations l p Q.angles Q.radii e - 1‖ < 0 := by
      rw [Q.varBase_at_radii, Q.phase_at_radii]
      linarith [Q.support_margin i j hij]
    exact (hc.eventually_lt continuousAt_const hvalue).mono (fun _ hh _ => by linarith)
  have hposAll : ∀ᶠ z in 𝓝 Q.radii, ∀ i, 0 < joinedRadii z i := by simpa only [eventually_all] using hpos
  have hnAll : ∀ᶠ z in 𝓝 Q.radii, ∀ i, ‖Q.varBase z i‖ < 1 := by simpa only [eventually_all] using hnorm
  have hiAll : ∀ᶠ z in 𝓝 Q.radii, ∀ i j, i ≠ j → joinedRadii z i ≠ joinedRadii z j := by
    simpa only [eventually_all] using hinj
  have hfAll : ∀ᶠ z in 𝓝 Q.radii, ∀ e, ChordFeasible (z.1 (l e)) (z.2 (p e)) := by
    simpa only [eventually_all] using hfeas
  have hmAll : ∀ᶠ z in 𝓝 Q.radii, ∀ i j, i ≠ j →
      support (Q.varBase z i) (Q.varBase z j) < -2 * ∑ e, ‖phaseRotations l p Q.angles z e - 1‖ := by
    simpa only [eventually_all] using hmargin
  filter_upwards [hposAll, hnAll, hiAll, hfAll, hmAll] with z hp hn hi hf hm
  exact ⟨hp, hn, fun i j h => by_contra (fun hij => hi i j hij h), hf, hm⟩

theorem PreparedSeed.exists_separated {L P E : Type*} [Fintype L] [Fintype P] [Fintype E]
    {l : E → L} {p : E → P} (Q : PreparedSeed l p)
    (hij : Function.Injective (fun e => (l e, p e))) : Nonempty (SeparatedSeed l p) := by
  classical
  obtain ⟨U, hUgood, hU, hz₀⟩ := mem_nhds_iff.mp Q.goodRadii_nhds
  have hne : U.Nonempty := ⟨Q.radii, hz₀⟩
  have hnz : ∀ z ∈ U, (∀ i, z.1 i ≠ 0) ∧ (∀ j, z.2 j ≠ 0) := by
    intro z hz
    exact ⟨fun i => ne_of_gt ((hUgood hz).1 (Sum.inl i)), fun j => ne_of_gt ((hUgood hz).1 (Sum.inr j))⟩
  obtain ⟨z, hz, hprod⟩ := exists_injective_subsetProducts l p hij Q.angles U hU hne hnz
    (fun e z hz => (hUgood hz).2.2.2.1 e)
  obtain ⟨hpos, hnorm, hinj, hfeas, hmargin⟩ := hUgood hz
  have hrnorm : ∀ i, ‖Q.varBase z i‖ = joinedRadii z i :=
    radialBase_norm Q.base Q.base_ne_zero (joinedRadii z) (fun i => (hpos i).le)
  refine ⟨{
    base := Q.varBase z
    rotation := phaseRotations l p Q.angles z
    base_ne_zero := fun i => norm_pos_iff.mp (by rw [hrnorm]; exact hpos i)
    base_norm_lt := hnorm
    radii_injective := ?_
    rotation_norm := phaseRotations_norm l p Q.angles z
    unit_edge := fun e => Q.varBase_unit_edge z e (hfeas e)
    support_margin := hmargin
    products_injective := hprod }⟩
  intro i j hh
  dsimp only at hh
  rw [hrnorm, hrnorm] at hh
  exact hinj hh

end
end Proof

end OriginalPerturbation

/- ## Counting -/

section OriginalCounting

/- Exact vertex counts and a lower bound for unordered unit pairs. -/

namespace Proof


noncomputable section

def pairDistance {X : Type*} [MetricSpace X] (p : Sym2 X) : ℝ :=
  Sym2.lift ⟨dist, fun a b => dist_comm a b⟩ p

def unitPairs {X : Type*} [MetricSpace X] (P : Finset X) : Finset (Sym2 X) := by
  classical
  exact P.sym2.filter (fun p => pairDistance p = 1)

def rotatedSet {I E : Type*} [Fintype I] [Fintype E] (b : I → ℂ) (w : E → ℂ) : Finset ℂ := by
  classical
  exact Finset.univ.image (rotatedCopy b w)

theorem mem_rotatedSet {I E : Type*} [Fintype I] [Fintype E]
    (b : I → ℂ) (w : E → ℂ) (x : I × Finset E) :
    rotatedCopy b w x ∈ rotatedSet b w := by
  classical
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

theorem rotatedSet_card {I E : Type*} [Fintype I] [Fintype E]
    (b : I → ℂ) (w : E → ℂ) (hinj : Function.Injective (rotatedCopy b w)) :
    (rotatedSet b w).card = Fintype.card I * 2 ^ Fintype.card E := by
  classical
  rw [rotatedSet, Finset.card_image_of_injective _ hinj]
  simp

theorem rotatedSet_convexIndependent {I E : Type*} [Fintype I] [Fintype E]
    (b : I → ℂ) (w : E → ℂ) (hc : ConvexIndependent ℝ (rotatedCopy b w)) :
    ConvexIndependent ℝ (fun z : ↥(rotatedSet b w : Set ℂ) => (z : ℂ)) := by
  have he : (rotatedSet b w : Set ℂ) = Set.range (rotatedCopy b w) := by
    classical
    simp [rotatedSet]
  rw [he]
  exact hc.range

abbrev LiftedEdge (E : Type*) := (e : E) × {S : Finset E // e ∉ S}

theorem subsets_avoiding_card {E : Type*} [Fintype E] [DecidableEq E] (e : E) :
    Fintype.card {S : Finset E // e ∉ S} = 2 ^ (Fintype.card E - 1) := by
  rw [Fintype.card_of_subtype ((Finset.univ.erase e).powerset)
    (fun S => by simp [Finset.mem_powerset, Finset.subset_erase])]
  simp

theorem liftedEdge_card {E : Type*} [Fintype E] [DecidableEq E] :
    Fintype.card (LiftedEdge E) = Fintype.card E * 2 ^ (Fintype.card E - 1) := by
  simp only [LiftedEdge, Fintype.card_sigma, subsets_avoiding_card,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

def liftedPair {L P E : Type*} [DecidableEq E]
    (l : E → L) (p : E → P) (b : L ⊕ P → ℂ) (w : E → ℂ) (x : LiftedEdge E) : Sym2 ℂ :=
  s(rotatedCopy b w (Sum.inl (l x.1), x.2.val),
    rotatedCopy b w (Sum.inr (p x.1), insert x.1 x.2.val))

theorem liftedPair_injective {L P E : Type*} [DecidableEq E]
    (l : E → L) (p : E → P) (b : L ⊕ P → ℂ) (w : E → ℂ)
    (he : Function.Injective (fun e => (l e, p e)))
    (hinj : Function.Injective (rotatedCopy b w)) :
    Function.Injective (liftedPair l p b w) := by
  rintro ⟨e, S⟩ ⟨f, T⟩ hh
  simp only [liftedPair, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hh
  rcases hh with ⟨hl, hp⟩ | ⟨hl, hp⟩
  · have hl := hinj hl
    have hp := hinj hp
    have hlf : l e = l f := Sum.inl.inj (congrArg Prod.fst hl)
    have hpf : p e = p f := Sum.inr.inj (congrArg Prod.fst hp)
    have hef := he (Prod.ext hlf hpf)
    subst f
    have hST : S = T := Subtype.ext (congrArg Prod.snd hl)
    subst T
    rfl
  · have hbad := congrArg Prod.fst (hinj hl)
    cases hbad

theorem liftedPair_mem_unitPairs {L P E : Type*}
    [Fintype L] [Fintype P] [Fintype E] [DecidableEq E]
    (l : E → L) (p : E → P) (b : L ⊕ P → ℂ) (w : E → ℂ)
    (hw : ∀ e, ‖w e‖ = 1)
    (hedge : ∀ e, ‖b (Sum.inl (l e)) - b (Sum.inr (p e)) * w e‖ = 1)
    (x : LiftedEdge E) : liftedPair l p b w x ∈ unitPairs (rotatedSet b w) := by
  classical
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mk_mem_sym2_iff.mpr
    exact ⟨mem_rotatedSet b w _, mem_rotatedSet b w _⟩
  · exact rotatedCopy_unit_edge b w hw _ _ x.1 (hedge x.1) x.2.val x.2.property

theorem amplification_unitPairs_bound {L P E : Type*}
    [Fintype L] [Fintype P] [Fintype E] [DecidableEq E]
    (l : E → L) (p : E → P) (b : L ⊕ P → ℂ) (w : E → ℂ)
    (he : Function.Injective (fun e => (l e, p e)))
    (hinj : Function.Injective (rotatedCopy b w)) (hw : ∀ e, ‖w e‖ = 1)
    (hedge : ∀ e, ‖b (Sum.inl (l e)) - b (Sum.inr (p e)) * w e‖ = 1) :
    Fintype.card E * 2 ^ (Fintype.card E - 1) ≤ (unitPairs (rotatedSet b w)).card := by
  let f : LiftedEdge E → unitPairs (rotatedSet b w) := fun x =>
    ⟨liftedPair l p b w x, liftedPair_mem_unitPairs l p b w hw hedge x⟩
  have hf : Function.Injective f := fun x y h =>
    liftedPair_injective l p b w he hinj (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [liftedEdge_card, Fintype.card_coe] using hc

end
end Proof

end OriginalCounting

/- ## Counterexample -/

section OriginalCounterexample

/- Convex configurations with an unbounded ratio of unit distances to vertices. -/

namespace Proof

noncomputable section

def constructionSize (d : ℕ) : ℕ := 2 * d ^ d * 2 ^ (d ^ (d + 1))

theorem convex_unit_counterexample (d : ℕ) (hd : 2 ≤ d) :
    ∃ P : Finset ℂ,
      ConvexIndependent ℝ (fun z : ↥(P : Set ℂ) => (z : ℂ)) ∧
      P.card = constructionSize d ∧ d * P.card ≤ 4 * (unitPairs P).card := by
  classical
  obtain ⟨Q⟩ := (coordinatePattern d).exists_prepared
  obtain ⟨R⟩ := Q.exists_separated (coordinatePattern d).endpoints_injective
  let P := rotatedSet R.base R.rotation
  have hinj := rotatedCopy_injective R.base R.rotation R.base_ne_zero R.radii_injective
    R.rotation_norm R.products_injective
  have hconv := rotatedCopy_convexIndependent R.base R.rotation R.base_ne_zero R.radii_injective
    (fun i => (R.base_norm_lt i).le) R.rotation_norm R.products_injective R.support_margin
  have hcard := rotatedSet_card R.base R.rotation hinj
  have hcount := amplification_unitPairs_bound (coordinatePattern d).line (coordinatePattern d).point
    R.base R.rotation (coordinatePattern d).endpoints_injective hinj R.rotation_norm R.unit_edge
  refine ⟨P, rotatedSet_convexIndependent R.base R.rotation hconv, ?_, ?_⟩
  · simpa [P, vertexLabel_card (by omega : 1 ≤ d), edgeLabel_card, constructionSize,
      pow_succ] using hcard
  · have hm : 1 ≤ Fintype.card (EdgeLabel d) := by
      rw [edgeLabel_card]
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    have hpow : 2 ^ Fintype.card (EdgeLabel d) = 2 * 2 ^ (Fintype.card (EdgeLabel d) - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hm]
    have hid : d * P.card = 4 * (Fintype.card (EdgeLabel d) * 2 ^ (Fintype.card (EdgeLabel d) - 1)) := by
      dsimp [P]
      rw [hcard, vertexLabel_card (by omega : 1 ≤ d), hpow, edgeLabel_card, pow_succ]
      ring
    rw [hid]
    exact Nat.mul_le_mul_left 4 hcount

theorem constructionSize_pos {d : ℕ} (hd : 1 ≤ d) : 0 < constructionSize d := by
  unfold constructionSize
  positivity

theorem convex_unit_ratios_unbounded (C : ℝ) :
    ∃ P : Finset ℂ, ConvexIndependent ℝ (fun z : ↥(P : Set ℂ) => (z : ℂ)) ∧
      C * (P.card : ℝ) < ((unitPairs P).card : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * C)
  obtain ⟨P, hconv, hcard, hcount⟩ := convex_unit_counterexample (n + 2) (by omega)
  have hP : (0 : ℝ) < P.card := by exact_mod_cast (hcard ▸ constructionSize_pos (by omega : 1 ≤ n + 2))
  have hcountR : ((n + 2 : ℕ) : ℝ) * P.card ≤ 4 * (unitPairs P).card := by exact_mod_cast hcount
  have hdR : 4 * C < ((n + 2 : ℕ) : ℝ) := by push_cast; linarith
  refine ⟨P, hconv, ?_⟩
  nlinarith [mul_pos (sub_pos.mpr hdR) hP]

end
end Proof

end OriginalCounterexample

/- ## PlaneBridge -/

section OriginalPlaneBridge

/- Transfer from the complex plane to the literal Euclidean-plane definitions. -/

namespace Proof


noncomputable section

open scoped EuclideanGeometry

def complexToPlane : ℂ ≃ₗᵢ[ℝ] ℝ² := Complex.orthonormalBasisOneI.repr

theorem pairDistance_eq_out {X : Type*} [MetricSpace X] (p : Sym2 X) :
    pairDistance p = dist p.out.1 p.out.2 := by
  have hp : s(p.out.1, p.out.2) = p := by rw [Sym2.mk, p.out_eq]
  conv_lhs => rw [← hp]
  rfl

theorem unitDistNum_eq_card_unitPairs {X : Type*} [MetricSpace X] (P : Finset X) :
    unitDistNum P = (unitPairs P).card := by
  classical
  simp only [unitDistNum, unitPairs, pairDistance_eq_out]

theorem pairDistance_map_isometry {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (hf : Isometry f) (p : Sym2 X) :
    pairDistance (Sym2.map f p) = pairDistance p := by
  refine Sym2.inductionOn p ?_
  intro a b
  exact hf.dist_eq a b

theorem unitPairs_image_isometry {X Y : Type*} [MetricSpace X] [MetricSpace Y] [DecidableEq Y]
    (f : X → Y) (hf : Isometry f) (P : Finset X) :
    unitPairs (P.image f) = (unitPairs P).image (Sym2.map f) := by
  classical
  rw [unitPairs, Finset.sym2_image, Finset.filter_image]
  congr 1
  ext p
  simp only [Finset.mem_filter, pairDistance_map_isometry f hf, unitPairs]

theorem unitPairs_card_image_isometry {X Y : Type*} [MetricSpace X] [MetricSpace Y] [DecidableEq Y]
    (f : X → Y) (hf : Isometry f) (P : Finset X) :
    (unitPairs (P.image f)).card = (unitPairs P).card := by
  classical
  rw [unitPairs_image_isometry f hf, Finset.card_image_of_injective _
    (Sym2.map.injective hf.injective)]

theorem convexIndependent_linearMap {I V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (hf : Function.Injective f) (p : I → V)
    (hp : ConvexIndependent ℝ p) : ConvexIndependent ℝ (f ∘ p) := by
  intro S i hi
  apply hp S i
  have himg : (f ∘ p) '' S = f '' (p '' S) := (Set.image_image f p S).symm
  rw [himg, ← f.image_convexHull] at hi
  obtain ⟨x, hx, hxi⟩ := hi
  have heq : x = p i := hf hxi
  simpa only [heq] using hx

theorem convexIndep_image_complexToPlane (P : Finset ℂ)
    (hp : ConvexIndependent ℝ (fun z : ↥(P : Set ℂ) => (z : ℂ))) :
    EuclideanGeometry.ConvexIndep (P.image complexToPlane) := by
  classical
  apply convexIndependent_set_iff_notMem_convexHull_sdiff.mp
  have hc := convexIndependent_linearMap complexToPlane.toLinearEquiv.toLinearMap
    complexToPlane.injective (fun z : ↥(P : Set ℂ) => (z : ℂ)) hp
  have hrange : (P.image complexToPlane : Set ℝ²) =
      Set.range (fun z : ↥(P : Set ℂ) => complexToPlane (z : ℂ)) := by
    ext y
    simp
  rw [hrange]
  exact hc.range

theorem convexUnitDistanceCounts_bddAbove (n : ℕ) :
    BddAbove (convexUnitDistanceCounts n) := by
  classical
  refine ⟨(n + 1).choose 2, ?_⟩
  rintro _ ⟨P, hP, _, rfl⟩
  rw [unitDistNum_eq_card_unitPairs]
  calc
    (unitPairs P).card ≤ P.sym2.card := Finset.card_filter_le _ _
    _ = (n + 1).choose 2 := by rw [Finset.card_sym2, hP]

theorem unitDistNum_le_max (P : Finset ℝ²) (hP : EuclideanGeometry.ConvexIndep P) :
    unitDistNum P ≤ maxConvexUnitDistances P.card := by
  apply le_csSup (convexUnitDistanceCounts_bddAbove P.card)
  exact ⟨P, rfl, hP, rfl⟩

end
end Proof

end OriginalPlaneBridge

/- ## Problem -/

section OriginalProblem

/-
The negation of Erdős problem 96, with the Euclidean-plane, convexity,
unordered-pair-count, and supremum definitions of Formal Conjectures.
-/

namespace Proof

noncomputable section

open Filter EuclideanGeometry
open scoped EuclideanGeometry

theorem constructionSize_ge_dimension {d : ℕ} (hd : 1 ≤ d) :
    d ≤ constructionSize d := by
  have hpow : 1 ≤ 2 ^ (d ^ (d + 1)) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc
    d ≤ d ^ d := le_self_pow hd (by omega)
    _ ≤ 2 * d ^ d := by omega
    _ ≤ constructionSize d := by
      simpa only [constructionSize, mul_one] using Nat.mul_le_mul_left (2 * d ^ d) hpow

/-- The explicit family in the literal Euclidean plane. -/
theorem plane_counterexample (d : ℕ) (hd : 2 ≤ d) :
    ∃ points : Finset ℝ²,
      ConvexIndep points ∧ points.card = constructionSize d ∧
      d * points.card ≤ 4 * unitDistNum points := by
  classical
  obtain ⟨P, hconv, hcard, hcount⟩ := convex_unit_counterexample d hd
  let points := P.image complexToPlane
  have hcard' : points.card = P.card :=
    Finset.card_image_of_injective _ complexToPlane.injective
  have hunit : unitDistNum points = (unitPairs P).card := by
    rw [unitDistNum_eq_card_unitPairs]
    exact unitPairs_card_image_isometry complexToPlane complexToPlane.isometry P
  refine ⟨points, convexIndep_image_complexToPlane P hconv, hcard'.trans hcard, ?_⟩
  rw [hcard', hunit]
  exact hcount

/-- Counterexamples occur past every cardinality threshold and every proposed linear bound. -/
theorem large_convex_counterexample (C : ℝ) (N₀ : ℕ) :
    ∃ points : Finset ℝ²,
      N₀ ≤ points.card ∧ ConvexIndep points ∧
      C * (points.card : ℝ) < (unitDistNum points : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * C)
  let d := n + N₀ + 2
  have hd : 2 ≤ d := by dsimp [d]; omega
  obtain ⟨P, hconv, hcard, hcount⟩ := plane_counterexample d hd
  have hsize : N₀ ≤ P.card := by
    rw [hcard]
    exact le_trans (by dsimp [d]; omega) (constructionSize_ge_dimension (by omega))
  have hP : (0 : ℝ) < P.card := by
    have hh : 0 < P.card := by rw [hcard]; exact constructionSize_pos (by omega)
    exact_mod_cast hh
  have hcountR : (d : ℝ) * P.card ≤ 4 * unitDistNum P := by exact_mod_cast hcount
  have hdR : 4 * C < (d : ℝ) := by dsimp [d]; push_cast; linarith
  refine ⟨P, hsize, hconv, ?_⟩
  nlinarith [mul_pos (sub_pos.mpr hdR) hP]

/-- The maximum number of unit distances in a convex n-gon is not O(n). -/
theorem erdos_96_false :
    ¬ ((fun n => (maxConvexUnitDistances n : ℝ)) =O[atTop] fun n => (n : ℝ)) := by
  intro h
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hC
  obtain ⟨P, hlarge, hconv, hcount⟩ := large_convex_counterexample C N₀
  have hupper := hN₀ P.card hlarge
  have hmax : (unitDistNum P : ℝ) ≤ (maxConvexUnitDistances P.card : ℝ) := by
    exact_mod_cast unitDistNum_le_max P hconv
  simp only [Real.norm_natCast] at hupper
  linarith

end
end Proof

end OriginalProblem

/-- The negation of the exact proposition in the supplied task. -/
theorem target : ¬ (True ↔
    ((fun n => (Erdos96.maxConvexUnitDistances n : ℝ)) =O[Filter.atTop]
      fun n => (n : ℝ))) := by
  intro h
  exact Proof.erdos_96_false (h.mp True.intro)

end Combined_Erdos96

/-! ## Source: UnitDegree.lean -/

section Combined_UnitDegree

/-! Unit-distance degrees and density-preserving vertex deletion (Lemma 4.1). -/

namespace Proof

noncomputable section

variable {X : Type*} [MetricSpace X]

def unitNeighbors (P : Finset X) (x : X) : Finset X := by
  classical
  exact P.filter (fun y => dist x y = 1)

def unitDegree (P : Finset X) (x : X) : ℕ := (unitNeighbors P x).card

def HasUnitMinDegree (P : Finset X) (k : ℕ) : Prop :=
  ∀ x ∈ P, k ≤ unitDegree P x

@[simp] theorem mem_unitNeighbors {P : Finset X} {x y : X} :
    y ∈ unitNeighbors P x ↔ y ∈ P ∧ dist x y = 1 := by
  classical
  simp [unitNeighbors]

@[simp] theorem self_not_mem_unitNeighbors (P : Finset X) (x : X) :
    x ∉ unitNeighbors P x := by simp

@[simp] theorem mk_mem_unitPairs {P : Finset X} {x y : X} :
    s(x, y) ∈ unitPairs P ↔ x ∈ P ∧ y ∈ P ∧ dist x y = 1 := by
  classical
  rw [unitPairs, Finset.mem_filter, Finset.mk_mem_sym2_iff]
  change ((x ∈ P ∧ y ∈ P) ∧ dist x y = 1) ↔ _
  exact and_assoc

@[simp] theorem unitPairs_empty : unitPairs (∅ : Finset X) = ∅ := by
  classical
  simp [unitPairs]

theorem unitDegree_mono {P Q : Finset X} (h : P ⊆ Q) (x : X) :
    unitDegree P x ≤ unitDegree Q x := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem unitDegree_lt_card {P : Finset X} {x : X} (hx : x ∈ P) :
    unitDegree P x < P.card := by
  classical
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.filter_subset _ _, fun he => self_not_mem_unitNeighbors P x (he.symm ▸ hx)⟩

theorem unitPairs_mono {P Q : Finset X} (h : P ⊆ Q) : unitPairs P ⊆ unitPairs Q := by
  classical
  intro e
  induction e using Sym2.inductionOn with
  | hf x y => simp only [mk_mem_unitPairs]; exact fun hh => ⟨h hh.1, h hh.2.1, hh.2.2⟩

theorem unitDegree_erase_le [DecidableEq X] (P : Finset X) (x v : X) :
    unitDegree P x ≤ unitDegree (P.erase v) x + 1 := by
  classical
  unfold unitDegree unitNeighbors
  rw [Finset.filter_erase]
  by_cases h : v ∈ P.filter (fun y => dist x y = 1)
  · exact (Finset.card_erase_add_one h).ge
  · rw [Finset.erase_eq_of_notMem h]
    omega

theorem unitPairs_erase_add_degree [DecidableEq X] {P : Finset X} {x : X} (hx : x ∈ P) :
    (unitPairs (P.erase x)).card + unitDegree P x = (unitPairs P).card := by
  classical
  let f : X → Sym2 X := fun y => s(x, y)
  have hf : Function.Injective f := by
    intro y z h
    simp only [f, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
    rcases h with h | h
    · exact h.2
    · exact h.2.trans h.1
  have hunion : unitPairs (P.erase x) ∪ (unitNeighbors P x).image f = unitPairs P := by
    ext e
    induction e using Sym2.inductionOn with
    | hf a b =>
      simp only [Finset.mem_union, mk_mem_unitPairs, Finset.mem_erase, Finset.mem_image,
        mem_unitNeighbors, f, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      constructor
      · rintro (⟨⟨_, ha⟩, ⟨_, hb⟩, hab⟩ | ⟨y, ⟨hy, hxy⟩, he⟩)
        · exact ⟨ha, hb, hab⟩
        · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hx, hy, hxy⟩
          · exact ⟨hy, hx, by simpa only [dist_comm] using hxy⟩
      · rintro ⟨ha, hb, hab⟩
        by_cases hax : a = x
        · subst a
          exact Or.inr ⟨b, ⟨hb, hab⟩, Or.inl ⟨rfl, rfl⟩⟩
        by_cases hbx : b = x
        · subst b
          exact Or.inr ⟨a, ⟨ha, by simpa only [dist_comm] using hab⟩, Or.inr ⟨rfl, rfl⟩⟩
        exact Or.inl ⟨⟨hax, ha⟩, ⟨hbx, hb⟩, hab⟩
  have hdis : Disjoint (unitPairs (P.erase x)) ((unitNeighbors P x).image f) := by
    apply Finset.disjoint_left.mpr
    intro e he hfmem
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hfmem
    have hh := (mk_mem_unitPairs.mp he).1
    exact (Finset.mem_erase.mp hh).1 rfl
  rw [← hunion, Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ hf]
  rfl

/-- Repeated deletion retains both a minimum-degree bound and the original density. -/
theorem dense_subset_min_degree (α : ℝ) (k : ℕ) (hα : (k : ℝ) < α)
    (P : Finset X) (hP : P.Nonempty) (hcount : α * P.card ≤ (unitPairs P).card) :
    ∃ Q : Finset X, Q ⊆ P ∧ Q.Nonempty ∧ HasUnitMinDegree Q (k + 1) ∧
      α * Q.card ≤ (unitPairs Q).card := by
  classical
  revert hP hcount
  refine Finset.strongInductionOn P ?_
  intro P ih hP hcount
  by_cases hd : HasUnitMinDegree P (k + 1)
  · exact ⟨P, Finset.Subset.refl P, hP, hd, hcount⟩
  simp only [HasUnitMinDegree, not_forall, not_le] at hd
  obtain ⟨x, hx, hdeg⟩ := hd
  have hdeg' : (unitDegree P x : ℝ) ≤ k := by exact_mod_cast (by omega : unitDegree P x ≤ k)
  have hcard : ((P.erase x).card : ℝ) + 1 = P.card := by
    exact_mod_cast Finset.card_erase_add_one hx
  have hedge : ((unitPairs (P.erase x)).card : ℝ) + unitDegree P x = (unitPairs P).card := by
    exact_mod_cast unitPairs_erase_add_degree hx
  have hnew : α * (P.erase x).card < (unitPairs (P.erase x)).card := by
    nlinarith
  have hne : (P.erase x).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hnew
    simpa using hnew
  obtain ⟨Q, hQP, hQ, hdQ, hcQ⟩ := ih (P.erase x) (Finset.erase_ssubset hx) hne hnew.le
  exact ⟨Q, hQP.trans (Finset.erase_subset _ _), hQ, hdQ, hcQ⟩

open EuclideanGeometry
open scoped EuclideanGeometry

theorem convexIndep_subset {P Q : Finset ℝ²} (hP : ConvexIndep P) (hQP : Q ⊆ P) :
    ConvexIndep Q := by
  intro x hx hh
  apply hP x (hQP hx)
  have hsub : ((Q : Set ℝ²) \ {x}) ⊆ ((P : Set ℝ²) \ {x}) :=
    fun y hy => ⟨hQP hy.1, hy.2⟩
  exact convexHull_mono hsub hh

/-- All vertices can have arbitrarily many neighbours at the same distance, namely one. -/
theorem exists_convex_min_degree (k : ℕ) :
    ∃ P : Finset ℝ², P.Nonempty ∧ ConvexIndep P ∧ HasUnitMinDegree P k := by
  obtain ⟨P, _, hconv, hc⟩ := large_convex_counterexample ((k : ℝ) + 1) 0
  rw [unitDistNum_eq_card_unitPairs] at hc
  have hP : P.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hc
    simpa using hc
  obtain ⟨Q, hQP, hQ, hd, _⟩ := dense_subset_min_degree ((k : ℝ) + 1) k
    (by linarith) P hP hc.le
  exact ⟨Q, hQ, convexIndep_subset hconv hQP, fun x hx => (Nat.le_succ k).trans (hd x hx)⟩

theorem exists_convex_equidistant (k : ℕ) :
    ∃ P : Finset ℝ², P.Nonempty ∧ ConvexIndep P ∧ Erdos97.HasNEquidistantProperty k P := by
  obtain ⟨P, hP, hconv, hd⟩ := exists_convex_min_degree k
  exact ⟨P, hP, hconv, fun x hx => ⟨1, by norm_num, hd x hx⟩⟩

theorem erdos_97_false :
    ¬ (∀ P : Finset ℝ², P.Nonempty → ConvexIndep P → ¬ Erdos97.HasNEquidistantProperty 4 P) := by
  obtain ⟨P, hP, hconv, he⟩ := exists_convex_equidistant 4
  exact fun h => h P hP hconv he

theorem erdos_97_general_false :
    ¬ (∃ k : ℕ, ∀ P : Finset ℝ², P.Nonempty → ConvexIndep P →
      ¬ Erdos97.HasNEquidistantProperty k P) := by
  rintro ⟨k, hk⟩
  obtain ⟨P, hP, hconv, he⟩ := exists_convex_equidistant k
  exact hk P hP hconv he

end
end Proof

end Combined_UnitDegree

/-! ## Source: GeneralProducts.lean -/

section Combined_GeneralProducts

/-! Products with bounded exponents: Lemma 2.1 and the general form of Lemma 3.4. -/

namespace Proof
noncomputable section

def boundedProduct {E : Type*} [Fintype E] {q : ℕ}
    (w : E → ℂ) (a : E → Fin q) : ℂ := ∏ e, w e ^ (a e).val

def rotationBudget {E : Type*} [Fintype E] (q : ℕ) (w : E → ℂ) : ℝ :=
  (q - 1 : ℕ) * ∑ e, ‖w e - 1‖

theorem boundedProduct_norm {E : Type*} [Fintype E] {q : ℕ}
    (w : E → ℂ) (hw : ∀ e, ‖w e‖ = 1) (a : E → Fin q) :
    ‖boundedProduct w a‖ = 1 := by
  simp [boundedProduct, norm_prod, norm_pow, hw]

theorem norm_pow_sub_one_le (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) :
    ‖w ^ n - 1‖ ≤ n * ‖w - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ‖w ^ (n + 1) - 1‖ = ‖(w ^ n - 1) * w + (w - 1)‖ := by
        congr 1
        rw [pow_succ]
        ring
      _ ≤ ‖(w ^ n - 1) * w‖ + ‖w - 1‖ := norm_add_le _ _
      _ = ‖w ^ n - 1‖ + ‖w - 1‖ := by rw [norm_mul, hw, mul_one]
      _ ≤ (n + 1 : ℕ) * ‖w - 1‖ := by push_cast; nlinarith

theorem boundedProduct_close {E : Type*} [Fintype E] {q : ℕ}
    (w : E → ℂ) (hw : ∀ e, ‖w e‖ = 1) (a : E → Fin q) :
    ‖boundedProduct w a - 1‖ ≤ rotationBudget q w := by
  classical
  calc
    ‖boundedProduct w a - 1‖ ≤ ∑ e, ‖w e ^ (a e).val - 1‖ :=
      norm_prod_sub_one_le Finset.univ _ (by simp [norm_pow, hw])
    _ ≤ ∑ e, ((a e).val : ℝ) * ‖w e - 1‖ :=
      Finset.sum_le_sum (fun e _ => norm_pow_sub_one_le _ (hw e) _)
    _ ≤ ∑ e, ((q - 1 : ℕ) : ℝ) * ‖w e - 1‖ := by
      apply Finset.sum_le_sum
      intro e _
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact_mod_cast Nat.le_sub_one_of_lt (a e).isLt
    _ = rotationBudget q w := by rw [rotationBudget, Finset.mul_sum]

def boundedCopy {I E : Type*} [Fintype E] {q : ℕ}
    (b : I → ℂ) (w : E → ℂ) (x : I × (E → Fin q)) : ℂ :=
  b x.1 * boundedProduct w x.2

theorem boundedCopy_injective {I E : Type*} [Fintype E] {q : ℕ}
    (b : I → ℂ) (w : E → ℂ) (hb : ∀ i, b i ≠ 0)
    (hn : Function.Injective (fun i => ‖b i‖)) (hw : ∀ e, ‖w e‖ = 1)
    (hprod : Function.Injective (boundedProduct (q := q) w)) :
    Function.Injective (boundedCopy (q := q) b w) := by
  rintro ⟨i, a⟩ ⟨j, c⟩ he
  have hnorm := congrArg norm he
  simp only [boundedCopy, norm_mul, boundedProduct_norm w hw, mul_one] at hnorm
  have hij := hn hnorm
  subst j
  exact Prod.ext rfl (hprod (mul_left_cancel₀ (hb i) he))

theorem boundedCopy_support {I E : Type*} [Fintype E] {q : ℕ}
    (b : I → ℂ) (w : E → ℂ) (hb : ∀ i, b i ≠ 0)
    (hn : Function.Injective (fun i => ‖b i‖)) (hb1 : ∀ i, ‖b i‖ ≤ 1)
    (hw : ∀ e, ‖w e‖ = 1) (hprod : Function.Injective (boundedProduct (q := q) w))
    (hs : ∀ i j, i ≠ j → support (b i) (b j) < -2 * rotationBudget q w)
    (x y : I × (E → Fin q)) (hne : x ≠ y) :
    support (boundedCopy b w x) (boundedCopy b w y) < 0 := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, c⟩
  by_cases hij : i = j
  · subst j
    apply support_negative_of_equal_norm
    · exact (boundedCopy_injective b w hb hn hw hprod).ne hne
    · simp only [boundedCopy, norm_mul, boundedProduct_norm w hw]
  · have hh := rotated_support_bound (hb1 i) (hb1 j)
      (boundedProduct_norm w hw a) (boundedProduct_norm w hw c)
      (boundedProduct_close w hw a) (boundedProduct_close w hw c)
    dsimp [boundedCopy]
    linarith [hs i j hij]

theorem boundedCopy_displacement {I E : Type*} [Fintype E] {q : ℕ}
    (b : I → ℂ) (w : E → ℂ) (hb : ∀ i, ‖b i‖ ≤ 1)
    (hw : ∀ e, ‖w e‖ = 1) (x : I × (E → Fin q)) :
    ‖boundedCopy b w x - b x.1‖ ≤ rotationBudget q w := by
  rw [boundedCopy, ← mul_sub_one, norm_mul]
  exact (mul_le_mul (hb _) (boundedProduct_close w hw _) (norm_nonneg _)
    (by norm_num)).trans_eq (one_mul _)

def boundedSet {I E : Type*} [Fintype I] [Fintype E] {q : ℕ}
    (b : I → ℂ) (w : E → ℂ) : Finset ℂ := by
  classical
  exact Finset.univ.image (boundedCopy (q := q) b w)

theorem boundedSet_card {I E : Type*} [Fintype I] [Fintype E] {q : ℕ}
    (b : I → ℂ) (w : E → ℂ) (hi : Function.Injective (boundedCopy (q := q) b w)) :
    (boundedSet (q := q) b w).card = Fintype.card I * q ^ Fintype.card E := by
  classical
  rw [boundedSet, Finset.card_image_of_injective _ hi]
  simp

def exponentDifference {E : Type*} {q : ℕ} (a b : E → Fin q) (e : E) : ℝ :=
  ((a e).val : ℝ) - (b e).val

theorem exponentDifference_nonzero {E : Type*} {q : ℕ} {a b : E → Fin q}
    (hne : a ≠ b) : ∃ e, exponentDifference a b e ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  funext e
  apply Fin.ext
  have hh := sub_eq_zero.mp (h e)
  exact_mod_cast hh

def boundedPhase {L P E : Type*} [Fintype E] {q : ℕ}
    (l : E → L) (p : E → P) (θ : E → ℝ) (a : E → Fin q)
    (z : (L → ℝ) × (P → ℝ)) : ℝ :=
  ∑ e, ((a e).val : ℝ) * (θ e - chordAngle (z.1 (l e)) (z.2 (p e)))

theorem boundedProduct_phase {L P E : Type*} [Fintype E] {q : ℕ}
    (l : E → L) (p : E → P) (θ : E → ℝ) (z : (L → ℝ) × (P → ℝ))
    (a : E → Fin q) :
    boundedProduct (phaseRotations l p θ z) a =
      Complex.exp ((boundedPhase l p θ a z : ℂ) * Complex.I) := by
  unfold boundedProduct phaseRotations boundedPhase
  simp_rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Finset.sum_mul,
    mul_assoc]

theorem boundedPhase_difference {L P E : Type*} [Fintype E] {q : ℕ}
    (l : E → L) (p : E → P) (θ : E → ℝ) (a b : E → Fin q)
    (z : (L → ℝ) × (P → ℝ)) :
    boundedPhase l p θ a z - boundedPhase l p θ b z =
      (∑ e, exponentDifference a b e * θ e) - edgeAngleSum l p (exponentDifference a b) z := by
  simp only [boundedPhase, edgeAngleSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  unfold exponentDifference
  ring

open Set Filter
open scoped Topology

theorem bounded_products_separate {L P E : Type*} [Fintype E] {q : ℕ}
    [DecidableEq L] [DecidableEq P] [DecidableEq E]
    (l : E → L) (p : E → P) (hij : Function.Injective (fun e => (l e, p e)))
    (θ : E → ℝ) (U : Set ((L → ℝ) × (P → ℝ))) (hU : IsOpen U) (hne : U.Nonempty)
    (hnz : ∀ z ∈ U, (∀ i, z.1 i ≠ 0) ∧ (∀ j, z.2 j ≠ 0))
    (hf : ∀ e, ∀ z ∈ U, ChordFeasible (z.1 (l e)) (z.2 (p e)))
    (a b : E → Fin q) (hab : a ≠ b) :
    ∃ z ∈ U, boundedProduct (phaseRotations l p θ z) a ≠
      boundedProduct (phaseRotations l p θ z) b := by
  by_contra hnone
  push Not at hnone
  obtain ⟨e, he⟩ := exponentDifference_nonzero hab
  obtain ⟨z₀, hz₀⟩ := hne
  let φ := fun z => boundedPhase l p θ a z - boundedPhase l p θ b z
  have hφ : ∀ z, φ z = (∑ e, exponentDifference a b e * θ e) -
      edgeAngleSum l p (exponentDifference a b) z := boundedPhase_difference l p θ a b
  have hc : ContinuousOn φ U := by
    intro z hz
    have hh : ContinuousAt (fun z => (∑ e, exponentDifference a b e * θ e) -
        edgeAngleSum l p (exponentDifference a b) z) z := continuousAt_const.sub
      (edge_angles_continuousAt l p (exponentDifference a b) z (hnz z hz).1 (hnz z hz).2)
    simpa only [show φ = fun z => (∑ e, exponentDifference a b e * θ e) -
      edgeAngleSum l p (exponentDifference a b) z from funext hφ] using hh.continuousWithinAt
  have hexp : ∀ z ∈ U, Complex.exp ((φ z : ℂ) * Complex.I) = 1 := by
    intro z hz
    dsimp [φ]
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, ← boundedProduct_phase,
      ← boundedProduct_phase, hnone z hz]
    apply div_self
    rw [boundedProduct_phase]
    exact Complex.exp_ne_zero _
  let V := U ∩ (fun z => |φ z - φ z₀|) ⁻¹' Iio Real.pi
  have hVo : IsOpen V :=
    (hc.sub continuousOn_const).abs.isOpen_inter_preimage hU isOpen_Iio
  have hVne : V.Nonempty := ⟨z₀, hz₀, by simpa using Real.pi_pos⟩
  have hVU : V ⊆ U := inter_subset_left
  have hconst : ∀ z ∈ V, edgeAngleSum l p (exponentDifference a b) z =
      (∑ e, exponentDifference a b e * θ e) - φ z₀ := by
    intro z hz
    have hh : φ z = φ z₀ := exp_phase_small_injective hz.2
      ((hexp z (hVU hz)).trans (hexp z₀ hz₀).symm)
    rw [hφ] at hh
    linarith
  obtain ⟨z, hz, hh⟩ := edge_angle_sum_not_constant l p hij (exponentDifference a b) e he
    V hVo hVne (fun z hz => hf e z (hVU hz))
    ((∑ e, exponentDifference a b e * θ e) - φ z₀)
  exact hh (hconst z hz)

theorem exists_injective_boundedProducts {L P E : Type*} [Fintype E] (q : ℕ)
    [DecidableEq L] [DecidableEq P] [DecidableEq E]
    (l : E → L) (p : E → P) (hij : Function.Injective (fun e => (l e, p e)))
    (θ : E → ℝ) (U : Set ((L → ℝ) × (P → ℝ))) (hU : IsOpen U) (hne : U.Nonempty)
    (hnz : ∀ z ∈ U, (∀ i, z.1 i ≠ 0) ∧ (∀ j, z.2 j ≠ 0))
    (hf : ∀ e, ∀ z ∈ U, ChordFeasible (z.1 (l e)) (z.2 (p e))) :
    ∃ z ∈ U, Function.Injective (boundedProduct (q := q) (phaseRotations l p θ z)) := by
  classical
  let K := {ab : (E → Fin q) × (E → Fin q) // ab.1 ≠ ab.2}
  let f := fun (k : K) (z : (L → ℝ) × (P → ℝ)) =>
    boundedProduct (phaseRotations l p θ z) k.val.1 -
      boundedProduct (phaseRotations l p θ z) k.val.2
  have hc : ∀ k, ContinuousOn (f k) U := by
    intro k z hz
    have hrot := phaseRotations_continuousAt l p θ z (hnz z hz).1 (hnz z hz).2
    apply ContinuousAt.continuousWithinAt
    unfold f boundedProduct
    fun_prop
  have hnc : ∀ k, ∀ V : Set ((L → ℝ) × (P → ℝ)),
      V ⊆ U → IsOpen V → V.Nonempty → ∃ z ∈ V, f k z ≠ 0 := by
    intro k V hVU hVo hVne
    obtain ⟨z, hz, hh⟩ := bounded_products_separate l p hij θ V hVo hVne
      (fun z hz => hnz z (hVU hz)) (fun e z hz => hf e z (hVU hz))
      k.val.1 k.val.2 k.property
    exact ⟨z, hz, sub_ne_zero.mpr hh⟩
  obtain ⟨z, hz, hh⟩ := finite_avoidance f U hU hne hc hnc Finset.univ
  refine ⟨z, hz, ?_⟩
  intro a b heq
  by_contra hab
  exact hh (⟨(a, b), hab⟩ : K) (Finset.mem_univ _) (sub_eq_zero.mpr heq)

end
end Proof

end Combined_GeneralProducts

/-! ## Source: BoundedCounting.lean -/

section Combined_BoundedCounting

/-! The exact number of distinct lifted unit edges for bounded exponents. -/

namespace Proof
noncomputable section

def incrementExponent {E : Type*} [DecidableEq E] {q : ℕ}
    (a : E → Fin q) (e : E) (h : (a e).val + 1 < q) : E → Fin q :=
  Function.update a e ⟨(a e).val + 1, h⟩

theorem boundedProduct_increment {E : Type*} [Fintype E] [DecidableEq E] {q : ℕ}
    (w : E → ℂ) (a : E → Fin q) (e : E) (h : (a e).val + 1 < q) :
    boundedProduct w (incrementExponent a e h) = boundedProduct w a * w e := by
  have he : ∀ f, w f ^ (incrementExponent a e h f).val =
      w f ^ (a f).val * (if f = e then w e else 1) := by
    intro f
    by_cases hf : f = e
    · subst f
      simp [incrementExponent, pow_succ]
    · simp [incrementExponent, Function.update_of_ne hf, hf]
  simp only [boundedProduct, he, Finset.prod_mul_distrib]
  simp

abbrev BoundedLiftedEdge (E : Type*) (q : ℕ) :=
  (e : E) × (Fin (q - 1) × ({f : E // f ≠ e} → Fin q))

def edgeExponent {E : Type*} [DecidableEq E] {q : ℕ}
    (e : E) (a : Fin (q - 1) × ({f : E // f ≠ e} → Fin q)) (f : E) : Fin q :=
  if h : f = e then ⟨a.1.val, by have := a.1.isLt; omega⟩ else a.2 ⟨f, h⟩

@[simp] theorem edgeExponent_self {E : Type*} [DecidableEq E] {q : ℕ}
    (e : E) (a : Fin (q - 1) × ({f : E // f ≠ e} → Fin q)) :
    (edgeExponent e a e).val = a.1.val := by simp [edgeExponent]

theorem edgeExponent_injective {E : Type*} [DecidableEq E] {q : ℕ} (e : E) :
    Function.Injective (edgeExponent (q := q) e) := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    simpa using congrArg (fun f => (f e).val) h
  · funext f
    have hh := congrFun h f.val
    simpa [edgeExponent, f.property] using hh

theorem edgeExponent_succ_lt {E : Type*} [DecidableEq E] {q : ℕ}
    (e : E) (a : Fin (q - 1) × ({f : E // f ≠ e} → Fin q)) :
    (edgeExponent e a e).val + 1 < q := by
  rw [edgeExponent_self]
  have := a.1.isLt
  omega

theorem boundedLiftedEdge_card {E : Type*} [Fintype E] [DecidableEq E] (q : ℕ) :
    Fintype.card (BoundedLiftedEdge E q) =
      Fintype.card E * (q - 1) * q ^ (Fintype.card E - 1) := by
  simp [BoundedLiftedEdge, Fintype.card_sigma, mul_assoc]

def boundedLiftedPair {L P E : Type*} [Fintype E] [DecidableEq E] {q : ℕ}
    (l : E → L) (p : E → P) (b : L ⊕ P → ℂ) (w : E → ℂ)
    (x : BoundedLiftedEdge E q) : Sym2 ℂ :=
  s(boundedCopy b w (Sum.inl (l x.1), edgeExponent x.1 x.2),
    boundedCopy b w (Sum.inr (p x.1),
      incrementExponent (edgeExponent x.1 x.2) x.1 (edgeExponent_succ_lt x.1 x.2)))

theorem boundedLiftedPair_injective {L P E : Type*} [Fintype E] [DecidableEq E] {q : ℕ}
    (l : E → L) (p : E → P) (b : L ⊕ P → ℂ) (w : E → ℂ)
    (he : Function.Injective (fun e => (l e, p e)))
    (hinj : Function.Injective (boundedCopy (q := q) b w)) :
    Function.Injective (boundedLiftedPair (q := q) l p b w) := by
  rintro ⟨e, a⟩ ⟨f, c⟩ hh
  simp only [boundedLiftedPair, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hh
  rcases hh with ⟨hl, hp⟩ | ⟨hl, _⟩
  · have hl := hinj hl
    have hp := hinj hp
    have hef := he (Prod.ext (Sum.inl.inj (congrArg Prod.fst hl))
      (Sum.inr.inj (congrArg Prod.fst hp)))
    subst f
    have hac := edgeExponent_injective e (congrArg Prod.snd hl)
    subst c
    rfl
  · have hbad := congrArg Prod.fst (hinj hl)
    cases hbad

theorem mem_boundedSet {I E : Type*} [Fintype I] [Fintype E] {q : ℕ}
    (b : I → ℂ) (w : E → ℂ) (x : I × (E → Fin q)) :
    boundedCopy b w x ∈ boundedSet (q := q) b w := by
  classical
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

theorem boundedCopy_unit_edge {I E : Type*} [Fintype E] [DecidableEq E] {q : ℕ}
    (b : I → ℂ) (w : E → ℂ) (hw : ∀ e, ‖w e‖ = 1)
    (i j : I) (e : E) (he : ‖b i - b j * w e‖ = 1)
    (a : E → Fin q) (h : (a e).val + 1 < q) :
    dist (boundedCopy b w (i, a)) (boundedCopy b w (j, incrementExponent a e h)) = 1 := by
  simp only [boundedCopy, boundedProduct_increment, dist_eq_norm]
  rw [show b i * boundedProduct w a - b j * (boundedProduct w a * w e) =
    (b i - b j * w e) * boundedProduct w a by ring]
  rw [norm_mul, he, boundedProduct_norm w hw, one_mul]

theorem boundedLiftedPair_mem_unitPairs {L P E : Type*}
    [Fintype L] [Fintype P] [Fintype E] [DecidableEq E] {q : ℕ}
    (l : E → L) (p : E → P) (b : L ⊕ P → ℂ) (w : E → ℂ)
    (hw : ∀ e, ‖w e‖ = 1)
    (hedge : ∀ e, ‖b (Sum.inl (l e)) - b (Sum.inr (p e)) * w e‖ = 1)
    (x : BoundedLiftedEdge E q) :
    boundedLiftedPair l p b w x ∈ unitPairs (boundedSet (q := q) b w) := by
  classical
  apply mk_mem_unitPairs.mpr
  exact ⟨mem_boundedSet b w _, mem_boundedSet b w _,
    boundedCopy_unit_edge b w hw _ _ x.1 (hedge x.1) _ _⟩

theorem bounded_amplification_unitPairs_bound {L P E : Type*}
    [Fintype L] [Fintype P] [Fintype E] [DecidableEq E] {q : ℕ}
    (l : E → L) (p : E → P) (b : L ⊕ P → ℂ) (w : E → ℂ)
    (he : Function.Injective (fun e => (l e, p e)))
    (hinj : Function.Injective (boundedCopy (q := q) b w)) (hw : ∀ e, ‖w e‖ = 1)
    (hedge : ∀ e, ‖b (Sum.inl (l e)) - b (Sum.inr (p e)) * w e‖ = 1) :
    Fintype.card E * (q - 1) * q ^ (Fintype.card E - 1) ≤
      (unitPairs (boundedSet (q := q) b w)).card := by
  let f : BoundedLiftedEdge E q → unitPairs (boundedSet (q := q) b w) :=
    fun x => ⟨boundedLiftedPair l p b w x, boundedLiftedPair_mem_unitPairs l p b w hw hedge x⟩
  have hf : Function.Injective f := fun x y h =>
    boundedLiftedPair_injective l p b w he hinj (congrArg Subtype.val h)
  simpa only [boundedLiftedEdge_card, Fintype.card_coe] using Fintype.card_le_of_injective f hf

end
end Proof

end Combined_BoundedCounting

/-! ## Source: MiddleLevels.lean -/

section Combined_MiddleLevels

/-! The middle-levels incidence graph and its powers-of-five seed pattern. -/

namespace Proof
noncomputable section

abbrev MiddleLower (d : ℕ) := {A : Finset (Fin (2 * d - 1)) // A.card = d - 1}
abbrev MiddleUpper (d : ℕ) := {B : Finset (Fin (2 * d - 1)) // B.card = d}
abbrev MiddleEdge (d : ℕ) := (B : MiddleUpper d) × {j : Fin (2 * d - 1) // j ∈ B.val}

def middlePoint {d : ℕ} (e : MiddleEdge d) : MiddleUpper d := e.1

def middleLine {d : ℕ} (e : MiddleEdge d) : MiddleLower d :=
  ⟨e.1.val.erase e.2.val, by rw [Finset.card_erase_of_mem e.2.property, e.1.property]⟩

theorem middle_endpoints_injective (d : ℕ) :
    Function.Injective (fun e : MiddleEdge d => (middleLine e, middlePoint e)) := by
  rintro ⟨B, j⟩ ⟨C, k⟩ h
  have hBC : B = C := congrArg Prod.snd h
  subst C
  have hjk : j = k := by
    apply Subtype.ext
    exact (Finset.erase_inj B.val j.property).mp (congrArg (fun z => z.1.val) h)
  subst k
  rfl

theorem finite_layer_card (n r : ℕ) :
    Fintype.card {A : Finset (Fin n) // A.card = r} = n.choose r := by
  classical
  rw [Fintype.card_of_subtype (Finset.univ.powersetCard r)
    (fun A => by simp [Finset.mem_powersetCard])]
  simp [Finset.card_powersetCard]

theorem middleLower_card (d : ℕ) :
    Fintype.card (MiddleLower d) = (2 * d - 1).choose (d - 1) := finite_layer_card _ _

theorem middleUpper_card (d : ℕ) :
    Fintype.card (MiddleUpper d) = (2 * d - 1).choose d := finite_layer_card _ _

theorem middle_layers_equal {d : ℕ} (hd : 1 ≤ d) :
    (2 * d - 1).choose (d - 1) = (2 * d - 1).choose d :=
  Nat.choose_symm_of_eq_add (by omega)

def middleVertexCount (d : ℕ) : ℕ := (2 * d).choose d
def middleEdgeCount (d : ℕ) : ℕ := d * (2 * d - 1).choose d
def finiteSize (d q : ℕ) : ℕ := middleVertexCount d * q ^ middleEdgeCount d

theorem middleVertex_card {d : ℕ} (hd : 1 ≤ d) :
    Fintype.card (MiddleLower d ⊕ MiddleUpper d) = middleVertexCount d := by
  rw [Fintype.card_sum, middleLower_card, middleUpper_card]
  unfold middleVertexCount
  have h := Nat.choose_succ_succ' (2 * d - 1) (d - 1)
  simpa only [Nat.sub_add_cancel hd, Nat.sub_add_cancel (by omega : 1 ≤ 2 * d)] using h.symm

theorem middleEdge_card (d : ℕ) : Fintype.card (MiddleEdge d) = middleEdgeCount d := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  simp_rw [show ∀ B : MiddleUpper d, B.val.card = d from fun B => B.property]
  simp [middleUpper_card, middleEdgeCount, mul_comm]

theorem middleVertexCount_eq_twice {d : ℕ} (hd : 1 ≤ d) :
    middleVertexCount d = 2 * (2 * d - 1).choose d := by
  rw [← middleVertex_card hd, Fintype.card_sum, middleLower_card, middleUpper_card,
    middle_layers_equal hd]
  omega

theorem middleEdgeCount_twice {d : ℕ} (hd : 1 ≤ d) :
    2 * middleEdgeCount d = d * middleVertexCount d := by
  rw [middleVertexCount_eq_twice hd, middleEdgeCount]
  ring

theorem middleEdgeCount_formula {d : ℕ} (hd : 1 ≤ d) :
    middleEdgeCount d = d * (2 * d).choose d / 2 := by
  have h := middleEdgeCount_twice hd
  change 2 * middleEdgeCount d = d * (2 * d).choose d at h
  omega

theorem middleVertexCount_pos (d : ℕ) : 0 < middleVertexCount d := by
  exact Nat.choose_pos (by omega)

theorem middleEdgeCount_pos {d : ℕ} (hd : 1 ≤ d) : 0 < middleEdgeCount d := by
  exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))

theorem finiteSize_pos {d q : ℕ} (hq : 1 ≤ q) : 0 < finiteSize d q :=
  Nat.mul_pos (middleVertexCount_pos d) (pow_pos (by omega) _)

def finiteDigits {n : ℕ} (A : Finset (Fin n)) : Finset ℕ :=
  A.map ⟨Fin.val, Fin.val_injective⟩

theorem finiteDigits_injective (n : ℕ) : Function.Injective (@finiteDigits n) :=
  Finset.map_injective _

def middleX {n : ℕ} (A : Finset (Fin n)) : ℝ := digitSum 5 (finiteDigits A)
def middleT {n : ℕ} (A : Finset (Fin n)) : ℝ := 1 + digitSum 25 (finiteDigits A)

theorem middleT_pos {n : ℕ} (A : Finset (Fin n)) : 0 < middleT A := by
  have h : 0 ≤ digitSum 25 (finiteDigits A) := Finset.sum_nonneg (fun _ _ => by positivity)
  dsimp [middleT]
  linarith

theorem middleT_injective (n : ℕ) : Function.Injective (@middleT n) := by
  intro A B h
  by_contra hne
  have hh := (digit_separation ((finiteDigits_injective n).ne hne)).2.1
  apply hh
  dsimp [middleT] at h
  linarith

theorem middle_digit_margin {n : ℕ} {A B : Finset (Fin n)} (hne : A ≠ B) :
    -(middleX B - middleX A) ^ 2 / 2 - (middleT B - middleT A) / 4 < 0 ∧
    -(middleX B - middleX A) ^ 2 / 2 + (middleT B - middleT A) / 4 < 0 := by
  obtain ⟨hX, _, hsep⟩ := digit_separation ((finiteDigits_injective n).ne hne.symm)
  have hm := signed_digit_margin hsep
  have hsq : 0 < (digitSum 5 (finiteDigits B) - digitSum 5 (finiteDigits A)) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hX)
  dsimp [middleX, middleT]
  constructor <;> nlinarith [hm.1, hm.2]

theorem middle_incidence_digits {d : ℕ} (e : MiddleEdge d) :
    middleX e.1.val - middleX (middleLine e).val = (5 : ℝ) ^ e.2.val.val ∧
    middleT e.1.val - middleT (middleLine e).val = ((5 : ℝ) ^ e.2.val.val) ^ 2 := by
  have he : finiteDigits e.1.val = insert e.2.val.val (finiteDigits (middleLine e).val) := by
    calc
      finiteDigits e.1.val = finiteDigits (insert e.2.val (middleLine e).val) :=
        congrArg finiteDigits (Finset.insert_erase e.2.property).symm
      _ = _ := Finset.map_insert _ _ _
  have hne : e.2.val.val ∉ finiteDigits (middleLine e).val := by
    simp [finiteDigits, middleLine]
  constructor
  · simp [middleX, he, digitSum, Finset.sum_insert hne]
  · simp only [middleT, he, digitSum, Finset.sum_insert hne]
    have hp : (25 : ℝ) ^ e.2.val.val = ((5 : ℝ) ^ e.2.val.val) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm e.2.val.val 2, pow_mul]
      norm_num
    linarith

def middlePattern (d : ℕ) : SeedPattern (MiddleLower d) (MiddleUpper d) (MiddleEdge d) where
  line := middleLine
  point := middlePoint
  endpoints_injective := middle_endpoints_injective d
  LX A := middleX A.val
  LT A := middleT A.val
  PX B := middleX B.val
  PT B := middleT B.val
  LT_pos A := middleT_pos A.val
  PT_pos B := middleT_pos B.val
  LT_injective := fun A B h => Subtype.ext (middleT_injective _ h)
  PT_injective := fun A B h => Subtype.ext (middleT_injective _ h)
  line_margin A B h := (middle_digit_margin (fun he => h (Subtype.ext he))).1
  point_margin A B h := (middle_digit_margin (fun he => h (Subtype.ext he))).2
  edge_positive e := by
    have hh := (middle_incidence_digits e).1
    have hp : 0 < (5 : ℝ) ^ e.2.val.val := by positivity
    change middleX (middleLine e).val < middleX e.1.val
    linarith
  edge_identity e := by
    change middleT e.1.val - middleT (middleLine e).val =
      (middleX e.1.val - middleX (middleLine e).val) ^ 2
    rw [(middle_incidence_digits e).1, (middle_incidence_digits e).2]

end
end Proof

end Combined_MiddleLevels

/-! ## Source: LocalizedSeeds.lean -/

section Combined_LocalizedSeeds

/-! Seed preparation with an arbitrary exponent bound and prescribed localization. -/

namespace Proof
noncomputable section
open Set Filter
open scoped Topology

def seedCenter {L P : Type*} : L ⊕ P → ℂ :=
  Sum.elim (fun _ => ⟨0, -1 / 2⟩) (fun _ => ⟨0, 1 / 2⟩)

theorem SeedPattern.base_zero {L P E : Type*} (S : SeedPattern L P E) (i : L ⊕ P) :
    S.base 0 i = seedCenter i := by
  cases i <;> simp [SeedPattern.base, lineSeed, pointSeed, seedCenter]

structure LocalPreparedSeed {L P E : Type*} [Fintype E]
    (l : E → L) (p : E → P) (q : ℕ) (η : ℝ) where
  seed : PreparedSeed l p
  support_margin : ∀ i j, i ≠ j →
    support (seed.base i) (seed.base j) < -2 * rotationBudget q seed.rotation
  localized : ∀ i, ‖seed.base i - seedCenter i‖ + rotationBudget q seed.rotation < η

theorem SeedPattern.exists_local_prepared {L P E : Type*}
    [Fintype L] [Fintype P] [Fintype E] (S : SeedPattern L P E)
    (q : ℕ) (hq : 2 ≤ q) (η : ℝ) (hη : 0 < η) :
    Nonempty (LocalPreparedSeed S.line S.point q η) := by
  let A := fun ε : ℝ => 2 * ((q - 1 : ℕ) : ℝ) * ∑ e, ‖S.coeff ε e‖
  have hcoeff : ∀ e, ContinuousAt (fun ε => S.coeff ε e) 0 := S.coeff_continuous
  have hA : ContinuousAt A 0 := by unfold A; fun_prop
  have hbase : ∀ i, Continuous (fun ε => S.base ε i) := by
    intro i
    cases i with
    | inl l => exact continuous_lineSeed _ _
    | inr p => exact continuous_pointSeed _ _
  have hbase0 : ∀ i, ‖S.base 0 i‖ = 1 / 2 := by
    intro i
    cases i <;> norm_num [SeedPattern.base, lineSeed, pointSeed, Complex.norm_def, Complex.normSq_apply]
  have hbounds : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.base ε i ≠ 0 ∧ ‖S.base ε i‖ < 1 := by
    intro i
    have hlo : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < ‖S.base ε i‖ :=
      continuousAt_const.eventually_lt (hbase i).norm.continuousAt (by rw [hbase0]; norm_num)
    have hhi : ∀ᶠ ε in 𝓝 (0 : ℝ), ‖S.base ε i‖ < 1 :=
      (hbase i).norm.continuousAt.eventually_lt continuousAt_const (by rw [hbase0]; norm_num)
    filter_upwards [hlo.filter_mono nhdsWithin_le_nhds, hhi.filter_mono nhdsWithin_le_nhds] with ε hlo hhi
    exact ⟨norm_pos_iff.mp hlo, hhi⟩
  have hnorms : ∀ i j, ∀ᶠ ε in 𝓝[>] (0 : ℝ), i ≠ j → ‖S.base ε i‖ ≠ ‖S.base ε j‖ := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    cases i with
    | inl l =>
      cases j with
      | inl k =>
        have hk : l ≠ k := fun h => hij (congrArg Sum.inl h)
        exact (eventually_line_norm_ne _ _ _ _ (S.LT_injective.ne hk)).mono (fun _ h _ => h)
      | inr p =>
        exact (eventually_cross_norm_ne _ _ _ _ (S.LT_pos l) (S.PT_pos p)).mono (fun _ h _ => h)
    | inr p =>
      cases j with
      | inl l =>
        exact (eventually_cross_norm_ne _ _ _ _ (S.LT_pos l) (S.PT_pos p)).mono (fun _ h _ => h.symm)
      | inr r =>
        have hr : p ≠ r := fun h => hij (congrArg Sum.inr h)
        exact (eventually_point_norm_ne _ _ _ _ (S.PT_injective.ne hr)).mono (fun _ h _ => h)
  have hsupports : ∀ i j, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      i ≠ j → support (S.base ε i) (S.base ε j) < -ε ^ 3 * A ε := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    cases i with
    | inl l =>
      cases j with
      | inl k =>
        have hk : l ≠ k := fun h => hij (congrArg Sum.inl h)
        exact (eventually_line_support _ _ _ _ A hA (S.line_margin l k hk)).mono (fun _ h _ => h)
      | inr p =>
        exact (eventually_cross_support _ _ _ _ A hA).mono (fun _ h _ => h.1)
    | inr p =>
      cases j with
      | inl l =>
        exact (eventually_cross_support _ _ _ _ A hA).mono (fun _ h _ => h.2)
      | inr r =>
        have hr : p ≠ r := fun h => hij (congrArg Sum.inr h)
        exact (eventually_point_support _ _ _ _ A hA (S.point_margin p r hr)).mono (fun _ h _ => h)
  have hedges : ∀ e, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖S.rot ε e‖ = 1 ∧
      ‖S.base ε (Sum.inl (S.line e)) - S.base ε (Sum.inr (S.point e)) * S.rot ε e‖ = 1 ∧
      S.rot ε e - 1 = (ε : ℂ) ^ 3 * S.coeff ε e := fun e =>
    (seedCorrection_properties _ _ _ _ (S.edge_positive e) (S.edge_identity e)).filter_mono
      nhdsWithin_le_nhds
  have him : ∀ e, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (starRingEnd ℂ (S.base ε (Sum.inl (S.line e))) *
        S.base ε (Sum.inr (S.point e)) * S.rot ε e).im < 0 := fun e =>
    seedCorrection_im_negative _ _ _ _ (S.edge_positive e)
  have hlocal : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖S.base ε i - seedCenter i‖ + ε ^ 3 * A ε / 2 < η := by
    intro i
    have hc : ContinuousAt (fun ε => ‖S.base ε i - seedCenter i‖ + ε ^ 3 * A ε / 2) 0 := by
      fun_prop
    exact (hc.eventually_lt continuousAt_const (by simpa [S.base_zero] using hη)).filter_mono
      nhdsWithin_le_nhds
  have hbAll : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, S.base ε i ≠ 0 ∧ ‖S.base ε i‖ < 1 := by
    simpa only [eventually_all] using hbounds
  have hnAll : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j, i ≠ j → ‖S.base ε i‖ ≠ ‖S.base ε j‖ := by
    simpa only [eventually_all] using hnorms
  have hsAll : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j, i ≠ j →
      support (S.base ε i) (S.base ε j) < -ε ^ 3 * A ε := by
    simpa only [eventually_all] using hsupports
  have heAll : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ e,
      ‖S.rot ε e‖ = 1 ∧
      ‖S.base ε (Sum.inl (S.line e)) - S.base ε (Sum.inr (S.point e)) * S.rot ε e‖ = 1 ∧
      S.rot ε e - 1 = (ε : ℂ) ^ 3 * S.coeff ε e := by
    simpa only [eventually_all] using hedges
  have hiAll : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ e,
      (starRingEnd ℂ (S.base ε (Sum.inl (S.line e))) *
        S.base ε (Sum.inr (S.point e)) * S.rot ε e).im < 0 := by
    simpa only [eventually_all] using him
  have hlAll : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i,
      ‖S.base ε i - seedCenter i‖ + ε ^ 3 * A ε / 2 < η := by
    simpa only [eventually_all] using hlocal
  obtain ⟨ε, hb, hn, hs, he, hi, hl, hε⟩ :=
    (hbAll.and (hnAll.and (hsAll.and (heAll.and (hiAll.and (hlAll.and self_mem_nhdsWithin)))))).exists
  have hε : 0 < ε := hε
  have hsum : 2 * rotationBudget q (S.rot ε) = ε ^ 3 * A ε := by
    unfold rotationBudget
    simp_rw [fun e => (he e).2.2, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε]
    rw [← Finset.mul_sum]
    dsimp [A]
    ring
  have hsup : ∀ i j, i ≠ j →
      support (S.base ε i) (S.base ε j) < -2 * rotationBudget q (S.rot ε) := by
    intro i j hij
    linarith [hs i j hij]
  let Q : PreparedSeed S.line S.point := {
    base := S.base ε
    rotation := S.rot ε
    base_ne_zero := fun i => (hb i).1
    base_norm_lt := fun i => (hb i).2
    radii_injective := fun i j hh => by_contra fun hij => hn i j hij hh
    rotation_norm := fun e => (he e).1
    unit_edge := fun e => (he e).2.1
    support_margin := by
      intro i j hij
      have hh := hsup i j hij
      have hK : (1 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ q - 1)
      have hnn : 0 ≤ ∑ e, ‖S.rot ε e - 1‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      unfold rotationBudget at hh
      nlinarith
    chord_im_negative := hi }
  refine ⟨⟨Q, hsup, ?_⟩⟩
  intro i
  change ‖S.base ε i - seedCenter i‖ + rotationBudget q (S.rot ε) < η
  linarith [hl i]

structure LocalSeparatedSeed {L P E : Type*} [Fintype E]
    (l : E → L) (p : E → P) (q : ℕ) (η : ℝ) where
  base : L ⊕ P → ℂ
  rotation : E → ℂ
  base_ne_zero : ∀ i, base i ≠ 0
  base_norm_lt : ∀ i, ‖base i‖ < 1
  radii_injective : Function.Injective (fun i => ‖base i‖)
  rotation_norm : ∀ e, ‖rotation e‖ = 1
  unit_edge : ∀ e, ‖base (Sum.inl (l e)) - base (Sum.inr (p e)) * rotation e‖ = 1
  support_margin : ∀ i j, i ≠ j → support (base i) (base j) < -2 * rotationBudget q rotation
  products_injective : Function.Injective (boundedProduct (q := q) rotation)
  localized : ∀ i, ‖base i - seedCenter i‖ + rotationBudget q rotation < η

theorem LocalPreparedSeed.exists_separated {L P E : Type*}
    [Fintype L] [Fintype P] [Fintype E] {l : E → L} {p : E → P} {q : ℕ} {η : ℝ}
    (R : LocalPreparedSeed l p q η) (hij : Function.Injective (fun e => (l e, p e))) :
    Nonempty (LocalSeparatedSeed l p q η) := by
  classical
  let Q := R.seed
  have hr : ∀ i, Q.radii.1 i ≠ 0 := fun i => norm_ne_zero_iff.mpr (Q.base_ne_zero _)
  have hs : ∀ j, Q.radii.2 j ≠ 0 := fun j => norm_ne_zero_iff.mpr (Q.base_ne_zero _)
  have hrot : ∀ e, ContinuousAt (fun z => phaseRotations l p Q.angles z e) Q.radii :=
    phaseRotations_continuousAt l p Q.angles Q.radii hr hs
  have hbase : ∀ i, ContinuousAt (fun z => Q.varBase z i) Q.radii :=
    fun i => (Q.varBase_continuous i).continuousAt
  have hH : ContinuousAt (fun z => rotationBudget q (phaseRotations l p Q.angles z)) Q.radii := by
    unfold rotationBudget
    fun_prop
  have hmargin : ∀ i j, ∀ᶠ z in 𝓝 Q.radii, i ≠ j →
      support (Q.varBase z i) (Q.varBase z j) < -2 * rotationBudget q (phaseRotations l p Q.angles z) := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    have hc : ContinuousAt (fun z => support (Q.varBase z i) (Q.varBase z j) +
        2 * rotationBudget q (phaseRotations l p Q.angles z)) Q.radii := by
      have hri := Complex.continuous_re.continuousAt.comp (hbase i)
      have hrj := Complex.continuous_re.continuousAt.comp (hbase j)
      have hii := Complex.continuous_im.continuousAt.comp (hbase i)
      have hij := Complex.continuous_im.continuousAt.comp (hbase j)
      unfold support
      exact ((hri.mul (hrj.sub hri)).add (hii.mul (hij.sub hii))).add
        (continuousAt_const.mul hH)
    have hvalue : support (Q.varBase Q.radii i) (Q.varBase Q.radii j) +
        2 * rotationBudget q (phaseRotations l p Q.angles Q.radii) < 0 := by
      rw [Q.varBase_at_radii, Q.phase_at_radii]
      linarith [R.support_margin i j hij]
    exact (hc.eventually_lt continuousAt_const hvalue).mono (fun _ hh _ => by linarith)
  have hlocal : ∀ i, ∀ᶠ z in 𝓝 Q.radii,
      ‖Q.varBase z i - seedCenter i‖ + rotationBudget q (phaseRotations l p Q.angles z) < η := by
    intro i
    have hc : ContinuousAt (fun z => ‖Q.varBase z i - seedCenter i‖ +
        rotationBudget q (phaseRotations l p Q.angles z)) Q.radii := by fun_prop
    apply hc.eventually_lt continuousAt_const
    rw [Q.varBase_at_radii, Q.phase_at_radii]
    exact R.localized i
  have hmAll : ∀ᶠ z in 𝓝 Q.radii, ∀ i j, i ≠ j →
      support (Q.varBase z i) (Q.varBase z j) < -2 * rotationBudget q (phaseRotations l p Q.angles z) := by
    simpa only [eventually_all] using hmargin
  have hlAll : ∀ᶠ z in 𝓝 Q.radii, ∀ i,
      ‖Q.varBase z i - seedCenter i‖ + rotationBudget q (phaseRotations l p Q.angles z) < η := by
    simpa only [eventually_all] using hlocal
  obtain ⟨U, hUgood, hU, hz₀⟩ := mem_nhds_iff.mp (Q.goodRadii_nhds.and (hmAll.and hlAll))
  have hne : U.Nonempty := ⟨Q.radii, hz₀⟩
  have hnz : ∀ z ∈ U, (∀ i, z.1 i ≠ 0) ∧ (∀ j, z.2 j ≠ 0) := by
    intro z hz
    exact ⟨fun i => ne_of_gt ((hUgood hz).1.1 (Sum.inl i)),
      fun j => ne_of_gt ((hUgood hz).1.1 (Sum.inr j))⟩
  obtain ⟨z, hz, hprod⟩ := exists_injective_boundedProducts q l p hij Q.angles U hU hne hnz
    (fun e z hz => (hUgood hz).1.2.2.2.1 e)
  obtain ⟨⟨hpos, hnorm, hinj, hfeas, _⟩, hmargin, hloc⟩ := hUgood hz
  have hrnorm : ∀ i, ‖Q.varBase z i‖ = joinedRadii z i :=
    radialBase_norm Q.base Q.base_ne_zero (joinedRadii z) (fun i => (hpos i).le)
  refine ⟨{
    base := Q.varBase z
    rotation := phaseRotations l p Q.angles z
    base_ne_zero := fun i => norm_pos_iff.mp (by rw [hrnorm]; exact hpos i)
    base_norm_lt := hnorm
    radii_injective := ?_
    rotation_norm := phaseRotations_norm l p Q.angles z
    unit_edge := fun e => Q.varBase_unit_edge z e (hfeas e)
    support_margin := hmargin
    products_injective := hprod
    localized := hloc }⟩
  intro i j hh
  dsimp only at hh
  rw [hrnorm, hrnorm] at hh
  exact hinj hh

end
end Proof

end Combined_LocalizedSeeds

/-! ## Source: FiniteConstruction.lean -/

section Combined_FiniteConstruction

/-! The full finite construction of Theorem 1.3. -/

namespace Proof
noncomputable section

def lowerCenter : ℂ := ⟨0, -1 / 2⟩
def upperCenter : ℂ := ⟨0, 1 / 2⟩
def twoDisks (η : ℝ) : Set ℂ := Metric.ball lowerCenter η ∪ Metric.ball upperCenter η

def RadialSupport (P : Finset ℂ) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, x ≠ y → support x y < 0

theorem RadialSupport.mono {P Q : Finset ℂ} (hP : RadialSupport P) (hQP : Q ⊆ P) :
    RadialSupport Q := fun x hx y hy hne => hP x (hQP hx) y (hQP hy) hne

theorem RadialSupport.convexIndependent {P : Finset ℂ} (hP : RadialSupport P) :
    ConvexIndependent ℝ (fun z : ↥(P : Set ℂ) => (z : ℂ)) := by
  apply convexIndependent_of_support
  intro x y hne
  exact hP x.val x.property y.val y.property (fun h => hne (Subtype.ext h))

theorem twoDisks_open (η : ℝ) : IsOpen (twoDisks η) :=
  Metric.isOpen_ball.union Metric.isOpen_ball

theorem SeedPattern.finite_construction {L R E : Type*}
    [Fintype L] [Fintype R] [Fintype E] (S : SeedPattern L R E)
    (q : ℕ) (hq : 2 ≤ q) (η : ℝ) (hη : 0 < η) :
    ∃ P : Finset ℂ,
      P.card = Fintype.card (L ⊕ R) * q ^ Fintype.card E ∧
      Fintype.card E * (q - 1) * q ^ (Fintype.card E - 1) ≤ (unitPairs P).card ∧
      RadialSupport P ∧ 0 ∉ P ∧ (P : Set ℂ) ⊆ twoDisks η := by
  classical
  obtain ⟨Q⟩ := S.exists_local_prepared q hq η hη
  obtain ⟨B⟩ := Q.exists_separated S.endpoints_injective
  let P := boundedSet (q := q) B.base B.rotation
  have hinj := boundedCopy_injective B.base B.rotation B.base_ne_zero B.radii_injective
    B.rotation_norm B.products_injective
  refine ⟨P, boundedSet_card B.base B.rotation hinj,
    bounded_amplification_unitPairs_bound S.line S.point B.base B.rotation
      S.endpoints_injective hinj B.rotation_norm B.unit_edge, ?_, ?_, ?_⟩
  · intro x hx y hy hne
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
    exact boundedCopy_support B.base B.rotation B.base_ne_zero B.radii_injective
      (fun i => (B.base_norm_lt i).le) B.rotation_norm B.products_injective B.support_margin
      a b (fun h => hne (congrArg (boundedCopy B.base B.rotation) h))
  · intro hz
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hz
    have hn : boundedProduct B.rotation a.2 ≠ 0 := norm_ne_zero_iff.mp
      (by rw [boundedProduct_norm B.rotation B.rotation_norm]; norm_num)
    exact mul_ne_zero (B.base_ne_zero a.1) hn ha
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    have hclose : ‖boundedCopy B.base B.rotation a - seedCenter a.1‖ < η := by
      have hd := boundedCopy_displacement B.base B.rotation (fun i => (B.base_norm_lt i).le)
        B.rotation_norm a
      have ht := norm_sub_le_norm_sub_add_norm_sub (boundedCopy B.base B.rotation a)
        (B.base a.1) (seedCenter a.1)
      linarith [B.localized a.1]
    cases h : a.1 with
    | inl l =>
      apply Or.inl
      simpa only [Metric.mem_ball, dist_eq_norm, h, seedCenter, Sum.elim_inl, lowerCenter] using hclose
    | inr r =>
      apply Or.inr
      simpa only [Metric.mem_ball, dist_eq_norm, h, seedCenter, Sum.elim_inr, upperCenter] using hclose

/-- The finite theorem with an integer form of its edge-density bound. -/
theorem finite_construction (d q : ℕ) (hd : 2 ≤ d) (hq : 2 ≤ q)
    (η : ℝ) (hη : 0 < η) :
    ∃ P : Finset ℂ,
      P.card = finiteSize d q ∧ d * (q - 1) * P.card ≤ 2 * q * (unitPairs P).card ∧
      RadialSupport P ∧ 0 ∉ P ∧ (P : Set ℂ) ⊆ twoDisks η := by
  obtain ⟨P, hc, he, hs, hn, hl⟩ := (middlePattern d).finite_construction q hq η hη
  simp only [middleVertex_card (by omega : 1 ≤ d), middleEdge_card] at hc he
  refine ⟨P, hc, ?_, hs, hn, hl⟩
  have hm : 1 ≤ middleEdgeCount d := middleEdgeCount_pos (by omega)
  have hpow : q ^ middleEdgeCount d = q * q ^ (middleEdgeCount d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hm]
  calc
    d * (q - 1) * P.card =
        2 * q * (middleEdgeCount d * (q - 1) * q ^ (middleEdgeCount d - 1)) := by
      calc
        _ = (d * middleVertexCount d) * (q - 1) * q * q ^ (middleEdgeCount d - 1) := by
          rw [hc, hpow]
          ring
        _ = _ := by rw [← middleEdgeCount_twice (by omega : 1 ≤ d)]; ring
    _ ≤ 2 * q * (unitPairs P).card := Nat.mul_le_mul_left _ he

/-- Theorem 1.3 in the manuscript's real-valued notation. -/
theorem finite_construction_real (d q : ℕ) (hd : 2 ≤ d) (hq : 2 ≤ q)
    (η : ℝ) (hη : 0 < η) :
    ∃ P : Finset ℂ,
      P.card = finiteSize d q ∧
      (d : ℝ) / 2 * (1 - 1 / (q : ℝ)) * P.card ≤ (unitPairs P).card ∧
      RadialSupport P ∧ 0 ∉ P ∧ (P : Set ℂ) ⊆ twoDisks η := by
  obtain ⟨P, hc, he, hs, hn, hl⟩ := finite_construction d q hd hq η hη
  refine ⟨P, hc, ?_, hs, hn, hl⟩
  have heR : (d : ℝ) * ((q - 1 : ℕ) : ℝ) * P.card ≤ 2 * q * (unitPairs P).card := by
    exact_mod_cast he
  rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] at heR
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 2 * q by positivity)).mp
  have hid : (2 * (q : ℝ)) * ((d : ℝ) / 2 * (1 - 1 / (q : ℝ)) * P.card) =
      (d : ℝ) * ((q : ℝ) - 1) * P.card := by
    field_simp [ne_of_gt hqR] <;> ring
  rw [hid]
  exact heR

end
end Proof

end Combined_FiniteConstruction

/-! ## Source: UnitGraph.lean -/

section Combined_UnitGraph

/-! Graph and finite-set counting tools for the prescribed-cardinality construction. -/

namespace Proof
noncomputable section
open Classical

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def unitDistanceGraph (P : Finset X) : SimpleGraph P where
  Adj x y := dist (x : X) (y : X) = 1
  symm := ⟨fun x y h => by simpa only [dist_comm] using h⟩
  loopless := ⟨fun x => by simp⟩

theorem unitDistanceGraph_degree (P : Finset X) (x : P) :
    (unitDistanceGraph P).degree x = unitDegree P x.val := by
  have he : ((unitDistanceGraph P).neighborFinset x).image Subtype.val = unitNeighbors P x.val := by
    ext y
    simp only [Finset.mem_image, mem_unitNeighbors]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, ((unitDistanceGraph P).mem_neighborFinset x z).mp hz⟩
    · rintro ⟨hy, hxy⟩
      exact ⟨⟨y, hy⟩, ((unitDistanceGraph P).mem_neighborFinset x ⟨y, hy⟩).mpr hxy, rfl⟩
  have hc := Finset.card_image_of_injective ((unitDistanceGraph P).neighborFinset x)
    (show Function.Injective (Subtype.val : P → X) from Subtype.val_injective)
  rw [he] at hc
  exact hc.symm

theorem unitDistanceGraph_edges (P : Finset X) :
    ((unitDistanceGraph P).edgeFinset).image (Sym2.map (Subtype.val : P → X)) = unitPairs P := by
  ext e
  induction e using Sym2.inductionOn with
  | hf x y =>
    rw [mk_mem_unitPairs]
    constructor
    · rintro he
      obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
      induction f using Sym2.inductionOn with
      | hf a b =>
        have hab : dist (a : X) (b : X) = 1 := by
          exact (SimpleGraph.mem_edgeSet (unitDistanceGraph P)).mp (SimpleGraph.mem_edgeFinset.mp hf)
        have hm : s(a.val, b.val) ∈ unitPairs P :=
          mk_mem_unitPairs.mpr ⟨a.property, b.property, hab⟩
        rw [show s(a.val, b.val) = s(x, y) from hfe] at hm
        exact mk_mem_unitPairs.mp hm
    · rintro ⟨hx, hy, hxy⟩
      apply Finset.mem_image.mpr
      refine ⟨s((⟨x, hx⟩ : P), (⟨y, hy⟩ : P)), ?_, rfl⟩
      exact SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet (unitDistanceGraph P)).mpr hxy)

theorem unitDistanceGraph_card_edges (P : Finset X) :
    (unitDistanceGraph P).edgeFinset.card = (unitPairs P).card := by
  rw [← unitDistanceGraph_edges, Finset.card_image_of_injective _
    (Sym2.map.injective (show Function.Injective (Subtype.val : P → X) from Subtype.val_injective))]

theorem sum_unitDegree (P : Finset X) :
    ∑ x ∈ P, unitDegree P x = 2 * (unitPairs P).card := by
  have h := (unitDistanceGraph P).sum_degrees_eq_twice_card_edges
  simp_rw [unitDistanceGraph_degree] at h
  rw [unitDistanceGraph_card_edges] at h
  simpa only [Finset.univ_eq_attach, Finset.sum_attach] using h

theorem exists_degree_le_average (P : Finset X) (hP : P.Nonempty) :
    ∃ x ∈ P, (unitDegree P x : ℝ) * P.card ≤ 2 * (unitPairs P).card := by
  by_contra h
  push Not at h
  have hsum : ∑ x ∈ P, (2 * ((unitPairs P).card : ℝ)) <
      ∑ x ∈ P, (unitDegree P x : ℝ) * P.card :=
    Finset.sum_lt_sum_of_nonempty hP (fun x hx => h x hx)
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, ← Nat.cast_sum, sum_unitDegree] at hsum
  push_cast at hsum
  nlinarith

theorem unitNeighbors_image_isometry (f : X → Y) (hf : Isometry f) (P : Finset X) (x : X) :
    unitNeighbors (P.image f) (f x) = (unitNeighbors P x).image f := by
  unfold unitNeighbors
  rw [Finset.filter_image]
  simp only [hf.dist_eq]

theorem unitDegree_image_isometry (f : X → Y) (hf : Isometry f) (P : Finset X) (x : X) :
    unitDegree (P.image f) (f x) = unitDegree P x := by
  rw [unitDegree, unitNeighbors_image_isometry f hf, Finset.card_image_of_injective _ hf.injective]
  rfl

theorem unitPairs_disjoint {P Q : Finset X} (h : Disjoint P Q) :
    Disjoint (unitPairs P) (unitPairs Q) := by
  apply Finset.disjoint_left.mpr
  intro e hp hq
  induction e using Sym2.inductionOn with
  | hf x y => exact Finset.disjoint_left.mp h (mk_mem_unitPairs.mp hp).1 (mk_mem_unitPairs.mp hq).1

theorem unitPairs_union_bound {P Q : Finset X} (h : Disjoint P Q) :
    (unitPairs P).card + (unitPairs Q).card ≤ (unitPairs (P ∪ Q)).card := by
  rw [← Finset.card_union_of_disjoint (unitPairs_disjoint h)]
  apply Finset.card_le_card
  exact Finset.union_subset (unitPairs_mono Finset.subset_union_left)
    (unitPairs_mono Finset.subset_union_right)

end
end Proof

end Combined_UnitGraph

/-! ## Source: RotatedCopies.lean -/

section Combined_RotatedCopies

/-! Arbitrarily small disjoint rotations preserving strict support (Lemma 4.2). -/

namespace Proof
noncomputable section
open Set Filter Classical
open scoped Topology

def rotate (θ : ℝ) (z : ℂ) : ℂ := z * Complex.exp ((θ : ℂ) * Complex.I)

theorem rotate_zero (z : ℂ) : rotate 0 z = z := by simp [rotate]

theorem rotate_norm (θ : ℝ) (z : ℂ) : ‖rotate θ z‖ = ‖z‖ := by
  rw [rotate, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem rotate_isometry (θ : ℝ) : Isometry (rotate θ) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [rotate, dist_eq_norm, ← sub_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem rotate_ne_zero (θ : ℝ) {z : ℂ} (hz : z ≠ 0) : rotate θ z ≠ 0 :=
  mul_ne_zero hz (Complex.exp_ne_zero _)

def rotatedUnion {I : Type*} [Fintype I] (A : I → Finset ℂ) (θ : I → ℝ) : Finset ℂ :=
  Finset.univ.biUnion (fun i => (A i).image (rotate (θ i)))

theorem small_rotations {I : Type*} [Fintype I] (Q : Finset ℂ)
    (hzero : 0 ∉ Q) (hQ : RadialSupport Q) (O : Set ℂ) (hO : IsOpen O)
    (hQO : (Q : Set ℂ) ⊆ O) (τ : ℝ) (hτ : 0 < τ) :
    ∃ θ : I → ℝ,
      (∀ i, |θ i| < τ) ∧
      Function.Injective (fun a : I × Q => rotate (θ a.1) a.2.val) ∧
      (∀ a b : I × Q, a ≠ b → support (rotate (θ a.1) a.2.val) (rotate (θ b.1) b.2.val) < 0) ∧
      (∀ a : I × Q, rotate (θ a.1) a.2.val ∈ O) := by
  let rank : I → ℝ := fun i => ((Fintype.equivFin I i).val : ℝ)
  have hrank : Function.Injective rank := by
    intro i j h
    apply (Fintype.equivFin I).injective
    apply Fin.ext
    dsimp [rank] at h
    exact_mod_cast h
  let F := fun (ε : ℝ) (a : I × Q) => rotate (ε * rank a.1) a.2.val
  have hF : ∀ a, Continuous (fun ε => F ε a) := by
    intro a
    unfold F rotate
    fun_prop
  have hF0 : ∀ a, F 0 a = a.2.val := fun a => by simp [F, rotate]
  have hsupport : ∀ a b : I × Q, ∀ᶠ ε in 𝓝 (0 : ℝ), a.2.val ≠ b.2.val →
      support (F ε a) (F ε b) < 0 := by
    intro a b
    by_cases hab : a.2.val = b.2.val
    · exact Eventually.of_forall (fun _ h => (h hab).elim)
    have hc : ContinuousAt (fun ε => support (F ε a) (F ε b)) 0 := by
      have ha := (hF a).continuousAt (x := 0)
      have hb := (hF b).continuousAt (x := 0)
      unfold support
      fun_prop
    have h0 : support (F 0 a) (F 0 b) < 0 := by
      rw [hF0, hF0]
      exact hQ _ a.2.property _ b.2.property hab
    exact (hc.eventually_lt continuousAt_const h0).mono (fun _ h _ => h)
  have hloc : ∀ a : I × Q, ∀ᶠ ε in 𝓝 (0 : ℝ), F ε a ∈ O := by
    intro a
    apply (hF a).continuousAt.eventually
    apply hO.mem_nhds
    change F 0 a ∈ O
    rw [hF0]
    exact hQO a.2.property
  have hphase : ∀ i j : I, ∀ᶠ ε in 𝓝 (0 : ℝ), |ε * rank i - ε * rank j| < Real.pi := by
    intro i j
    have hc : ContinuousAt (fun ε : ℝ => |ε * rank i - ε * rank j|) 0 := by fun_prop
    exact hc.eventually_lt continuousAt_const (by simpa using Real.pi_pos)
  have hsmall : ∀ i : I, ∀ᶠ ε in 𝓝 (0 : ℝ), |ε * rank i| < τ := by
    intro i
    have hc : ContinuousAt (fun ε : ℝ => |ε * rank i|) 0 := by fun_prop
    exact hc.eventually_lt continuousAt_const (by simpa using hτ)
  have hsAll : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ a b : I × Q, a.2.val ≠ b.2.val →
      support (F ε a) (F ε b) < 0 := by simpa only [eventually_all] using hsupport
  have hlAll : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ a : I × Q, F ε a ∈ O := by
    simpa only [eventually_all] using hloc
  have hpAll : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i j : I, |ε * rank i - ε * rank j| < Real.pi := by
    simpa only [eventually_all] using hphase
  have htAll : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : I, |ε * rank i| < τ := by
    simpa only [eventually_all] using hsmall
  obtain ⟨ε, ⟨hs, hl, hp, ht⟩, hε⟩ :=
    (((hsAll.and (hlAll.and (hpAll.and htAll))).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioi 0)).exists
  have hε : 0 < ε := hε
  have hinj : Function.Injective (F ε) := by
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    by_cases hxy : x = y
    · subst y
      have hx : (x : ℂ) ≠ 0 := fun h => hzero (h ▸ x.property)
      have hexp := mul_left_cancel₀ hx he
      have hangle := exp_phase_small_injective (hp i j) hexp
      exact Prod.ext (hrank (mul_left_cancel₀ (ne_of_gt hε) hangle)) rfl
    · have hn := hs (i, x) (j, y) (fun h => hxy (Subtype.ext h))
      rw [he] at hn
      simpa [support] using hn
  refine ⟨fun i => ε * rank i, ht, hinj, ?_, hl⟩
  intro a b hab
  by_cases hxy : a.2.val = b.2.val
  · apply support_negative_of_equal_norm (hinj.ne hab)
    change ‖rotate (ε * rank a.1) a.2.val‖ = ‖rotate (ε * rank b.1) b.2.val‖
    rw [rotate_norm, rotate_norm, hxy]
  · exact hs a b hxy

theorem small_rotated_copies {I : Type*} [Fintype I] (Q : Finset ℂ)
    (hzero : 0 ∉ Q) (hQ : RadialSupport Q) (O : Set ℂ) (hO : IsOpen O)
    (hQO : (Q : Set ℂ) ⊆ O) (A : I → Finset ℂ) (hA : ∀ i, A i ⊆ Q)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ θ : I → ℝ,
      (∀ i, |θ i| < τ) ∧
      Pairwise (fun i j => Disjoint ((A i).image (rotate (θ i))) ((A j).image (rotate (θ j)))) ∧
      RadialSupport (rotatedUnion A θ) ∧
      (rotatedUnion A θ : Set ℂ) ⊆ O ∧ 0 ∉ rotatedUnion A θ := by
  obtain ⟨θ, ht, hinj, hs, hl⟩ := small_rotations (I := I) Q hzero hQ O hO hQO τ hτ
  refine ⟨θ, ht, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro z hi hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hj
    have hh := hinj (a₁ := (j, ⟨y, hA j hy⟩)) (a₂ := (i, ⟨x, hA i hx⟩)) he
    exact hij (congrArg Prod.fst hh).symm
  · intro x hx y hy hxy
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, _, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    apply hs (i, ⟨a, hA i ha⟩) (j, ⟨b, hA j hb⟩)
    exact fun h => hxy (congrArg (fun a : I × Q => rotate (θ a.1) a.2.val) h)
  · intro x hx
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hl (i, ⟨a, hA i ha⟩)
  · intro hz
    obtain ⟨i, _, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hz
    exact rotate_ne_zero (θ i) (fun h => hzero (h ▸ hA i ha)) he

end
end Proof

end Combined_RotatedCopies

/-! ## Source: Gluing.lean -/

section Combined_Gluing

/-! Counting and minimum-degree bounds for unions of disjoint rotated copies. -/

namespace Proof
noncomputable section
open Classical

theorem rotatedUnion_card {I : Type*} [Fintype I] (A : I → Finset ℂ) (θ : I → ℝ)
    (hd : Pairwise (fun i j => Disjoint ((A i).image (rotate (θ i))) ((A j).image (rotate (θ j))))) :
    (rotatedUnion A θ).card = ∑ i, (A i).card := by
  rw [rotatedUnion, Finset.card_biUnion (fun i _ j _ hij => hd hij)]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.card_image_of_injective _ (rotate_isometry (θ i)).injective

theorem rotatedUnion_edges {I : Type*} [Fintype I] (A : I → Finset ℂ) (θ : I → ℝ)
    (hd : Pairwise (fun i j => Disjoint ((A i).image (rotate (θ i))) ((A j).image (rotate (θ j))))) :
    ∑ i, (unitPairs (A i)).card ≤ (unitPairs (rotatedUnion A θ)).card := by
  let U := fun i => unitPairs ((A i).image (rotate (θ i)))
  have hdu : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint U :=
    fun i _ j _ hij => unitPairs_disjoint (hd hij)
  have hsub : Finset.univ.biUnion U ⊆ unitPairs (rotatedUnion A θ) := by
    intro e he
    obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
    exact unitPairs_mono (Finset.subset_biUnion_of_mem
      (fun i => (A i).image (rotate (θ i))) hi) he
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdu] at hc
  simpa only [U, unitPairs_card_image_isometry _ (rotate_isometry _)] using hc

theorem rotatedUnion_degree {I : Type*} [Fintype I] (A : I → Finset ℂ) (θ : I → ℝ)
    (k : ℕ) (hk : ∀ i, HasUnitMinDegree (A i) k) : HasUnitMinDegree (rotatedUnion A θ) k := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hm := unitDegree_mono (Finset.subset_biUnion_of_mem
    (fun i => (A i).image (rotate (θ i))) hi) (rotate (θ i) a)
  rw [unitDegree_image_isometry _ (rotate_isometry _)] at hm
  exact (hk i a ha).trans hm

theorem glue_dense_copies {I : Type*} [Fintype I] (Q : Finset ℂ)
    (hzero : 0 ∉ Q) (hQ : RadialSupport Q) (η : ℝ)
    (hloc : (Q : Set ℂ) ⊆ twoDisks η) (A : I → Finset ℂ) (hA : ∀ i, A i ⊆ Q)
    (k : ℕ) (hk : ∀ i, HasUnitMinDegree (A i) k)
    (α : ℝ) (hα : ∀ i, α * (A i).card ≤ (unitPairs (A i)).card) :
    ∃ P : Finset ℂ, P.card = ∑ i, (A i).card ∧ RadialSupport P ∧
      0 ∉ P ∧ (P : Set ℂ) ⊆ twoDisks η ∧ HasUnitMinDegree P k ∧
      α * P.card ≤ (unitPairs P).card := by
  obtain ⟨θ, _, hd, hs, hl, hn⟩ := small_rotated_copies Q hzero hQ (twoDisks η)
    (twoDisks_open η) hloc A hA 1 (by norm_num)
  refine ⟨rotatedUnion A θ, rotatedUnion_card A θ hd, hs, hn, hl,
    rotatedUnion_degree A θ k hk, ?_⟩
  have he : (∑ i, ((unitPairs (A i)).card : ℝ)) ≤ (unitPairs (rotatedUnion A θ)).card := by
    exact_mod_cast rotatedUnion_edges A θ hd
  rw [rotatedUnion_card A θ hd, Nat.cast_sum, Finset.mul_sum]
  exact (Finset.sum_le_sum (fun i _ => hα i)).trans he

/-- Every sufficiently large integer is a nonnegative combination of two consecutive sizes. -/
theorem consecutive_sizes_representation (s n : ℕ) (hs : 2 ≤ s) (hn : s ^ 2 ≤ n) :
    ∃ a b : ℕ, n = a * s + b * (s - 1) := by
  let r := n % (s - 1)
  let t := n / (s - 1)
  have hs' : 0 < s - 1 := by omega
  have hr : r < s - 1 := Nat.mod_lt n hs'
  have ht : s ≤ t := (Nat.le_div_iff_mul_le hs').mpr
    ((Nat.mul_le_mul_left s (Nat.sub_le s 1)).trans (by simpa [pow_two] using hn))
  have hrt : r ≤ t := by omega
  refine ⟨r, t - r, ?_⟩
  have he : r + (s - 1) * t = n := Nat.mod_add_div n (s - 1)
  have hs1 : s - 1 + 1 = s := by omega
  calc
    n = r + (s - 1) * t := he.symm
    _ = r + (s - 1) * ((t - r) + r) := by rw [Nat.sub_add_cancel hrt]
    _ = r * (s - 1 + 1) + (t - r) * (s - 1) := by ring
    _ = r * s + (t - r) * (s - 1) := by rw [hs1]

end
end Proof

end Combined_Gluing

/-! ## Source: PrescribedCardinality.lean -/

section Combined_PrescribedCardinality

/-! Dense configurations of every sufficiently large prescribed cardinality (Proposition 4.3). -/

namespace Proof
noncomputable section
open Classical

theorem erase_low_degree_density (Q : Finset ℂ) (hQ : Q.Nonempty) (k : ℕ)
    (α : ℝ) (hα : (k : ℝ) < α) (hd : HasUnitMinDegree Q (k + 1))
    (hc : α * Q.card ≤ (unitPairs Q).card) :
    ∃ v ∈ Q, HasUnitMinDegree (Q.erase v) k ∧
      ((k : ℝ) - 1) * (Q.erase v).card ≤ (unitPairs (Q.erase v)).card := by
  obtain ⟨v, hv, havg⟩ := exists_degree_le_average Q hQ
  have hsize : k + 2 ≤ Q.card := by
    have hlo := hd v hv
    have hhi := unitDegree_lt_card hv
    omega
  have hsizeR : (k : ℝ) + 2 ≤ Q.card := by exact_mod_cast hsize
  have hspos : (0 : ℝ) < Q.card := by exact_mod_cast Finset.card_pos.mpr hQ
  have hs2 : (0 : ℝ) ≤ (Q.card : ℝ) - 2 := by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have hcard : ((Q.erase v).card : ℝ) = (Q.card : ℝ) - 1 := by
    have hh : ((Q.erase v).card : ℝ) + 1 = Q.card := by
      exact_mod_cast Finset.card_erase_add_one hv
    linarith
  have he : ((unitPairs (Q.erase v)).card : ℝ) + unitDegree Q v = (unitPairs Q).card := by
    exact_mod_cast unitPairs_erase_add_degree hv
  have heMul := congrArg (fun x : ℝ => x * (Q.card : ℝ)) he
  have hm := mul_le_mul_of_nonneg_right hc hs2
  have hremaining : α * Q.card * ((Q.card : ℝ) - 2) ≤
      (unitPairs (Q.erase v)).card * (Q.card : ℝ) := by nlinarith
  have hcoeff : ((k : ℝ) - 1) * (Q.erase v).card ≤ α * ((Q.card : ℝ) - 2) := by
    calc
      ((k : ℝ) - 1) * (Q.erase v).card =
          (k : ℝ) * ((Q.card : ℝ) - 2) - ((Q.card : ℝ) - k - 1) := by rw [hcard]; ring
      _ ≤ (k : ℝ) * ((Q.card : ℝ) - 2) := by linarith
      _ ≤ α * ((Q.card : ℝ) - 2) := mul_le_mul_of_nonneg_right hα.le hs2
  refine ⟨v, hv, ?_, ?_⟩
  · intro x hx
    have hdx := hd x (Finset.mem_of_mem_erase hx)
    have her := unitDegree_erase_le Q x v
    omega
  · apply (mul_le_mul_iff_left₀ hspos).mp
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hspos.le]

def thresholdSize (k : ℕ) : ℕ := finiteSize (2 * k + 1) (2 * k + 2)

theorem thresholdSize_pos (k : ℕ) : 0 < thresholdSize k := finiteSize_pos (by omega)

theorem threshold_configuration (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : thresholdSize k ^ 2 ≤ n) (η : ℝ) (hη : 0 < η) :
    ∃ P : Finset ℂ, P.card = n ∧ RadialSupport P ∧ 0 ∉ P ∧
      (P : Set ℂ) ⊆ twoDisks η ∧ HasUnitMinDegree P k ∧
      ((k : ℝ) - 1) * n ≤ (unitPairs P).card := by
  let α : ℝ := (k : ℝ) + 1 / (4 * (k : ℝ) + 4)
  have hα : (k : ℝ) < α := by
    have hh : (0 : ℝ) < 1 / (4 * (k : ℝ) + 4) := by positivity
    dsimp [α]
    linarith
  obtain ⟨P, hPcard, hPcount, hP, hzero, hloc⟩ :=
    finite_construction_real (2 * k + 1) (2 * k + 2) (by omega) (by omega) η hη
  have hratio : ((2 * k + 1 : ℕ) : ℝ) / 2 * (1 - 1 / ((2 * k + 2 : ℕ) : ℝ)) = α := by
    dsimp [α]
    push_cast
    field_simp
    ring
  rw [hratio] at hPcount
  have hPne : P.Nonempty := Finset.card_pos.mp (by rw [hPcard]; exact finiteSize_pos (by omega))
  obtain ⟨Q, hQP, hQ, hdegree, hcount⟩ := dense_subset_min_degree α k hα P hPne hPcount
  obtain ⟨v, hv, hminusDegree, hminusCount⟩ := erase_low_degree_density Q hQ k α hα hdegree hcount
  have hs : 2 ≤ Q.card := by
    have h1 := hdegree v hv
    have h2 := unitDegree_lt_card hv
    omega
  have hQM : Q.card ≤ thresholdSize k := by
    exact (Finset.card_le_card hQP).trans_eq hPcard
  have hnQ : Q.card ^ 2 ≤ n := (Nat.pow_le_pow_left hQM 2).trans hn
  obtain ⟨a, b, hab⟩ := consecutive_sizes_representation Q.card n hs hnQ
  let A : Fin a ⊕ Fin b → Finset ℂ := Sum.elim (fun _ => Q) (fun _ => Q.erase v)
  have hA : ∀ i, A i ⊆ Q := by
    intro i
    cases i
    · exact Finset.Subset.refl Q
    · exact Finset.erase_subset _ _
  have hdA : ∀ i, HasUnitMinDegree (A i) k := by
    intro i
    cases i
    · exact fun x hx => (Nat.le_succ k).trans (hdegree x hx)
    · exact hminusDegree
  have hcA : ∀ i, ((k : ℝ) - 1) * (A i).card ≤ (unitPairs (A i)).card := by
    intro i
    cases i
    · exact (mul_le_mul_of_nonneg_right (by linarith : (k : ℝ) - 1 ≤ α)
        (Nat.cast_nonneg Q.card)).trans hcount
    · exact hminusCount
  obtain ⟨R, hRc, hRs, hRz, hRl, hRd, hRe⟩ := glue_dense_copies Q
    (fun h => hzero (hQP h)) (hP.mono hQP) η (fun _ hx => hloc (hQP hx)) A hA k hdA
    ((k : ℝ) - 1) hcA
  have hsum : ∑ i, (A i).card = n := by
    simpa [A, Fintype.sum_sum_type, Finset.card_erase_of_mem hv] using hab.symm
  refine ⟨R, hRc.trans hsum, hRs, hRz, hRl, hRd, ?_⟩
  rwa [hRc, hsum] at hRe

end
end Proof

end Combined_PrescribedCardinality

/-! ## Source: CardinalEstimates.lean -/

section Combined_CardinalEstimates

/-! Explicit cardinality estimates used to invert the construction thresholds. -/

namespace Proof
noncomputable section

def logTwo (x : ℝ) : ℝ := Real.logb 2 x
def doubleLog (x : ℝ) : ℝ := logTwo (logTwo x)
def tripleLog (x : ℝ) : ℝ := logTwo (doubleLog x)

theorem logTwo_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : logTwo x ≤ logTwo y :=
  Real.logb_le_logb_of_le (by norm_num) hx hxy

theorem logTwo_le_logTwo {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logTwo x ≤ logTwo y ↔ x ≤ y := Real.logb_le_logb (by norm_num) hx hy

theorem logTwo_pos {x : ℝ} (hx : 1 < x) : 0 < logTwo x := Real.logb_pos (by norm_num) hx

@[simp] theorem logTwo_two : logTwo 2 = 1 := Real.logb_self_eq_one (by norm_num)

@[simp] theorem logTwo_four : logTwo 4 = 2 := by
  unfold logTwo
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

theorem middleVertexCount_le_four_pow (d : ℕ) : middleVertexCount d ≤ 4 ^ d := by
  have h := Nat.choose_le_two_pow (2 * d) d
  simpa only [middleVertexCount, pow_mul, show (2 : ℕ) ^ 2 = 4 from rfl] using h

theorem middleEdgeCount_le (d : ℕ) : middleEdgeCount d ≤ d * 4 ^ d := by
  apply Nat.mul_le_mul_left
  calc
    (2 * d - 1).choose d ≤ 2 ^ (2 * d - 1) := Nat.choose_le_two_pow _ _
    _ ≤ 2 ^ (2 * d) := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    _ = 4 ^ d := by rw [pow_mul]; rfl

theorem finiteSize_square_bound (d : ℕ) :
    finiteSize d (d + 1) ^ 2 ≤ 2 ^ (4 * (d + 1) ^ 2 * 4 ^ d) := by
  have hq : d + 1 ≤ 2 ^ (d + 1) := Nat.lt_two_pow_self.le
  have hN : finiteSize d (d + 1) ≤ 2 ^ (2 * d + (d + 1) * middleEdgeCount d) := by
    calc
      finiteSize d (d + 1) ≤ 4 ^ d * (2 ^ (d + 1)) ^ middleEdgeCount d :=
        Nat.mul_le_mul (middleVertexCount_le_four_pow d) (Nat.pow_le_pow_left hq _)
      _ = 2 ^ (2 * d + (d + 1) * middleEdgeCount d) := by
        rw [show (4 : ℕ) ^ d = 2 ^ (2 * d) by rw [pow_mul]; rfl, ← pow_mul, ← pow_add]
  have hR : 1 ≤ 4 ^ d := Nat.one_le_pow d 4 (by norm_num)
  have hE : 2 * (2 * d + (d + 1) * middleEdgeCount d) ≤ 4 * (d + 1) ^ 2 * 4 ^ d := by
    calc
      2 * (2 * d + (d + 1) * middleEdgeCount d) ≤
          2 * (2 * d + (d + 1) * (d * 4 ^ d)) := by gcongr; exact middleEdgeCount_le d
      _ ≤ 2 * ((2 * d) * 4 ^ d + (d + 1) * (d * 4 ^ d)) := by
        apply Nat.mul_le_mul_left
        apply Nat.add_le_add_right
        simpa only [mul_one] using Nat.mul_le_mul_left (2 * d) hR
      _ = (2 * (2 * d + (d + 1) * d)) * 4 ^ d := by ring
      _ ≤ (4 * (d + 1) ^ 2) * 4 ^ d := Nat.mul_le_mul_right _ (by nlinarith)
  calc
    finiteSize d (d + 1) ^ 2 ≤ (2 ^ (2 * d + (d + 1) * middleEdgeCount d)) ^ 2 :=
      Nat.pow_le_pow_left hN _
    _ = 2 ^ (2 * (2 * d + (d + 1) * middleEdgeCount d)) := by
      rw [← pow_mul, Nat.mul_comm (2 * d + (d + 1) * middleEdgeCount d) 2]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hE

theorem finiteSize_ge_two {d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) : 2 ≤ finiteSize d q := by
  have hv : 2 ≤ middleVertexCount d := by
    rw [middleVertexCount_eq_twice hd]
    have h := Nat.choose_pos (show d ≤ 2 * d - 1 by omega)
    omega
  have hp : 1 ≤ q ^ middleEdgeCount d := Nat.one_le_pow _ _ hq
  exact hv.trans (by simpa [finiteSize] using Nat.mul_le_mul_left (middleVertexCount d) hp)

theorem finiteSize_doubleLog_bound (d : ℕ) (hd : 1 ≤ d) :
    doubleLog ((finiteSize d (d + 1) ^ 2 : ℕ) : ℝ) ≤
      2 * (d : ℝ) + 2 * logTwo ((d : ℝ) + 1) + 2 := by
  let E := 4 * (d + 1) ^ 2 * 4 ^ d
  have hsize := finiteSize_ge_two hd (show 1 ≤ d + 1 by omega)
  have hN : (1 : ℝ) < ((finiteSize d (d + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (by nlinarith : 1 < finiteSize d (d + 1) ^ 2)
  have hbound : (((finiteSize d (d + 1) ^ 2 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ E := by
    exact_mod_cast finiteSize_square_bound d
  have hlog : logTwo ((finiteSize d (d + 1) ^ 2 : ℕ) : ℝ) ≤ (E : ℝ) := by
    have h := logTwo_mono (by linarith : (0 : ℝ) < ((finiteSize d (d + 1) ^ 2 : ℕ) : ℝ)) hbound
    simpa only [logTwo, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using h
  have hloglog := logTwo_mono (logTwo_pos hN) hlog
  have hE : logTwo (E : ℝ) = 2 * (d : ℝ) + 2 * logTwo ((d : ℝ) + 1) + 2 := by
    simp only [E, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, logTwo]
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]
    change logTwo 4 + 2 * logTwo ((d : ℝ) + 1) + (d : ℝ) * logTwo 4 = _
    rw [logTwo_four]
    change 2 + 2 * logTwo ((d : ℝ) + 1) + (d : ℝ) * 2 =
      2 * (d : ℝ) + 2 * logTwo ((d : ℝ) + 1) + 2
    ring
  exact hloglog.trans_eq hE

end
end Proof

end Combined_CardinalEstimates

/-! ## Source: AnalyticThresholds.lean -/

section Combined_AnalyticThresholds

/-! Inversion of the size thresholds with an explicit absolute error constant. -/

namespace Proof
noncomputable section
open Filter

theorem tendsto_logTwo_atTop : Tendsto logTwo atTop atTop :=
  Real.tendsto_logb_atTop (by norm_num)

theorem tendsto_doubleLog_nat : Tendsto (fun n : ℕ => doubleLog (n : ℝ)) atTop atTop :=
  (tendsto_logTwo_atTop.comp tendsto_logTwo_atTop).comp tendsto_natCast_atTop_atTop

theorem logTwo_sublinear (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, logTwo x ≤ c * x := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.isLittleO_log_id_atTop.def (mul_pos hc hl)
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  change ‖Real.log x‖ ≤ c * Real.log 2 * ‖x‖ at hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0] at hx
  change Real.log x / Real.log 2 ≤ c * x
  apply (div_le_iff₀ hl).mpr
  nlinarith [le_abs_self (Real.log x)]

theorem threshold_doubleLog_bound (k : ℕ) :
    doubleLog ((thresholdSize k ^ 2 : ℕ) : ℝ) ≤
      4 * (k : ℝ) + 2 * logTwo ((k : ℝ) + 1) + 6 := by
  have h := finiteSize_doubleLog_bound (2 * k + 1) (by omega)
  have he : logTwo ((2 * k + 1 : ℕ) + 1 : ℝ) = 1 + logTwo ((k : ℝ) + 1) := by
    push_cast
    rw [show 2 * (k : ℝ) + 1 + 1 = 2 * ((k : ℝ) + 1) by ring]
    change Real.logb 2 (2 * ((k : ℝ) + 1)) = _
    rw [Real.logb_mul (by norm_num) (by positivity)]
    change logTwo 2 + logTwo ((k : ℝ) + 1) = _
    rw [logTwo_two]
  change doubleLog ((thresholdSize k ^ 2 : ℕ) : ℝ) ≤ _ at h
  rw [he] at h
  push_cast at h ⊢
  linarith

theorem doubleLog_le_iff {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    doubleLog x ≤ doubleLog y ↔ x ≤ y := by
  unfold doubleLog
  rw [logTwo_le_logTwo (logTwo_pos hx) (logTwo_pos hy),
    logTwo_le_logTwo (by linarith) (by linarith)]

theorem logarithmic_index : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ k : ℕ,
    1 ≤ k ∧ thresholdSize k ^ 2 ≤ n ∧
      doubleLog (n : ℝ) / 4 - 7 * tripleLog (n : ℝ) ≤ (k : ℝ) - 1 := by
  have hreal : ∀ᶠ L : ℝ in atTop,
      40 ≤ L ∧ 1 ≤ logTwo L ∧ logTwo L ≤ L / 8 := by
    filter_upwards [eventually_ge_atTop (40 : ℝ),
      tendsto_logTwo_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      logTwo_sublinear (1 / 8) (by norm_num)] with L hL hlog hsmall
    exact ⟨hL, hlog, by linarith⟩
  have hnat := tendsto_doubleLog_nat.eventually hreal
  have hall : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      40 ≤ doubleLog (n : ℝ) ∧ 1 ≤ logTwo (doubleLog (n : ℝ)) ∧
      logTwo (doubleLog (n : ℝ)) ≤ doubleLog (n : ℝ) / 8 :=
    (eventually_ge_atTop 2).and hnat
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hall
  refine ⟨n₀, ?_⟩
  intro n hn
  obtain ⟨hn2, hL, hlog, hsmall⟩ := hn₀ n hn
  let L := doubleLog (n : ℝ)
  let x := L / 4 - logTwo L - 4
  let k := Nat.floor x
  have hx : 1 ≤ x := by dsimp [x, L]; linarith
  have hk : 1 ≤ k := Nat.le_floor (by simpa using hx)
  have hklo : x < (k : ℝ) + 1 := Nat.lt_floor_add_one x
  have hkhi : (k : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hkl : (k : ℝ) + 1 ≤ L := by dsimp [x] at hkhi; dsimp [L]; linarith
  have hlogk : logTwo ((k : ℝ) + 1) ≤ logTwo L := logTwo_mono (by positivity) hkl
  have hT : doubleLog ((thresholdSize k ^ 2 : ℕ) : ℝ) ≤ L := by
    have ht := threshold_doubleLog_bound k
    dsimp [x] at hkhi
    dsimp [L] at *
    linarith
  have hs : 2 ≤ thresholdSize k := finiteSize_ge_two (by omega) (by omega)
  have hsR : (1 : ℝ) < ((thresholdSize k ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (by nlinarith : 1 < thresholdSize k ^ 2)
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hthreshold : thresholdSize k ^ 2 ≤ n := by
    exact_mod_cast (doubleLog_le_iff hsR hnR).mp hT
  refine ⟨k, hk, hthreshold, ?_⟩
  change L / 4 - 7 * logTwo L ≤ (k : ℝ) - 1
  dsimp [x] at hklo
  dsimp [L] at *
  linarith

end
end Proof

end Combined_AnalyticThresholds

/-! ## Source: PlaneGeometry.lean -/

section Combined_PlaneGeometry

/-! Literal Euclidean-plane statements, and bipartiteness of the full unit-distance graph. -/

namespace Proof
noncomputable section
open Classical EuclideanGeometry
open scoped EuclideanGeometry

def planeLowerCenter : ℝ² := complexToPlane lowerCenter
def planeUpperCenter : ℝ² := complexToPlane upperCenter
def planeTwoDisks (η : ℝ) : Set ℝ² :=
  Metric.ball planeLowerCenter η ∪ Metric.ball planeUpperCenter η

@[simp] theorem planeLowerCenter_first : planeLowerCenter 0 = 0 := rfl
@[simp] theorem planeLowerCenter_second : planeLowerCenter 1 = -1 / 2 := rfl
@[simp] theorem planeUpperCenter_first : planeUpperCenter 0 = 0 := rfl
@[simp] theorem planeUpperCenter_second : planeUpperCenter 1 = 1 / 2 := rfl
@[simp] theorem complexToPlane_second (z : ℂ) : complexToPlane z 1 = z.im := rfl

def PlaneRadialSupport (P : Finset ℝ²) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, x ≠ y → inner ℝ x (y - x) < 0

def minimumUnitDegree {X : Type*} [MetricSpace X] (P : Finset X) : ℕ :=
  (unitDistanceGraph P).minDegree

theorem le_minimumUnitDegree {X : Type*} [MetricSpace X] (P : Finset X)
    (hP : P.Nonempty) (k : ℕ) (hk : HasUnitMinDegree P k) : k ≤ minimumUnitDegree P := by
  letI : Nonempty P := ⟨⟨hP.choose, hP.choose_spec⟩⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro x
  rw [unitDistanceGraph_degree]
  exact hk x x.property

theorem radialSupport_image {P : Finset ℂ} (hP : RadialSupport P) :
    PlaneRadialSupport (P.image complexToPlane) := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  rw [← map_sub, complexToPlane.inner_map_map, ← support_eq_inner]
  exact hP a ha b hb (fun h => hxy (congrArg complexToPlane h))

theorem twoDisks_image {P : Finset ℂ} {η : ℝ} (hP : (P : Set ℂ) ⊆ twoDisks η) :
    ((P.image complexToPlane : Finset ℝ²) : Set ℝ²) ⊆ planeTwoDisks η := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have h := hP ha
  simpa only [twoDisks, planeTwoDisks, planeLowerCenter, planeUpperCenter,
    Set.mem_union, Metric.mem_ball, complexToPlane.isometry.dist_eq] using h

theorem unitMinDegree_image {P : Finset ℂ} {k : ℕ} (hP : HasUnitMinDegree P k) :
    HasUnitMinDegree (P.image complexToPlane) k := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have he : (unitNeighbors P a).image complexToPlane ⊆
      unitNeighbors (P.image complexToPlane) (complexToPlane a) := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hbP, hbd⟩ := mem_unitNeighbors.mp hb
    exact mem_unitNeighbors.mpr ⟨Finset.mem_image_of_mem _ hbP,
      (complexToPlane.isometry.dist_eq a b).trans hbd⟩
  have hc := Finset.card_le_card he
  rw [Finset.card_image_of_injective _ complexToPlane.injective] at hc
  exact (hP a ha).trans hc

theorem im_neg_of_lower_ball {z : ℂ} {η : ℝ} (hη : η < 1 / 2)
    (hz : z ∈ Metric.ball lowerCenter η) : z.im < 0 := by
  have hnorm : ‖z - lowerCenter‖ < η := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hi := Complex.im_le_norm (z - lowerCenter)
  simp only [Complex.sub_im, lowerCenter] at hi hnorm
  linarith

theorem im_pos_of_upper_ball {z : ℂ} {η : ℝ} (hη : η < 1 / 2)
    (hz : z ∈ Metric.ball upperCenter η) : 0 < z.im := by
  have hnorm : ‖z - upperCenter‖ < η := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hi := (abs_le.mp (Complex.abs_im_le_norm (z - upperCenter))).1
  simp only [Complex.sub_im, upperCenter] at hi hnorm
  linarith

theorem second_neg_of_lower_ball {x : ℝ²} {η : ℝ} (hη : η < 1 / 2)
    (hx : x ∈ Metric.ball planeLowerCenter η) : x 1 < 0 := by
  obtain ⟨z, rfl⟩ := complexToPlane.surjective x
  apply im_neg_of_lower_ball hη
  simpa only [planeLowerCenter, Metric.mem_ball, complexToPlane.isometry.dist_eq] using hx

theorem second_pos_of_upper_ball {x : ℝ²} {η : ℝ} (hη : η < 1 / 2)
    (hx : x ∈ Metric.ball planeUpperCenter η) : 0 < x 1 := by
  obtain ⟨z, rfl⟩ := complexToPlane.surjective x
  apply im_pos_of_upper_ball hη
  simpa only [planeUpperCenter, Metric.mem_ball, complexToPlane.isometry.dist_eq] using hx

theorem no_unit_pair_in_ball {X : Type*} [MetricSpace X] {x y c : X} {η : ℝ}
    (hη : η < 1 / 2) (hx : x ∈ Metric.ball c η) (hy : y ∈ Metric.ball c η) :
    dist x y ≠ 1 := by
  have ht := dist_triangle x c y
  have hx' := Metric.mem_ball.mp hx
  have hy' := Metric.mem_ball.mp hy
  rw [dist_comm c y] at ht
  linarith

def HorizontalBipartition (P : Finset ℝ²) : Prop :=
  (unitDistanceGraph P).IsBipartiteWith {x | x.val 1 < 0} {x | 0 < x.val 1} ∧
    ∀ x ∈ P, x 1 < 0 ∨ 0 < x 1

theorem twoDisks_horizontalBipartition {P : Finset ℝ²} {η : ℝ} (hη : η < 1 / 2)
    (hP : (P : Set ℝ²) ⊆ planeTwoDisks η) : HorizontalBipartition P := by
  have hc : ∀ x ∈ P, x 1 < 0 ∨ 0 < x 1 := by
    intro x hx
    rcases hP hx with h | h
    · exact Or.inl (second_neg_of_lower_ball hη h)
    · exact Or.inr (second_pos_of_upper_ball hη h)
  refine ⟨⟨?_, ?_⟩, hc⟩
  · apply Set.disjoint_left.mpr
    intro x hx hy
    change x.val 1 < 0 at hx
    change 0 < x.val 1 at hy
    exact lt_asymm hx hy
  · intro x y hxy
    change dist x.val y.val = 1 at hxy
    rcases hP x.property with hx | hx <;> rcases hP y.property with hy | hy
    · exact False.elim (no_unit_pair_in_ball hη hx hy hxy)
    · exact Or.inl ⟨second_neg_of_lower_ball hη hx, second_pos_of_upper_ball hη hy⟩
    · exact Or.inr ⟨second_pos_of_upper_ball hη hx, second_neg_of_lower_ball hη hy⟩
    · exact False.elim (no_unit_pair_in_ball hη hx hy hxy)

theorem HorizontalBipartition.isBipartite {P : Finset ℝ²} (hP : HorizontalBipartition P) :
    (unitDistanceGraph P).IsBipartite := hP.1.isBipartite

end
end Proof

end Combined_PlaneGeometry

/-! ## Source: MainTheorem.lean -/

section Combined_MainTheorem

/-! The quantitative theorem in the literal Euclidean plane. -/

namespace Proof
noncomputable section
open Classical EuclideanGeometry
open scoped EuclideanGeometry

/-- The finite construction, with the exact size and density in Theorem 1.3. -/
theorem finite_construction_plane (d q : ℕ) (hd : 2 ≤ d) (hq : 2 ≤ q)
    (η : ℝ) (hη : 0 < η) : ∃ P : Finset ℝ²,
    P.card = finiteSize d q ∧
    (d : ℝ) / 2 * (1 - 1 / (q : ℝ)) * P.card ≤ unitDistNum P ∧
    ConvexIndep P ∧ PlaneRadialSupport P ∧ 0 ∉ P ∧
    (P : Set ℝ²) ⊆ planeTwoDisks η := by
  obtain ⟨Q, hc, he, hs, hz, hl⟩ := finite_construction_real d q hd hq η hη
  have hcard : (Q.image complexToPlane).card = Q.card :=
    Finset.card_image_of_injective _ complexToPlane.injective
  have hedge : unitDistNum (Q.image complexToPlane) = (unitPairs Q).card := by
    rw [unitDistNum_eq_card_unitPairs, unitPairs_card_image_isometry _ complexToPlane.isometry]
  refine ⟨Q.image complexToPlane, hcard.trans hc, ?_,
    convexIndep_image_complexToPlane Q hs.convexIndependent, radialSupport_image hs, ?_,
    twoDisks_image hl⟩
  · rwa [hcard, hedge]
  · intro hh
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
    have ha0 := complexToPlane.injective (he.trans (map_zero complexToPlane).symm)
    exact hz (ha0 ▸ ha)

/-- Proposition 4.3, including strict support and arbitrarily small prescribed disks. -/
theorem threshold_configuration_plane (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : thresholdSize k ^ 2 ≤ n) (η : ℝ) (hη : 0 < η) :
    ∃ P : Finset ℝ², P.card = n ∧ ConvexIndep P ∧ PlaneRadialSupport P ∧
      0 ∉ P ∧ (P : Set ℝ²) ⊆ planeTwoDisks η ∧ HasUnitMinDegree P k ∧
      ((k : ℝ) - 1) * n ≤ unitDistNum P := by
  obtain ⟨Q, hc, hs, hz, hl, hd, he⟩ := threshold_configuration k hk n hn η hη
  have hcard : (Q.image complexToPlane).card = Q.card :=
    Finset.card_image_of_injective _ complexToPlane.injective
  have hedge : unitDistNum (Q.image complexToPlane) = (unitPairs Q).card := by
    rw [unitDistNum_eq_card_unitPairs, unitPairs_card_image_isometry _ complexToPlane.isometry]
  refine ⟨Q.image complexToPlane, hcard.trans hc,
    convexIndep_image_complexToPlane Q hs.convexIndependent, radialSupport_image hs, ?_,
    twoDisks_image hl, unitMinDegree_image hd, ?_⟩
  · intro hh
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
    have ha0 := complexToPlane.injective (he.trans (map_zero complexToPlane).symm)
    exact hz (ha0 ▸ ha)
  · rwa [hedge]

/-- Theorem 1.1, with the explicit absolute choice C = 7. Both the minimum degree
and the number of unordered unit-distance pairs have the leading coefficient 1/4. -/
theorem main_quantitative : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ η : ℝ, 0 < η → η < 1 / 2 →
    ∃ P : Finset ℝ², P.Nonempty ∧ P.card = n ∧ ConvexIndep P ∧
      PlaneRadialSupport P ∧ 0 ∉ P ∧ (P : Set ℝ²) ⊆ planeTwoDisks η ∧
      (unitDistanceGraph P).IsBipartite ∧ HorizontalBipartition P ∧
      doubleLog (n : ℝ) / 4 - 7 * tripleLog (n : ℝ) ≤
        min (minimumUnitDegree P : ℝ) ((unitDistNum P : ℝ) / n) := by
  obtain ⟨n₀, hn₀⟩ := logarithmic_index
  refine ⟨n₀, ?_⟩
  intro n hn η hη hηhalf
  obtain ⟨k, hk, ht, hbound⟩ := hn₀ n hn
  obtain ⟨P, hc, hconv, hs, hz, hl, hd, he⟩ :=
    threshold_configuration_plane k hk n ht η hη
  have hnpos : 0 < n := (pow_pos (thresholdSize_pos k) 2).trans_le ht
  have hP : P.Nonempty := Finset.card_pos.mp (by rwa [hc])
  have hdeg : (k : ℝ) ≤ minimumUnitDegree P := by
    exact_mod_cast le_minimumUnitDegree P hP k hd
  have hdiv : (k : ℝ) - 1 ≤ (unitDistNum P : ℝ) / n :=
    (le_div_iff₀ (by exact_mod_cast hnpos)).mpr he
  have hb := twoDisks_horizontalBipartition hηhalf hl
  exact ⟨P, hP, hc, hconv, hs, hz, hl, hb.isBipartite, hb,
    le_min (by linarith) (hbound.trans hdiv)⟩

/-- The exact constant-quantified form of Theorem 1.1. -/
theorem main_theorem : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
    ∀ n ≥ n₀, ∀ η : ℝ, 0 < η → η < 1 / 2 →
    ∃ P : Finset ℝ², P.Nonempty ∧ P.card = n ∧ ConvexIndep P ∧
      (P : Set ℝ²) ⊆ planeTwoDisks η ∧ (unitDistanceGraph P).IsBipartite ∧
      HorizontalBipartition P ∧
      doubleLog (n : ℝ) / 4 - C * tripleLog (n : ℝ) ≤
        min (minimumUnitDegree P : ℝ) ((unitDistNum P : ℝ) / n) := by
  obtain ⟨n₀, hn₀⟩ := main_quantitative
  refine ⟨7, by norm_num, n₀, ?_⟩
  intro n hn η hη hηhalf
  obtain ⟨P, hP, hc, hv, _, _, hl, hb, hh, he⟩ := hn₀ n hn η hη hηhalf
  exact ⟨P, hP, hc, hv, hl, hb, hh, he⟩

end
end Proof

end Combined_MainTheorem

/-! ## Source: GrowthEstimates.lean -/

section Combined_GrowthEstimates

/-! Two-sided growth estimates, including the double-exponential size bound. -/

namespace Proof
noncomputable section
open Filter

theorem finiteSize_doubleLog_lower (d : ℕ) (hd : 2 ≤ d) :
    2 * (d : ℝ) - logTwo (2 * (d : ℝ) + 1) ≤
      doubleLog (finiteSize d (d + 1) : ℝ) := by
  have hv := middleVertexCount_pos d
  have hvm : middleVertexCount d ≤ middleEdgeCount d := by
    have ht := middleEdgeCount_twice (show 1 ≤ d by omega)
    nlinarith
  have hpow : 2 ^ middleEdgeCount d ≤ finiteSize d (d + 1) := by
    calc
      2 ^ middleEdgeCount d ≤ (d + 1) ^ middleEdgeCount d := Nat.pow_le_pow_left (by omega) _
      _ ≤ middleVertexCount d * (d + 1) ^ middleEdgeCount d := by
        simpa only [one_mul] using Nat.mul_le_mul_right ((d + 1) ^ middleEdgeCount d) (show 1 ≤ middleVertexCount d by omega)
  have hpowR : (2 : ℝ) ^ middleEdgeCount d ≤ (finiteSize d (d + 1) : ℝ) := by
    exact_mod_cast hpow
  have hm : (middleEdgeCount d : ℝ) ≤ logTwo (finiteSize d (d + 1) : ℝ) := by
    have h := logTwo_mono (by positivity : (0 : ℝ) < 2 ^ middleEdgeCount d) hpowR
    simpa only [logTwo, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using h
  have hvlog : (middleVertexCount d : ℝ) ≤ logTwo (finiteSize d (d + 1) : ℝ) :=
    (show (middleVertexCount d : ℝ) ≤ middleEdgeCount d by exact_mod_cast hvm).trans hm
  have hlower := logTwo_mono (by exact_mod_cast hv) hvlog
  have hbin : (4 : ℝ) ^ d ≤ (2 * (d : ℝ) + 1) * (middleVertexCount d : ℝ) := by
    exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_central_binom d
  have hb := logTwo_mono (by positivity : (0 : ℝ) < 4 ^ d) hbin
  change Real.logb 2 ((4 : ℝ) ^ d) ≤ Real.logb 2 ((2 * (d : ℝ) + 1) * ↑(middleVertexCount d)) at hb
  rw [Real.logb_pow, Real.logb_mul (by positivity) (by exact_mod_cast hv.ne')] at hb
  change (d : ℝ) * logTwo 4 ≤ logTwo (2 * (d : ℝ) + 1) + logTwo (middleVertexCount d : ℝ) at hb
  rw [logTwo_four] at hb
  change logTwo (middleVertexCount d : ℝ) ≤ doubleLog (finiteSize d (d + 1) : ℝ) at hlower
  linarith

theorem finiteSize_doubleLog_upper (d : ℕ) (hd : 1 ≤ d) :
    doubleLog (finiteSize d (d + 1) : ℝ) ≤
      2 * (d : ℝ) + 2 * logTwo ((d : ℝ) + 1) + 2 := by
  have hs := finiteSize_ge_two hd (show 1 ≤ d + 1 by omega)
  have hsR : (1 : ℝ) < (finiteSize d (d + 1) : ℝ) := by exact_mod_cast (by omega : 1 < finiteSize d (d + 1))
  have hs2R : (1 : ℝ) < ((finiteSize d (d + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast (by nlinarith : 1 < finiteSize d (d + 1) ^ 2)
  have hle : (finiteSize d (d + 1) : ℝ) ≤ ((finiteSize d (d + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (by nlinarith : finiteSize d (d + 1) ≤ finiteSize d (d + 1) ^ 2)
  exact ((doubleLog_le_iff hsR hs2R).mpr hle).trans (finiteSize_doubleLog_bound d hd)

theorem threshold_doubleLog_lower (k : ℕ) (hk : 1 ≤ k) :
    4 * (k : ℝ) - logTwo ((k : ℝ) + 1) ≤
      doubleLog ((thresholdSize k ^ 2 : ℕ) : ℝ) := by
  have h := finiteSize_doubleLog_lower (2 * k + 1) (by omega)
  have hm : logTwo (2 * ((2 * k + 1 : ℕ) : ℝ) + 1) ≤ 2 + logTwo ((k : ℝ) + 1) := by
    have he : logTwo (4 * ((k : ℝ) + 1)) = 2 + logTwo ((k : ℝ) + 1) := by
      unfold logTwo
      rw [Real.logb_mul (by norm_num) (by positivity)]
      change logTwo 4 + logTwo ((k : ℝ) + 1) = _
      rw [logTwo_four]
      rfl
    rw [← he]
    apply logTwo_mono (by positivity)
    push_cast
    linarith
  have hs := finiteSize_ge_two (show 1 ≤ 2 * k + 1 by omega) (show 1 ≤ 2 * k + 2 by omega)
  change 2 ≤ thresholdSize k at hs
  have hr : (1 : ℝ) < (thresholdSize k : ℝ) := by exact_mod_cast (by omega : 1 < thresholdSize k)
  have hr2 : (1 : ℝ) < ((thresholdSize k ^ 2 : ℕ) : ℝ) := by exact_mod_cast (by nlinarith : 1 < thresholdSize k ^ 2)
  have hle : (thresholdSize k : ℝ) ≤ ((thresholdSize k ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (by nlinarith : thresholdSize k ≤ thresholdSize k ^ 2)
  have ht := (doubleLog_le_iff hr hr2).mpr hle
  change 2 * ((2 * k + 1 : ℕ) : ℝ) - _ ≤ doubleLog (thresholdSize k : ℝ) at h
  push_cast at h hm
  linarith

theorem threshold_growth :
    (fun k : ℕ => doubleLog ((thresholdSize k ^ 2 : ℕ) : ℝ) - 4 * (k : ℝ))
      =O[atTop] (fun k => logTwo ((k : ℝ) + 1)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨8, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hl := threshold_doubleLog_lower k hk
  have hu := threshold_doubleLog_bound k
  have hlog : 1 ≤ logTwo ((k : ℝ) + 1) := by
    calc
      1 = logTwo 2 := logTwo_two.symm
      _ ≤ logTwo ((k : ℝ) + 1) := logTwo_mono (by norm_num) (by exact_mod_cast (by omega : 2 ≤ k + 1))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ logTwo ((k : ℝ) + 1))]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def degreeSizeBound (k : ℕ) : ℕ := finiteSize (2 * k - 1) (2 * k)

theorem degreeSizeBound_growth_estimate (k : ℕ) (hk : 2 ≤ k) :
    |doubleLog (degreeSizeBound k : ℝ) - 4 * (k : ℝ)| ≤ 5 * logTwo (k : ℝ) := by
  have hlow := finiteSize_doubleLog_lower (2 * k - 1) (by omega)
  have hu := finiteSize_doubleLog_upper (2 * k - 1) (by omega)
  have he : 2 * k - 1 + 1 = 2 * k := by omega
  rw [he] at hlow hu
  change 2 * ((2 * k - 1 : ℕ) : ℝ) - _ ≤ doubleLog (degreeSizeBound k : ℝ) at hlow
  change doubleLog (degreeSizeBound k : ℝ) ≤ _ at hu
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hcast : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [hcast] at hlow hu
  have hl : logTwo (2 * (k : ℝ)) = 1 + logTwo (k : ℝ) := by
    unfold logTwo
    rw [Real.logb_mul (by norm_num) (by positivity)]
    change logTwo 2 + logTwo (k : ℝ) = _
    rw [logTwo_two]
    rfl
  rw [sub_add_cancel, hl] at hu
  have hlog : 1 ≤ logTwo (k : ℝ) := by
    exact logTwo_two ▸ logTwo_mono (by norm_num : (0 : ℝ) < 2) hkR
  have hl4 : logTwo (2 * (2 * (k : ℝ) - 1) + 1) ≤ 2 + logTwo (k : ℝ) := by
    have hm := logTwo_mono (by linarith : 0 < 2 * (2 * (k : ℝ) - 1) + 1)
      (by linarith : 2 * (2 * (k : ℝ) - 1) + 1 ≤ 4 * (k : ℝ))
    change _ ≤ Real.logb 2 (4 * (k : ℝ)) at hm
    rw [Real.logb_mul (by norm_num) (by positivity)] at hm
    change _ ≤ logTwo 4 + logTwo (k : ℝ) at hm
    rwa [logTwo_four] at hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem degreeSizeBound_growth :
    (fun k : ℕ => doubleLog (degreeSizeBound k : ℝ) - 4 * (k : ℝ))
      =O[atTop] (fun k => logTwo (k : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨5, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
  have hl : 0 ≤ logTwo (k : ℝ) := (logTwo_pos (by exact_mod_cast (by omega : 1 < k))).le
  simpa only [Real.norm_eq_abs, abs_of_nonneg hl] using degreeSizeBound_growth_estimate k hk

/-- The double-exponential equality, with the error term separately proved to be O(log k). -/
theorem degreeSizeBound_double_exponential (k : ℕ) (hk : 2 ≤ k) :
    (degreeSizeBound k : ℝ) = (2 : ℝ) ^ ((2 : ℝ) ^
      (4 * (k : ℝ) + (doubleLog (degreeSizeBound k : ℝ) - 4 * (k : ℝ)))) := by
  have hs : 2 ≤ degreeSizeBound k := finiteSize_ge_two (by omega) (by omega)
  have hr : (1 : ℝ) < (degreeSizeBound k : ℝ) := by exact_mod_cast (by omega : 1 < degreeSizeBound k)
  rw [add_sub_cancel]
  unfold doubleLog logTwo
  have hlogpos : 0 < Real.logb 2 (degreeSizeBound k : ℝ) := logTwo_pos hr
  rw [Real.rpow_logb (by norm_num) (by norm_num) hlogpos,
    Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]

end
end Proof

end Combined_GrowthEstimates

/-! ## Source: Corollaries.lean -/

section Combined_Corollaries

/-! The quantitative, fixed-degree, and explicit-size corollaries. -/

namespace Proof
noncomputable section
open Classical Filter EuclideanGeometry
open scoped EuclideanGeometry

/-- Every sufficiently large prescribed cardinality admits any fixed minimum degree. -/
theorem eventual_minimum_degree (k : ℕ) (hk : 1 ≤ k) : ∃ n₀ : ℕ,
    ∀ n ≥ n₀, ∀ η : ℝ, 0 < η → η < 1 / 2 →
    ∃ P : Finset ℝ², P.Nonempty ∧ P.card = n ∧ ConvexIndep P ∧
      HasUnitMinDegree P k ∧ (P : Set ℝ²) ⊆ planeTwoDisks η ∧
      HorizontalBipartition P := by
  refine ⟨thresholdSize k ^ 2, ?_⟩
  intro n hn η hη hηhalf
  obtain ⟨P, hc, hv, _, _, hl, hd, _⟩ := threshold_configuration_plane k hk n hn η hη
  have hpos : 0 < n := (pow_pos (thresholdSize_pos k) 2).trans_le hn
  exact ⟨P, Finset.card_pos.mp (by rwa [hc]), hc, hv, hd, hl,
    twoDisks_horizontalBipartition hηhalf hl⟩

/-- The Ω(n log log n) lower bound holds even with the prescribed disk restriction. -/
theorem eventual_localized_density : ∃ n₀ : ℕ,
    ∀ n ≥ n₀, ∀ η : ℝ, 0 < η → η < 1 / 2 →
    ∃ P : Finset ℝ², P.Nonempty ∧ P.card = n ∧ ConvexIndep P ∧
      (P : Set ℝ²) ⊆ planeTwoDisks η ∧ HorizontalBipartition P ∧
      (n : ℝ) * doubleLog (n : ℝ) / 8 ≤ unitDistNum P := by
  obtain ⟨n₀, hn₀⟩ := main_quantitative
  have hsmall : ∀ᶠ n : ℕ in atTop, 7 * tripleLog (n : ℝ) ≤ doubleLog (n : ℝ) / 8 := by
    have h := tendsto_doubleLog_nat.eventually (logTwo_sublinear (1 / 56) (by norm_num))
    filter_upwards [h] with n hn
    change logTwo (doubleLog (n : ℝ)) ≤ _ at hn
    change 7 * logTwo (doubleLog (n : ℝ)) ≤ _
    linarith
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop n₀, hsmall] with n hn hsmall
  intro η hη hηhalf
  obtain ⟨P, hP, hc, hv, _, _, hl, _, hh, hb⟩ := hn₀ n hn η hη hηhalf
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (hc ▸ Finset.card_pos.mpr hP)
  have hdiv : doubleLog (n : ℝ) / 8 ≤ (unitDistNum P : ℝ) / n := by
    have h := hb.trans (min_le_right _ _)
    linarith
  have he := (le_div_iff₀ hnpos).mp hdiv
  refine ⟨P, hP, hc, hv, hl, hh, ?_⟩
  nlinarith

/-- In standard asymptotic notation, n log₂ log₂ n = O(U_c(n)). -/
theorem convex_unit_distances_omega :
    (fun n : ℕ => (n : ℝ) * doubleLog (n : ℝ)) =O[atTop]
      (fun n => (Erdos96.maxConvexUnitDistances n : ℝ)) := by
  obtain ⟨n₀, hn₀⟩ := eventual_localized_density
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨8, ?_⟩
  filter_upwards [eventually_ge_atTop n₀,
    tendsto_doubleLog_nat.eventually (eventually_ge_atTop (0 : ℝ))] with n hn hlog
  obtain ⟨P, _, hc, hv, _, _, he⟩ := hn₀ n hn (1 / 4) (by norm_num) (by norm_num)
  have hm : (unitDistNum P : ℝ) ≤ Erdos96.maxConvexUnitDistances n := by
    have h := unitDistNum_le_max P hv
    rw [hc] at h
    exact_mod_cast h
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hlog), Real.norm_natCast]
  linarith

/-- Corollary 4.4: a nonempty convex set of minimum degree k, with the stated size bound. -/
theorem bounded_size_minimum_degree (k : ℕ) (hk : 2 ≤ k)
    (η : ℝ) (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ Q : Finset ℝ², Q.Nonempty ∧ ConvexIndep Q ∧
      HasUnitMinDegree Q k ∧ Q.card ≤ degreeSizeBound k ∧
      (Q : Set ℝ²) ⊆ planeTwoDisks η ∧
      HorizontalBipartition Q := by
  let α : ℝ := (k : ℝ) - 1 + 1 / (4 * (k : ℝ))
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hα : ((k - 1 : ℕ) : ℝ) < α := by
    rw [hcast]
    dsimp [α]
    have hp : (0 : ℝ) < 1 / (4 * (k : ℝ)) := by positivity
    linarith
  obtain ⟨P, hc, he, hv, _, _, hl⟩ :=
    finite_construction_plane (2 * k - 1) (2 * k) (by omega) (by omega) η hη
  have hratio : ((2 * k - 1 : ℕ) : ℝ) / 2 * (1 - 1 / ((2 * k : ℕ) : ℝ)) = α := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    dsimp [α]
    field_simp
    ring
  rw [hratio, unitDistNum_eq_card_unitPairs] at he
  have hP : P.Nonempty := Finset.card_pos.mp (by rw [hc]; exact finiteSize_pos (by omega))
  obtain ⟨Q, hQP, hQ, hd, _⟩ := dense_subset_min_degree α (k - 1) hα P hP he
  have hd' : HasUnitMinDegree Q k := by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hd
  have hloc : (Q : Set ℝ²) ⊆ planeTwoDisks η := fun _ hx => hl (hQP hx)
  exact ⟨Q, hQ, convexIndep_subset hv hQP, hd', (Finset.card_le_card hQP).trans_eq hc,
    hloc, twoDisks_horizontalBipartition hηhalf hloc⟩

theorem degreeSizeBound_four : degreeSizeBound 4 = 3432 * 2 ^ 36036 := by
  have hv : middleVertexCount 7 = 3432 := by norm_num [middleVertexCount, Nat.choose]
  have hm : middleEdgeCount 7 = 12012 := by norm_num [middleEdgeCount, Nat.choose]
  change finiteSize 7 8 = _
  rw [finiteSize, hv, hm, show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_mul]

/-- The numerical bound in the manuscript, for the exact equidistance predicate. -/
theorem explicit_erdos_97_counterexample (η : ℝ) (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ Q : Finset ℝ², Q.Nonempty ∧ ConvexIndep Q ∧
      Erdos97.HasNUnitDistanceProperty 4 Q ∧ Erdos97.HasNEquidistantProperty 4 Q ∧
      Q.card ≤ 3432 * 2 ^ 36036 ∧ (Q : Set ℝ²) ⊆ planeTwoDisks η ∧
      HorizontalBipartition Q := by
  obtain ⟨Q, hQ, hv, hd, hc, hl, hh⟩ := bounded_size_minimum_degree 4 (by norm_num) η hη hηhalf
  rw [degreeSizeBound_four] at hc
  exact ⟨Q, hQ, hv, hd, fun x hx => ⟨1, by norm_num, hd x hx⟩, hc, hl, hh⟩

/-- The logical equivalence noted after Corollary 4.4. -/
theorem unbounded_density_iff_unbounded_minimum_degree :
    (∀ α : ℝ, ∃ P : Finset ℝ², P.Nonempty ∧ ConvexIndep P ∧
      α * P.card ≤ (unitPairs P).card) ↔
    (∀ k : ℕ, ∃ P : Finset ℝ², P.Nonempty ∧ ConvexIndep P ∧ HasUnitMinDegree P k) := by
  constructor
  · intro h k
    obtain ⟨P, hP, hv, hc⟩ := h ((k : ℝ) + 1)
    obtain ⟨Q, hQP, hQ, hd, _⟩ := dense_subset_min_degree ((k : ℝ) + 1) k
      (by linarith) P hP hc
    exact ⟨Q, hQ, convexIndep_subset hv hQP, fun x hx => (Nat.le_succ k).trans (hd x hx)⟩
  · intro h α
    obtain ⟨k, hk⟩ := exists_nat_ge (2 * α)
    obtain ⟨P, hP, hv, hd⟩ := h k
    have hsum : ∑ x ∈ P, k ≤ ∑ x ∈ P, unitDegree P x := Finset.sum_le_sum (fun x hx => hd x hx)
    rw [sum_unitDegree, Finset.sum_const, nsmul_eq_mul] at hsum
    have hs : (P.card : ℝ) * (k : ℝ) ≤ 2 * (unitPairs P).card := by exact_mod_cast hsum
    have hm := mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg P.card : (0 : ℝ) ≤ P.card)
    exact ⟨P, hP, hv, by nlinarith⟩

end
end Proof

end Combined_Corollaries

/- The upstream custom axiom-audit command is omitted for the platform soundness guard.
The original source and successful local axiom audit are retained in this packet. -/

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

/-!
# Bridge from the upstream Erdős 96 count to the mission vocabulary

The upstream count and the mission count both enumerate unordered pairs in a
finite set.  This file records the count identity, the induced identity of
the two supremum functions, and the resulting negative Problem 96 adapter.

This fragment is appended after `upstream/Erdos9697Complete.lean`.
-/

namespace Erdos9796MissionBridge

open Erdos9796Mission

lemma unitDistancePairsCount_eq_unitDistNum (A : Finset Plane) :
    unitDistancePairsCount A = unitDistNum A := by
  classical
  simp only [unitDistancePairsCount, unitDistNum]
  change
    (A.sym2.filter (Sym2.lift ⟨fun p q : Plane ↦ 0 < dist p q ∧ dist p q = 1, _⟩)).card =
    (A.sym2.filter (fun p ↦ dist p.out.1 p.out.2 = 1)).card
  congr 1
  ext p
  simp only [Finset.mem_filter]
  have hrel : (Sym2.lift ⟨fun p q : Plane ↦ 0 < dist p q ∧ dist p q = 1,
      fun p q ↦ congrArg (fun d : ℝ ↦ 0 < d ∧ d = 1) (dist_comm p q)⟩ p) ↔
      dist p.out.1 p.out.2 = 1 := by
    calc
      _ ↔ Proof.pairDistance p = 1 := by
        refine Sym2.inductionOn p ?_
        intro a b
        simp only [Sym2.lift_mk, Proof.pairDistance]
        constructor
        · exact fun h ↦ h.2
        · intro h
          exact ⟨by rw [h]; norm_num, h⟩
      _ ↔ _ := by rw [Proof.pairDistance_eq_out]
  rw [hrel]

lemma convexUnitDistanceCounts_eq (n : ℕ) :
    Erdos9796Mission.convexUnitDistanceCounts n = Erdos96.convexUnitDistanceCounts n := by
  ext k
  constructor
  · rintro ⟨A, hcard, hconv, rfl⟩
    exact ⟨A, hcard, hconv, (unitDistancePairsCount_eq_unitDistNum A).symm⟩
  · rintro ⟨A, hcard, hconv, rfl⟩
    exact ⟨A, hcard, hconv, unitDistancePairsCount_eq_unitDistNum A⟩

lemma maxConvexUnitDistances_eq (n : ℕ) :
    Erdos9796Mission.maxConvexUnitDistances n = Erdos96.maxConvexUnitDistances n := by
  simp only [Erdos9796Mission.maxConvexUnitDistances, Erdos96.maxConvexUnitDistances,
    convexUnitDistanceCounts_eq]

theorem problem96_false : ¬ Erdos9796Mission.Problem96 := by
  intro h
  apply Proof.erdos_96_false
  simpa only [Erdos9796Mission.Problem96, maxConvexUnitDistances_eq] using h

end Erdos9796MissionBridge


theorem solution : ¬ Erdos9796Mission.Problem96 := by
  exact Erdos9796MissionBridge.problem96_false

#print axioms solution
