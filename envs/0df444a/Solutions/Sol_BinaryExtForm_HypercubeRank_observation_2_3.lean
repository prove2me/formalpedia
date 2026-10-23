-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.observation_2_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T19:02:55.52165+00:00
-- url     : https://prove2.me/submissions/5f9a3ac1-6055-4925-a05b-b2cb2761f3d5

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank.FiberProof

lemma binarization_convex {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) : Convex ℝ B := by
  obtain ⟨S,hS⟩ := hB.1
  rw [hS]
  exact convex_convexHull ℝ _

lemma binary_label {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {p : Fin (d + 1) → ℝ}
    (hp : p ∈ B) (hb : IsBinaryY p) : ∃ m : ℕ, m ≤ k ∧ p 0 = m := by
  have hh : p 0 ∈ (fun p => p 0) '' {p | p ∈ B ∧ IsBinaryY p} := ⟨p,⟨hp,hb⟩,rfl⟩
  rw [hB.2.2.2] at hh
  exact hh

lemma binary_fiber_no_lt {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {u v : Fin (d + 1) → ℝ}
    (hu : u ∈ B) (hv : v ∈ B) (hb : IsBinaryY u)
    (hy : yproj u = yproj v) : ¬ u 0 < v 0 := by
  intro hlt
  have hb' : IsBinaryY v := by
    intro i
    have heq : u i.succ = v i.succ := congrFun hy i
    rw [← heq]
    exact hb i
  obtain ⟨a,ha,hua⟩ := binary_label hB hu hb
  obtain ⟨b,hbnd,hvb⟩ := binary_label hB hv hb'
  have hab : a < b := by exact_mod_cast (show (a:ℝ)<b by simpa [hua,hvb] using hlt)
  have hdiff : 1 ≤ v 0-u 0 := by
    have hh : (a:ℝ)+1 ≤ b := by exact_mod_cast (show a+1≤b by omega)
    rw [hua,hvb]
    linarith
  let t : ℝ := 1 / (2*(v 0-u 0))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_iff₀ (by linarith : 0 < 2*(v 0-u 0))).mpr; linarith
  let p : Fin (d+1) → ℝ := (1-t) • u + t • v
  have hp : p ∈ B := binarization_convex hB hu hv (sub_nonneg.mpr ht1) ht.le (by ring)
  have hpy (i : Fin d) : p i.succ = u i.succ := by
    have hh : u i.succ = v i.succ := congrFun hy i
    simp only [p,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [← hh]
    ring
  have hpb : IsBinaryY p := by
    intro i
    rw [hpy]
    exact hb i
  obtain ⟨m,hm,hpm⟩ := binary_label hB hp hpb
  have hp0 : p 0 = u 0+1/2 := by
    simp only [p,Pi.add_apply,Pi.smul_apply,smul_eq_mul,t]
    field_simp
    ring
  have ham : a < m := by
    have hh : (a : ℝ) < m := by rw [← hpm,hp0,hua]; norm_num
    exact_mod_cast hh
  have hma : m < a+1 := by
    have hh : (m : ℝ) < (a : ℝ) + 1 := by rw [← hpm,hp0,hua]; norm_num
    exact_mod_cast hh
  omega

lemma binary_fiber_unique {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {u v : Fin (d + 1) → ℝ}
    (hu : u ∈ B) (hv : v ∈ B) (hb : IsBinaryY u)
    (hy : yproj u = yproj v) : u = v := by
  have hb' : IsBinaryY v := by
    intro i
    have heq : u i.succ = v i.succ := congrFun hy i
    rw [← heq]
    exact hb i
  have hx : u 0 = v 0 := le_antisymm
    (le_of_not_gt (binary_fiber_no_lt hB hv hu hb' hy.symm))
    (le_of_not_gt (binary_fiber_no_lt hB hu hv hb hy))
  ext i
  refine Fin.cases hx (fun j => congrFun hy j) i

end BinaryExtForm.HypercubeRank.FiberProof

namespace BinaryExtForm.HypercubeRank.FiberProof

lemma binary_point_extreme {d k : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) {p : Fin (d+1) → ℝ}
    (hp : p ∈ B) (hpbin : IsBinaryY p) : p ∈ Set.extremePoints ℝ B := by
  refine ⟨hp,?_⟩
  intro u hu v hv hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  have hy : yproj u = yproj p := by
    ext i
    have hcoord : a*u i.succ+b*v i.succ=p i.succ := congrFun heq i.succ
    obtain ⟨hu0,hu1⟩ := hB.2.2.1 u hu i
    obtain ⟨hv0,hv1⟩ := hB.2.2.1 v hv i
    rcases hpbin i with h0|h1
    · change u i.succ=p i.succ
      rw [h0]
      rw [h0] at hcoord
      nlinarith [mul_nonneg hb.le hv0]
    · change u i.succ=p i.succ
      rw [h1]
      rw [h1] at hcoord
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hv1)]
  exact (binary_fiber_unique hB hp hu hpbin hy.symm).symm

end BinaryExtForm.HypercubeRank.FiberProof

open BinaryExtForm.HypercubeRank BinaryExtForm.HypercubeRank.FiberProof

theorem solution {d k : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsBinarization d k B) :
    (∀ p ∈ B, ∀ q ∈ B, IsBinaryY p → yproj q = yproj p → q 0 = p 0) ∧
    (∀ p ∈ B, IsBinaryY p → (∃ m : ℕ, m ≤ k ∧ p 0 = m) ∧ p ∈ Set.extremePoints ℝ B) := by
  constructor
  · intro p hp q hq hbin hy
    exact congrFun (binary_fiber_unique hB hp hq hbin hy.symm).symm 0
  · intro p hp hbin
    exact ⟨binary_label hB hp hbin,binary_point_extreme hB hp hbin⟩
