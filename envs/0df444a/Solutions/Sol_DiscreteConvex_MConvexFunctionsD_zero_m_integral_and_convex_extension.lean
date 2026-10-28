-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsD.zero_m_integral_and_convex_extension
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:28:57.12479+00:00
-- url     : https://prove2.me/submissions/163fd7ac-85f3-4753-94cd-90fbce679581

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ConvexClosureVal
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMZR

open scoped Pointwise
open Classical

namespace DisZMI
open DiscreteConvex.MConvexFunctionsD

/-- Indicator (value 0) of `{x | ∑ x = 0, x i ≠ 0 for some i ∈ I}`. -/
noncomputable def F {W : Type} [Fintype W] (I : Set W) : (W → ℝ) → WithTop ℝ :=
  fun x => if ∑ w, x w = 0 ∧ ∃ i ∈ I, x i ≠ 0 then 0 else ⊤

lemma charvec_sum {W : Type} [Fintype W] [DecidableEq W] (u : W) :
    ∑ w, ((CharVec u w : ℤ) : ℝ) = 1 := by
  simp [CharVec]

lemma charvec_abs {W : Type} [DecidableEq W] (u v w : W) :
    |((CharVec u w : ℤ) : ℝ) - ((CharVec v w : ℤ) : ℝ)| ≤ 1 := by
  unfold CharVec; split_ifs <;> norm_num

lemma exch {W : Type} [Fintype W] [DecidableEq W] (I : Set W) : MExchangeAxiomR (F I) := by
  intro x hx y hy u hu
  have hx' : ∑ w, x w = 0 ∧ ∃ i ∈ I, x i ≠ 0 := by
    by_contra hc; exact hx (if_neg hc)
  have hy' : ∑ w, y w = 0 ∧ ∃ i ∈ I, y i ≠ 0 := by
    by_contra hc; exact hy (if_neg hc)
  have hfx : F I x = 0 := if_pos hx'
  have hfy : F I y = 0 := if_pos hy'
  obtain ⟨hxs, i, hiI, hxi⟩ := hx'
  obtain ⟨hys, j, hjI, hyj⟩ := hy'
  obtain ⟨v, hv⟩ : ∃ v, x v < y v := by
    by_contra hc
    push Not at hc
    have : ∑ w, y w < ∑ w, x w :=
      Finset.sum_lt_sum (fun w _ => hc w) ⟨u, Finset.mem_univ _, hu⟩
    linarith
  have hm : 0 < min |x i| |y j| := lt_min (abs_pos.2 hxi) (abs_pos.2 hyj)
  refine ⟨v, hv, min |x i| |y j| / 2, half_pos hm, fun α h0 h1 => ?_⟩
  have hlx : α < |x i| := by have := min_le_left |x i| |y j|; linarith
  have hly : α < |y j| := by have := min_le_right |x i| |y j|; linarith
  have key1 : F I (fun w => x w - α * (CharVec u w - CharVec v w : ℝ)) = 0 := by
    apply if_pos
    refine ⟨?_, i, hiI, ?_⟩
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, charvec_sum,
        charvec_sum, hxs]; ring
    · intro h
      have hb := charvec_abs u v i
      have e : x i = α * (((CharVec u i : ℤ) : ℝ) - ((CharVec v i : ℤ) : ℝ)) := by linarith
      have : |x i| ≤ α := by
        rw [e, abs_mul, abs_of_nonneg h0]
        nlinarith
      linarith
  have key2 : F I (fun w => y w + α * (CharVec u w - CharVec v w : ℝ)) = 0 := by
    apply if_pos
    refine ⟨?_, j, hjI, ?_⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, charvec_sum,
        charvec_sum, hys]; ring
    · intro h
      have hb := charvec_abs u v j
      have e : y j = -(α * (((CharVec u j : ℤ) : ℝ) - ((CharVec v j : ℤ) : ℝ))) := by linarith
      have : |y j| ≤ α := by
        rw [e, abs_neg, abs_mul, abs_of_nonneg h0]
        nlinarith
      linarith
  rw [key1, key2, hfx, hfy]

lemma poshom {W : Type} [Fintype W] [DecidableEq W] :
    PosHomogeneous (F (Set.univ : Set W)) := by
  intro x t ht
  simp only [F]
  have e : (∑ w, t * x w = 0 ∧ ∃ i ∈ (Set.univ : Set W), t * x i ≠ 0) ↔
      (∑ w, x w = 0 ∧ ∃ i ∈ (Set.univ : Set W), x i ≠ 0) := by
    rw [← Finset.mul_sum]; simp [ht.ne']
  by_cases h : ∑ w, x w = 0 ∧ ∃ i ∈ (Set.univ : Set W), x i ≠ 0
  · rw [if_pos h, if_pos (e.2 h)]; simp [PosScalarMul]
  · rw [if_neg h, if_neg (fun h' => h (e.1 h'))]; simp [PosScalarMul, ht.ne']

lemma zeroMR {W : Type} [Fintype W] [DecidableEq W] : ZeroMR (F (Set.univ : Set W)) :=
  ⟨exch _, poshom⟩

lemma not_int : ¬ IntegralPolyhedralFunction (F (Set.univ : Set (Fin 2))) := by
  intro h
  have hLW : LinearWeightR (F (Set.univ : Set (Fin 2))) 0 = F Set.univ := by
    funext x; simp [LinearWeightR]
  have hF : ∀ y : Fin 2 → ℝ, (0 : WithTop ℝ) ≤ F Set.univ y := by
    intro y; unfold F; split_ifs <;> simp
  let a : Fin 2 → ℝ := ![1, -1]
  let b : Fin 2 → ℝ := ![-1, 1]
  have hFa : F (Set.univ : Set (Fin 2)) a = 0 := by
    unfold F; rw [if_pos]; refine ⟨by simp [a, Fin.sum_univ_two], 0, Set.mem_univ _, by simp [a]⟩
  have hFb : F (Set.univ : Set (Fin 2)) b = 0 := by
    unfold F; rw [if_pos]; refine ⟨by simp [b, Fin.sum_univ_two], 0, Set.mem_univ _, by simp [b]⟩
  have hF0 : F (Set.univ : Set (Fin 2)) 0 = ⊤ := by
    unfold F; rw [if_neg]; simp
  have ha : a ∈ ArgMinOn (LinearWeightR (F (Set.univ : Set (Fin 2))) 0) := by
    rw [hLW]; intro y; rw [hFa]; exact hF y
  have hb : b ∈ ArgMinOn (LinearWeightR (F (Set.univ : Set (Fin 2))) 0) := by
    rw [hLW]; intro y; rw [hFb]; exact hF y
  have h0 : (0 : Fin 2 → ℝ) ∉ ArgMinOn (LinearWeightR (F (Set.univ : Set (Fin 2))) 0) := by
    rw [hLW]; intro h0; have := h0 a; rw [hF0, hFa] at this; simp at this
  have hI := h 0 ⟨a, ha⟩
  apply h0
  rw [hI]
  have hai : a ∈ {x : Fin 2 → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)} := by
    intro v; fin_cases v
    · exact ⟨1, by simp [a]⟩
    · exact ⟨-1, by simp [a]⟩
  have hbi : b ∈ {x : Fin 2 → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)} := by
    intro v; fin_cases v
    · exact ⟨-1, by simp [b]⟩
    · exact ⟨1, by simp [b]⟩
  have hs := segment_subset_convexHull (𝕜 := ℝ) (show a ∈ _ ∩ _ from ⟨ha, hai⟩)
    (show b ∈ _ ∩ _ from ⟨hb, hbi⟩)
  apply hs
  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
  funext i; fin_cases i <;> simp [a, b]

end DisZMI

open DiscreteConvex.MConvexFunctionsD in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (f : (V → ℝ) → WithTop ℝ)
    (fZ : (V → ℤ) → WithTop ℝ),
    (ZeroMZR f ↔ ZeroMR f) ∧ (ZeroMZ fZ → ZeroMR (ConvexClosureVal fZ))) := by
  intro h
  have := ((h (V := Fin 2) (DisZMI.F Set.univ) (fun _ => ⊤)).1).2 DisZMI.zeroMR
  exact DisZMI.not_int this.2
