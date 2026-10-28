-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsE.dir_deriv_eq_finite_diff_on_integral_mconvex
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:33:58.484509+00:00
-- url     : https://prove2.me/submissions/360005bb-c7fe-4d36-a1d1-45e41979eea6

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DirDeriv
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MConvexIntegralR

namespace S98Ham

theorem exists_A : ∃ A : ℝ →+ ℝ, A 1 = 0 ∧ A (Real.sqrt 2) = 1 ∧
    ∀ (q : ℚ), A (q : ℝ) = 0 := by
  have hx : Real.sqrt 2 ∉ (ℚ ∙ (1 : ℝ)) := by
    intro h
    rw [Submodule.mem_span_singleton] at h
    obtain ⟨q, hq⟩ := h
    apply irrational_sqrt_two
    exact ⟨q, by rw [← hq, Rat.smul_def, mul_one]⟩
  obtain ⟨f, hf, hp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hq : ∀ q : ℚ, f (q : ℝ) = 0 := by
    intro q
    have : f (q : ℝ) ∈ (ℚ ∙ (1 : ℝ)).map f := Submodule.mem_map_of_mem
      (Submodule.mem_span_singleton.2 ⟨q, by rw [Rat.smul_def, mul_one]⟩)
    rw [hp] at this; simpa using this
  refine ⟨(((f (Real.sqrt 2))⁻¹ • f : Module.Dual ℚ ℝ).toAddMonoidHom.comp
    (AddMonoidHom.id ℝ)).comp (AddMonoidHom.id ℝ) |>
      fun g => (Rat.castHom ℝ : ℚ →+* ℝ).toAddMonoidHom.comp g, ?_, ?_, ?_⟩
  · have h1 : f 1 = 0 := by simpa using hq 1
    simp [h1]
  · simp [inv_mul_cancel₀ hf]
  · intro q; simp [hq q]

/-- the abstract additive map. -/
noncomputable def A : ℝ →+ ℝ := Classical.choose exists_A

theorem A_rat (q : ℚ) : A (q : ℝ) = 0 := (Classical.choose_spec exists_A).2.2 q
theorem A_sqrt : A (Real.sqrt 2) = 1 := (Classical.choose_spec exists_A).2.1

theorem A_nat_mul (n : ℕ) (x : ℝ) : A ((n : ℝ) * x) = n * A x := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

/-- Points `t ∈ (0,1)` with `A t` very negative. -/
theorem exists_neg (M : ℝ) : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ A t < -M := by
  obtain ⟨n, hn⟩ := exists_nat_gt M
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (n : ℝ) * Real.sqrt 2 < n * Real.sqrt 2 + 1 by linarith)
  refine ⟨q - n * Real.sqrt 2, by linarith, by linarith, ?_⟩
  rw [map_sub, A_rat, A_nat_mul, A_sqrt]; linarith

theorem exists_pos (M : ℝ) : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ M < A t := by
  obtain ⟨n, hn⟩ := exists_nat_gt M
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show -((n : ℝ) * Real.sqrt 2) < -(n * Real.sqrt 2) + 1 by linarith)
  refine ⟨q + n * Real.sqrt 2, by linarith, by linarith, ?_⟩
  rw [map_add, A_rat, A_nat_mul, A_sqrt]; linarith

/-- `A t < c t` for some `t > 0`. -/
theorem exists_lt_mul (c : ℝ) : ∃ t : ℝ, 0 < t ∧ A t < c * t := by
  obtain ⟨t, h0, h1, h⟩ := exists_neg |c|
  refine ⟨t, h0, ?_⟩
  have : -|c| * t ≤ c * t := by nlinarith [neg_abs_le c]
  nlinarith [abs_nonneg c]

theorem exists_gt_mul (c : ℝ) : ∃ t : ℝ, 0 < t ∧ c * t < A t := by
  obtain ⟨t, h0, h1, h⟩ := exists_pos |c|
  refine ⟨t, h0, ?_⟩
  have : c * t ≤ |c| * t := by nlinarith [le_abs_self c]
  nlinarith [abs_nonneg c]

open scoped Classical in
theorem sInf_top {S : Set (WithTop ℝ)} (h : ∀ M : ℝ, ∃ r : ℝ, (r : WithTop ℝ) ∈ S ∧ r < M) :
    sInf S = ⊤ := by
  show (if S ⊆ {⊤} ∨ ¬BddBelow S then ⊤ else _) = ⊤
  rw [if_pos]
  right
  rintro ⟨b, hb⟩
  induction b with
  | top => obtain ⟨r, hr, -⟩ := h 0; exact absurd (hb hr) (by simp)
  | coe b =>
    obtain ⟨r, hr, hlt⟩ := h b
    have := hb hr
    rw [WithTop.coe_le_coe] at this; linarith

noncomputable def F2 (x : Fin 2 → ℝ) : WithTop ℝ :=
  if x 0 + x 1 = 0 then ((A (x 0) : ℝ) : WithTop ℝ) else ⊤

theorem F2_eval (x : Fin 2 → ℝ) (hx : x 0 + x 1 = 0) : F2 x = ((A (x 0) : ℝ) : WithTop ℝ) := by
  simp [F2, hx]

theorem F2_dom (x : Fin 2 → ℝ) (hx : F2 x ≠ ⊤) : x 0 + x 1 = 0 := by
  by_contra h; simp [F2, h] at hx

end S98Ham

open Classical
open scoped Pointwise
open DiscreteConvex.MConvexFunctionsE

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (f : (V → ℝ) → WithTop ℝ)
    (hf : MConvexIntegralR f) (x : V → ℝ) (hx : x ∈ DomR f)
    (hxZ : ∀ v, ∃ k : ℤ, x v = (k : ℝ)) (u v : V),
    DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ)) =
      f (fun w => x w - (CharVec u w : ℝ) + (CharVec v w : ℝ)) - f x) := by
  intro h
  open S98Ham in
  have hf : MConvexIntegralR F2 := by
    refine ⟨?_, ?_⟩
    · intro x hx y hy u hu
      have hx0 := F2_dom x hx
      have hy0 := F2_dom y hy
      simp only [SuppPosR, Set.mem_ofPred_eq] at hu
      fin_cases u
      · refine ⟨1, show x 1 < y 1 by simp at hu; linarith, 1, one_pos, fun α _ _ => ?_⟩
        rw [F2_eval x hx0, F2_eval y hy0, F2_eval _ (by simp [CharVec]; linarith),
          F2_eval _ (by simp [CharVec]; linarith)]
        simp only [CharVec, ge_iff_le]
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
        simp [map_sub]
      · refine ⟨0, show x 0 < y 0 by simp at hu; linarith, 1, one_pos, fun α _ _ => ?_⟩
        rw [F2_eval x hx0, F2_eval y hy0, F2_eval _ (by simp [CharVec]; linarith),
          F2_eval _ (by simp [CharVec]; linarith)]
        simp only [CharVec, ge_iff_le]
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
        simp [map_add]; linarith
    · intro w ⟨x, hx⟩
      exfalso
      have h0 := hx 0
      have hxd : x 0 + x 1 = 0 := by
        by_contra hne
        simp [LinearWeightR, F2, hne] at h0
      obtain ⟨s, hs0, hs⟩ := exists_lt_mul (w 0 - w 1)
      have h1 := hx ![x 0 + s, x 1 - s]
      simp only [LinearWeightR] at h1
      rw [F2_eval x hxd, F2_eval _ (by simp; linarith)] at h1
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h1
      simp [Fin.sum_univ_two, map_add] at h1
      nlinarith
  have hp : (0 : Fin 2 → ℝ) ∈ DomR F2 := by simp [DomR, F2]
  have key := h F2 hf 0 hp (fun v => ⟨0, by simp⟩) 0 1
  have hL : DirDeriv F2 0 (fun w => (CharVec 1 w - CharVec 0 w : ℝ)) = ⊤ := by
    apply S98Ham.sInf_top
    intro M
    obtain ⟨t, ht0, ht⟩ := S98Ham.exists_gt_mul (-M)
    refine ⟨1 / t * (- S98Ham.A t), ⟨t, ht0, ?_⟩, ?_⟩
    · have : F2 (fun v => (0 : Fin 2 → ℝ) v + t * (CharVec 1 v - CharVec 0 v : ℝ))
          - F2 0 = ((- S98Ham.A t : ℝ) : WithTop ℝ) := by
        rw [S98Ham.F2_eval _ (by simp [CharVec]), S98Ham.F2_eval 0 (by simp)]
        simp [CharVec]
      rw [this]; rfl
    · rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ ht0]; linarith
  rw [hL] at key
  have hR : F2 (fun w => (0 : Fin 2 → ℝ) w - (CharVec 0 w : ℝ) + (CharVec 1 w : ℝ))
      - F2 0 = ((S98Ham.A (-1) - S98Ham.A 0 : ℝ) : WithTop ℝ) := by
    rw [S98Ham.F2_eval _ (by simp [CharVec]), S98Ham.F2_eval 0 (by simp)]
    simp [CharVec]
  rw [hR] at key
  exact WithTop.top_ne_coe key
