-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.dir_deriv_eq_finite_diff_l_convex
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:33:40.112431+00:00
-- url     : https://prove2.me/submissions/99cc8b4b-b480-47aa-b8ac-67418cb18823

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexIntegralR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DirDeriv

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

theorem A_max_min (a b : ℝ) : A (a ⊔ b) + A (a ⊓ b) = A a + A b := by
  rcases le_total a b with h | h
  · rw [sup_of_le_right h, inf_of_le_left h]; ring
  · rw [sup_of_le_left h, inf_of_le_right h]

end S98Ham

open Classical
open scoped Pointwise
open DiscreteConvex.LConvexFunctionsD

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (g : (V → ℝ) → WithTop ℝ) (hg : LConvexIntegralR g)
    (p : V → ℝ) (hp : p ∈ DomR g) (hpZ : ∀ v, ∃ k : ℤ, p v = (k : ℝ)) (X : Finset V),
    DirDeriv g p (fun v => if v ∈ X then (1 : ℝ) else 0) =
      g (fun v => p v + (if v ∈ X then (1 : ℝ) else 0)) - g p) := by
  intro h
  open S98Ham in
  let g : (Fin 2 → ℝ) → WithTop ℝ := fun p => ((A (p 0) - A (p 1) : ℝ) : WithTop ℝ)
  have hA1 : S98Ham.A 1 = 0 := by simpa using S98Ham.A_rat 1
  have hg : LConvexIntegralR g := by
    refine ⟨?_, ?_, ?_⟩
    · intro p q
      simp only [g, Pi.sup_apply, Pi.inf_apply, ge_iff_le]
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      have h0 := S98Ham.A_max_min (p 0) (q 0)
      have h1 := S98Ham.A_max_min (p 1) (q 1)
      linarith
    · refine ⟨0, fun p a => ?_⟩
      simp only [g, map_add, mul_zero, WithTop.coe_zero, add_zero]
      congr 1; ring
    · intro w ⟨x, hx⟩
      exfalso
      obtain ⟨s, hs0, hs⟩ := S98Ham.exists_lt_mul (w 0)
      have := hx (fun v => if v = 0 then x v + s else x v)
      simp only [LinearWeightR, g, Fin.sum_univ_two, if_true, if_pos,
        show (1 : Fin 2) ≠ 0 by decide, if_false] at this
      rw [map_add] at this
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at this
      nlinarith
  have hp : (0 : Fin 2 → ℝ) ∈ DomR g := by simp [DomR, g]
  have key := h g hg 0 hp (fun v => ⟨0, by simp⟩) {0}
  have hL : DirDeriv g 0 (fun v => if v ∈ ({0} : Finset (Fin 2)) then (1 : ℝ) else 0) = ⊤ := by
    apply S98Ham.sInf_top
    intro M
    obtain ⟨t, ht0, ht⟩ := S98Ham.exists_lt_mul M
    refine ⟨1 / t * S98Ham.A t, ⟨t, ht0, ?_⟩, ?_⟩
    · have : g (fun v => (0 : Fin 2 → ℝ) v + t * (if v ∈ ({0} : Finset (Fin 2)) then (1 : ℝ) else 0))
          - g 0 = ((S98Ham.A t : ℝ) : WithTop ℝ) := by
        simp [g]
      rw [this]; rfl
    · rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ ht0]; linarith
  rw [hL] at key
  have hR : g (fun v => (0 : Fin 2 → ℝ) v + (if v ∈ ({0} : Finset (Fin 2)) then (1 : ℝ) else 0))
      - g 0 = ((0 : ℝ) : WithTop ℝ) := by
    simp [g, hA1]
  rw [hR] at key
  exact WithTop.top_ne_coe key
