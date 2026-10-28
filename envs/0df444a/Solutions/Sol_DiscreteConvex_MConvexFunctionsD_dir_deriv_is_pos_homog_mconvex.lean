-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsD.dir_deriv_is_pos_homog_mconvex
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:34:17.798595+00:00
-- url     : https://prove2.me/submissions/7b5f686d-5c43-49c3-a698-303ea4a45fe9

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DirDeriv
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMR

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

open scoped Classical in
theorem sInf_ne_top {S : Set (WithTop ℝ)} (r : ℝ) (hS : ∀ L ∈ S, L = (r : WithTop ℝ))
    (hr : (r : WithTop ℝ) ∈ S) : sInf S ≠ ⊤ := by
  show (if S ⊆ {⊤} ∨ ¬BddBelow S then ⊤ else _) ≠ ⊤
  rw [if_neg]
  · exact WithTop.coe_ne_top
  · push Not
    refine ⟨fun h => ?_, ⟨r, fun L hL => (hS L hL).ge⟩⟩
    have := h hr; simp at this

noncomputable def F3 (x : Fin 3 → ℝ) : WithTop ℝ :=
  if x 0 + x 1 + x 2 = 0 then ((A (x 0) - A (x 1) : ℝ) : WithTop ℝ) else ⊤

theorem F3_eval (x : Fin 3 → ℝ) (hx : x 0 + x 1 + x 2 = 0) :
    F3 x = ((A (x 0) - A (x 1) : ℝ) : WithTop ℝ) := by
  simp [F3, hx]

theorem F3_dom (x : Fin 3 → ℝ) (hx : F3 x ≠ ⊤) : x 0 + x 1 + x 2 = 0 := by
  by_contra h; simp [F3, h] at hx

theorem A_swap (a b c d : ℝ) (h : a + b = c + d) : A a + A b = A c + A d := by
  rw [← map_add, ← map_add, h]

end S98Ham

open Classical
open scoped Pointwise
open DiscreteConvex.MConvexFunctionsD

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f)
    (x : V → ℝ) (hx : x ∈ DomR f), ZeroMR (DirDeriv f x)) := by
  intro h
  open S98Ham in
  have hf : MExchangeAxiomR F3 := by
    intro x hx y hy u hu
    have hx0 := F3_dom x hx
    have hy0 := F3_dom y hy
    simp only [SuppPosR, Set.mem_ofPred_eq] at hu
    obtain ⟨v, hv⟩ : ∃ v, x v < y v := by
      by_contra hc; push Not at hc
      have := hc 0; have := hc 1; have := hc 2
      fin_cases u <;> simp at hu <;> linarith
    have huv : u ≠ v := by rintro rfl; linarith
    have hc : ∀ w, (CharVec u w - CharVec v w : ℝ) =
        (if w = u then 1 else 0) - (if w = v then 1 else 0) := by
      intro w; simp [CharVec]
    have hsum : (CharVec u 0 - CharVec v 0 : ℝ) + (CharVec u 1 - CharVec v 1 : ℝ)
        + (CharVec u 2 - CharVec v 2 : ℝ) = 0 := by
      rw [hc, hc, hc]
      fin_cases u <;> fin_cases v <;> simp at huv ⊢
    refine ⟨v, hv, 1, one_pos, fun α _ _ => ?_⟩
    rw [F3_eval x hx0, F3_eval y hy0,
      F3_eval _ (by linear_combination hx0 - α * hsum),
      F3_eval _ (by linear_combination hy0 + α * hsum)]
    simp only [ge_iff_le]
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
    have e0 := A_swap (x 0 - α * (CharVec u 0 - CharVec v 0 : ℝ))
      (y 0 + α * (CharVec u 0 - CharVec v 0 : ℝ)) (x 0) (y 0) (by ring)
    have e1 := A_swap (x 1 - α * (CharVec u 1 - CharVec v 1 : ℝ))
      (y 1 + α * (CharVec u 1 - CharVec v 1 : ℝ)) (x 1) (y 1) (by ring)
    linarith
  have hp : (0 : Fin 3 → ℝ) ∈ DomR F3 := by simp [DomR, F3]
  obtain ⟨hE, -⟩ := h F3 hf 0 hp
  let p : Fin 3 → ℝ := ![1, 1, -2]
  have hfin : ∀ d : Fin 3 → ℝ, (∀ t : ℝ, F3 (fun v => (0 : Fin 3 → ℝ) v + t * d v) = F3 0) →
      DirDeriv F3 0 d ≠ ⊤ := by
    intro d hd
    have h0 : F3 0 = ((0 : ℝ) : WithTop ℝ) := by simp [F3]
    apply S98Ham.sInf_ne_top 0
    · rintro L ⟨t, ht, rfl⟩
      rw [hd t, h0]
      show PosScalarMul (1 / t) (((0:ℝ):WithTop ℝ) - ((0:ℝ):WithTop ℝ)) = ((0:ℝ):WithTop ℝ)
      show PosScalarMul (1 / t) (((0 - 0 : ℝ)) : WithTop ℝ) = ((0:ℝ):WithTop ℝ)
      rw [sub_zero]
      show ((1 / t * 0 : ℝ) : WithTop ℝ) = _; simp
    · refine ⟨1, one_pos, ?_⟩
      rw [hd 1, h0]
      show ((0:ℝ):WithTop ℝ) = PosScalarMul (1 / 1) (((0:ℝ):WithTop ℝ) - ((0:ℝ):WithTop ℝ))
      show ((0:ℝ):WithTop ℝ) = PosScalarMul (1 / 1) (((0 - 0 : ℝ)) : WithTop ℝ)
      rw [sub_zero]
      show _ = ((1 / 1 * 0 : ℝ) : WithTop ℝ); simp
  have hpD : p ∈ DomR (DirDeriv F3 0) := hfin p (fun t => by
    rw [S98Ham.F3_eval _ (by simp [p]; ring), S98Ham.F3_eval 0 (by simp)]; simp [p])
  have h0D : (0 : Fin 3 → ℝ) ∈ DomR (DirDeriv F3 0) := hfin 0 (fun t => by simp; rfl)
  obtain ⟨v, hv, α0, hα0, hex⟩ := hE p hpD 0 h0D 0 (by simp [SuppPosR, p])
  have hv2 : v = 2 := by
    fin_cases v <;> simp [SuppNegR, p] at hv ⊢ <;> linarith
  subst hv2
  have hex := hex α0 hα0.le le_rfl
  have hT : DirDeriv F3 0 (fun w => p w - α0 * (CharVec 0 w - CharVec 2 w : ℝ)) = ⊤ := by
    apply S98Ham.sInf_top
    intro M
    obtain ⟨s, hs0, hs⟩ := S98Ham.exists_gt_mul (-M / α0)
    refine ⟨1 / (s / α0) * (- S98Ham.A s), ⟨s / α0, div_pos hs0 hα0, ?_⟩, ?_⟩
    · have : F3 (fun v => (0 : Fin 3 → ℝ) v + s / α0 *
          (fun w => p w - α0 * (CharVec 0 w - CharVec 2 w : ℝ)) v)
          - F3 0 = ((- S98Ham.A s : ℝ) : WithTop ℝ) := by
        rw [S98Ham.F3_eval _ (by simp [p, CharVec]; ring), S98Ham.F3_eval 0 (by simp)]
        have e : s / α0 * (1 - α0) = s / α0 - s := by field_simp
        simp [p, CharVec, e]
      rw [this]; rfl
    · have : 1 / (s / α0) * -S98Ham.A s = -(α0 * S98Ham.A s) / s := by
        field_simp
      rw [this, div_lt_iff₀ hs0]
      have := mul_lt_mul_of_pos_left hs hα0
      rw [div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hα0.ne'] at this
      linarith
  rw [hT, top_add, ge_iff_le, top_le_iff, WithTop.add_eq_top] at hex
  rcases hex with h1 | h1
  · exact hpD h1
  · exact h0D h1
