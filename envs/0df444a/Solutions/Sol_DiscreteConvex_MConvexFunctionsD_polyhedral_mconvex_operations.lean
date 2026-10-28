-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsD.polyhedral_mconvex_operations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:34:52.360385+00:00
-- url     : https://prove2.me/submissions/f3b0de82-2d1f-481d-bf06-5d2e189a76c3

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosScalarMul
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsConvexUniv
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SeparablePerturbR

open DiscreteConvex.MConvexFunctionsD

namespace MCOpsAux

theorem psm_top (c : ℝ) : PosScalarMul c ⊤ = if c = 0 then (0 : WithTop ℝ) else ⊤ := rfl

theorem psm_coe (c r : ℝ) : PosScalarMul c (r : WithTop ℝ) = ((c * r : ℝ) : WithTop ℝ) := rfl

theorem psm_ne_top {c : ℝ} (hc : 0 < c) (a : WithTop ℝ) :
    PosScalarMul c a ≠ ⊤ ↔ a ≠ ⊤ := by
  induction a using WithTop.recTopCoe with
  | top => simp [psm_top, hc.ne']
  | coe r =>
    rw [psm_coe]
    exact ⟨fun _ => WithTop.coe_ne_top, fun _ => WithTop.coe_ne_top⟩

theorem psm_add {c : ℝ} (hc : 0 < c) (a b : WithTop ℝ) :
    PosScalarMul c (a + b) = PosScalarMul c a + PosScalarMul c b := by
  induction a using WithTop.recTopCoe with
  | top => simp [psm_top, hc.ne']
  | coe r =>
    induction b using WithTop.recTopCoe with
    | top => simp [psm_top, hc.ne']
    | coe s =>
      rw [← WithTop.coe_add, psm_coe, psm_coe, psm_coe, ← WithTop.coe_add, mul_add]

theorem psm_mono {c : ℝ} (hc : 0 < c) {a b : WithTop ℝ} (h : a ≤ b) :
    PosScalarMul c a ≤ PosScalarMul c b := by
  induction b using WithTop.recTopCoe with
  | top =>
    rw [psm_top, if_neg hc.ne']
    exact le_top
  | coe s =>
    induction a using WithTop.recTopCoe with
    | top => exact absurd h (by simp)
    | coe r =>
      rw [psm_coe, psm_coe, WithTop.coe_le_coe]
      have : r ≤ s := WithTop.coe_le_coe.mp h
      exact mul_le_mul_of_nonneg_left this hc.le

theorem convex_pair {φ : ℝ → WithTop ℝ} (hφ : IsConvexUniv φ) {p q α : ℝ}
    (hqp : q < p) (h0 : 0 ≤ α) (h1 : α ≤ p - q) (hp : φ p ≠ ⊤) (hq : φ q ≠ ⊤) :
    φ (p - α) + φ (q + α) ≤ φ p + φ q := by
  have hd : 0 < p - q := sub_pos.mpr hqp
  set t := α / (p - q) with ht
  have t0 : 0 ≤ t := div_nonneg h0 hd.le
  have t1 : t ≤ 1 := (div_le_one hd).mpr h1
  have e : t * (p - q) = α := by rw [ht]; field_simp
  have A := hφ q p t t0 t1
  have B := hφ p q t t0 t1
  have eA : t * q + (1 - t) * p = p - α := by rw [← e]; ring
  have eB : t * p + (1 - t) * q = q + α := by rw [← e]; ring
  rw [eA] at A
  rw [eB] at B
  lift φ p to ℝ using hp with P
  lift φ q to ℝ using hq with Q
  calc φ (p - α) + φ (q + α)
      ≤ (PosScalarMul t (Q : WithTop ℝ) + PosScalarMul (1 - t) (P : WithTop ℝ)) +
        (PosScalarMul t (P : WithTop ℝ) + PosScalarMul (1 - t) (Q : WithTop ℝ)) :=
        add_le_add A B
    _ = ((P + Q : ℝ) : WithTop ℝ) := by
        simp only [psm_coe]
        rw [← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_inj]
        ring
    _ = (P : WithTop ℝ) + Q := WithTop.coe_add _ _

end MCOpsAux

open MCOpsAux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f) :
    (∀ lam : ℝ, 0 < lam → MExchangeAxiomR (fun x => PosScalarMul lam (f x))) ∧
    (∀ (a : V → ℝ) (beta : ℝ), beta ≠ 0 → MExchangeAxiomR (fun x => f (fun v => a v + beta * x v))) ∧
    (∀ p : V → ℝ, MExchangeAxiomR (LinearWeightR f p)) ∧
    (∀ phi : V → ℝ → WithTop ℝ, (∀ v, IsConvexUniv (phi v)) →
      (DomR (SeparablePerturbR f phi)).Nonempty → MExchangeAxiomR (SeparablePerturbR f phi)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) positive scalar multiple
    intro lam hlam x hx y hy u hu
    have hx' : f x ≠ ⊤ := (psm_ne_top hlam _).mp hx
    have hy' : f y ≠ ⊤ := (psm_ne_top hlam _).mp hy
    obtain ⟨v, hv, α0, hα0, H⟩ := hf x hx' y hy' u hu
    refine ⟨v, hv, α0, hα0, fun α h0 h1 => ?_⟩
    have := H α h0 h1
    show PosScalarMul lam (f x) + PosScalarMul lam (f y) ≥ _ + _
    rw [← psm_add hlam, ← psm_add hlam]
    exact psm_mono hlam this
  · -- (2) affine change of variables
    intro a beta hbeta x hx y hy u hu
    set X : V → ℝ := fun v => a v + beta * x v with hX
    set Y : V → ℝ := fun v => a v + beta * y v with hY
    have hxu : y u < x u := hu
    rcases lt_or_gt_of_ne hbeta with hneg | hpos
    · -- beta < 0
      have hu' : u ∈ SuppPosR Y X := by
        show X u < Y u
        simp only [hX, hY]
        nlinarith
      obtain ⟨v, hv, α0, hα0, H⟩ := hf Y hy X hx u hu'
      have hv' : Y v < X v := hv
      refine ⟨v, ?_, α0 / (-beta), div_pos hα0 (neg_pos.mpr hneg), fun α h0 h1 => ?_⟩
      · show x v < y v
        simp only [hX, hY] at hv'
        nlinarith
      have hγ0 : 0 ≤ α * (-beta) := mul_nonneg h0 (neg_pos.mpr hneg).le
      have hγ1 : α * (-beta) ≤ α0 := (le_div_iff₀ (neg_pos.mpr hneg)).mp h1
      have := H (α * (-beta)) hγ0 hγ1
      have e1 : (fun v_1 => a v_1 + beta *
          (x v_1 - α * ((CharVec u v_1 : ℝ) - (CharVec v v_1 : ℝ)))) =
          fun w => X w + α * (-beta) * ((CharVec u w : ℝ) - (CharVec v w : ℝ)) := by
        funext w; simp only [hX]; ring
      have e2 : (fun v_1 => a v_1 + beta *
          (y v_1 + α * ((CharVec u v_1 : ℝ) - (CharVec v v_1 : ℝ)))) =
          fun w => Y w - α * (-beta) * ((CharVec u w : ℝ) - (CharVec v w : ℝ)) := by
        funext w; simp only [hY]; ring
      show f X + f Y ≥ _ + _
      simp only []
      rw [e1, e2, ge_iff_le, add_comm (f X) (f Y)]
      rw [ge_iff_le] at this
      exact (add_comm _ _).le.trans this
    · -- beta > 0
      have hu' : u ∈ SuppPosR X Y := by
        show Y u < X u
        simp only [hX, hY]
        nlinarith
      obtain ⟨v, hv, α0, hα0, H⟩ := hf X hx Y hy u hu'
      have hv' : X v < Y v := hv
      refine ⟨v, ?_, α0 / beta, div_pos hα0 hpos, fun α h0 h1 => ?_⟩
      · show x v < y v
        simp only [hX, hY] at hv'
        nlinarith
      have hγ0 : 0 ≤ α * beta := mul_nonneg h0 hpos.le
      have hγ1 : α * beta ≤ α0 := (le_div_iff₀ hpos).mp h1
      have := H (α * beta) hγ0 hγ1
      have e1 : (fun v_1 => a v_1 + beta *
          (x v_1 - α * ((CharVec u v_1 : ℝ) - (CharVec v v_1 : ℝ)))) =
          fun w => X w - α * beta * ((CharVec u w : ℝ) - (CharVec v w : ℝ)) := by
        funext w; simp only [hX]; ring
      have e2 : (fun v_1 => a v_1 + beta *
          (y v_1 + α * ((CharVec u v_1 : ℝ) - (CharVec v v_1 : ℝ)))) =
          fun w => Y w + α * beta * ((CharVec u w : ℝ) - (CharVec v w : ℝ)) := by
        funext w; simp only [hY]; ring
      show f X + f Y ≥ _ + _
      simp only []
      rw [e1, e2]
      exact this
  · -- (3) linear weight
    intro p x hx y hy u hu
    have hx' : f x ≠ ⊤ := (WithTop.add_ne_top.mp hx).1
    have hy' : f y ≠ ⊤ := (WithTop.add_ne_top.mp hy).1
    obtain ⟨v, hv, α0, hα0, H⟩ := hf x hx' y hy' u hu
    refine ⟨v, hv, α0, hα0, fun α h0 h1 => ?_⟩
    have Hα := H α h0 h1
    set x' : V → ℝ := fun w => x w - α * ((CharVec u w : ℝ) - (CharVec v w : ℝ)) with hx'def
    set y' : V → ℝ := fun w => y w + α * ((CharVec u w : ℝ) - (CharVec v w : ℝ)) with hy'def
    have hsum : (∑ w, p w * x' w) + (∑ w, p w * y' w) = (∑ w, p w * x w) + (∑ w, p w * y w) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [hx'def, hy'def]; ring
    show (f x + _) + (f y + _) ≥ (f x' + _) + (f y' + _)
    lift f x to ℝ using hx' with A
    lift f y to ℝ using hy' with B
    have hx'' : f x' ≠ ⊤ := by
      intro h; rw [h, top_add] at Hα; exact absurd Hα (by simp [← WithTop.coe_add])
    have hy'' : f y' ≠ ⊤ := by
      intro h; rw [h, add_top] at Hα; exact absurd Hα (by simp [← WithTop.coe_add])
    lift f x' to ℝ using hx'' with A'
    lift f y' to ℝ using hy'' with B'
    rw [← WithTop.coe_add, ← WithTop.coe_add] at Hα
    have Hr : A' + B' ≤ A + B := WithTop.coe_le_coe.mp Hα
    simp only [← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe]
    linarith
  · -- (4) separable convex perturbation
    intro phi hphi _ x hx y hy u hu
    have hx1 : f x ≠ ⊤ := (WithTop.add_ne_top.mp hx).1
    have hy1 : f y ≠ ⊤ := (WithTop.add_ne_top.mp hy).1
    have hx2 : ∀ w, phi w (x w) ≠ ⊤ := by
      intro w h
      apply (WithTop.add_ne_top.mp hx).2
      exact WithTop.sum_eq_top.mpr ⟨w, Finset.mem_univ _, h⟩
    have hy2 : ∀ w, phi w (y w) ≠ ⊤ := by
      intro w h
      apply (WithTop.add_ne_top.mp hy).2
      exact WithTop.sum_eq_top.mpr ⟨w, Finset.mem_univ _, h⟩
    obtain ⟨v, hv, α0, hα0, H⟩ := hf x hx1 y hy1 u hu
    have hxu : y u < x u := hu
    have hxv : x v < y v := hv
    have huv : u ≠ v := by
      rintro rfl; linarith
    refine ⟨v, hv, min α0 (min (x u - y u) (y v - x v)),
      lt_min hα0 (lt_min (by linarith) (by linarith)), fun α h0 h1 => ?_⟩
    have hα0' : α ≤ α0 := h1.trans (min_le_left _ _)
    have hαu : α ≤ x u - y u := h1.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hαv : α ≤ y v - x v := h1.trans ((min_le_right _ _).trans (min_le_right _ _))
    have Hα := H α h0 hα0'
    show f x + _ + (f y + _) ≥ f _ + _ + (f _ + _)
    have key : ∀ w, phi w (x w - α * ((CharVec u w : ℝ) - (CharVec v w : ℝ))) +
        phi w (y w + α * ((CharVec u w : ℝ) - (CharVec v w : ℝ))) ≤
        phi w (x w) + phi w (y w) := by
      intro w
      by_cases hwu : w = u
      · subst hwu
        simp only [CharVec, if_true, if_neg huv, Int.cast_one, Int.cast_zero, sub_zero, mul_one]
        exact convex_pair (hphi w) hxu h0 hαu (hx2 w) (hy2 w)
      by_cases hwv : w = v
      · subst hwv
        simp only [CharVec, if_true, if_neg hwu, Int.cast_one, Int.cast_zero, zero_sub,
          mul_neg, mul_one, sub_neg_eq_add, ← sub_eq_add_neg]
        rw [add_comm (phi w (x w + α)), add_comm (phi w (x w))]
        exact convex_pair (hphi w) hxv h0 hαv (hy2 w) (hx2 w)
      · simp only [CharVec, if_neg hwu, if_neg hwv, Int.cast_zero, sub_zero, mul_zero, add_zero]
        exact le_rfl
    have hS := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => key w)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hS
    rw [ge_iff_le, add_add_add_comm, add_add_add_comm (f x)]
    exact add_le_add Hα hS
