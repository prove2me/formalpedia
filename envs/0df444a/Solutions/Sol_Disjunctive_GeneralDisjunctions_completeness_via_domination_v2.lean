-- Prove2me | solution 1 for Disjunctive.GeneralDisjunctions.completeness_via_domination_v2
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:41:39.658888+00:00
-- url     : https://prove2.me/submissions/f099c785-243f-430b-a6ef-62b2c17c537b

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Cglp_v2



namespace Disjunctive.GeneralDisjunctions

noncomputable section CompCx

def cxA : Matrix (Fin 2) (Fin 1) ℝ := !![1; -1]
def cxb : Fin 2 → ℝ := ![2, -1]
def cxd : Fin 3 → Fin 1 → ℝ := ![![-1], ![1], ![0]]
def cxd0 : Fin 3 → ℝ := ![0, 3, 1]
def cxu : Fin 3 → Fin 2 → ℝ := ![![1/6, 0], ![0, 1/6], ![0, 0]]
def cxu0 : Fin 3 → ℝ := ![1/6, 1/6, 1/3]
def cxal : Fin 1 → ℝ := fun _ => 0

lemma cx_eqs {α : Fin 1 → ℝ} {u : Fin 3 → Fin 2 → ℝ} {u0 : Fin 3 → ℝ} {β : ℝ}
    (h : IsCGLP116Feasible cxA cxb cxd cxd0 α u u0 β) :
    α 0 = u 0 0 - u 0 1 - u0 0 ∧ β = 2 * u 0 0 - u 0 1 ∧
    α 0 = u 1 0 - u 1 1 + u0 1 ∧ β = 2 * u 1 0 - u 1 1 + 3 * u0 1 ∧
    α 0 = u 2 0 - u 2 1 ∧ β = 2 * u 2 0 - u 2 1 + u0 2 ∧
    (u 0 0 + u 0 1 + u0 0) + (u 1 0 + u 1 1 + u0 1) + (u 2 0 + u 2 1 + u0 2) = 1 := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  have a0 := congrFun (h1 0) 0
  have a1 := congrFun (h1 1) 0
  have a2 := congrFun (h1 2) 0
  have b0 := h2 0
  have b1 := h2 1
  have b2 := h2 2
  simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_two, cxA, cxb, cxd, cxd0] at a0 a1 a2 b0 b1 b2
  simp [Fin.sum_univ_two, Fin.sum_univ_three] at h3
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

lemma cx_feas_iff {α : Fin 1 → ℝ} {u : Fin 3 → Fin 2 → ℝ} {u0 : Fin 3 → ℝ} {β : ℝ}
    (e1 : α 0 = u 0 0 - u 0 1 - u0 0) (e2 : β = 2 * u 0 0 - u 0 1)
    (e3 : α 0 = u 1 0 - u 1 1 + u0 1) (e4 : β = 2 * u 1 0 - u 1 1 + 3 * u0 1)
    (e5 : α 0 = u 2 0 - u 2 1) (e6 : β = 2 * u 2 0 - u 2 1 + u0 2)
    (e7 : (u 0 0 + u 0 1 + u0 0) + (u 1 0 + u 1 1 + u0 1) + (u 2 0 + u 2 1 + u0 2) = 1)
    (hu : ∀ t i, 0 ≤ u t i) (hu0 : ∀ t, 0 ≤ u0 t) :
    IsCGLP116Feasible cxA cxb cxd cxd0 α u u0 β := by
  refine ⟨fun t => ?_, fun t => ?_, ?_, hu, hu0⟩
  · funext j; fin_cases j; fin_cases t <;>
      simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_two, cxA, cxd] <;> linarith
  · fin_cases t <;> simp [dotProduct, Fin.sum_univ_two, cxb, cxd0] <;> linarith
  · simp [Fin.sum_univ_two, Fin.sum_univ_three]; linarith

lemma cx_w_feas : IsCGLP116Feasible cxA cxb cxd cxd0 cxal cxu cxu0 (1/3) := by
  refine cx_feas_iff ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun t i => ?_) (fun t => ?_)
  rotate_right 2
  · fin_cases t <;> fin_cases i <;> simp [cxu] <;> norm_num
  · fin_cases t <;> simp [cxu0] <;> norm_num
  all_goals simp [cxal, cxu, cxu0]
  all_goals norm_num

lemma cx_unique {α : Fin 1 → ℝ} {u : Fin 3 → Fin 2 → ℝ} {u0 : Fin 3 → ℝ} {β : ℝ}
    (h : IsCGLP116Feasible cxA cxb cxd cxd0 α u u0 β)
    (z1 : u 0 1 = 0) (z2 : u 1 0 = 0) (z3 : u 2 0 = 0) (z4 : u 2 1 = 0) :
    (α, u, u0, β) = (cxal, cxu, cxu0, (1/3 : ℝ)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := cx_eqs h
  have hα : α 0 = 0 := by linarith
  have hβ : β = 1/3 := by linarith
  have h00 : u 0 0 = 1/6 := by linarith
  have h11 : u 1 1 = 1/6 := by linarith
  have h00' : u0 0 = 1/6 := by linarith
  have h01' : u0 1 = 1/6 := by linarith
  have h02' : u0 2 = 1/3 := by linarith
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ hβ))
  · funext j; fin_cases j; simpa [cxal] using hα
  · funext t i; fin_cases t <;> fin_cases i <;> simp [cxu, *]
  · funext t; fin_cases t <;> simp [cxu0, *]

lemma cx_basic : IsBasicCGLP116Solution cxA cxb cxd cxd0 cxal cxu cxu0 (1/3) := by
  refine ⟨cx_w_feas, ?_⟩
  rintro ⟨pα, pu, pu0, pβ⟩ hp ⟨qα, qu, qu0, qβ⟩ hq ⟨a, b, ha, hb, hab, heq⟩
  have hp' : IsCGLP116Feasible cxA cxb cxd cxd0 pα pu pu0 pβ := hp
  have hq' : IsCGLP116Feasible cxA cxb cxd cxd0 qα qu qu0 qβ := hq
  have hu := congrArg (fun z => z.2.1) heq
  simp only [Prod.smul_mk, Prod.mk_add_mk] at hu
  have zero_of : ∀ t i, cxu t i = 0 → pu t i = 0 := by
    intro t i hz
    have := congrFun (congrFun hu t) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz] at this
    have h1 := hp'.2.2.2.1 t i
    have h2 := hq'.2.2.2.1 t i
    nlinarith [mul_nonneg ha.le h1, mul_nonneg hb.le h2]
  exact cx_unique hp' (zero_of 0 1 (by simp [cxu])) (zero_of 1 0 (by simp [cxu]))
    (zero_of 2 0 (by simp [cxu])) (zero_of 2 1 (by simp [cxu]))

lemma cx_not_cond (μ : ℝ) (hμ : 0 < μ) (u : Fin 3 → Fin 2 → ℝ) (u0 : Fin 3 → ℝ)
    (h : IsCGLP116Feasible cxA cxb cxd cxd0 (μ • cxal) u u0 (μ * (1/3))) :
    ¬ SatisfiesThm119Condition cxA u := by
  rintro ⟨ι, -, -, hs⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := cx_eqs h
  have hα : (μ • cxal) 0 = 0 := by simp [cxal]
  have hu := h.2.2.2.1
  have hu0 := h.2.2.2.2
  have hi : ι 0 = 0 ∨ ι 0 = 1 := by
    rcases Fin.exists_fin_two.mp ⟨ι 0, rfl⟩ with h | h <;> simp [h]
  rcases hi with hi | hi
  · have : u 1 1 = 0 := hs 1 1 (by simp [Finset.mem_image, Fin.forall_fin_one, hi])
    nlinarith [hu 1 0, hu0 1]
  · have : u 0 0 = 0 := hs 0 0 (by simp [Finset.mem_image, Fin.forall_fin_one, hi])
    nlinarith [hu 0 1, hu0 0]

def cxx : Fin 1 → ℝ := fun _ => 3/2

lemma cx_uniqueMin : IsCGLP116UniqueMin cxA cxb cxd cxd0 cxx cxal (1/3) := by
  refine ⟨⟨cxu, cxu0, cx_w_feas⟩, ?_, ?_⟩
  · intro α' β' u' u0' h
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := cx_eqs h
    have hu := h.2.2.2.1
    have hu0 := h.2.2.2.2
    simp only [dotProduct, Fin.sum_univ_one, cxal, cxx]
    linarith [hu 0 0, hu 0 1, hu 1 0, hu 1 1, hu 2 0, hu 2 1, hu0 0, hu0 1, hu0 2]
  · intro α' β' u' u0' h heq
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := cx_eqs h
    have hu := h.2.2.2.1
    have hu0 := h.2.2.2.2
    simp only [dotProduct, Fin.sum_univ_one, cxal, cxx] at heq
    have z1 : u' 0 1 = 0 := le_antisymm (by
      linarith [hu 0 0, hu 0 1, hu 1 0, hu 1 1, hu 2 0, hu 2 1, hu0 0, hu0 1, hu0 2]) (hu 0 1)
    have z2 : u' 1 0 = 0 := le_antisymm (by
      linarith [hu 0 0, hu 0 1, hu 1 0, hu 1 1, hu 2 0, hu 2 1, hu0 0, hu0 1, hu0 2]) (hu 1 0)
    have z3 : u' 2 0 = 0 := le_antisymm (by
      linarith [hu 0 0, hu 0 1, hu 1 0, hu 1 1, hu 2 0, hu 2 1, hu0 0, hu0 1, hu0 2]) (hu 2 0)
    have z4 : u' 2 1 = 0 := le_antisymm (by
      linarith [hu 0 0, hu 0 1, hu 1 0, hu 1 1, hu 2 0, hu 2 1, hu0 0, hu0 1, hu0 2]) (hu 2 1)
    have := cx_unique h z1 z2 z3 z4
    simp only [Prod.mk.injEq] at this
    exact ⟨this.1, this.2.2.2⟩

def cxat : Fin 1 → ℝ := fun _ => -1/5
def cxut : Fin 3 → Fin 2 → ℝ := ![![0, 0], ![0, 3/10], ![0, 1/5]]
def cxut0 : Fin 3 → ℝ := ![1/5, 1/10, 1/5]

lemma cx_t_feas : IsCGLP116Feasible cxA cxb cxd cxd0 cxat cxut cxut0 0 := by
  refine cx_feas_iff ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun t i => ?_) (fun t => ?_)
  rotate_right 2
  · fin_cases t <;> fin_cases i <;> simp [cxut] <;> norm_num
  · fin_cases t <;> simp [cxut0] <;> norm_num
  all_goals simp [cxat, cxut, cxut0]
  all_goals norm_num

def cxι : Fin 1 → Fin 2 := fun _ => 1

lemma cx_inv : (Ahat cxA cxι)⁻¹ = !![-1] := by
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i; fin_cases j; simp [Ahat, cxA, cxι, Matrix.vecMul, dotProduct]

lemma cx_A00 : Ahat cxA cxι 0 0 = -1 := by simp [Ahat, cxA, cxι]

lemma cx_abar0 (i : Fin 1) : Abar0 cxA cxb cxι i = 1 := by
  fin_cases i
  simp [Abar0, cx_inv, cx_A00, Bhat, cxb, cxι, Matrix.mulVec, dotProduct]

lemma cx_piT (t : Fin 3) : piT cxA cxb cxι cxd cxd0 t 0 = ![1, -1/2, 0] t := by
  fin_cases t <;> simp [piT, Abar, cx_inv, cx_A00, cx_abar0, dotProduct, cxd, cxd0] <;> norm_num

lemma cx_pi : piCoef cxA cxb cxι cxd cxd0 0 = 1 := by
  unfold piCoef
  apply le_antisymm
  · apply Finset.sup'_le
    intro t _
    rw [cx_piT]; fin_cases t <;> simp <;> norm_num
  · calc (1:ℝ) = piT cxA cxb cxι cxd cxd0 0 0 := by rw [cx_piT]; simp
      _ ≤ _ := Finset.le_sup' (fun t => piT cxA cxb cxι cxd cxd0 t 0) (Finset.mem_univ 0)

lemma cx_IC : IsEquivalentToIntersectionCutFromS cxA cxb cxd cxd0 cxat 0 := by
  refine ⟨cxι, fun a b _ => Subsingleton.elim a b, ?_, ?_, ?_⟩
  · have : Ahat cxA cxι = !![-1] := by
      ext i j; fin_cases i; fin_cases j; simp [Ahat, cxA, cxι]
    rw [this]; simp
  · intro t
    have : (fun i => Abar0 cxA cxb cxι i) = fun _ => 1 := funext cx_abar0
    rw [this]
    fin_cases t <;> simp [dotProduct, cxd, cxd0]
  · ext x
    simp only [Set.mem_setOf_eq, IntersectionCutFromS, Fin.sum_univ_one]
    have hp : piCoef cxA cxb cxι cxd cxd0 0 = 1 := cx_pi
    rw [hp]
    simp [SurplusM, dotProduct, cxA, cxb, cxι, cxat]
    constructor <;> intro h <;> linarith

lemma cx_dom : Dominates (LPPoly cxA cxb) cxat 0 cxal (1/3) := by
  intro x hx _
  have h0 := hx 0
  have h1 := hx 1
  simp [dotProduct, cxA, cxb] at h0 h1
  linarith

theorem comp_disproof : ¬ (∀ {n : ℕ} {M T : Type} [Fintype M] [Fintype T]
    [Nonempty T] [DecidableEq M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (xbarN : Fin n → ℝ)
    (alphaBar : Fin n → ℝ) (betaBar : ℝ) (u : T → M → ℝ) (u0 : T → ℝ)
    (hbasic : IsBasicCGLP116Solution Atil btil d d0 alphaBar u u0 betaBar)
    (hu0pos : ∀ t, 0 < u0 t)
    (hnot119 : ¬ SatisfiesThm119Condition Atil u)
    (hnoscaled119 : ∀ μ : ℝ, 0 < μ → ∀ u' u0',
      IsBasicCGLP116Solution Atil btil d d0 (μ • alphaBar) u' u0' (μ * betaBar) →
      ¬ SatisfiesThm119Condition Atil u'),
    ¬ IsEquivalentToIntersectionCutFromS Atil btil d d0 alphaBar betaBar ∧
      (IsCGLP116UniqueMin Atil btil d d0 xbarN alphaBar betaBar →
        ∀ alphaT : Fin n → ℝ, ∀ betaT : ℝ,
          (∃ uT u0T, IsCGLP116Feasible Atil btil d d0 alphaT uT u0T betaT) →
          IsEquivalentToIntersectionCutFromS Atil btil d d0 alphaT betaT →
          dotProduct alphaBar xbarN - betaBar < dotProduct alphaT xbarN - betaT ∧
            ¬ Dominates (LPPoly Atil btil) alphaT betaT alphaBar betaBar)) := by
  intro H
  have hu0pos : ∀ t, 0 < cxu0 t := by
    intro t; fin_cases t <;> simp [cxu0]
  have hnot : ¬ SatisfiesThm119Condition cxA cxu :=
    cx_not_cond 1 one_pos cxu cxu0 (by rw [one_smul, one_mul]; exact cx_w_feas)
  have := (H cxA cxb cxd cxd0 cxx cxal (1/3) cxu cxu0 cx_basic hu0pos hnot
    (fun μ hμ u' u0' hb => cx_not_cond μ hμ u' u0' hb.1)).2 cx_uniqueMin cxat 0
    ⟨cxut, cxut0, cx_t_feas⟩ cx_IC
  exact this.2 cx_dom

end CompCx

end Disjunctive.GeneralDisjunctions

open Disjunctive.GeneralDisjunctions


theorem solution : ¬ (∀ {n : ℕ} {M T : Type} [Fintype M] [Fintype T]
    [Nonempty T] [DecidableEq M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (xbarN : Fin n → ℝ)
    (alphaBar : Fin n → ℝ) (betaBar : ℝ) (u : T → M → ℝ) (u0 : T → ℝ)
    (hbasic : IsBasicCGLP116Solution Atil btil d d0 alphaBar u u0 betaBar)
    (hu0pos : ∀ t, 0 < u0 t)
    (hnot119 : ¬ SatisfiesThm119Condition Atil u)
    (hnoscaled119 : ∀ μ : ℝ, 0 < μ → ∀ u' u0',
      IsBasicCGLP116Solution Atil btil d d0 (μ • alphaBar) u' u0' (μ * betaBar) →
      ¬ SatisfiesThm119Condition Atil u'),
    ¬ IsEquivalentToIntersectionCutFromS Atil btil d d0 alphaBar betaBar ∧
      (IsCGLP116UniqueMin Atil btil d d0 xbarN alphaBar betaBar →
        ∀ alphaT : Fin n → ℝ, ∀ betaT : ℝ,
          (∃ uT u0T, IsCGLP116Feasible Atil btil d d0 alphaT uT u0T betaT) →
          IsEquivalentToIntersectionCutFromS Atil btil d d0 alphaT betaT →
          dotProduct alphaBar xbarN - betaBar < dotProduct alphaT xbarN - betaT ∧
            ¬ Dominates (LPPoly Atil btil) alphaT betaT alphaBar betaBar)) := Disjunctive.GeneralDisjunctions.comp_disproof
