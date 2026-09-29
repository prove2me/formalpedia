-- Prove2me | solution 1 for DecentralizedDistribution.FirstBest.dual_allocation_in_core
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:08:50.490983+00:00
-- url     : https://prove2.me/submissions/63ab4ceb-e7af-41ac-bd94-fa5f56a21a30

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_DualPrices

open Supermodularity.Cooperative

namespace DecentralizedDistribution.FirstBest

/-- The linear functional `x ↦ ∑ i, x i * s i`. -/
def aux_dac_lin {ι : Type} [Fintype ι] (s : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i * s i
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum, mul_assoc]

lemma aux_dac_update {ι : Type} [Fintype ι] [DecidableEq ι] (x g : ι → ℝ) (e : ι) (t : ℝ) :
    ∑ i, Function.update x e t i * g i = ∑ i, x i * g i + (t - x e) * g e := by
  have h : ∀ i, Function.update x e t i * g i
      = x i * g i + (if i = e then (t - x e) * g e else 0) := by
    intro i
    by_cases hi : i = e
    · subst hi; simp; ring
    · simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma aux_dac_memIcc {ι : Type} [DecidableEq ι] {x : ι → ℝ} {M : ℝ}
    (hx : x ∈ Set.Icc (0 : ι → ℝ) (fun _ => M)) (e : ι) (t : ℝ) (ht0 : 0 ≤ t) (htM : t ≤ M) :
    Function.update x e t ∈ Set.Icc (0 : ι → ℝ) (fun _ => M) := by
  constructor
  · intro j
    by_cases h : j = e
    · subst h; simpa using ht0
    · simpa [h] using hx.1 j
  · intro j
    by_cases h : j = e
    · subst h; simpa using htM
    · simpa [h] using hx.2 j

/-- The Lagrangian of the LP `max c·a, A a ≤ b, a ≥ 0`. -/
def aux_dac_L {ι κ : Type} [Fintype ι] [Fintype κ] (c : ι → ℝ) (A : κ → ι → ℝ) (b : κ → ℝ)
    (p : κ → ℝ) (a : ι → ℝ) : ℝ :=
  ∑ e, a e * c e + ∑ k, p k * (b k - ∑ e, A k e * a e)

lemma aux_dac_L_eq2 {ι κ : Type} [Fintype ι] [Fintype κ] (c : ι → ℝ) (A : κ → ι → ℝ)
    (b : κ → ℝ) (p : κ → ℝ) (a : ι → ℝ) :
    aux_dac_L c A b p a = ∑ k, p k * b k + ∑ e, a e * (c e - ∑ k, p k * A k e) := by
  unfold aux_dac_L
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  have : ∑ k, ∑ e, p k * (A k e * a e) = ∑ e, ∑ k, a e * (p k * A k e) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  linarith

lemma aux_dac_lp {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (c : ι → ℝ) (A : κ → ι → ℝ) (b : κ → ℝ) (M B : ℝ) (hM0 : 0 ≤ M) (hB0 : 0 ≤ B)
    (hA : ∀ k e, 0 ≤ A k e) (hb : ∀ k, 0 ≤ b k)
    (hM : ∀ k e, 0 < A k e → c e < M * A k e)
    (hB : ∀ e, ∃ k, b k < A k e * B) :
    ∃ a : ι → ℝ, ∃ p : κ → ℝ, (∀ e, 0 ≤ a e) ∧ (∀ k, ∑ e, A k e * a e ≤ b k) ∧
      (∀ k, 0 ≤ p k) ∧ (∀ e, c e ≤ ∑ k, p k * A k e) ∧
      ∑ k, p k * b k ≤ ∑ e, a e * c e := by
  have hX0 : (0 : κ → ℝ) ∈ Set.Icc (0 : κ → ℝ) (fun _ => M) :=
    ⟨le_refl _, fun _ => by simpa using hM0⟩
  have hY0 : (0 : ι → ℝ) ∈ Set.Icc (0 : ι → ℝ) (fun _ => B) :=
    ⟨le_refl _, fun _ => by simpa using hB0⟩
  obtain ⟨p, hp, a, ha, hsad⟩ := Sion.exists_isSaddlePointOn
    (X := Set.Icc (0 : κ → ℝ) (fun _ => M)) (Y := Set.Icc (0 : ι → ℝ) (fun _ => B))
    (f := aux_dac_L c A b)
    (ne_X := ⟨0, hX0⟩) (cX := convex_Icc _ _) (kX := isCompact_Icc)
    (hfy := fun a _ =>
      (Continuous.lowerSemicontinuous (by unfold aux_dac_L; fun_prop)).lowerSemicontinuousOn _)
    (hfy' := fun a _ => by
      have : (fun p => aux_dac_L c A b p a) = (fun _ => ∑ e, a e * c e)
          + ⇑(aux_dac_lin (fun k => b k - ∑ e, A k e * a e)) := by
        funext p; simp [aux_dac_L, aux_dac_lin]
      rw [this]
      exact ((convexOn_const _ (convex_Icc _ _)).add
        ((aux_dac_lin _).convexOn (convex_Icc _ _))).quasiconvexOn)
    (cY := convex_Icc _ _) (ne_Y := ⟨0, hY0⟩) (kY := isCompact_Icc)
    (hfx := fun p _ =>
      (Continuous.upperSemicontinuous (by unfold aux_dac_L; fun_prop)).upperSemicontinuousOn _)
    (hfx' := fun p _ => by
      have : (fun a => aux_dac_L c A b p a) = (fun _ => ∑ k, p k * b k)
          + ⇑(aux_dac_lin (fun e => c e - ∑ k, p k * A k e)) := by
        funext a; simp [aux_dac_L_eq2, aux_dac_lin]
      rw [this]
      exact ((concaveOn_const _ (convex_Icc _ _)).add
        ((aux_dac_lin _).concaveOn (convex_Icc _ _))).quasiconcaveOn)
  have ha0 : ∀ e, 0 ≤ a e := fun e => by simpa using ha.1 e
  have hp0 : ∀ k, 0 ≤ p k := fun k => by simpa using hp.1 k
  have hA1 : ∀ e, 0 < c e - ∑ k, p k * A k e → B ≤ a e := by
    intro e he
    have h1 := hsad p hp (Function.update a e B) (aux_dac_memIcc ha e B hB0 le_rfl)
    rw [aux_dac_L_eq2, aux_dac_L_eq2, aux_dac_update] at h1
    by_contra hlt
    push Not at hlt
    have : 0 < (B - a e) * (c e - ∑ k, p k * A k e) := mul_pos (by linarith) he
    linarith
  have hA2 : ∀ e, c e - ∑ k, p k * A k e < 0 → a e = 0 := by
    intro e he
    have h1 := hsad p hp (Function.update a e 0) (aux_dac_memIcc ha e 0 le_rfl hB0)
    rw [aux_dac_L_eq2, aux_dac_L_eq2, aux_dac_update] at h1
    by_contra hne
    have hpos : 0 < a e := lt_of_le_of_ne (ha0 e) (Ne.symm hne)
    have : 0 < a e * -(c e - ∑ k, p k * A k e) := mul_pos hpos (by linarith)
    linarith
  have hP1 : ∀ k, b k - ∑ e, A k e * a e < 0 → M ≤ p k := by
    intro k hk
    have h1 := hsad (Function.update p k M) (aux_dac_memIcc hp k M hM0 le_rfl) a ha
    simp only [aux_dac_L] at h1
    rw [aux_dac_update] at h1
    by_contra hlt
    push Not at hlt
    have : 0 < (M - p k) * -(b k - ∑ e, A k e * a e) := mul_pos (by linarith) (by linarith)
    linarith
  refine ⟨a, p, ha0, ?_, hp0, ?_, ?_⟩
  · intro k
    by_contra hlt
    push Not at hlt
    have hpk := hP1 k (by linarith)
    have hz : ∀ e, A k e * a e = 0 := by
      intro e
      rcases (hA k e).eq_or_lt with h0 | hpos
      · rw [← h0]; ring
      · have h1 : p k * A k e ≤ ∑ k', p k' * A k' e :=
          Finset.single_le_sum (f := fun k' => p k' * A k' e)
            (fun k' _ => mul_nonneg (hp0 k') (hA k' e)) (Finset.mem_univ k)
        have h2 : M * A k e ≤ p k * A k e := mul_le_mul_of_nonneg_right hpk (hA k e)
        have h3 := hM k e hpos
        rw [hA2 e (by linarith)]; ring
    rw [Finset.sum_eq_zero (fun e _ => hz e)] at hlt
    linarith [hb k]
  · intro e
    by_contra hlt
    push Not at hlt
    have haeB := hA1 e (by linarith)
    obtain ⟨k, hk⟩ := hB e
    have hAke : 0 < A k e := by
      by_contra h
      push Not at h
      have : A k e * B ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hB0
      linarith [hb k]
    have hs1 : A k e * a e ≤ ∑ e', A k e' * a e' :=
      Finset.single_le_sum (f := fun e' => A k e' * a e')
        (fun e' _ => mul_nonneg (hA k e') (ha0 e')) (Finset.mem_univ e)
    have hs2 : A k e * B ≤ A k e * a e := mul_le_mul_of_nonneg_left haeB (hA k e)
    have hpk := hP1 k (by linarith)
    have h1 : p k * A k e ≤ ∑ k', p k' * A k' e :=
      Finset.single_le_sum (f := fun k' => p k' * A k' e)
        (fun k' _ => mul_nonneg (hp0 k') (hA k' e)) (Finset.mem_univ k)
    have h2 : M * A k e ≤ p k * A k e := mul_le_mul_of_nonneg_right hpk (hA k e)
    have h3 := hM k e hAke
    linarith
  · have h1 := hsad p hp 0 hY0
    have h2 := hsad 0 hX0 a ha
    have e1 : aux_dac_L c A b p 0 = ∑ k, p k * b k := by simp [aux_dac_L]
    have e2 : aux_dac_L c A b 0 a = ∑ e, a e * c e := by simp [aux_dac_L]
    linarith

lemma aux_dac_pt (β m π δ q : ℝ) (hβ : 0 ≤ β) (hq : 0 ≤ q) (hq0 : β = 0 → q = 0)
    (h : β * m ≤ β * π + δ) : m * q ≤ π * q + δ * (q / β) := by
  rcases hβ.eq_or_lt with h0 | hpos
  · rw [hq0 h0.symm]; simp
  · have e : π * q + δ * (q / β) = (β * π * q + δ * q) / β := by field_simp
    rw [e, le_div_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_right h hq]

lemma aux_dac_sumalloc {N W : ℕ} (Z : Profile N W) (D : Demand N) (p : DualPrices N W)
    (S : Finset (Fin N)) :
    ∑ n ∈ S, dualAllocation Z D p n = (∑ j ∈ S, p.1 j * residualInv Z D j)
      + (∑ w, p.2.1 w * ∑ n ∈ S, (Z n).Y w) + ∑ n ∈ S, p.2.2 n * residualDem Z D n := by
  unfold dualAllocation
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm (s := S)]
  simp only [Finset.mul_sum]

lemma aux_dac_weak {N W : ℕ} (sys : System N W) (S : Finset (Fin N)) (Z : Profile N W)
    (D : Demand N) (q : ShippingPlan N W) (hq : IsFeasibleShipping sys S Z D q)
    (p : DualPrices N W) (hp : IsDualFeasible sys p) :
    shippingProfit sys S q ≤ ∑ n ∈ S, dualAllocation Z D p n := by
  obtain ⟨hq0, -, hqβ, hqH, hqY, hqE⟩ := hq
  obtain ⟨hν, hγ, hδ, hdj, hdw⟩ := hp
  rw [aux_dac_sumalloc]
  unfold shippingProfit
  have h1 : ∑ j ∈ S, ∑ n ∈ S, sys.margin (Sum.inl j) n * q (Sum.inl j) n
      ≤ ∑ j ∈ S, ∑ n ∈ S, (p.1 j * q (Sum.inl j) n
          + p.2.2 n * (q (Sum.inl j) n / sys.β (Sum.inl j) n)) :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun n _ =>
      aux_dac_pt _ _ _ _ _ (sys.β_nonneg _ _) (hq0 _ _) (hqβ _ _) (by linarith [hdj j n])
  have h2 : ∑ w, ∑ n ∈ S, sys.margin (Sum.inr w) n * q (Sum.inr w) n
      ≤ ∑ w, ∑ n ∈ S, (p.2.1 w * q (Sum.inr w) n
          + p.2.2 n * (q (Sum.inr w) n / sys.β (Sum.inr w) n)) :=
    Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun n _ =>
      aux_dac_pt _ _ _ _ _ (sys.β_nonneg _ _) (hq0 _ _) (hqβ _ _) (by linarith [hdw w n])
  simp only [Finset.sum_add_distrib] at h1 h2
  have h3 : ∑ j ∈ S, ∑ n ∈ S, p.1 j * q (Sum.inl j) n ≤ ∑ j ∈ S, p.1 j * residualInv Z D j := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hqH j hj) (hν j)
  have h4 : ∑ w, ∑ n ∈ S, p.2.1 w * q (Sum.inr w) n ≤ ∑ w, p.2.1 w * ∑ n ∈ S, (Z n).Y w := by
    refine Finset.sum_le_sum fun w _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hqY w) (hγ w)
  have h5 : ∑ j ∈ S, ∑ n ∈ S, p.2.2 n * (q (Sum.inl j) n / sys.β (Sum.inl j) n)
      + ∑ w, ∑ n ∈ S, p.2.2 n * (q (Sum.inr w) n / sys.β (Sum.inr w) n)
      ≤ ∑ n ∈ S, p.2.2 n * residualDem Z D n := by
    rw [Finset.sum_comm (s := S), Finset.sum_comm (s := Finset.univ), ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hqE n hn) (hδ n)
  linarith

/-- The constraint matrix of the grand-coalition LP in the variables `a_{i,n} = q_{i,n}/β_{i,n}`. -/
def aux_dac_A {N W : ℕ} (sys : System N W) :
    ((Fin N ⊕ Fin W) ⊕ Fin N) → ((Fin N ⊕ Fin W) × Fin N) → ℝ
  | Sum.inl i, e => if e.1 = i then sys.β e.1 e.2 else 0
  | Sum.inr n, e => if e.2 = n then 1 else 0

/-- The right-hand side of the grand-coalition LP. -/
def aux_dac_b {N W : ℕ} (Z : Profile N W) (D : Demand N) : ((Fin N ⊕ Fin W) ⊕ Fin N) → ℝ
  | Sum.inl (Sum.inl j) => residualInv Z D j
  | Sum.inl (Sum.inr w) => ∑ n, (Z n).Y w
  | Sum.inr n => residualDem Z D n

/-- The objective of the grand-coalition LP. -/
def aux_dac_c {N W : ℕ} (sys : System N W) : ((Fin N ⊕ Fin W) × Fin N) → ℝ :=
  fun e => sys.β e.1 e.2 * sys.margin e.1 e.2

lemma aux_dac_colsum {N W : ℕ} (sys : System N W) (p : ((Fin N ⊕ Fin W) ⊕ Fin N) → ℝ)
    (i : Fin N ⊕ Fin W) (n : Fin N) :
    ∑ k, p k * aux_dac_A sys k (i, n) = p (Sum.inl i) * sys.β i n + p (Sum.inr n) := by
  rw [Fintype.sum_sum_type]
  simp [aux_dac_A, mul_ite, Finset.sum_ite_eq]

lemma aux_dac_rowsum_inl {N W : ℕ} (sys : System N W) (a : ((Fin N ⊕ Fin W) × Fin N) → ℝ)
    (i : Fin N ⊕ Fin W) :
    ∑ e, aux_dac_A sys (Sum.inl i) e * a e = ∑ n, sys.β i n * a (i, n) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [aux_dac_A, ite_mul, Finset.sum_ite_eq']

lemma aux_dac_rowsum_inr {N W : ℕ} (sys : System N W) (a : ((Fin N ⊕ Fin W) × Fin N) → ℝ)
    (n : Fin N) :
    ∑ e, aux_dac_A sys (Sum.inr n) e * a e = ∑ i, a (i, n) := by
  rw [Fintype.sum_prod_type]
  simp [aux_dac_A, ite_mul, Finset.sum_ite_eq']

lemma aux_dac_divle (β a : ℝ) (hβ : 0 ≤ β) (ha : 0 ≤ a) : β * a / β ≤ a := by
  rcases hβ.eq_or_lt with h | h
  · simp [← h, ha]
  · rw [mul_div_cancel_left₀ _ h.ne']

end DecentralizedDistribution.FirstBest

open DecentralizedDistribution.FirstBest

theorem solution {N W : ℕ} (sys : System N W) (Z : Profile N W) (hZ : Z.Nonneg)
    (D : Demand N) :
    (Core Finset.univ (fun S => coalitionValue sys S Z D)).Nonempty ∧
    (∃ p, IsOptimalDual sys Z D p) ∧
    ∀ p, IsOptimalDual sys Z D p →
      dualAllocation Z D p ∈ Core Finset.univ (fun S => coalitionValue sys S Z D) := by
  classical
  have hH : ∀ j, 0 ≤ residualInv Z D j := fun j => le_max_right _ _
  have hE : ∀ n, 0 ≤ residualDem Z D n := fun n => le_max_right _ _
  have hY : ∀ n w, 0 ≤ (Z n).Y w := fun n w => (hZ n).2 w
  have hweak : ∀ S (p' : DualPrices N W), IsDualFeasible sys p' →
      coalitionValue sys S Z D ≤ ∑ n ∈ S, dualAllocation Z D p' n := by
    intro S p' hp'
    apply csSup_le
    · refine ⟨_, 0, ?_, rfl⟩
      exact ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
        fun j _ => by simpa using hH j,
        fun w => by simpa using Finset.sum_nonneg (fun n _ => hY n w),
        fun n _ => by simpa using hE n⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact aux_dac_weak sys S Z D q hq p' hp'
  have hMbound : ∀ i n, sys.margin i n < 1 + ∑ i, ∑ n, |sys.margin i n| := by
    intro i n
    have h1 : |sys.margin i n| ≤ ∑ n, |sys.margin i n| :=
      Finset.single_le_sum (f := fun n => |sys.margin i n|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ n)
    have h2 : ∑ n, |sys.margin i n| ≤ ∑ i, ∑ n, |sys.margin i n| :=
      Finset.single_le_sum (f := fun i => ∑ n, |sys.margin i n|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [le_abs_self (sys.margin i n)]
  obtain ⟨a, p, ha0, hAa, hp0, hdual, hobj⟩ := aux_dac_lp (aux_dac_c sys) (aux_dac_A sys)
    (aux_dac_b Z D) (1 + ∑ i, ∑ n, |sys.margin i n|) (1 + ∑ n, residualDem Z D n)
    (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      abs_nonneg _))
    (add_nonneg zero_le_one (Finset.sum_nonneg fun n _ => hE n))
    (by
      rintro (i | n) e
      · simp only [aux_dac_A]; split_ifs
        · exact sys.β_nonneg _ _
        · exact le_rfl
      · simp only [aux_dac_A]; split_ifs
        · exact zero_le_one
        · exact le_rfl)
    (by
      rintro ((j | w) | n)
      · exact hH j
      · exact Finset.sum_nonneg fun n _ => hY n w
      · exact hE n)
    (by
      rintro (i | n) ⟨i', n'⟩ h
      · simp only [aux_dac_A, aux_dac_c] at h ⊢
        split_ifs at h ⊢ with h1
        · rw [mul_comm _ (sys.β i' n')]
          exact mul_lt_mul_of_pos_left (hMbound i' n') h
        · exact absurd h (lt_irrefl 0)
      · simp only [aux_dac_A, aux_dac_c] at h ⊢
        split_ifs at h ⊢ with h1
        · have hb0 := sys.β_nonneg i' n'
          have hb1 := sys.β_le_one i' n'
          have : sys.β i' n' * sys.margin i' n' ≤ |sys.margin i' n'| := by
            calc sys.β i' n' * sys.margin i' n' ≤ sys.β i' n' * |sys.margin i' n'| :=
                  mul_le_mul_of_nonneg_left (le_abs_self _) hb0
              _ ≤ 1 * |sys.margin i' n'| := mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
              _ = |sys.margin i' n'| := one_mul _
          have h1 : |sys.margin i' n'| ≤ ∑ n, |sys.margin i' n| :=
            Finset.single_le_sum (f := fun n => |sys.margin i' n|) (fun _ _ => abs_nonneg _)
              (Finset.mem_univ n')
          have h2 : ∑ n, |sys.margin i' n| ≤ ∑ i, ∑ n, |sys.margin i n| :=
            Finset.single_le_sum (f := fun i => ∑ n, |sys.margin i n|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i')
          linarith
        · exact absurd h (lt_irrefl 0))
    (by
      rintro ⟨i, n⟩
      refine ⟨Sum.inr n, ?_⟩
      simp only [aux_dac_A, aux_dac_b, if_true, one_mul]
      have := Finset.single_le_sum (f := fun n => residualDem Z D n) (fun n _ => hE n)
        (Finset.mem_univ n)
      linarith)
  let q : ShippingPlan N W := fun i n => sys.β i n * a (i, n)
  let P : DualPrices N W :=
    (fun j => p (Sum.inl (Sum.inl j)), fun w => p (Sum.inl (Sum.inr w)), fun n => p (Sum.inr n))
  have hqfeas : IsFeasibleShipping sys Finset.univ Z D q := by
    refine ⟨fun i n => mul_nonneg (sys.β_nonneg i n) (ha0 _), fun i n h => ?_,
      fun i n h => by simp [q, h], fun j _ => ?_, fun w => ?_, fun n _ => ?_⟩
    · exfalso; apply h; rcases i with j | w <;> simp [LocIn]
    · have := hAa (Sum.inl (Sum.inl j))
      rw [aux_dac_rowsum_inl] at this
      simpa [aux_dac_b, q] using this
    · have := hAa (Sum.inl (Sum.inr w))
      rw [aux_dac_rowsum_inl] at this
      simpa [aux_dac_b, q] using this
    · have := hAa (Sum.inr n)
      rw [aux_dac_rowsum_inr, Fintype.sum_sum_type] at this
      simp only [aux_dac_b] at this
      refine le_trans (add_le_add (Finset.sum_le_sum fun j _ => ?_)
        (Finset.sum_le_sum fun w _ => ?_)) this
      · exact aux_dac_divle _ _ (sys.β_nonneg _ _) (ha0 _)
      · exact aux_dac_divle _ _ (sys.β_nonneg _ _) (ha0 _)
  have hPfeas : IsDualFeasible sys P := by
    refine ⟨fun j => hp0 _, fun w => hp0 _, fun n => hp0 _, fun j n => ?_, fun w n => ?_⟩
    · have := hdual (Sum.inl j, n)
      rw [aux_dac_colsum] at this
      simp only [aux_dac_c] at this
      show sys.β (Sum.inl j) n * sys.margin (Sum.inl j) n
        ≤ sys.β (Sum.inl j) n * p (Sum.inl (Sum.inl j)) + p (Sum.inr n)
      linarith [mul_comm (sys.β (Sum.inl j) n) (p (Sum.inl (Sum.inl j)))]
    · have := hdual (Sum.inr w, n)
      rw [aux_dac_colsum] at this
      simp only [aux_dac_c] at this
      show sys.β (Sum.inr w) n * sys.margin (Sum.inr w) n
        ≤ sys.β (Sum.inr w) n * p (Sum.inl (Sum.inr w)) + p (Sum.inr n)
      linarith [mul_comm (sys.β (Sum.inr w) n) (p (Sum.inl (Sum.inr w)))]
  have hprofit : shippingProfit sys Finset.univ q = ∑ e, a e * aux_dac_c sys e := by
    rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
    simp only [shippingProfit, aux_dac_c, q]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hPobj : dualObjective Z D P = ∑ k, p k * aux_dac_b Z D k := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    rfl
  have hle : dualObjective Z D P ≤ coalitionValue sys Finset.univ Z D := by
    rw [hPobj]
    refine hobj.trans ?_
    rw [← hprofit]
    apply le_csSup
    · exact ⟨_, by rintro _ ⟨q', hq', rfl⟩; exact aux_dac_weak sys _ Z D q' hq' P hPfeas⟩
    · exact ⟨q, hqfeas, rfl⟩
  have hsumU : ∀ p' : DualPrices N W, ∑ n, dualAllocation Z D p' n = dualObjective Z D p' := by
    intro p'; rw [aux_dac_sumalloc]; rfl
  have hopt : IsOptimalDual sys Z D P :=
    ⟨hPfeas, fun p' hp' => hle.trans ((hweak _ p' hp').trans (hsumU p').le)⟩
  have hcore : ∀ p', IsOptimalDual sys Z D p' →
      dualAllocation Z D p' ∈ Core Finset.univ (fun S => coalitionValue sys S Z D) := by
    rintro p' ⟨hf, hmin⟩
    show (∑ i ∈ Finset.univ, dualAllocation Z D p' i) = coalitionValue sys Finset.univ Z D ∧
      ∀ S ⊆ Finset.univ, coalitionValue sys S Z D ≤ ∑ i ∈ S, dualAllocation Z D p' i
    refine ⟨le_antisymm ?_ (hweak _ p' hf), fun S _ => hweak S p' hf⟩
    rw [hsumU]
    exact (hmin P hPfeas).trans hle
  exact ⟨⟨_, hcore P hopt⟩, ⟨P, hopt⟩, hcore⟩
