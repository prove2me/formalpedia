-- Prove2me | solution 1 for FramingFulfillment.RFF.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T15:36:27.83099+00:00
-- url     : https://prove2.me/submissions/3b895176-4caa-4a93-ba6f-bd5a0d1a4a1d

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model

open FramingFulfillment.RFF Finset

namespace RFF5

lemma vnn (P : Inst) (hP : P.Standing) : ∀ i j r, 0 ≤ P.v i j r := by
  obtain ⟨-, -, -, -, -, -, hvpos, hv0, -, -⟩ := hP
  intro i j r
  by_cases h : r = P.noDisp
  · rw [h, hv0]
  · exact (hvpos i j r h).le

lemma mix_ratio {ι : Type*} [Fintype ι] (μ D N : ι → ℝ) (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) (hD : ∀ s, 0 < D s) :
    0 < ∑ s, μ s / D s ∧
    (∑ s, μ s / D s / (∑ s', μ s' / D s') = 1) ∧
    (∑ s, μ s / D s / (∑ s', μ s' / D s') * N s) /
      (∑ s, μ s / D s / (∑ s', μ s' / D s') * D s) = ∑ s, μ s * (N s / D s) := by
  have hA : 0 < ∑ s, μ s / D s := by
    obtain ⟨s, -, hs⟩ : ∃ s ∈ (univ : Finset ι), 0 < μ s := by
      by_contra hc
      push Not at hc
      have : ∑ s, μ s = 0 := Finset.sum_eq_zero fun s hs => le_antisymm (hc s hs) (hμ s)
      linarith
    calc (0:ℝ) < μ s / D s := div_pos hs (hD s)
      _ ≤ _ := Finset.single_le_sum (f := fun s => μ s / D s)
          (fun s _ => div_nonneg (hμ s) (hD s).le) (Finset.mem_univ s)
  set A := ∑ s, μ s / D s with hAdef
  refine ⟨hA, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hA.ne']
  · have h1 : (∑ s, μ s / D s / A * D s) = 1 / A := by
      rw [← hμ1, Finset.sum_div]
      refine Finset.sum_congr rfl fun s _ => ?_
      field_simp [(hD s).ne']
    have h2 : (∑ s, μ s / D s / A * N s) = (∑ s, μ s * (N s / D s)) / A := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun s _ => ?_
      field_simp [(hD s).ne']
    rw [h1, h2]
    field_simp

/-- Charnes–Cooper mixing: a `μ`-mixture of the MNL quantities of several framings is
realised by a single framing which is a convex combination of them. -/
lemma mix (P : Inst) (hv : ∀ i j r, 0 ≤ P.v i j r) (j : Fin P.J) {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (hμ : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1)
    (xs : ι → Fin P.I → Fin P.R → ℝ) (hx : ∀ s i r, 0 ≤ xs s i r) :
    ∃ w : ι → ℝ, (∀ s, 0 ≤ w s) ∧ (∑ s, w s = 1) ∧
      (∀ i, P.thetaX j (fun i r => ∑ s, w s * xs s i r) i = ∑ s, μ s * P.thetaX j (xs s) i) ∧
      (∀ i, P.revX j (fun i r => ∑ s, w s * xs s i r) i = ∑ s, μ s * P.revX j (xs s) i) := by
  set D : ι → ℝ := fun s => 1 + ∑ l, ∑ r, P.v l j r * xs s l r with hDdef
  have hD : ∀ s, 0 < D s := by
    intro s
    have : 0 ≤ ∑ l, ∑ r, P.v l j r * xs s l r :=
      Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ => mul_nonneg (hv _ _ _) (hx s l r)
    simp only [hDdef]; linarith
  obtain ⟨hA, hw1, -⟩ := mix_ratio μ D (fun _ => (0:ℝ)) hμ hμ1 hD
  set A := ∑ s, μ s / D s with hAdef
  set w : ι → ℝ := fun s => μ s / D s / A with hwdef
  have hwnn : ∀ s, 0 ≤ w s := fun s => div_nonneg (div_nonneg (hμ s) (hD s).le) hA.le
  have hden : (1 + ∑ l, ∑ r, P.v l j r * ∑ s, w s * xs s l r) = ∑ s, w s * D s := by
    have h1 : ∀ s, w s * D s = w s + ∑ l, ∑ r, P.v l j r * (w s * xs s l r) := by
      intro s
      simp only [hDdef, mul_add, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun r _ => ?_; ring
    rw [Finset.sum_congr rfl fun s _ => h1 s, Finset.sum_add_distrib, hw1]
    congr 1
    simp_rw [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_comm
  refine ⟨w, hwnn, hw1, fun i => ?_, fun i => ?_⟩
  · have hnum : (∑ r, P.v i j r * ∑ s, w s * xs s i r) =
        ∑ s, w s * (∑ r, P.v i j r * xs s i r) := by
      simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_; ring
    have key := (mix_ratio μ D (fun s => ∑ r, P.v i j r * xs s i r) hμ hμ1 hD).2.2
    simp only [Inst.thetaX]
    rw [hnum, hden, mul_div_assoc, key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hDdef]; ring
  · have hnum : (∑ r, P.v i j r * (∑ s, w s * xs s i r) * P.p i r) =
        ∑ s, w s * (∑ r, P.v i j r * xs s i r * P.p i r) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_; ring
    have key := (mix_ratio μ D (fun s => ∑ r, P.v i j r * xs s i r * P.p i r) hμ hμ1 hD).2.2
    simp only [Inst.revX]
    rw [hnum, hden, mul_div_assoc, key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hDdef]; ring

/-- the period map `Fin θ × Fin T → Fin (θ T)` and its sums -/
lemma swap3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]

lemma swap4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm,
    Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]

abbrev Space (P : Inst) := (Fin P.T → Fin P.J → Fin P.I → Fin P.R → ℝ) ×
    (Fin P.T → Fin P.J → Fin P.I → Fin P.K → ℝ)

def feas (P : Inst) : Set (Space P) := {e |
    (∀ t j r, ∑ i, e.1 t j i r ≤ (P.Q r : ℝ)) ∧
    (∀ t j i, ∑ r, e.1 t j i r = 1) ∧
    (∀ t j i, (∑ k, e.2 t j i k) * (1 + ∑ l, ∑ r, P.v l j r * e.1 t j l r) =
        P.lam j * (∑ r, P.v i j r * e.1 t j i r)) ∧
    (∀ i k, ∑ t, ∑ j, e.2 t j i k ≤ (P.C i k : ℝ)) ∧
    (∀ t j i r, 0 ≤ e.1 t j i r ∧ e.1 t j i r ≤ 1) ∧
    (∀ t j i k, 0 ≤ e.2 t j i k ∧ e.2 t j i k ≤ 1)}

lemma feas_closed (P : Inst) : IsClosed (feas P) := by
  simp only [feas, Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_
    (IsClosed.inter ?_ ?_))))
  all_goals
    repeat (first | (apply isClosed_iInter; intro _) | apply IsClosed.inter)
  all_goals
    first
    | exact isClosed_le (by fun_prop) (by fun_prop)
    | exact isClosed_eq (by fun_prop) (by fun_prop)

lemma feas_bdd (P : Inst) : Bornology.IsBounded (feas P) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨1, fun e he => ?_⟩
  obtain ⟨-, -, -, -, h5, h6⟩ := he
  rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff]
  constructor
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun t => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun r => ?_
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h5 t j i r]
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun t => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h6 t j i k]

lemma feas_cont (P : Inst) (hv : ∀ i j r, 0 ≤ P.v i j r) :
    ContinuousOn (fun e : Space P => P.detObj ⟨e.1, e.2⟩) (feas P) := by
  have hDpos : ∀ (xx : Fin P.I → Fin P.R → ℝ) (j : Fin P.J), (∀ i r, 0 ≤ xx i r) →
      0 < 1 + ∑ l, ∑ r, P.v l j r * xx l r := by
    intro xx j hx
    have : 0 ≤ ∑ l, ∑ r, P.v l j r * xx l r :=
      Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ => mul_nonneg (hv _ _ _) (hx l r)
    linarith
  simp only [Inst.detObj, Inst.revX]
  refine ContinuousOn.sub ?_ (Continuous.continuousOn (by fun_prop))
  refine continuousOn_finset_sum _ fun t _ => continuousOn_finset_sum _ fun i _ =>
    continuousOn_finset_sum _ fun j _ => ?_
  refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
    (Continuous.continuousOn (by fun_prop)) fun e he => ?_
  exact (hDpos _ j (fun i r => (he.2.2.2.2.1 t j i r).1)).ne'

lemma feas_ne (P : Inst) (hv0 : ∀ i j, P.v i j P.noDisp = 0) (hQR : P.I ≤ P.Q P.noDisp) :
    (feas P).Nonempty := by
  classical
  refine ⟨(fun _ _ _ r => if r = P.noDisp then 1 else 0, fun _ _ _ _ => 0), ?_⟩
  simp only [feas, Set.mem_setOf_eq]
  refine ⟨fun t j r => ?_, fun t j i => by simp, fun t j i => ?_, fun i k => by simp,
    fun t j i r => by split_ifs <;> norm_num, fun t j i k => by simp⟩
  · by_cases hr : r = P.noDisp
    · simp only [hr, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      exact_mod_cast hQR
    · simp [hr]
  · simp only [Finset.sum_const_zero, zero_mul]
    have : ∑ r, P.v i j r * (if r = P.noDisp then (1:ℝ) else 0) = 0 := by
      simp [hv0]
    rw [this, mul_zero]

lemma feas_cpt (P : Inst) : IsCompact (feas P) :=
  Metric.isCompact_of_isClosed_isBounded (feas_closed P) (feas_bdd P)

theorem exists_DETOpt (P : Inst) (hP : P.Standing) : ∃ s, P.IsDETOpt s := by
  classical
  have hv := vnn P hP
  obtain ⟨-, -, -, -, -, -, -, hv0, -, hQR⟩ := hP
  let S : Set (Space P) := feas P
  have hDpos : ∀ (xx : Fin P.I → Fin P.R → ℝ) (j : Fin P.J), (∀ i r, 0 ≤ xx i r) →
      0 < 1 + ∑ l, ∑ r, P.v l j r * xx l r := by
    intro xx j hx
    have : 0 ≤ ∑ l, ∑ r, P.v l j r * xx l r :=
      Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ => mul_nonneg (hv _ _ _) (hx l r)
    linarith
  have hiff : ∀ s : DETSol P, s ∈ P.DETFeasible ↔ ((s.x, s.y) : Space P) ∈ S := by
    intro s
    simp only [Inst.DETFeasible, Set.mem_setOf_eq, S, feas, Inst.thetaX]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨h1, h2, fun t j i => ?_, h4, h5, h6⟩
      rw [h3 t j i, div_mul_cancel₀ _ (hDpos _ j (fun i r => (h5 t j i r).1)).ne']
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨h1, h2, fun t j i => ?_, h4, h5, h6⟩
      rw [eq_div_iff (hDpos _ j (fun i r => (h5 t j i r).1)).ne', h3 t j i]
  have hclosed : IsClosed S := feas_closed P
  have hbdd : Bornology.IsBounded S := feas_bdd P
  have hcpt : IsCompact S := feas_cpt P
  have hne : S.Nonempty := feas_ne P hv0 hQR
  let f : Space P → ℝ := fun e => P.detObj ⟨e.1, e.2⟩
  have hcont : ContinuousOn f S := feas_cont P hv
  obtain ⟨e, he, hmax⟩ := hcpt.exists_isMaxOn hne hcont
  refine ⟨⟨e.1, e.2⟩, (hiff ⟨e.1, e.2⟩).2 he, fun s' hs' => ?_⟩
  rcases s' with ⟨x', y'⟩
  have h1 : ((x', y') : Space P) ∈ S := (hiff ⟨x', y'⟩).1 hs'
  have h2 : f (x', y') ≤ f e := isMaxOn_iff.1 hmax _ h1
  exact h2


lemma JD_eq (Q : Inst) (s : DETSol Q) (hs : Q.IsDETOpt s) : Q.JD = Q.detObj s :=
  IsGreatest.csSup_eq ⟨⟨s, hs.1, rfl⟩, by rintro _ ⟨s', hs', rfl⟩; exact hs.2 s' hs'⟩

structure GSol (P : Inst) (n : ℕ) where
  x : Fin n → Fin P.J → Fin P.I → Fin P.R → ℝ
  y : Fin n → Fin P.J → Fin P.I → Fin P.K → ℝ

def PerOK (P : Inst) (x0 : Fin P.J → Fin P.I → Fin P.R → ℝ)
    (y0 : Fin P.J → Fin P.I → Fin P.K → ℝ) : Prop :=
  (∀ j r, ∑ i, x0 j i r ≤ (P.Q r : ℝ)) ∧ (∀ j i, ∑ r, x0 j i r = 1) ∧
  (∀ j i, ∑ k, y0 j i k = P.thetaX j (x0 j) i) ∧
  (∀ j i r, 0 ≤ x0 j i r ∧ x0 j i r ≤ 1) ∧ (∀ j i k, 0 ≤ y0 j i k ∧ y0 j i k ≤ 1)

def GFeas (P : Inst) (n : ℕ) (cap : Fin P.I → Fin P.K → ℝ) (s : GSol P n) : Prop :=
  (∀ t, PerOK P (s.x t) (s.y t)) ∧ (∀ i k, ∑ t, ∑ j, s.y t j i k ≤ cap i k)

noncomputable def perObj (P : Inst) (x0 : Fin P.J → Fin P.I → Fin P.R → ℝ)
    (y0 : Fin P.J → Fin P.I → Fin P.K → ℝ) : ℝ :=
  (∑ i, ∑ j, P.revX j (x0 j) i) - ∑ j, ∑ i, ∑ k, P.c i j k * y0 j i k

noncomputable def gObj (P : Inst) (n : ℕ) (s : GSol P n) : ℝ := ∑ t, perObj P (s.x t) (s.y t)

lemma mixPer (P : Inst) (hv : ∀ i j r, 0 ≤ P.v i j r) {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (hπ : ∀ a, 0 ≤ π a) (hπ1 : ∑ a, π a = 1)
    (xs : ι → Fin P.J → Fin P.I → Fin P.R → ℝ) (ys : ι → Fin P.J → Fin P.I → Fin P.K → ℝ)
    (hok : ∀ a, PerOK P (xs a) (ys a)) :
    ∃ xb : Fin P.J → Fin P.I → Fin P.R → ℝ,
      PerOK P xb (fun j i k => ∑ a, π a * ys a j i k) ∧
      perObj P xb (fun j i k => ∑ a, π a * ys a j i k) = ∑ a, π a * perObj P (xs a) (ys a) := by
  have hm : ∀ j, ∃ w : ι → ℝ, (∀ a, 0 ≤ w a) ∧ (∑ a, w a = 1) ∧
      (∀ i, P.thetaX j (fun i r => ∑ a, w a * xs a j i r) i = ∑ a, π a * P.thetaX j (xs a j) i) ∧
      (∀ i, P.revX j (fun i r => ∑ a, w a * xs a j i r) i = ∑ a, π a * P.revX j (xs a j) i) :=
    fun j => mix P hv j π hπ hπ1 (fun a => xs a j) (fun a i r => ((hok a).2.2.2.1 j i r).1)
  choose w hw0 hw1 hwθ hwR using hm
  refine ⟨fun j i r => ∑ a, w j a * xs a j i r, ⟨fun j r => ?_, fun j i => ?_, fun j i => ?_,
    fun j i r => ⟨?_, ?_⟩, fun j i k => ⟨?_, ?_⟩⟩, ?_⟩
  · dsimp only
    rw [Finset.sum_comm]
    calc _ ≤ ∑ a, w j a * (P.Q r : ℝ) := Finset.sum_le_sum fun a _ => by
          rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left ((hok a).1 j r) (hw0 j a)
      _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]
  · dsimp only
    rw [Finset.sum_comm]
    calc (∑ a, ∑ r, w j a * xs a j i r) = ∑ a, w j a * 1 :=
          Finset.sum_congr rfl fun a _ => by rw [← Finset.mul_sum, (hok a).2.1 j i]
      _ = 1 := by rw [← Finset.sum_mul, hw1 j, one_mul]
  · dsimp only
    rw [Finset.sum_comm, hwθ j i]
    exact Finset.sum_congr rfl fun a _ => by rw [← Finset.mul_sum, (hok a).2.2.1 j i]
  · exact Finset.sum_nonneg fun a _ => mul_nonneg (hw0 j a) ((hok a).2.2.2.1 j i r).1
  · calc (∑ a, w j a * xs a j i r) ≤ ∑ a, w j a :=
          Finset.sum_le_sum fun a _ => mul_le_of_le_one_right (hw0 j a) ((hok a).2.2.2.1 j i r).2
      _ = 1 := hw1 j
  · exact Finset.sum_nonneg fun a _ => mul_nonneg (hπ a) ((hok a).2.2.2.2 j i k).1
  · calc (∑ a, π a * ys a j i k) ≤ ∑ a, π a :=
          Finset.sum_le_sum fun a _ => mul_le_of_le_one_right (hπ a) ((hok a).2.2.2.2 j i k).2
      _ = 1 := hπ1
  · simp only [perObj]
    simp_rw [hwR, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [swap3]
      simp only [Finset.mul_sum]
    · simp only [Finset.mul_sum]
      rw [swap4]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring

lemma mixG (P : Inst) (hv : ∀ i j r, 0 ≤ P.v i j r) (n : ℕ) {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (hπ : ∀ a, 0 ≤ π a) (hπ1 : ∑ a, π a = 1)
    (cap : ι → Fin P.I → Fin P.K → ℝ) (s : ι → GSol P n) (hs : ∀ a, GFeas P n (cap a) (s a)) :
    ∃ sb : GSol P n, GFeas P n (fun i k => ∑ a, π a * cap a i k) sb ∧
      gObj P n sb = ∑ a, π a * gObj P n (s a) := by
  have hm := fun t : Fin n => mixPer P hv π hπ hπ1 (fun a => (s a).x t) (fun a => (s a).y t)
    (fun a => (hs a).1 t)
  choose xb hxb hob using hm
  refine ⟨⟨xb, fun t j i k => ∑ a, π a * (s a).y t j i k⟩, ⟨fun t => hxb t, fun i k => ?_⟩, ?_⟩
  · dsimp only
    rw [swap3]
    exact Finset.sum_le_sum fun a _ => by
      simp only [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left ((hs a).2 i k) (hπ a)
  · simp only [gObj]
    rw [Finset.sum_congr rfl fun t _ => hob t, Finset.sum_comm]
    simp only [Finset.mul_sum]

lemma prepend (P : Inst) (n : ℕ) (x0 : Fin P.J → Fin P.I → Fin P.R → ℝ)
    (y0 : Fin P.J → Fin P.I → Fin P.K → ℝ) (h0 : PerOK P x0 y0)
    (cap : Fin P.I → Fin P.K → ℝ) (s : GSol P n) (hs : GFeas P n cap s) :
    GFeas P (n + 1) (fun i k => ∑ j, y0 j i k + cap i k) ⟨Fin.cons x0 s.x, Fin.cons y0 s.y⟩ ∧
      gObj P (n + 1) ⟨Fin.cons x0 s.x, Fin.cons y0 s.y⟩ = perObj P x0 y0 + gObj P n s := by
  refine ⟨⟨fun t => ?_, fun i k => ?_⟩, ?_⟩
  · refine Fin.cases ?_ (fun t => ?_) t
    · simpa using h0
    · simpa using hs.1 t
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    linarith [hs.2 i k]
  · simp only [gObj]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]

lemma GFeas_mono (P : Inst) (n : ℕ) (cap cap' : Fin P.I → Fin P.K → ℝ) (s : GSol P n)
    (hs : GFeas P n cap s) (h : ∀ i k, cap i k ≤ cap' i k) : GFeas P n cap' s :=
  ⟨hs.1, fun i k => (hs.2 i k).trans (h i k)⟩

theorem dp_le (P : Inst) (hP : P.Standing) : ∀ (n : ℕ) (C : P.Inv), ∃ s : GSol P n,
    GFeas P n (fun i k => (C i k : ℝ)) s ∧ P.optValue n C ≤ gObj P n s := by
  classical
  have hv := vnn P hP
  obtain ⟨-, -, hK, -, hlam, hlamsum, -, hv0, -, hQR⟩ := hP
  have hb_nn : ∀ j φ i, 0 ≤ P.buyProb j φ i := by
    intro j φ i
    unfold Inst.buyProb
    refine div_nonneg (hv _ _ _) ?_
    have : 0 ≤ ∑ k, P.vPhi j φ k := Finset.sum_nonneg fun k _ => hv _ _ _
    linarith
  have hb_sum : ∀ j φ, ∑ i, P.buyProb j φ i ≤ 1 := by
    intro j φ
    unfold Inst.buyProb
    rw [← Finset.sum_div]
    have h0 : 0 ≤ ∑ k, P.vPhi j φ k := Finset.sum_nonneg fun k _ => hv _ _ _
    rw [div_le_one (by linarith)]
    linarith
  have hb_le : ∀ j φ i, P.buyProb j φ i ≤ 1 := fun j φ i =>
    (Finset.single_le_sum (fun i _ => hb_nn j φ i) (Finset.mem_univ i)).trans (hb_sum j φ)
  intro n
  induction n with
  | zero =>
    intro C
    refine ⟨⟨Fin.elim0, Fin.elim0⟩, ⟨fun t => Fin.elim0 t, fun i k => by simp⟩, ?_⟩
    simp [Inst.optValue, gObj]
  | succ n ih =>
    intro C
    set V := P.optValue n with hV
    have hadm : (P.admissible C).Nonempty := by
      refine ⟨fun _ => P.noDisp, ?_⟩
      simp only [Inst.admissible, Inst.Omega, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun r => ?_, by simp⟩
      by_cases hr : P.noDisp = r
      · subst hr; simpa using hQR
      · simp [hr]
    let G : Fin P.J → (Fin P.I → Fin P.R) → ℝ := fun j φ =>
      (∑ i, P.buyProb j φ i *
          (P.p i (φ i) + Inst.finMax (univ.filter (fun k => 0 < C i k))
            (fun k => V (P.take C i k) - P.c i j k))) +
      (1 - ∑ i, P.buyProb j φ i) * V C
    have hopt : P.optValue (n + 1) C =
        (1 - ∑ j, P.lam j) * V C + ∑ j, P.lam j * Inst.finMax (P.admissible C) (G j) := by
      rw [Inst.optValue]
    choose φ hφ hφmax using fun j => Finset.exists_max_image (P.admissible C) (G j) hadm
    have hfm : ∀ j, Inst.finMax (P.admissible C) (G j) = G j (φ j) := by
      intro j; unfold Inst.finMax; rw [dif_pos hadm]
      exact le_antisymm (Finset.sup'_le _ _ (hφmax j)) (Finset.le_sup' _ (hφ j))
    have k0 : Fin P.K := ⟨0, hK⟩
    have hkex : ∀ (j : Fin P.J) (i : Fin P.I), ∃ k : Fin P.K,
        (univ.filter (fun k => 0 < C i k)).Nonempty →
          (k ∈ univ.filter (fun k => 0 < C i k) ∧
            Inst.finMax (univ.filter (fun k => 0 < C i k))
              (fun k => V (P.take C i k) - P.c i j k) = V (P.take C i k) - P.c i j k) := by
      intro j i
      by_cases hne : (univ.filter (fun k => 0 < C i k)).Nonempty
      · obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image _
          (fun k => V (P.take C i k) - P.c i j k) hne
        refine ⟨k, fun _ => ⟨hk, ?_⟩⟩
        unfold Inst.finMax; rw [dif_pos hne]
        exact le_antisymm (Finset.sup'_le _ _ hkmax)
          (Finset.le_sup' (f := fun k => V (P.take C i k) - P.c i j k) hk)
      · exact ⟨k0, fun h => absurd h hne⟩
    choose kc hkc using hkex
    set b : Fin P.J → Fin P.I → ℝ := fun j i => P.buyProb j (φ j) i with hbdef
    have hbne : ∀ j i, b j i ≠ 0 → (univ.filter (fun k => 0 < C i k)).Nonempty := by
      intro j i hb
      by_contra hne
      have hsum0 : ∑ k, C i k = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
        exact Finset.sum_eq_zero fun k _ => by have := hne (Finset.mem_univ k); omega
      have hnd := (Finset.mem_filter.1 (hφ j)).2 i hsum0
      apply hb
      simp only [hbdef, Inst.buyProb, Inst.vPhi, hnd, hv0, zero_div]
    have hterm : ∀ j i, b j i * Inst.finMax (univ.filter (fun k => 0 < C i k))
        (fun k => V (P.take C i k) - P.c i j k) =
        b j i * (V (P.take C i (kc j i)) - P.c i j (kc j i)) := by
      intro j i
      by_cases hb : b j i = 0
      · simp [hb]
      · rw [((hkc j i) (hbne j i hb)).2]
    have hstock : ∀ j i, b j i ≠ 0 → 0 < C i (kc j i) := fun j i hb => by
      have := ((hkc j i) (hbne j i hb)).1
      simpa using this
    -- next-state lottery
    let π : Option (Fin P.J × Fin P.I) → ℝ := fun o =>
      Option.elim o (1 - ∑ j, P.lam j * ∑ i, b j i) (fun q => P.lam q.1 * b q.1 q.2)
    let Cn : Option (Fin P.J × Fin P.I) → P.Inv := fun o =>
      Option.elim o C (fun q => P.take C q.2 (kc q.1 q.2))
    have hsumb : (∑ j, P.lam j * ∑ i, b j i) ≤ 1 := by
      calc _ ≤ ∑ j, P.lam j * 1 := Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hb_sum j (φ j)) (hlam j).1
        _ ≤ 1 := by simpa using hlamsum
    have hπ : ∀ o, 0 ≤ π o := by
      intro o
      cases o with
      | none => simp only [π, Option.elim_none]; linarith
      | some q => exact mul_nonneg (hlam q.1).1 (hb_nn _ _ _)
    have hπ1 : ∑ o, π o = 1 := by
      rw [Fintype.sum_option]
      simp only [π, Option.elim_none, Option.elim_some]
      rw [Fintype.sum_prod_type]
      simp only [Finset.mul_sum]
      ring
    choose sN hsN hvN using fun o => ih (Cn o)
    obtain ⟨sb, hsb, hsbobj⟩ := mixG P hv n π hπ hπ1 (fun o i k => (Cn o i k : ℝ)) sN hsN
    -- first period
    let x0 : Fin P.J → Fin P.I → Fin P.R → ℝ := fun j i r => if φ j i = r then 1 else 0
    let y0 : Fin P.J → Fin P.I → Fin P.K → ℝ := fun j i k =>
      if k = kc j i then P.lam j * b j i else 0
    have hV0 : ∀ j, (∑ l, ∑ r, P.v l j r * x0 j l r) = ∑ l, P.vPhi j (φ j) l := by
      intro j
      refine Finset.sum_congr rfl fun l _ => ?_
      simp [x0, Inst.vPhi, mul_ite]
    have hθ0 : ∀ j i, P.thetaX j (x0 j) i = P.lam j * b j i := by
      intro j i
      simp only [Inst.thetaX, hV0, hbdef, Inst.buyProb]
      have : (∑ r, P.v i j r * x0 j i r) = P.vPhi j (φ j) i := by
        simp [x0, Inst.vPhi, mul_ite]
      rw [this, mul_div_assoc]
    have hrev0 : ∀ j i, P.revX j (x0 j) i = P.lam j * b j i * P.p i (φ j i) := by
      intro j i
      simp only [Inst.revX, hV0, hbdef, Inst.buyProb]
      have : (∑ r, P.v i j r * x0 j i r * P.p i r) = P.vPhi j (φ j) i * P.p i (φ j i) := by
        simp [x0, Inst.vPhi, mul_ite]
      rw [this]
      ring
    have h0ok : PerOK P x0 y0 := by
      refine ⟨fun j r => ?_, fun j i => by simp [x0], fun j i => ?_, fun j i r => ?_,
        fun j i k => ?_⟩
      · have hm := (Finset.mem_filter.1 (hφ j)).1
        simp only [Inst.Omega, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        have : (∑ i, x0 j i r) = ((univ.filter (fun i => φ j i = r)).card : ℝ) := by
          simp only [x0]; rw [Finset.sum_boole]
        rw [this]; exact_mod_cast hm r
      · simp only [y0, hθ0]; simp
      · simp only [x0]; split_ifs <;> norm_num
      · simp only [y0]
        split_ifs
        · exact ⟨mul_nonneg (hlam j).1 (hb_nn _ _ _),
            mul_le_one₀ (hlam j).2 (hb_nn _ _ _) (hb_le _ _ _)⟩
        · norm_num
    obtain ⟨hs', hobj'⟩ := prepend P n x0 y0 h0ok _ sb hsb
    -- the next-state inventories average to C minus first-period consumption
    have hcapterm : ∀ (j : Fin P.J) (i' : Fin P.I) (i : Fin P.I) (k : Fin P.K),
        P.lam j * b j i' * ((P.take C i' (kc j i') i k : ℕ) : ℝ) =
          P.lam j * b j i' * (C i k : ℝ) -
            (if i' = i then (if k = kc j i then P.lam j * b j i else 0) else 0) := by
      intro j i' i k
      by_cases h : i' = i ∧ k = kc j i'
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Inst.take, and_self, if_true]
        by_cases hb : b j i' = 0
        · simp [hb]
        · rw [Nat.cast_sub (hstock j i' hb)]; push_cast; ring
      · have h' : ¬ (i = i' ∧ k = kc j i') := fun hh => h ⟨hh.1.symm, hh.2⟩
        simp only [Inst.take, h', if_false]
        by_cases hi : i' = i
        · subst hi
          have hk : ¬ k = kc j i' := fun hk => h ⟨rfl, hk⟩
          simp [hk]
        · simp [hi]
    have hcap : ∀ i k, (∑ j, y0 j i k + ∑ o, π o * (Cn o i k : ℝ)) ≤ (C i k : ℝ) := by
      intro i k
      refine le_of_eq ?_
      rw [Fintype.sum_option]
      simp only [π, Cn, Option.elim_none, Option.elim_some]
      rw [Fintype.sum_prod_type]
      simp only [hcapterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [y0]
      rw [show (∑ x, ∑ x_1, P.lam x * b x x_1 * (C i k : ℝ)) =
        (∑ x, P.lam x * ∑ i, b x i) * C i k by simp only [Finset.mul_sum, Finset.sum_mul]]
      ring
    refine ⟨_, GFeas_mono P (n + 1) _ _ _ hs' hcap, ?_⟩
    rw [hobj', hsbobj]
    have hj : ∀ j, P.lam j * G j (φ j) =
        (∑ i, (P.lam j * b j i * P.p i (φ j i) - P.c i j (kc j i) * (P.lam j * b j i) +
          P.lam j * b j i * V (P.take C i (kc j i)))) + P.lam j * V C -
          P.lam j * (∑ i, b j i) * V C := by
      intro j
      show P.lam j * ((∑ i, b j i * (P.p i (φ j i) + Inst.finMax (univ.filter (fun k => 0 < C i k))
            (fun k => V (P.take C i k) - P.c i j k))) + (1 - ∑ i, b j i) * V C) = _
      have e : (∑ i, b j i * (P.p i (φ j i) + Inst.finMax (univ.filter (fun k => 0 < C i k))
            (fun k => V (P.take C i k) - P.c i j k))) =
          ∑ i, (b j i * P.p i (φ j i) + b j i * (V (P.take C i (kc j i)) - P.c i j (kc j i))) :=
        Finset.sum_congr rfl fun i _ => by rw [mul_add, hterm j i]
      rw [e, mul_add, Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun i _ => show P.lam j * (b j i * P.p i (φ j i) +
          b j i * (V (P.take C i (kc j i)) - P.c i j (kc j i))) =
          P.lam j * b j i * P.p i (φ j i) - P.c i j (kc j i) * (P.lam j * b j i) +
          P.lam j * b j i * V (P.take C i (kc j i)) by ring)]
      ring
    have hper : perObj P x0 y0 = ∑ j, ∑ i,
        (P.lam j * b j i * P.p i (φ j i) - P.c i j (kc j i) * (P.lam j * b j i)) := by
      have hc : ∀ j i, (∑ k, P.c i j k * y0 j i k) = P.c i j (kc j i) * (P.lam j * b j i) := by
        intro j i; simp [y0, mul_ite]
      simp only [perObj, hrev0, hc]
      rw [Finset.sum_comm (f := fun i j => P.lam j * b j i * P.p i (φ j i)),
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => (Finset.sum_sub_distrib _ _).symm
    have hπV : ∑ o, π o * V (Cn o) = (1 - ∑ j, P.lam j * ∑ i, b j i) * V C +
        ∑ j, ∑ i, P.lam j * b j i * V (P.take C i (kc j i)) := by
      rw [Fintype.sum_option, Fintype.sum_prod_type]
      rfl
    have hval : P.optValue (n + 1) C = perObj P x0 y0 + ∑ o, π o * V (Cn o) := by
      rw [hopt, hper, hπV]
      simp only [hfm]
      rw [Finset.sum_congr rfl fun j _ => hj j]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_add_distrib]
      have e1 : (∑ j, P.lam j * V C) = (∑ j, P.lam j) * V C := by rw [Finset.sum_mul]
      have e2 : (∑ j, P.lam j * (∑ i, b j i) * V C) = (∑ j, P.lam j * ∑ i, b j i) * V C := by
        rw [Finset.sum_mul]
      rw [e1, e2]
      ring
    rw [hval]
    have := Finset.sum_le_sum (fun o (_ : o ∈ (univ : Finset (Option (Fin P.J × Fin P.I)))) =>
      mul_le_mul_of_nonneg_left (hvN o) (hπ o))
    linarith


end RFF5

open RFF5

theorem solution (P : Inst) (hP : P.Standing) : P.Jstar ≤ P.JD := by
  obtain ⟨s, hs, hle⟩ := dp_le P hP P.T P.C
  obtain ⟨sopt, hsopt⟩ := exists_DETOpt P hP
  rw [JD_eq P sopt hsopt]
  have hfeas : (⟨s.x, s.y⟩ : DETSol P) ∈ P.DETFeasible :=
    ⟨fun t => (hs.1 t).1, fun t => (hs.1 t).2.1, fun t => (hs.1 t).2.2.1, hs.2,
      fun t => (hs.1 t).2.2.2.1, fun t => (hs.1 t).2.2.2.2⟩
  have hobj : P.detObj ⟨s.x, s.y⟩ = gObj P P.T s := by
    simp only [Inst.detObj, gObj, perObj, Finset.sum_sub_distrib]
  calc P.Jstar = P.optValue P.T P.C := rfl
    _ ≤ gObj P P.T s := hle
    _ = P.detObj ⟨s.x, s.y⟩ := hobj.symm
    _ ≤ _ := hsopt.2 _ hfeas
