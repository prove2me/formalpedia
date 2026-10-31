-- Prove2me | solution 1 for FramingFulfillment.RFF.det_stationary
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T15:28:40.948219+00:00
-- url     : https://prove2.me/submissions/2d8a36c4-4b33-4a40-a780-62c9ce55622e

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model

open FramingFulfillment.RFF Finset

namespace RFFStat

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
lemma sum_rep0 (P : Inst) (θ : ℕ) (g : Fin (1 * P.T) → ℝ) :
    (∑ t : Fin (θ * P.T), g (finCongr (one_mul P.T).symm (finProdFinEquiv.symm t).2)) =
      (θ : ℝ) * ∑ u, g u := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  congr 1
  exact Equiv.sum_comp (finCongr (one_mul P.T).symm) g

lemma sum_fold0 (P : Inst) (θ : ℕ) (g : Fin (θ * P.T) → ℝ) :
    (∑ u : Fin (1 * P.T), ∑ a : Fin θ,
      g (finProdFinEquiv (a, finCongr (one_mul P.T) u))) = ∑ t, g t := by
  rw [Equiv.sum_comp (finCongr (one_mul P.T)) (fun b => ∑ a : Fin θ, g (finProdFinEquiv (a, b)))]
  rw [← Equiv.sum_comp finProdFinEquiv g, Fintype.sum_prod_type, Finset.sum_comm]


lemma swap3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]

lemma swap4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm,
    Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]

def rep (P : Inst) (θ : ℕ) (t : Fin (P.scale θ).T) : Fin (P.scale 1).T :=
  finCongr (one_mul P.T).symm ((finProdFinEquiv (m := θ) (n := P.T)).symm t).2

def emb (P : Inst) (θ : ℕ) (a : Fin θ) (u : Fin (P.scale 1).T) : Fin (P.scale θ).T :=
  finProdFinEquiv (m := θ) (n := P.T) (a, finCongr (one_mul P.T) u)

lemma sum_rep (P : Inst) (θ : ℕ) (g : Fin (P.scale 1).T → ℝ) :
    (∑ t : Fin (P.scale θ).T, g (rep P θ t)) = (θ : ℝ) * ∑ u, g u :=
  sum_rep0 P θ g

lemma sum_fold (P : Inst) (θ : ℕ) (g : Fin (P.scale θ).T → ℝ) :
    (∑ u : Fin (P.scale 1).T, ∑ a : Fin θ, g (emb P θ a u)) = ∑ t, g t :=
  sum_fold0 P θ g

lemma up (P : Inst) (θ : ℕ) (s1 : DETSol (P.scale 1)) (hs1 : s1 ∈ (P.scale 1).DETFeasible) :
    ∃ s : DETSol (P.scale θ), s ∈ (P.scale θ).DETFeasible ∧
      (P.scale θ).detObj s = (θ : ℝ) * (P.scale 1).detObj s1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs1
  let f := rep P θ
  refine ⟨⟨fun t => s1.x (f t), fun t => s1.y (f t)⟩, ⟨fun t => h1 (f t), fun t => h2 (f t),
    fun t => h3 (f t), fun i k => ?_, fun t => h5 (f t), fun t => h6 (f t)⟩, ?_⟩
  · have := sum_rep P θ (fun u => ∑ j, s1.y u j i k)
    refine (le_of_eq this).trans ?_
    have h : _ ≤ ((1 * P.C i k : ℕ) : ℝ) := h4 i k
    show (θ : ℝ) * _ ≤ ((θ * P.C i k : ℕ) : ℝ)
    push_cast at h ⊢
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  · simp only [Inst.detObj]
    rw [mul_sub]
    congr 1
    · exact sum_rep P θ (fun u => ∑ i, ∑ j, (P.scale 1).revX j (s1.x u j) i)
    · exact sum_rep P θ (fun u => ∑ j, ∑ i, ∑ k, (P.scale 1).c i j k * s1.y u j i k)

lemma down (P : Inst) (hv : ∀ i j r, 0 ≤ P.v i j r) (θ : ℕ) (hθ : 0 < θ)
    (s : DETSol (P.scale θ)) (hs : s ∈ (P.scale θ).DETFeasible) :
    ∃ s1 : DETSol (P.scale 1), s1 ∈ (P.scale 1).DETFeasible ∧
      (θ : ℝ) * (P.scale 1).detObj s1 = (P.scale θ).detObj s := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  have hθr : (0:ℝ) < θ := by exact_mod_cast hθ
  let g := emb P θ
  have hμ : ∀ a : Fin θ, (0:ℝ) ≤ 1 / θ := fun _ => by positivity
  have hμ1 : ∑ _a : Fin θ, (1 / θ : ℝ) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hmix : ∀ (u : Fin (P.scale 1).T) (j : Fin (P.scale 1).J), ∃ w : Fin θ → ℝ, (∀ a, 0 ≤ w a) ∧
      (∑ a, w a = 1) ∧
      (∀ i : Fin (P.scale 1).I, (P.scale 1).thetaX j (fun i r => ∑ a, w a * s.x (g a u) j i r) i =
        ∑ a, (1 / θ : ℝ) * (P.scale θ).thetaX j (s.x (g a u) j) i) ∧
      (∀ i : Fin (P.scale 1).I, (P.scale 1).revX j (fun i r => ∑ a, w a * s.x (g a u) j i r) i =
        ∑ a, (1 / θ : ℝ) * (P.scale θ).revX j (s.x (g a u) j) i) :=
    fun u j => mix P hv j (fun _ => (1 / θ : ℝ)) hμ hμ1 (fun a => s.x (g a u) j)
      (fun a i r => (h5 (g a u) j i r).1)
  choose w hw0 hw1 hwθ hwR using hmix
  let x1 : Fin (P.scale 1).T → Fin (P.scale 1).J → Fin (P.scale 1).I → Fin (P.scale 1).R → ℝ :=
    fun u j i r => ∑ a, w u j a * s.x (g a u) j i r
  let y1 : Fin (P.scale 1).T → Fin (P.scale 1).J → Fin (P.scale 1).I → Fin (P.scale 1).K → ℝ :=
    fun u j i k => (1 / θ : ℝ) * ∑ a, s.y (g a u) j i k
  refine ⟨⟨x1, y1⟩, ⟨fun u j r => ?_, fun u j i => ?_, fun u j i => ?_, fun i k => ?_,
    fun u j i r => ⟨?_, ?_⟩, fun u j i k => ⟨?_, ?_⟩⟩, ?_⟩
  · -- (10a)
    show ∑ i, ∑ a, w u j a * s.x (g a u) j i r ≤ _
    rw [Finset.sum_comm]
    calc _ ≤ ∑ a, w u j a * (P.Q r : ℝ) :=
          Finset.sum_le_sum fun a _ => by
            rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (h1 _ j r) (hw0 u j a)
      _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]; rfl
  · -- (10b)
    show ∑ r, ∑ a, w u j a * s.x (g a u) j i r = 1
    rw [Finset.sum_comm]
    calc (∑ a, ∑ r, w u j a * s.x (g a u) j i r) = ∑ a, w u j a * 1 :=
          Finset.sum_congr rfl fun a _ => by rw [← Finset.mul_sum]; congr 1; exact h2 (g a u) j i
      _ = 1 := by rw [← Finset.sum_mul, hw1 u j, one_mul]
  · -- (10c)
    show ∑ k, (1 / θ : ℝ) * ∑ a, s.y (g a u) j i k = (P.scale 1).thetaX j (x1 u j) i
    rw [← Finset.mul_sum, Finset.sum_comm, hwθ u j i, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ => h3 (g a u) j i
  · -- (10d)
    show ∑ u, ∑ j, (1 / θ : ℝ) * ∑ a, s.y (g a u) j i k ≤ _
    have hfold := sum_fold P θ (fun t => ∑ j, s.y t j i k)
    have : (∑ u, ∑ j, (1 / θ : ℝ) * ∑ a, s.y (g a u) j i k) =
        (1 / θ : ℝ) * ∑ t, ∑ j, s.y t j i k := by
      rw [← hfold, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.mul_sum, Finset.sum_comm]
    rw [this]
    have h : _ ≤ ((θ * P.C i k : ℕ) : ℝ) := h4 i k
    show _ ≤ ((1 * P.C i k : ℕ) : ℝ)
    push_cast at h ⊢
    rw [one_mul, div_mul_eq_mul_div, one_mul, div_le_iff₀ hθr]
    linarith
  · show 0 ≤ ∑ a, w u j a * s.x (g a u) j i r
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hw0 u j a) (h5 (g a u) j i r).1
  · show ∑ a, w u j a * s.x (g a u) j i r ≤ 1
    calc (∑ a, w u j a * s.x (g a u) j i r) ≤ ∑ a, w u j a :=
          Finset.sum_le_sum fun a _ => mul_le_of_le_one_right (hw0 u j a) (h5 _ j i r).2
      _ = 1 := hw1 u j
  · show 0 ≤ (1 / θ : ℝ) * ∑ a, s.y (g a u) j i k
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => (h6 _ j i k).1)
  · show (1 / θ : ℝ) * ∑ a, s.y (g a u) j i k ≤ 1
    have : (∑ a : Fin θ, s.y (g a u) j i k) ≤ θ := by
      calc _ ≤ ∑ _a : Fin θ, (1:ℝ) := Finset.sum_le_sum fun a _ => (h6 _ j i k).2
        _ = θ := by simp
    rw [div_mul_eq_mul_div, one_mul, div_le_one hθr]; exact this
  · -- objective
    simp only [Inst.detObj]
    rw [mul_sub]
    congr 1
    · rw [← sum_fold P θ (fun t => ∑ i, ∑ j, (P.scale θ).revX j (s.x t j) i), Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      have : ∀ (i : Fin (P.scale 1).I) (j : Fin (P.scale 1).J), (P.scale 1).revX j (x1 u j) i =
          ∑ a, (1 / θ : ℝ) * (P.scale θ).revX j (s.x (g a u) j) i := fun i j => hwR u j i
      simp_rw [this]
      rw [swap3]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => ?_
      field_simp
      rfl
    · rw [← sum_fold P θ (fun t => ∑ j, ∑ i, ∑ k, (P.scale θ).c i j k * s.y t j i k),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      have h : ∀ (j : Fin (P.scale 1).J) (i : Fin (P.scale 1).I) (k : Fin (P.scale 1).K),
          (P.scale 1).c i j k * y1 u j i k =
            ∑ a, (1 / θ : ℝ) * ((P.scale θ).c i j k * s.y (g a u) j i k) := by
        intro j i k
        simp only [y1, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by
          show P.c i j k * _ = _ * (P.c i j k * _)
          ring
      simp_rw [h]
      rw [swap4]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      field_simp
      rfl


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

end RFFStat

open RFFStat

theorem solution (P : Inst) (hP : P.Standing) (θ : ℕ) :
    (P.scale θ).JD = (θ : ℝ) * (P.scale 1).JD := by
  have hS : ∀ θ : ℕ, (P.scale θ).Standing := fun θ => hP
  obtain ⟨s1, hs1⟩ := exists_DETOpt _ (hS 1)
  obtain ⟨sθ, hsθ⟩ := exists_DETOpt _ (hS θ)
  rw [JD_eq _ s1 hs1, JD_eq _ sθ hsθ]
  rcases Nat.eq_zero_or_pos θ with h0 | hpos
  · subst h0
    haveI : IsEmpty (Fin (P.scale 0).T) := ⟨fun t => by
      have := t.2; simp [Inst.scale] at this⟩
    simp [Inst.detObj, Finset.univ_eq_empty]
  · refine le_antisymm ?_ ?_
    · obtain ⟨s1', hs1', hobj⟩ := down P (vnn P hP) θ hpos sθ hsθ.1
      rw [← hobj]
      exact mul_le_mul_of_nonneg_left (hs1.2 s1' hs1') (Nat.cast_nonneg _)
    · obtain ⟨s', hs', hobj⟩ := up P θ s1 hs1.1
      rw [← hobj]
      exact hsθ.2 s' hs'
