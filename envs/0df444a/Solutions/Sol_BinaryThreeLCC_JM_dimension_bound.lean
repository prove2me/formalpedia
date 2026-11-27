-- Prove2me | solution 1 for BinaryThreeLCC.JM.dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:05:58.276902+00:00
-- url     : https://prove2.me/submissions/684e738b-dba5-4a8b-9d39-bf7b96e70c00

import Mathlib
import Theorems.Thm_BinaryThreeLCC_JM_poincare_of_cut_dense
import Theorems.Thm_BinaryThreeLCC_JM_variance_step
import Theorems.Thm_BinaryThreeLCC_JM_palette_bound

set_option autoImplicit false

namespace BinaryThreeLCC.JM




namespace T8aux

set_option linter.unusedSectionVars false

variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ] [DecidableEq Ω] [DecidableEq Λ]

lemma sum_cons {α : Type} [Fintype α] {r : ℕ} (f : (Fin (r + 1) → α) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x : Fin r → α, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type]
  rfl

/-- End point of the walk. -/
def walkEnd (τ : Ω → Λ → Bool → Ω) : (r : ℕ) → Ω → (Fin r → Λ) → (Fin r → Bool) → Ω
  | 0, i, _, _ => i
  | r + 1, i, a, o => walkEnd τ r (τ i (a 0) (o 0)) (Fin.tail a) (Fin.tail o)

/-- The b-sequence of the walk. -/
def bseq (β : Ω → Λ → Bool → Λ) (τ : Ω → Λ → Bool → Ω) :
    (r : ℕ) → Ω → (Fin r → Λ) → (Fin r → Bool) → (Fin r → Λ)
  | 0, _, _, _ => Fin.elim0
  | r + 1, i, a, o => Fin.cons (β i (a 0) (o 0)) (bseq β τ r (τ i (a 0) (o 0)) (Fin.tail a) (Fin.tail o))

/-- Real-valued walk count. -/
noncomputable def cnt (τ : Ω → Λ → Bool → Ω) (r : ℕ) (j : Ω) (a : Fin r → Λ) (u : Ω) : ℝ :=
  ∑ o : Fin r → Bool, if walkEnd τ r j a o = u then 1 else 0

lemma cnt_zero (τ : Ω → Λ → Bool → Ω) (j : Ω) (a : Fin 0 → Λ) (u : Ω) :
    cnt τ 0 j a u = if j = u then 1 else 0 := by
  simp only [cnt, Finset.univ_unique, Finset.sum_singleton]
  rfl

lemma cnt_succ (τ : Ω → Λ → Bool → Ω) (hlazy : ∀ u a, τ u a false = u)
    (r : ℕ) (j : Ω) (a0 : Λ) (a : Fin r → Λ) (u : Ω) :
    cnt τ (r + 1) j (Fin.cons a0 a) u = cnt τ r j a u + cnt τ r (τ j a0 true) a u := by
  unfold cnt
  rw [sum_cons, Fintype.sum_bool]
  simp [walkEnd, hlazy, add_comm]

lemma ite_cons {α : Type} [DecidableEq α] {r : ℕ} (x : α) (xs : Fin r → α) (b : Fin (r + 1) → α) :
    (if (Fin.cons x xs : Fin (r + 1) → α) = b then (1 : ℝ) else 0) =
      (if x = b 0 then (1 : ℝ) else 0) * (if xs = Fin.tail b then (1 : ℝ) else 0) := by
  have hb : b = Fin.cons (b 0) (Fin.tail b) := (Fin.cons_self_tail b).symm
  by_cases h1 : x = b 0 <;> by_cases h2 : xs = Fin.tail b
  · subst h1 h2; simp [Fin.cons_self_tail]
  · rw [if_neg, if_neg h2]; · simp
    intro h; apply h2; rw [hb] at h; exact (Fin.cons_inj.mp h).2
  · rw [if_neg, if_neg h1]; · simp
    intro h; apply h1; rw [hb] at h; exact (Fin.cons_inj.mp h).1
  · rw [if_neg, if_neg h1]; · simp
    intro h; apply h1; rw [hb] at h; exact (Fin.cons_inj.mp h).1

lemma bcount (β : Ω → Λ → Bool → Λ) (τ : Ω → Λ → Bool → Ω)
    (hright : ∀ u b, (Finset.univ.filter (fun p : Λ × Bool => β u p.1 p.2 = b)).card = 2) :
    ∀ (r : ℕ) (j : Ω) (b : Fin r → Λ),
      ∑ a : Fin r → Λ, ∑ o : Fin r → Bool, (if bseq β τ r j a o = b then (1 : ℝ) else 0) = 2 ^ r
  | 0, j, b => by
      simp [bseq]
      have : (Fin.elim0 : Fin 0 → Λ) = b := Subsingleton.elim _ _
      simp [this]
  | r + 1, j, b => by
      have hr2 : ∀ u b, ∑ a : Λ, ∑ o : Bool, (if β u a o = b then (1 : ℝ) else 0) = 2 := by
        intro u b
        have := hright u b
        rw [← Fintype.sum_prod_type' (f := fun a o => if β u a o = b then (1 : ℝ) else 0)]
        rw [Finset.sum_boole]
        exact_mod_cast this
      rw [sum_cons]
      have e1 : ∀ a0 : Λ, ∑ a : Fin r → Λ, ∑ o : Fin (r + 1) → Bool,
          (if bseq β τ (r + 1) j (Fin.cons a0 a) o = b then (1 : ℝ) else 0) =
          ∑ o0 : Bool, (if β j a0 o0 = b 0 then (1 : ℝ) else 0) * 2 ^ r := by
        intro a0
        rw [Finset.sum_comm, sum_cons]
        refine Finset.sum_congr rfl (fun o0 _ => ?_)
        rw [Finset.sum_comm]
        have : ∀ a o, bseq β τ (r + 1) j (Fin.cons a0 a) (Fin.cons o0 o) =
            Fin.cons (β j a0 o0) (bseq β τ r (τ j a0 o0) a o) := by
          intro a o; simp [bseq]
        simp only [this, ite_cons, ← Finset.mul_sum]
        rw [bcount β τ hright r (τ j a0 o0) (Fin.tail b)]
      rw [Finset.sum_congr rfl (fun a0 _ => e1 a0)]
      simp_rw [← Finset.sum_mul]
      rw [hr2 j (b 0), pow_succ]
      ring

/-- Sum of squared deviations from the mean. -/
noncomputable def var {ι : Type} [Fintype ι] (g : ι → ℝ) : ℝ :=
  ∑ j, (g j - (∑ j', g j') / Fintype.card ι) ^ 2

lemma var_le {ι : Type} [Fintype ι] (x : ι → ℝ) (y : ℝ) : var x ≤ ∑ i, (x i - y) ^ 2 := by
  unfold var
  set c : ℝ := (Fintype.card ι : ℝ)
  set μ := (∑ j, x j) / c
  rw [← sub_nonneg, ← Finset.sum_sub_distrib]
  have h : ∀ i, (x i - y) ^ 2 - (x i - μ) ^ 2 = (μ - y) * 2 * x i - (μ - y) * (μ + y) := by
    intro i; ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  by_cases hc : c = 0
  · have : (Fintype.card ι) = 0 := Nat.cast_eq_zero.mp hc
    rw [Fintype.card_eq_zero_iff] at this
    simp
  · have hS : ∑ j, x j = c * μ := by simp only [μ]; field_simp
    rw [hS]
    have : (μ - y) * 2 * (c * μ) - (Fintype.card ι : ℝ) * ((μ - y) * (μ + y)) = c * (μ - y) ^ 2 := by
      simp only [c]; ring
    rw [this]
    positivity

lemma tele {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (v : Ω → W) (w : Λ → W) (β : Ω → Λ → Bool → Λ) (τ : Ω → Λ → Bool → Ω)
    (hpar : ∀ u a o, v u + w a + w (β u a o) + v (τ u a o) = 0) :
    ∀ (r : ℕ) (i : Ω) (a : Fin r → Λ) (o : Fin r → Bool),
      v (walkEnd τ r i a o) + ∑ t, w (a t) + ∑ t, w (bseq β τ r i a o t) = v i
  | 0, i, a, o => by simp [walkEnd]
  | r + 1, i, a, o => by
      have hneg : ∀ x : W, -x = x := by
        intro x
        have : x + x = 0 := by
          rw [← two_smul (ZMod 2) x]
          have : (2 : ZMod 2) = 0 := rfl
          rw [this, zero_smul]
        exact neg_eq_of_add_eq_zero_left this
      have ih := tele v w β τ hpar r (τ i (a 0) (o 0)) (Fin.tail a) (Fin.tail o)
      have hp := hpar i (a 0) (o 0)
      have e1 : v (τ i (a 0) (o 0)) = -(v i + w (a 0) + w (β i (a 0) (o 0))) :=
        eq_neg_of_add_eq_zero_right (by rw [← hp])
      simp only [walkEnd, bseq, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have e2 : ∑ t : Fin r, w (a t.succ) = ∑ t, w (Fin.tail a t) := rfl
      rw [e2]
      calc v (walkEnd τ r (τ i (a 0) (o 0)) (Fin.tail a) (Fin.tail o)) +
            (w (a 0) + ∑ t, w (Fin.tail a t)) +
            (w (β i (a 0) (o 0)) + ∑ t, w (bseq β τ r (τ i (a 0) (o 0)) (Fin.tail a) (Fin.tail o) t))
          = (v (walkEnd τ r (τ i (a 0) (o 0)) (Fin.tail a) (Fin.tail o)) + ∑ t, w (Fin.tail a t) +
            ∑ t, w (bseq β τ r (τ i (a 0) (o 0)) (Fin.tail a) (Fin.tail o) t)) + w (a 0) +
            w (β i (a 0) (o 0)) := by abel
        _ = -v i := by rw [ih, e1]; abel
        _ = v i := hneg _

lemma iter (τ : Ω → Λ → Bool → Ω) (hlazy : ∀ u a, τ u a false = u) (γ : ℝ) (hγ : γ ≤ 1)
    (hstep : ∀ g : Ω → ℝ, ∑ a, var (fun j => g j + g (τ j a true)) ≤
      4 * Fintype.card Λ * (1 - γ) * var g) :
    ∀ r : ℕ, ∑ a : Fin r → Λ, ∑ u, var (fun j => cnt τ r j a u) ≤
      Fintype.card Ω * (4 * Fintype.card Λ * (1 - γ)) ^ r
  | 0 => by
      simp only [Finset.univ_unique, Finset.sum_singleton, pow_zero, mul_one]
      calc ∑ u, var (fun j => cnt τ 0 j default u)
          ≤ ∑ u : Ω, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun u _ => ?_)
            refine (var_le _ 0).trans ?_
            simp only [cnt_zero, sub_zero]
            rw [Finset.sum_eq_single u]
            · simp
            · intro b _ hb; simp [hb]
            · simp
        _ = Fintype.card Ω := by simp
  | r + 1 => by
      have hc : 0 ≤ 4 * (Fintype.card Λ : ℝ) * (1 - γ) := by
        have : (0 : ℝ) ≤ 1 - γ := by linarith
        positivity
      rw [sum_cons]
      simp_rw [cnt_succ τ hlazy]
      rw [Finset.sum_comm]
      calc ∑ y : Fin r → Λ, ∑ x : Λ, ∑ u, var (fun j => cnt τ r j y u + cnt τ r (τ j x true) y u)
          = ∑ y : Fin r → Λ, ∑ u, ∑ x : Λ, var (fun j => cnt τ r j y u + cnt τ r (τ j x true) y u) := by
            refine Finset.sum_congr rfl (fun y _ => Finset.sum_comm)
        _ ≤ ∑ y : Fin r → Λ, ∑ u, 4 * Fintype.card Λ * (1 - γ) * var (fun j => cnt τ r j y u) := by
            refine Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun u _ => ?_))
            exact hstep (fun j => cnt τ r j y u)
        _ = 4 * Fintype.card Λ * (1 - γ) * ∑ y : Fin r → Λ, ∑ u, var (fun j => cnt τ r j y u) := by
            rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
        _ ≤ 4 * Fintype.card Λ * (1 - γ) * (Fintype.card Ω * (4 * Fintype.card Λ * (1 - γ)) ^ r) :=
            mul_le_mul_of_nonneg_left (iter τ hlazy γ hγ hstep r) hc
        _ = _ := by ring

lemma step_of_hyp [Nonempty Λ] (τ : Ω → Λ → Bool → Ω)
    (hdbl : ∀ u', (Finset.univ.filter
      (fun p : Ω × Λ => τ p.1 p.2 true = u')).card = Fintype.card Λ)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hcut : ∀ S : Finset Ω, κ * S.card * (Finset.univ \ S).card ≤
      ((Finset.univ.filter (fun p : Ω × Λ => p.1 ∈ S ∧ τ p.1 p.2 true ∉ S)).card : ℝ))
    (g : Ω → ℝ) :
    ∑ a, var (fun j => g j + g (τ j a true)) ≤
      4 * Fintype.card Λ * (1 - κ ^ 2 * (Fintype.card Ω : ℝ) ^ 2 /
        (16 * (Fintype.card Λ : ℝ) ^ 2)) * var g := by
  have hN : (0 : ℝ) < Fintype.card Λ := by exact_mod_cast Fintype.card_pos
  set N : ℝ := (Fintype.card Λ : ℝ)
  set wt : Ω → Ω → ℝ := fun i j => ∑ a : Λ, if τ i a true = j then (1 : ℝ) else 0 with hwt
  have hdblR : ∀ j, ∑ i, wt i j = N := by
    intro j
    have := hdbl j
    have h2 : ((Finset.univ.filter (fun p : Ω × Λ => τ p.1 p.2 true = j)).card : ℝ) = N := by
      rw [this]
    rw [Finset.natCast_card_filter, Fintype.sum_prod_type] at h2
    simpa [hwt] using h2
  have hpoinc : ∀ h : Ω → ℝ, ∑ i, h i = 0 →
      4 * Fintype.card Λ * (κ ^ 2 * (Fintype.card Ω : ℝ) ^ 2 / (16 * (Fintype.card Λ : ℝ) ^ 2)) *
        ∑ i, h i ^ 2 ≤ ∑ i, ∑ a, (h i - h (τ i a true)) ^ 2 := by
    intro h hsum
    have T5 := poincare_of_cut_dense wt
      (fun i j => Finset.sum_nonneg (fun a _ => by split_ifs <;> norm_num)) N
      (fun i => by
        apply le_of_eq
        simp only [hwt]
        rw [Finset.sum_comm]
        simp [N])
      (fun j => (hdblR j).le) κ hκ
      (fun S => by
        refine (hcut S).trans (le_of_eq ?_)
        rw [Finset.natCast_card_filter, Fintype.sum_prod_type]
        simp only [hwt]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S)]
        have h0 : ∑ x ∈ Finset.univ.filter (fun i => i ∉ S), ∑ y : Λ,
            (if x ∈ S ∧ τ x y true ∉ S then (1 : ℝ) else 0) = 0 := by
          refine Finset.sum_eq_zero (fun x hx => Finset.sum_eq_zero (fun y _ => ?_))
          simp only [Finset.mem_filter] at hx
          simp [hx.2]
        rw [h0, add_zero]
        have hf : Finset.univ.filter (fun i => i ∈ S) = S := by ext; simp
        rw [hf]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_ite_eq]
        simp [hi])
      h hsum
    have e : ∑ i, ∑ j, wt i j * (h i - h j) ^ 2 = ∑ i, ∑ a, (h i - h (τ i a true)) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hwt, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp
    rw [e] at T5
    refine le_trans (le_of_eq ?_) T5
    simp only [N]
    field_simp
    ring
  have hdbl' : ∀ u, (Finset.univ.filter (fun p : Λ × Ω => τ p.2 p.1 true = u)).card =
      Fintype.card Λ := by
    intro u
    rw [← hdbl u]
    refine Finset.card_bij (fun p _ => (p.2, p.1)) (by simp)
      (by intro a _ b _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1) ?_
    intro b hb
    exact ⟨(b.2, b.1), by simpa using hb, rfl⟩
  exact variance_step (fun a j => τ j a true) hdbl' _ hpoinc g

section Kikuchi

variable {K : Type} [Fintype K] [DecidableEq K]

/-- Left endpoint of a Kikuchi edge. -/
def pL (τ : Ω → Λ → Bool → Ω) (a : K → Ω) (r : ℕ) (e : K × (Fin r → Λ) × (Fin r → Bool)) :
    ((Fin r → Λ) × Ω) ⊕ (Fin r → Λ) :=
  Sum.inl (e.2.1, walkEnd τ r (a e.1) e.2.1 e.2.2)

/-- Right endpoint of a Kikuchi edge. -/
def qR (β : Ω → Λ → Bool → Λ) (τ : Ω → Λ → Bool → Ω) (a : K → Ω) (r : ℕ)
    (e : K × (Fin r → Λ) × (Fin r → Bool)) : ((Fin r → Λ) × Ω) ⊕ (Fin r → Λ) :=
  Sum.inr (bseq β τ r (a e.1) e.2.1 e.2.2)

lemma degL (β : Ω → Λ → Bool → Λ) (τ : Ω → Λ → Bool → Ω) (a : K → Ω) (r : ℕ)
    (i : K) (y : (Fin r → Λ) × Ω) :
    ((((Finset.univ.filter (fun e => e.1 = i ∧ pL τ a r e = Sum.inl y)).card +
      (Finset.univ.filter (fun e => e.1 = i ∧ qR β τ a r e = Sum.inl y)).card : ℕ)) : ℝ) =
      cnt τ r (a i) y.1 y.2 := by
  push_cast
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter]
  simp [pL, qR, Fintype.sum_prod_type, ite_and, cnt, Prod.ext_iff, eq_comm]

lemma degLtot (β : Ω → Λ → Bool → Λ) (τ : Ω → Λ → Bool → Ω) (a : K → Ω) (r : ℕ)
    (y : (Fin r → Λ) × Ω) :
    ((((Finset.univ.filter (fun e => pL τ a r e = Sum.inl y)).card +
      (Finset.univ.filter (fun e => qR β τ a r e = Sum.inl y)).card : ℕ)) : ℝ) =
      ∑ i, cnt τ r (a i) y.1 y.2 := by
  push_cast
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter]
  simp [pL, qR, Fintype.sum_prod_type, ite_and, cnt, Prod.ext_iff, eq_comm]

lemma degR (β : Ω → Λ → Bool → Λ) (τ : Ω → Λ → Bool → Ω)
    (hright : ∀ u b, (Finset.univ.filter (fun p : Λ × Bool => β u p.1 p.2 = b)).card = 2)
    (a : K → Ω) (r : ℕ) (i : K) (b : Fin r → Λ) :
    ((((Finset.univ.filter (fun e => e.1 = i ∧ pL τ a r e = Sum.inr b)).card +
      (Finset.univ.filter (fun e => e.1 = i ∧ qR β τ a r e = Sum.inr b)).card : ℕ)) : ℝ) =
      2 ^ r := by
  push_cast
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter]
  simp only [pL, qR, Fintype.sum_prod_type, reduceCtorEq, and_false, if_false,
    Finset.sum_const_zero, zero_add, Sum.inr.injEq, ite_and]
  rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp)]
  simp only [if_true]
  exact bcount β τ hright r (a i) b

lemma degRtot (β : Ω → Λ → Bool → Λ) (τ : Ω → Λ → Bool → Ω)
    (hright : ∀ u b, (Finset.univ.filter (fun p : Λ × Bool => β u p.1 p.2 = b)).card = 2)
    (a : K → Ω) (r : ℕ) (b : Fin r → Λ) :
    ((((Finset.univ.filter (fun e => pL τ a r e = Sum.inr b)).card +
      (Finset.univ.filter (fun e => qR β τ a r e = Sum.inr b)).card : ℕ)) : ℝ) =
      Fintype.card K * 2 ^ r := by
  push_cast
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter]
  simp only [pL, qR, Fintype.sum_prod_type, reduceCtorEq, if_false,
    Finset.sum_const_zero, zero_add, Sum.inr.injEq]
  rw [Finset.card_univ.symm, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact bcount β τ hright r (a i) b

end Kikuchi

end T8aux

end BinaryThreeLCC.JM

open BinaryThreeLCC.JM BinaryThreeLCC.JM.T8aux

/-- T8: Lemma 4.1 (variant, tuple system form). -/
theorem solution {Ω Λ : Type} [Fintype Ω] [Fintype Λ] [DecidableEq Ω] [DecidableEq Λ]
    [Nonempty Λ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (v : Ω → W) (w : Λ → W) (β : Ω → Λ → Bool → Λ) (τ : Ω → Λ → Bool → Ω)
    (hpar : ∀ u a o, v u + w a + w (β u a o) + v (τ u a o) = 0)
    (hlazy : ∀ u a, β u a false = a ∧ τ u a false = u)
    (hright : ∀ u b, (Finset.univ.filter (fun p : Λ × Bool => β u p.1 p.2 = b)).card = 2)
    (hdbl : ∀ u', (Finset.univ.filter
      (fun p : Ω × Λ => τ p.1 p.2 true = u')).card = Fintype.card Λ)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hcut : ∀ S : Finset Ω, κ * S.card * (Finset.univ \ S).card ≤
      ((Finset.univ.filter (fun p : Ω × Λ => p.1 ∈ S ∧ τ p.1 p.2 true ∉ S)).card : ℝ))
    (r : ℕ)
    (hγ : κ ^ 2 * (Fintype.card Ω : ℝ) ^ 2 / (16 * (Fintype.card Λ : ℝ) ^ 2) ≤ 1)
    (hr : (Fintype.card Ω : ℝ) * (Fintype.card Ω + 1) *
      (1 - κ ^ 2 * (Fintype.card Ω : ℝ) ^ 2 / (16 * (Fintype.card Λ : ℝ) ^ 2)) ^ r ≤ 1) :
    (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) : ℝ) ≤
      60 * (r * Real.logb 2 (Fintype.card Λ) + Real.logb 2 (Fintype.card Ω + 1)) := by
  classical
  open T8aux in
  set m : ℕ := Fintype.card Ω with hm
  set N : ℕ := Fintype.card Λ with hN
  set γ : ℝ := κ ^ 2 * (m : ℝ) ^ 2 / (16 * (N : ℝ) ^ 2) with hγdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  have hlog0 : 0 ≤ 60 * (r * Real.logb 2 N + Real.logb 2 (m + 1)) := by
    have h1 : 0 ≤ Real.logb 2 (N : ℝ) := Real.logb_nonneg one_lt_two (by exact_mod_cast Fintype.card_pos)
    have h2 : 0 ≤ Real.logb 2 ((m : ℝ) + 1) := Real.logb_nonneg one_lt_two (by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith)
    positivity
  obtain ⟨K, a, ha, hspan, hli⟩ := exists_linearIndependent'.{0} (ZMod 2) v
  have : Finite K := Finite.of_injective a ha
  letI : Fintype K := Fintype.ofFinite K
  have hk : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) = Fintype.card K := by
    rw [← hspan]; exact finrank_span_eq_card hli
  rw [hk]
  by_cases hK0 : Fintype.card K = 0
  · rw [hK0]; simpa using hlog0
  have : Nonempty K := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hK0)
  set k : ℕ := Fintype.card K with hkdef
  -- dual functionals
  have hex : ∀ i : K, ∃ g : W →ₗ[ZMod 2] ZMod 2,
      g.comp (Submodule.span (ZMod 2) (Set.range (v ∘ a))).subtype = (Module.Basis.span hli).coord i :=
    fun i => LinearMap.exists_extend _
  choose f hf0 using hex
  have hf : ∀ i j, f i (v (a j)) = if j = i then 1 else 0 := by
    intro i j
    have h1 := congrArg (fun g => g (Module.Basis.span hli j)) (hf0 i)
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self] at h1
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply,
      Function.comp_apply] at h1
    rw [h1, Finsupp.single_apply]
  -- the Kikuchi graph
  let label : ((Fin r → Λ) × Ω) ⊕ (Fin r → Λ) → W :=
    Sum.elim (fun y => v y.2 + ∑ t, w (y.1 t)) (fun b => ∑ t, w (b t))
  let φ : K → ((Fin r → Λ) × Ω) ⊕ (Fin r → Λ) → ZMod 2 := fun i x => f i (label x)
  have hφ : ∀ i (e : K × (Fin r → Λ) × (Fin r → Bool)),
      φ i (pL τ a r e) + φ i (qR β τ a r e) = if e.1 = i then 1 else 0 := by
    intro i e
    simp only [φ, label, pL, qR, Sum.elim_inl, Sum.elim_inr, ← map_add]
    rw [show v (walkEnd τ r (a e.1) e.2.1 e.2.2) + ∑ t, w (e.2.1 t) +
        ∑ t, w (bseq β τ r (a e.1) e.2.1 e.2.2 t) = v (a e.1) from
      tele v w β τ hpar r (a e.1) e.2.1 e.2.2]
    exact hf i e.1
  have hE : 0 < Fintype.card (K × (Fin r → Λ) × (Fin r → Bool)) := Fintype.card_pos
  have hcardV : (Fintype.card (((Fin r → Λ) × Ω) ⊕ (Fin r → Λ)) : ℝ) = (N : ℝ) ^ r * (m + 1) := by
    simp [Fintype.card_sum, Fintype.card_prod, hm, hN]; ring
  have hcardE : (Fintype.card (K × (Fin r → Λ) × (Fin r → Bool)) : ℝ) = k * ((N : ℝ) ^ r * 2 ^ r) := by
    simp [Fintype.card_prod, hkdef, hN]
  have hγ1 : γ ≤ 1 := hγ
  have hstep := step_of_hyp τ hdbl κ hκ hcut
  have hiter := iter τ (fun u a => (hlazy u a).2) γ hγ1 hstep r
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hK0
  have hvar : ∑ x, ∑ i, ((((Finset.univ.filter (fun e => e.1 = i ∧ pL τ a r e = x)).card +
        (Finset.univ.filter (fun e => e.1 = i ∧ qR β τ a r e = x)).card : ℕ) : ℝ) -
        (((Finset.univ.filter (fun e => pL τ a r e = x)).card +
          (Finset.univ.filter (fun e => qR β τ a r e = x)).card : ℕ) : ℝ) / Fintype.card K) ^ 2 ≤
      (Fintype.card (((Fin r → Λ) × Ω) ⊕ (Fin r → Λ)) : ℝ) * Fintype.card K *
        ((Fintype.card (K × (Fin r → Λ) × (Fin r → Bool)) : ℝ) /
          (Fintype.card K * Fintype.card (((Fin r → Λ) × Ω) ⊕ (Fin r → Λ)))) ^ 2 := by
    rw [Fintype.sum_sum_type]
    simp only [degL, degLtot, degR β τ hright a r, degRtot β τ hright a r]
    have hz : ∑ i : K, ((2 : ℝ) ^ r - (Fintype.card K : ℝ) * 2 ^ r / Fintype.card K) ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [mul_div_cancel_left₀ _ hkpos.ne']; ring
    simp only [hz, Finset.sum_const_zero, add_zero]
    rw [hcardV, hcardE]
    -- per-vertex bound
    have hpv : ∀ y : (Fin r → Λ) × Ω, ∑ i : K, (cnt τ r (a i) y.1 y.2 -
        (∑ i, cnt τ r (a i) y.1 y.2) / Fintype.card K) ^ 2 ≤
        var (fun j => cnt τ r j y.1 y.2) := by
      intro y
      have h1 := var_le (fun i : K => cnt τ r (a i) y.1 y.2)
        ((∑ j, cnt τ r j y.1 y.2) / Fintype.card Ω)
      refine le_trans h1 ?_
      unfold var
      rw [← Finset.sum_image (f := fun j => (cnt τ r j y.1 y.2 -
        (∑ j, cnt τ r j y.1 y.2) / Fintype.card Ω) ^ 2) (fun x _ y _ h => ha h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
    have hsum := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hpv y)
    refine le_trans hsum (le_trans (le_of_eq (Fintype.sum_prod_type _)) (le_trans hiter ?_))
    -- arithmetic
    have hX : (0 : ℝ) < (4 * N) ^ r := by positivity
    have h1γ : 0 ≤ 1 - γ := by linarith
    have hrr : (m : ℝ) * (m + 1) * (1 - γ) ^ r ≤ 1 := hr
    have hm1 : (0 : ℝ) < m + 1 := by positivity
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.pos_of_ne_zero hK0
    have hR : ((N : ℝ) ^ r * (m + 1)) * k * (k * ((N : ℝ) ^ r * 2 ^ r) /
        (k * ((N : ℝ) ^ r * (m + 1)))) ^ 2 = k * (4 * N) ^ r / (m + 1) := by
      have hNr : (0 : ℝ) < (N : ℝ) ^ r := by positivity
      field_simp
      rw [mul_pow, show (4 : ℝ) ^ r = (2 ^ r) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      ring
    rw [hR, le_div_iff₀ hm1, mul_pow]
    calc _ = (4 * (N : ℝ)) ^ r * ((m : ℝ) * (m + 1) * (1 - γ) ^ r) := by rw [hm, hN]; ring
      _ ≤ (4 * N) ^ r * 1 := mul_le_mul_of_nonneg_left hrr hX.le
      _ ≤ (4 * N) ^ r * k := mul_le_mul_of_nonneg_left hk1 hX.le
      _ = k * (4 * N) ^ r := by ring
  have T7 := palette_bound (pL τ a r) (qR β τ a r) Prod.fst φ hφ hE hvar
  refine le_trans T7 (le_of_eq ?_)
  rw [hcardV, Real.logb_mul (by positivity) (by positivity), Real.logb_pow]


namespace BinaryThreeLCC.JM

end BinaryThreeLCC.JM
