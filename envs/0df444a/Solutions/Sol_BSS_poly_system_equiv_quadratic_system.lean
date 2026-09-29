-- Prove2me | solution 1 for BSS.poly_system_equiv_quadratic_system
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T22:00:16.699003+00:00
-- url     : https://prove2.me/submissions/8ef22141-942e-4698-b186-efbecc65e88d

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset MvPolynomial

namespace BSSQuadAux

/-- Bounded exponent tuples: monomials in `n` variables with each exponent `≤ D`. -/
abbrev MonT (n D : ℕ) : Type := Fin n → Fin (D + 1)

variable {n D : ℕ}

/-- The exponent `Finsupp` attached to a bounded exponent tuple. -/
noncomputable def mexp (a : MonT n D) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (a i : ℕ)

@[simp] lemma mexp_apply (a : MonT n D) (i : Fin n) : mexp a i = (a i : ℕ) := rfl

lemma mexp_injective : Function.Injective (mexp (n := n) (D := D)) := by
  intro a b h
  funext i
  have : (a i : ℕ) = (b i : ℕ) := by
    have := congrArg (fun f : Fin n →₀ ℕ => f i) h
    simpa using this
  exact Fin.val_injective this

/-- Increase the `i`-th exponent by one (cyclically, but only used when `a i < D`). -/
def mincr (i : Fin n) (a : MonT n D) : MonT n D := fun j =>
  if j = i then ⟨((a j : ℕ) + 1) % (D + 1), Nat.mod_lt _ (Nat.succ_pos D)⟩ else a j

/-- Decrease the `i`-th exponent by one (truncated). -/
def mdecr (i : Fin n) (a : MonT n D) : MonT n D := fun j =>
  if j = i then ⟨(a j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) (a j).isLt⟩ else a j

/-- The exponent tuple of the variable `x i`. -/
def mone (i : Fin n) : MonT n D := mincr i 0

lemma mincr_val_self (i : Fin n) (a : MonT n D) (h : (a i : ℕ) < D) :
    ((mincr i a i : Fin (D + 1)) : ℕ) = (a i : ℕ) + 1 := by
  simp only [mincr]
  exact Nat.mod_eq_of_lt (by omega)

lemma mincr_val_ne (i j : Fin n) (a : MonT n D) (h : j ≠ i) :
    ((mincr i a j : Fin (D + 1)) : ℕ) = (a j : ℕ) := by
  simp [mincr, h]

lemma mdecr_val_self (i : Fin n) (a : MonT n D) :
    ((mdecr i a i : Fin (D + 1)) : ℕ) = (a i : ℕ) - 1 := by
  simp [mdecr]

lemma mdecr_val_ne (i j : Fin n) (a : MonT n D) (h : j ≠ i) :
    ((mdecr i a j : Fin (D + 1)) : ℕ) = (a j : ℕ) := by
  simp [mdecr, h]

lemma mincr_mdecr (i : Fin n) (a : MonT n D) (hi : 0 < (a i : ℕ)) :
    mincr i (mdecr i a) = a := by
  funext j
  apply Fin.val_injective
  by_cases h : j = i
  · subst h
    have hlt : ((mdecr j a j : Fin (D + 1)) : ℕ) < D := by
      rw [mdecr_val_self]
      have := (a j).isLt
      omega
    rw [mincr_val_self _ _ hlt, mdecr_val_self]
    omega
  · rw [mincr_val_ne _ _ _ h, mdecr_val_ne _ _ _ h]

/-- The monomial value `∏ j, x j ^ a j`. -/
def monval (x : Fin n → ℝ) (a : MonT n D) : ℝ := ∏ j, x j ^ (a j : ℕ)

lemma monval_zero (x : Fin n → ℝ) : monval x (0 : MonT n D) = 1 := by
  simp [monval]

lemma monval_mincr (x : Fin n → ℝ) (i : Fin n) (a : MonT n D) (h : (a i : ℕ) < D) :
    monval x (mincr i a) = x i * monval x a := by
  unfold monval
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul (f := fun j => x j ^ ((a j : Fin (D + 1)) : ℕ)) _ (Finset.mem_univ i)]
  have hE : ∀ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      x j ^ ((mincr i a j : Fin (D + 1)) : ℕ) = x j ^ ((a j : ℕ)) := by
    intro j hj
    rw [mincr_val_ne _ _ _ (Finset.ne_of_mem_erase hj)]
  rw [Finset.prod_congr rfl hE, mincr_val_self i a h, pow_succ]
  ring

lemma monval_mone (x : Fin n → ℝ) (i : Fin n) (hD : 0 < D) :
    monval x (mone (D := D) i) = x i := by
  have h : ((0 : MonT n D) i : ℕ) < D := by simpa using hD
  rw [mone, monval_mincr x i 0 h, monval_zero, mul_one]

lemma totalDegree_sub_le' {σ : Type*} (f g : MvPolynomial σ ℝ) :
    (f - g).totalDegree ≤ max f.totalDegree g.totalDegree := by
  rw [sub_eq_add_neg]
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  simp

end BSSQuadAux

namespace BSS

open BSSQuadAux

/-- The number of auxiliary (monomial) variables. -/
def numMon (n D : ℕ) : ℕ := Fintype.card (MonT n D)

noncomputable def monEquiv (n D : ℕ) : MonT n D ≃ Fin (numMon n D) := Fintype.equivFin _

variable {n D m : ℕ}

/-- Index of the variable `x i` among the variables of the quadratic system. -/
def xvar (n D : ℕ) (i : Fin n) : Fin (n + numMon n D) := Fin.castAdd _ i

/-- Index of the variable `t a` among the variables of the quadratic system. -/
noncomputable def tvar (a : MonT n D) : Fin (n + numMon n D) := Fin.natAdd n (monEquiv n D a)

/-- The normalisation equation `t_0 = 1`. -/
noncomputable def eqUnit (n D : ℕ) : MvPolynomial (Fin (n + numMon n D)) ℝ :=
  X (tvar (0 : MonT n D)) - 1

/-- The equation `t_{e i} = x i`. -/
noncomputable def eqVar (n D : ℕ) (i : Fin n) : MvPolynomial (Fin (n + numMon n D)) ℝ :=
  X (tvar (mone (D := D) i)) - X (xvar n D i)

/-- The quadratic relation `t_{a + e i} = t_{e i} * t_a`, imposed when `a i < D`. -/
noncomputable def eqProd (i : Fin n) (a : MonT n D) : MvPolynomial (Fin (n + numMon n D)) ℝ :=
  if (a i : ℕ) < D then X (tvar (mincr i a)) - X (tvar (mone (D := D) i)) * X (tvar a) else 0

/-- The linearised form of the equation `p l = 0`. -/
noncomputable def eqLin (D : ℕ) (p : Fin m → MvPolynomial (Fin n) ℝ) (l : Fin m) :
    MvPolynomial (Fin (n + numMon n D)) ℝ :=
  ∑ a : MonT n D, C (coeff (mexp a) (p l)) * X (tvar a)

/-- Index set of the equations of the quadratic system. -/
abbrev EqIdx (n D m : ℕ) : Type := Unit ⊕ Fin n ⊕ (Fin n × MonT n D) ⊕ Fin m

/-- The quadratic system attached to a polynomial system. -/
noncomputable def eqFam (D : ℕ) (p : Fin m → MvPolynomial (Fin n) ℝ) :
    EqIdx n D m → MvPolynomial (Fin (n + numMon n D)) ℝ :=
  Sum.elim (fun _ => eqUnit n D)
    (Sum.elim (fun i => eqVar n D i)
      (Sum.elim (fun ia => eqProd ia.1 ia.2) (fun l => eqLin D p l)))

lemma sum_monval_eq_eval (x : Fin n → ℝ) (f : MvPolynomial (Fin n) ℝ)
    (hsupp : ∀ α ∈ f.support, ∀ i, (α i) ≤ D) :
    ∑ a : MonT n D, coeff (mexp a) f * monval x a = eval x f := by
  classical
  have himg : f.support ⊆ Finset.image (mexp (n := n) (D := D)) Finset.univ := by
    intro α hα
    refine Finset.mem_image.2 ⟨fun i => ⟨α i, by have := hsupp α hα i; omega⟩, Finset.mem_univ _, ?_⟩
    ext i
    simp [mexp]
  have h1 : ∑ a : MonT n D, coeff (mexp a) f * monval x a
      = ∑ α ∈ Finset.image (mexp (n := n) (D := D)) Finset.univ,
          coeff α f * ∏ i, x i ^ (α i) := by
    rw [Finset.sum_image (fun a _ b _ h => mexp_injective h)]
    rfl
  have h2 : ∑ α ∈ Finset.image (mexp (n := n) (D := D)) Finset.univ,
      coeff α f * ∏ i, x i ^ (α i)
      = ∑ α ∈ f.support, coeff α f * ∏ i, x i ^ (α i) := by
    refine (Finset.sum_subset himg ?_).symm
    intro α _ hα
    rw [MvPolynomial.notMem_support_iff.mp hα, zero_mul]
  rw [h1, h2, MvPolynomial.eval_eq']

end BSS

open BSSQuadAux BSS in
theorem solution {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ) :
    ∃ (N k : ℕ) (hn : n ≤ N) (q : Fin k → MvPolynomial (Fin N) ℝ),
      (∀ j, (q j).totalDegree ≤ 2) ∧
      (∀ x : Fin n → ℝ, (∀ i, MvPolynomial.eval x (p i) = 0) →
          ∃ z : Fin N → ℝ, (∀ i : Fin n, z (Fin.castLE hn i) = x i) ∧
            ∀ j, MvPolynomial.eval z (q j) = 0) ∧
      (∀ z : Fin N → ℝ, (∀ j, MvPolynomial.eval z (q j) = 0) →
          ∀ i, MvPolynomial.eval (fun t : Fin n => z (Fin.castLE hn t)) (p i) = 0) := by
  classical
  set D : ℕ := 1 + ∑ l, (p l).totalDegree with hDdef
  have hD1 : 0 < D := by omega
  have hsupp : ∀ l, ∀ α ∈ (p l).support, ∀ i, (α i) ≤ D := by
    intro l α hα i
    have h1 : α i ≤ α.sum (fun _ e => e) := by
      by_cases h : α i = 0
      · simp [h]
      · exact Finset.single_le_sum (f := fun j => α j) (fun _ _ => Nat.zero_le _)
          (Finsupp.mem_support_iff.mpr h)
    have h2 : (α.sum fun _ e => e) ≤ (p l).totalDegree := MvPolynomial.le_totalDegree hα
    have h3 : (p l).totalDegree ≤ ∑ l', (p l').totalDegree :=
      Finset.single_le_sum (f := fun l' => (p l').totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)
    omega
  refine ⟨n + numMon n D, Fintype.card (EqIdx n D m), Nat.le_add_right _ _,
    fun j => eqFam D p ((Fintype.equivFin (EqIdx n D m)).symm j), ?_, ?_, ?_⟩
  · -- degrees
    have hall : ∀ c : EqIdx n D m, (eqFam D p c).totalDegree ≤ 2 := by
      rintro (u | i | ⟨i, a⟩ | l)
      · show (eqUnit n D).totalDegree ≤ 2
        refine le_trans (totalDegree_sub_le' _ _) ?_
        simp [MvPolynomial.totalDegree_X]
      · show (eqVar n D i).totalDegree ≤ 2
        refine le_trans (totalDegree_sub_le' _ _) ?_
        simp [MvPolynomial.totalDegree_X]
      · show (eqProd i a).totalDegree ≤ 2
        rw [eqProd]
        split
        · refine le_trans (totalDegree_sub_le' _ _) ?_
          refine max_le (by simp [MvPolynomial.totalDegree_X]) ?_
          refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
          simp [MvPolynomial.totalDegree_X]
        · simp
      · show (eqLin D p l).totalDegree ≤ 2
        rw [eqLin]
        refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
        refine Finset.sup_le ?_
        intro a _
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        simp [MvPolynomial.totalDegree_X]
    exact fun j => hall _
  · -- solutions lift
    intro x hx
    refine ⟨Fin.addCases (motive := fun _ => ℝ) (fun i => x i)
      (fun j => monval x ((monEquiv n D).symm j)), ?_, ?_⟩
    · intro i
      show Fin.addCases (motive := fun _ => ℝ) _ _ (Fin.castAdd _ i) = x i
      rw [Fin.addCases_left]
    · set z : Fin (n + numMon n D) → ℝ := Fin.addCases (motive := fun _ => ℝ) (fun i => x i)
        (fun j => monval x ((monEquiv n D).symm j)) with hzdef
      have hzt : ∀ a : MonT n D, z (tvar a) = monval x a := by
        intro a
        rw [hzdef, tvar, Fin.addCases_right]
        simp
      have hzx : ∀ i : Fin n, z (xvar n D i) = x i := by
        intro i
        rw [hzdef, xvar, Fin.addCases_left]
      have hall : ∀ c : EqIdx n D m, eval z (eqFam D p c) = 0 := by
        rintro (u | i | ⟨i, a⟩ | l)
        · show eval z (eqUnit n D) = 0
          rw [eqUnit, map_sub, eval_X, map_one, hzt, monval_zero, sub_self]
        · show eval z (eqVar n D i) = 0
          rw [eqVar, map_sub, eval_X, eval_X, hzt, hzx, monval_mone x i hD1, sub_self]
        · show eval z (eqProd i a) = 0
          rw [eqProd]
          split
          · rename_i h
            rw [map_sub, map_mul, eval_X, eval_X, eval_X, hzt, hzt, hzt,
              monval_mincr x i a h, monval_mone x i hD1, sub_self]
          · simp
        · show eval z (eqLin D p l) = 0
          rw [eqLin, map_sum]
          have hterm : ∀ a : MonT n D, eval z (C (coeff (mexp a) (p l)) * X (tvar a))
              = coeff (mexp a) (p l) * monval x a := by
            intro a
            rw [map_mul, eval_C, eval_X, hzt]
          rw [Finset.sum_congr rfl fun a _ => hterm a,
            sum_monval_eq_eval (D := D) x (p l) (hsupp l)]
          exact hx l
      exact fun j => hall _
  · -- solutions descend
    intro z hz l
    have hz' : ∀ c : EqIdx n D m, eval z (eqFam D p c) = 0 := by
      intro c
      have := hz ((Fintype.equivFin (EqIdx n D m)) c)
      simpa using this
    set x : Fin n → ℝ := fun t => z (xvar n D t) with hxdef
    have hone : ∀ i : Fin n, z (tvar (mone (D := D) i)) = x i := by
      intro i
      have h : eval z (eqVar n D i) = 0 := hz' (Sum.inr (Sum.inl i))
      rw [eqVar, map_sub, eval_X, eval_X, sub_eq_zero] at h
      exact h
    have hzero : z (tvar (0 : MonT n D)) = 1 := by
      have h : eval z (eqUnit n D) = 0 := hz' (Sum.inl ())
      rw [eqUnit, map_sub, eval_X, map_one, sub_eq_zero] at h
      exact h
    have hprod : ∀ (i : Fin n) (a : MonT n D), (a i : ℕ) < D →
        z (tvar (mincr i a)) = x i * z (tvar a) := by
      intro i a h
      have h2 : eval z (eqProd i a) = 0 := hz' (Sum.inr (Sum.inr (Sum.inl (i, a))))
      rw [eqProd, if_pos h, map_sub, map_mul, eval_X, eval_X, eval_X, sub_eq_zero, hone] at h2
      exact h2
    have key : ∀ s : ℕ, ∀ a : MonT n D, (∑ j, (a j : ℕ)) = s → z (tvar a) = monval x a := by
      intro s
      induction s using Nat.strong_induction_on with
      | _ s ih =>
        intro a ha
        by_cases h0 : ∀ j, (a j : ℕ) = 0
        · have hzz : a = 0 := by
            funext j
            exact Fin.val_injective (by simp [h0 j])
          subst hzz
          rw [hzero, monval_zero]
        · obtain ⟨i, hi⟩ := not_forall.mp h0
          have hipos : 0 < (a i : ℕ) := Nat.pos_of_ne_zero hi
          set b : MonT n D := mdecr i a with hbdef
          have hbi : ((b i : Fin (D + 1)) : ℕ) = (a i : ℕ) - 1 := mdecr_val_self i a
          have hbilt : ((b i : Fin (D + 1)) : ℕ) < D := by
            have := (a i).isLt
            omega
          have hba : mincr i b = a := mincr_mdecr i a hipos
          have hsum : (∑ j, (b j : ℕ)) + 1 = ∑ j, (a j : ℕ) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
              ← Finset.add_sum_erase (f := fun j => ((a j : Fin (D + 1)) : ℕ)) _
                (Finset.mem_univ i)]
            have he : ∀ j ∈ (Finset.univ : Finset (Fin n)).erase i,
                ((b j : Fin (D + 1)) : ℕ) = ((a j : Fin (D + 1)) : ℕ) := by
              intro j hj
              exact mdecr_val_ne _ _ _ (Finset.ne_of_mem_erase hj)
            rw [Finset.sum_congr rfl he, hbi]
            omega
          have hlt : (∑ j, (b j : ℕ)) < s := by omega
          have hbeq := ih _ hlt b rfl
          calc z (tvar a) = z (tvar (mincr i b)) := by rw [hba]
            _ = x i * z (tvar b) := hprod i b hbilt
            _ = x i * monval x b := by rw [hbeq]
            _ = monval x (mincr i b) := (monval_mincr x i b hbilt).symm
            _ = monval x a := by rw [hba]
    have h2 : eval z (eqLin D p l) = 0 := hz' (Sum.inr (Sum.inr (Sum.inr l)))
    rw [eqLin, map_sum] at h2
    have h3 : ∀ a : MonT n D, eval z (C (coeff (mexp a) (p l)) * X (tvar a))
        = coeff (mexp a) (p l) * monval x a := by
      intro a
      rw [map_mul, eval_C, eval_X, key _ a rfl]
    rw [Finset.sum_congr rfl fun a _ => h3 a,
      sum_monval_eq_eval (D := D) x (p l) (hsupp l)] at h2
    exact h2

