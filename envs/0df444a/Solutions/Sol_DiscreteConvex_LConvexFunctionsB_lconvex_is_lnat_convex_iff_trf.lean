-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.lconvex_is_lnat_convex_iff_trf
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:49:29.36062+00:00
-- url     : https://prove2.me/submissions/db5b7b91-1b9e-44bf-825b-bdbd8679dff0

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex

open Classical
open scoped Pointwise
open DiscreteConvex.LConvexFunctionsB

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma add_coe_inj {a b : WithTop ℝ} {r : ℝ}
    (h : a + (r : WithTop ℝ) = b + (r : WithTop ℝ)) : a = b := by
  cases a <;> cases b <;> simp [← WithTop.coe_add] at h ⊢
  exact h

private lemma trf_shift {g : (V → ℤ) → WithTop ℝ} {r : ℝ}
    (hr : ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ))
    (k : ℤ) (p : V → ℤ) :
    g (fun v => p v + k) = g p + (((k : ℝ) * r : ℝ) : WithTop ℝ) := by
  induction k using Int.induction_on with
  | zero =>
    simp
  | succ i ih =>
    have h1 : (fun v => p v + ((i : ℤ) + 1)) = (fun v => p v + (i : ℤ)) + 1 := by
      ext v; simp [Pi.add_apply, add_assoc]
    rw [h1, hr, ih, add_assoc, ← WithTop.coe_add]
    congr 2
    push_cast
    ring
  | pred i ih =>
    apply add_coe_inj (r := r)
    have h1 := hr (fun v => p v + (-(i : ℤ) - 1))
    have h2 : (fun v => p v + (-(i : ℤ) - 1)) + 1 = (fun v => p v + (-(i : ℤ))) := by
      ext v; simp [Pi.add_apply]; ring
    rw [h2, ih] at h1
    rw [← h1, add_assoc, ← WithTop.coe_add]
    congr 2
    push_cast
    ring

theorem solution (g : (V → ℤ) → WithTop ℝ) :
    ((SBF g ∧ TRF g) → LNaturalConvex g) ∧
    (LNaturalConvex g → (TRF g → SBF g)) := by
  constructor
  · rintro ⟨hSBF, r, hr⟩
    constructor
    · intro x y
      unfold LiftedFunctionL
      have hx : g (fun v => x (some v) - x none) =
          g (fun v => x (some v)) + (((-(x none : ℝ)) * r : ℝ) : WithTop ℝ) := by
        simpa [sub_eq_add_neg] using trf_shift hr (-x none) (fun v => x (some v))
      have hy : g (fun v => y (some v) - y none) =
          g (fun v => y (some v)) + (((-(y none : ℝ)) * r : ℝ) : WithTop ℝ) := by
        simpa [sub_eq_add_neg] using trf_shift hr (-y none) (fun v => y (some v))
      have hsup : g (fun v => (x ⊔ y) (some v) - (x ⊔ y) none) =
          g ((fun v => x (some v)) ⊔ (fun v => y (some v))) +
            (((-((x ⊔ y) none : ℝ)) * r : ℝ) : WithTop ℝ) := by
        have h0 := trf_shift hr (-(x ⊔ y) none) (fun v => (x ⊔ y) (some v))
        have h1 : (fun v => (x ⊔ y) (some v) + -(x ⊔ y) none) =
            (fun v => (x ⊔ y) (some v) - (x ⊔ y) none) := by
          ext v; ring
        have h2 : (fun v => (x ⊔ y) (some v)) = (fun v => x (some v)) ⊔ (fun v => y (some v)) := rfl
        rw [h1, h2] at h0
        simpa using h0
      have hinf : g (fun v => (x ⊓ y) (some v) - (x ⊓ y) none) =
          g ((fun v => x (some v)) ⊓ (fun v => y (some v))) +
            (((-((x ⊓ y) none : ℝ)) * r : ℝ) : WithTop ℝ) := by
        have h0 := trf_shift hr (-(x ⊓ y) none) (fun v => (x ⊓ y) (some v))
        have h1 : (fun v => (x ⊓ y) (some v) + -(x ⊓ y) none) =
            (fun v => (x ⊓ y) (some v) - (x ⊓ y) none) := by
          ext v; ring
        have h2 : (fun v => (x ⊓ y) (some v)) = (fun v => x (some v)) ⊓ (fun v => y (some v)) := rfl
        rw [h1, h2] at h0
        simpa using h0
      rw [hx, hy, hsup, hinf]
      have hadd_lhs :
          (g (fun v => x (some v)) + (((-(x none : ℝ)) * r : ℝ) : WithTop ℝ)) +
          (g (fun v => y (some v)) + (((-(y none : ℝ)) * r : ℝ) : WithTop ℝ)) =
          (g (fun v => x (some v)) + g (fun v => y (some v))) +
          (((-(x none : ℝ)) * r + (-(y none : ℝ)) * r : ℝ) : WithTop ℝ) := by
        rw [WithTop.coe_add]
        ac_rfl
      have hadd_rhs :
          (g ((fun v => x (some v)) ⊔ (fun v => y (some v))) +
            (((-((x ⊔ y) none : ℝ)) * r : ℝ) : WithTop ℝ)) +
          (g ((fun v => x (some v)) ⊓ (fun v => y (some v))) +
            (((-((x ⊓ y) none : ℝ)) * r : ℝ) : WithTop ℝ)) =
          (g ((fun v => x (some v)) ⊔ (fun v => y (some v))) +
            g ((fun v => x (some v)) ⊓ (fun v => y (some v)))) +
          (((-((x ⊔ y) none : ℝ)) * r + (-((x ⊓ y) none : ℝ)) * r : ℝ) : WithTop ℝ) := by
        rw [WithTop.coe_add]
        ac_rfl
      rw [hadd_lhs, hadd_rhs]
      have hnone :
          ((-(x none : ℝ)) * r + (-(y none : ℝ)) * r : ℝ) =
          ((-((x ⊔ y) none : ℝ)) * r + (-((x ⊓ y) none : ℝ)) * r : ℝ) := by
        have hmm : ((x ⊔ y) none : ℤ) + ((x ⊓ y) none : ℤ) = x none + y none :=
          max_add_min (x none) (y none)
        have hmmR : (((x ⊔ y) none : ℝ) + ((x ⊓ y) none : ℝ)) =
            (x none : ℝ) + (y none : ℝ) := by
          exact_mod_cast hmm
        calc (-(x none : ℝ)) * r + (-(y none : ℝ)) * r
          _ = -((x none : ℝ) + (y none : ℝ)) * r := by ring
          _ = -(((x ⊔ y) none : ℝ) + ((x ⊓ y) none : ℝ)) * r := by rw [hmmR]
          _ = (-((x ⊔ y) none : ℝ)) * r + (-((x ⊓ y) none : ℝ)) * r := by ring
      rw [hnone]
      exact add_le_add (hSBF (fun v => x (some v)) (fun v => y (some v))) le_rfl
    · refine ⟨0, fun x => ?_⟩
      unfold LiftedFunctionL
      have h1 : (fun v => (x + 1) (some v) - (x + 1) none) = (fun v => x (some v) - x none) := by
        ext v
        simp [Pi.add_apply]
      rw [h1]
      simp
  · rintro ⟨hSBF, _⟩ _ p q
    have h := hSBF (fun o => Option.elim o 0 p) (fun o => Option.elim o 0 q)
    unfold LiftedFunctionL at h
    have hp : (fun v => Option.elim (some v) 0 p - Option.elim (none : Option V) 0 p) = p := by
      ext v; simp
    have hq : (fun v => Option.elim (some v) 0 q - Option.elim (none : Option V) 0 q) = q := by
      ext v; simp
    have hsup : (fun v => ((fun o => Option.elim o 0 p) ⊔ (fun o => Option.elim o 0 q)) (some v) -
        ((fun o => Option.elim o 0 p) ⊔ (fun o => Option.elim o 0 q)) none) = p ⊔ q := by
      ext v; simp [Pi.sup_apply]
    have hinf : (fun v => ((fun o => Option.elim o 0 p) ⊓ (fun o => Option.elim o 0 q)) (some v) -
        ((fun o => Option.elim o 0 p) ⊓ (fun o => Option.elim o 0 q)) none) = p ⊓ q := by
      ext v; simp [Pi.inf_apply]
    rw [hp, hq, hsup, hinf] at h
    exact h
