-- Prove2me | solution 1 for ConsModCount.carbonnel_minority_term
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-09T17:21:33.846538+00:00
-- url     : https://prove2.me/submissions/2dc3d00a-ac98-4770-a68e-a581c402b2af

import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount
namespace CMT

/-- The minority term `t(x, y, z) = h(x, h(y, h(y, x, z), z), h(y, x, z))`. -/
def tC : Term3 :=
  Term3.app (Term3.var 0)
    (Term3.app (Term3.var 1) (Term3.app (Term3.var 1) (Term3.var 0) (Term3.var 2)) (Term3.var 2))
    (Term3.app (Term3.var 1) (Term3.var 0) (Term3.var 2))

theorem tC_eval {D : Type} (h : D → D → D → D) (x y z : D) :
    tC.eval h x y z = h x (h y (h y x z) z) (h y x z) := by
  simp [tC, Term3.eval]

/-- Term operations of a conservative operation are conservative. -/
theorem eval_conservative {D : Type} (h : D → D → D → D) (hc : IsConservativeOp h) :
    ∀ t : Term3, IsConservativeOp (t.eval h)
  | Term3.var i => by
      intro x y z
      fin_cases i <;> simp [Term3.eval]
  | Term3.app a b c => by
      intro x y z
      have ha := eval_conservative h hc a x y z
      have hb := eval_conservative h hc b x y z
      have hcc := eval_conservative h hc c x y z
      simp only [Term3.eval]
      rcases hc (a.eval h x y z) (b.eval h x y z) (c.eval h x y z) with e | e | e <;> rw [e]
      · exact ha
      · exact hb
      · exact hcc

/-- Term operations preserve every relation preserved by the basic operation. -/
theorem eval_preserves {D : Type} (h : D → D → D → D) {m : ℕ} (R : Set (Fin m → D))
    (hR : Preserves (ternary h) R) : ∀ t : Term3, Preserves (ternary (t.eval h)) R
  | Term3.var i => by
      intro tt htt
      have : (fun j => ternary (Term3.eval h (Term3.var i)) (fun l => tt l j)) = tt i := by
        funext j
        fin_cases i <;> simp [ternary, Term3.eval]
      rw [this]
      exact htt i
  | Term3.app a b c => by
      intro tt htt
      have hA := eval_preserves h R hR a tt htt
      have hB := eval_preserves h R hR b tt htt
      have hC := eval_preserves h R hR c tt htt
      let A : Fin m → D := fun j => ternary (a.eval h) (fun l => tt l j)
      let B : Fin m → D := fun j => ternary (b.eval h) (fun l => tt l j)
      let C : Fin m → D := fun j => ternary (c.eval h) (fun l => tt l j)
      have hrows : ∀ l, (![A, B, C] : Fin 3 → Fin m → D) l ∈ R := by
        intro l; fin_cases l
        · exact hA
        · exact hB
        · exact hC
      have := hR ![A, B, C] hrows
      convert this using 1
      funext j
      simp [ternary, Term3.eval, A, B, C]

theorem cmt_main {D : Type} [Fintype D] (h : D → D → D → D)
    (hM : IsMaltsev h) (hc : IsConservativeOp h) :
    ∃ t : Term3, IsMinority (t.eval h) ∧ IsConservativeOp (t.eval h) ∧
      ∀ H : Template D, IsPolymorphism H (ternary h) → IsPolymorphism H (ternary (t.eval h)) := by
  refine ⟨tC, ?_, eval_conservative h hc tC, fun H hH i => eval_preserves h _ (hH i) tC⟩
  intro x y
  have m1 : ∀ a b : D, h a b b = a := fun a b => (hM a b).1
  have m2 : ∀ a b : D, h b b a = a := fun a b => (hM a b).2
  refine ⟨?_, ?_, ?_⟩
  · -- t(x,x,y) = h x (h x (h x x y) y) (h x x y) = y
    rw [tC_eval, m2, m1, m2]
  · -- t(x,y,x) = h x (h y (h y x x) x) (h y x x) = y
    rw [tC_eval, m1, m2, m2]
  · -- t(y,x,x) = h y (h x (h x y x) x) (h x y x) = y, by cases on h x y x ∈ {x, y}
    rw [tC_eval]
    have hu : h x y x = x ∨ h x y x = y := by
      rcases hc x y x with e | e | e
      · exact Or.inl e
      · exact Or.inr e
      · exact Or.inl e
    rcases hu with e | e
    · rw [e, m1, m1]
    · rw [e, e, m1]

end CMT
end ConsModCount

open ConsModCount in
theorem solution {D : Type} [Fintype D] (h : D → D → D → D)
    (hM : IsMaltsev h) (hc : IsConservativeOp h) :
    ∃ t : Term3, IsMinority (t.eval h) ∧ IsConservativeOp (t.eval h) ∧
      ∀ H : Template D, IsPolymorphism H (ternary h) → IsPolymorphism H (ternary (t.eval h)) :=
  ConsModCount.CMT.cmt_main h hM hc
