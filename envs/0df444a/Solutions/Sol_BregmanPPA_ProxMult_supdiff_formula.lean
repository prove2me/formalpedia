-- Prove2me | solution 1 for BregmanPPA.ProxMult.supdiff_formula
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T23:37:44.20062+00:00
-- url     : https://prove2.me/submissions/890ad48b-f322-43c4-a7b3-b0c1cab29f3a

import Definitions.Def_BregmanPPA_ProxMult_Saddle
set_option autoImplicit false
section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult
namespace BregmanProxMultCodex

theorem indicator_support {m : ℕ} (p u : E m) (hp : p ∈ nonnegOrthant m) :
    IsSubgradient (indicatorPos m) p u ↔
      ∀ q ∈ nonnegOrthant m, inner ℝ u (q-p) ≤ 0 := by
  classical
  constructor
  · rintro ⟨_,h⟩ q hq
    simpa [indicatorPos,hp,hq] using h q
  · intro h
    refine ⟨by simp [indicatorPos,hp],?_⟩
    intro q
    by_cases hq : q ∈ nonnegOrthant m
    · simpa [indicatorPos,hp,hq] using h q hq
    · simp [indicatorPos,hp,hq]

theorem lagr_finite_rep {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x : E n) (hx : x ∈ C) (q : E m) (hq : q ∈ nonnegOrthant m) :
    lagr C f g x q = ((f x).toReal + inner ℝ q (gvec g x) : ℝ) := by
  classical
  simp only [lagr,if_pos hx,if_pos hq]
  rw [← EReal.coe_toReal (hP.f_finite x hx) (hP.f_proper.1 x),← EReal.coe_add]
  congr 1
  simp [PiLp.inner_apply,gvec,mul_comm]

theorem super_support {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x : E n) (hx : x ∈ C) (p v : E m) (hp : p ∈ nonnegOrthant m) :
    v ∈ supdiffP C f g x p ↔
      ∀ q ∈ nonnegOrthant m, inner ℝ (gvec g x-v) (q-p) ≤ 0 := by
  classical
  constructor
  · rintro ⟨_,hs⟩ q hq
    have hi := hs q
    dsimp only at hi
    rw [lagr_finite_rep C f g hP x hx p hp,lagr_finite_rep C f g hP x hx q hq] at hi
    have hr : -((f x).toReal+inner ℝ p (gvec g x))+
        inner ℝ (-v) (q-p) ≤ -((f x).toReal+inner ℝ q (gvec g x)) := by
      simpa only [← EReal.coe_neg,← EReal.coe_add,EReal.coe_le_coe_iff] using hi
    rw [inner_sub_left,inner_sub_right,real_inner_comm q (gvec g x),
      real_inner_comm p (gvec g x)]
    rw [inner_neg_left] at hr
    linarith
  · intro hs
    change IsSubgradient (fun q => -lagr C f g x q) p (-v)
    refine ⟨?_,?_⟩
    · change -lagr C f g x p ≠ ⊤
      rw [lagr_finite_rep C f g hP x hx p hp,← EReal.coe_neg]
      exact EReal.coe_ne_top _
    · intro q
      dsimp only
      by_cases hq : q ∈ nonnegOrthant m
      · rw [lagr_finite_rep C f g hP x hx p hp,lagr_finite_rep C f g hP x hx q hq]
        have hr := hs q hq
        rw [inner_sub_left,inner_sub_right,real_inner_comm q (gvec g x),
          real_inner_comm p (gvec g x)] at hr
        simp only [← EReal.coe_neg,← EReal.coe_add,EReal.coe_le_coe_iff,inner_neg_left]
        linarith
      · simp [lagr,hx,hq]
end BregmanProxMultCodex

namespace BregmanProxMultCodex

theorem original_supdiff_formula {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g) :
    ∀ x ∈ C, ∀ p ∈ nonnegOrthant m,
      supdiffP C f g x p =
        {v | ∃ u ∈ BregmanPPA.Convergence.subdiffOp (indicatorPos m) p,
          v = gvec g x-u} := by
  intro x hx p hp
  ext v
  change v ∈ supdiffP C f g x p ↔
    ∃ u, IsSubgradient (indicatorPos m) p u ∧ v = gvec g x-u
  rw [super_support C f g hP x hx p v hp]
  constructor
  · intro hs
    exact ⟨gvec g x-v,(indicator_support p (gvec g x-v) hp).mpr hs,by abel⟩
  · rintro ⟨u,hu,hv⟩ q hq
    have he : gvec g x-v=u := by rw [hv]; abel
    rw [he]
    exact (indicator_support p u hp).mp hu q hq
end BregmanProxMultCodex

end

set_option autoImplicit false
open InertialFB.IFB BregmanPPA.ProxMult
theorem solution {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g) :
    ∀ x ∈ C, ∀ p ∈ BregmanPPA.IneqMult.nonnegOrthant m,
      supdiffP C f g x p = {v | ∃ u ∈ BregmanPPA.Convergence.subdiffOp (BregmanPPA.IneqMult.indicatorPos m) p, v = BregmanPPA.IneqMult.gvec g x - u} := BregmanProxMultCodex.original_supdiff_formula C f g hP

#print axioms solution
