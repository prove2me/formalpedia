-- Prove2me | solution 1 for BregmanPPA.ProxMult.saddle_iff_zero
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T23:28:21.163261+00:00
-- url     : https://prove2.me/submissions/4c40a2b6-ec5f-4cd2-b739-c17cbf04266e

import Definitions.Def_BregmanPPA_ProxMult_Saddle
set_option autoImplicit false
section
set_option autoImplicit false
open InertialFB.IFB ThreeOpSplitting.Convergence BregmanPPA.IneqMult BregmanPPA.ProxMult
namespace BregmanProxMultCodex

theorem saddle_value_finite {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x : E n) (p : E m) (hs : IsSaddlePair C f g x p) :
    lagr C f g x p ≠ ⊤ ∧ lagr C f g x p ≠ ⊥ := by
  classical
  obtain ⟨y,hy⟩ := hP.nonempty
  have hz : (0 : E m) ∈ nonnegOrthant m := by simp [nonnegOrthant]
  have hyt : lagr C f g y p ≠ ⊤ := by
    by_cases hp : p ∈ nonnegOrthant m
    · simp only [lagr,if_pos hy,if_pos hp]
      exact EReal.add_ne_top (hP.f_finite y hy) (EReal.coe_ne_top _)
    · simp [lagr,hy,hp]
  have ht : lagr C f g x p ≠ ⊤ := by
    intro he
    have hi := (hs y p).2
    rw [he] at hi
    exact hyt (top_le_iff.mp hi)
  have hx : x ∈ C := by
    by_contra hn
    exact ht (by simp [lagr,hn])
  have hxb : lagr C f g x (0 : E m) ≠ ⊥ := by
    simpa [lagr,hx,hz] using hP.f_proper.1 x
  have hb : lagr C f g x p ≠ ⊥ := by
    intro he
    have hi := (hs x 0).1
    rw [he] at hi
    exact hxb (le_bot_iff.mp hi)
  exact ⟨ht,hb⟩

theorem original_saddle_iff_zero {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x : E n) (p : E m) :
    IsSaddlePair C f g x p ↔ pair x p ∈ zer (opK C f g) := by
  change IsSaddlePair C f g x p ↔
    IsSubgradient (fun y => lagr C f g y p) x 0 ∧
    IsSubgradient (fun q => -lagr C f g x q) p (-(-0))
  simp only [neg_zero]
  constructor
  · intro hs
    obtain ⟨ht,hb⟩ := saddle_value_finite C f g hP x p hs
    refine ⟨⟨ht,?_⟩,⟨?_,?_⟩⟩
    · intro y
      simpa using (hs y p).2
    · exact fun he => hb (EReal.neg_eq_top_iff.mp he)
    · intro q
      simpa using EReal.neg_le_neg_iff.mpr ((hs x q).1)
  · rintro ⟨⟨ht,hmin⟩,⟨hb,hmax⟩⟩ y q
    refine ⟨?_,?_⟩
    · have hi := hmax q
      simpa using hi
    · simpa using hmin y
end BregmanProxMultCodex

end

set_option autoImplicit false
open BregmanPPA.IneqMult BregmanPPA.ProxMult ThreeOpSplitting.Convergence

theorem solution {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x' : E n) (p' : E m) :
    IsSaddlePair C f g x' p' ↔ pair x' p' ∈ zer (opK C f g) :=
  BregmanProxMultCodex.original_saddle_iff_zero C f g hP x' p'

#print axioms solution
