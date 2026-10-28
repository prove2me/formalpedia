-- Prove2me | solution 1 for D1Bound5.pellMatchingCheck_no_three
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:38:51.677311+00:00
-- url     : https://prove2.me/submissions/4d152b06-4af6-415a-90e2-ecec61ca6c95

import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
import Theorems.Thm_D1Bound5_pellMatchingCheck_sound

section
namespace D1Bound5



































private theorem pell_signed_pair_abs_eq (d : ℤ) (hd : 0 < d)
    (ms : List PellSquareMasks) (hvalid : ∀ m ∈ ms, m.Valid d)
    (xs : List ℤ) (wss : List (List (ℕ × ℕ)))
    (hcheck : pellMatchingCheck ms xs wss = true)
    (hlarge : ∀ x ∈ xs, 2 ≤ x)
    (x y a b : ℤ) (hx : x ∈ xs) (hy : y ∈ xs)
    (ha : a = x ∨ a = -x) (hb : b = y ∨ b = -y)
    (hsq : PellIntegerSquare d (a*b+1)) : x = y := by
  by_contra hne
  obtain ⟨hnpos,hnneg⟩ := pellMatchingCheck_sound d ms hvalid xs wss hcheck x y hx hy hne
  have hx2 := hlarge x hx
  have hy2 := hlarge y hy
  have hxy : 0 < x*y-1 := by
    nlinarith [mul_nonneg (show 0 ≤ x-2 by omega) (show 0 ≤ y-2 by omega)]
  have hd0 : 0 ≤ d := hd.le
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hsq with ⟨r,hr⟩ | ⟨r,hr⟩
  · exact hnpos ⟨r,hr⟩
  · nlinarith [sq_nonneg r, mul_nonneg hd0 (sq_nonneg r)]
  · nlinarith [sq_nonneg r]
  · apply hnneg; exact ⟨r,by nlinarith [hr]⟩
  · nlinarith [sq_nonneg r]
  · apply hnneg; exact ⟨r,by nlinarith [hr]⟩
  · apply hnpos; exact ⟨r,by nlinarith [hr]⟩
  · nlinarith [sq_nonneg r, mul_nonneg hd0 (sq_nonneg r)]

/-- The graph certificate proves a matching, a stronger property than the
triangle exclusion needed by the article. No huge integer square roots are
trusted or executed by this checker. -/
theorem _root_.solution (d : ℤ) (hd : 0 < d)
    (ms : List PellSquareMasks) (hvalid : ∀ m ∈ ms, m.Valid d)
    (xs : List ℤ) (wss : List (List (ℕ × ℕ)))
    (hcheck : pellMatchingCheck ms xs wss = true)
    (hlarge : ∀ x ∈ xs, 2 ≤ x)
    (a b c : ℤ) (ha : PellSignedMember xs a) (hb : PellSignedMember xs b)
    (hc : PellSignedMember xs c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsab : PellIntegerSquare d (a*b+1))
    (hsac : PellIntegerSquare d (a*c+1)) : False := by
  obtain ⟨x,hx,hax⟩ := ha
  obtain ⟨y,hy,hby⟩ := hb
  obtain ⟨z,hz,hcz⟩ := hc
  have hxy := pell_signed_pair_abs_eq d hd ms hvalid xs wss hcheck hlarge
    x y a b hx hy hax hby hsab
  have hxz := pell_signed_pair_abs_eq d hd ms hvalid xs wss hcheck hlarge
    x z a c hx hz hax hcz hsac
  subst y; subst z
  rcases hax with rfl | rfl <;> rcases hby with rfl | rfl <;>
    rcases hcz with rfl | rfl <;> simp_all







end D1Bound5
end
