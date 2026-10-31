-- Prove2me | solution 1 for DiazModulus.vanishOrd_ideal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:04:01.33862+00:00
-- url     : https://prove2.me/submissions/e5651f14-5ed6-4f2b-83a3-b40b8cef7fa8

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_torusDeriv_mem_torusBox

open Complex ComplexConjugate

/-! # Vanishing to order `> t` along `W` is an ideal

Write `S_n = {Q | D_l Q ∈ J for every list l in W of length ≤ n}`, so `vanishOrd J W t = S_t`. It is a `K`-subspace
since every `D_l` is linear. Stability under multiplication, `Q ∈ S_n ⇒ rQ ∈ S_n` for all `r`, goes by induction on
`n`, for all `Q` and `r` at once. For `n = 0` it says `J` is an ideal. For `n + 1`, write a nonempty list as
`l = L ++ [b]`, so `D_l = D_L ∘ D_b` and `D_b (rQ) = r D_b Q + Q D_b r` (Leibniz). Now `D_b Q ∈ S_n` (as
`D_{L'} D_b Q = D_{L' ++ [b]} Q`) and `Q ∈ S_n`, so the induction hypothesis puts `r D_b Q` and `(D_b r) Q` in `S_n`,
and `D_L` sends both into `J`. Finally, if `J₀ ≤ J` then `J₀ ≤ S_t`, because every `D_w` maps `J₀` into itself (the
imported node `torusDeriv_mem_torusBox`, second part), hence so does every `D_l`. -/

namespace C13_O6
open DiazModulus MvPolynomial

theorem torusDerivList_cons {K A₀ A₁ : Type*} [Field K] (w : (A₀ → K) × (A₁ → K))
    (l : List ((A₀ → K) × (A₁ → K))) (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :
    torusDerivList (w :: l) f = torusDeriv w (torusDerivList l f) := by
  simp [torusDerivList, List.map_cons, List.prod_cons, Module.End.mul_apply]

theorem torusDerivList_concat {K A₀ A₁ : Type*} [Field K] (w : (A₀ → K) × (A₁ → K))
    (l : List ((A₀ → K) × (A₁ → K))) (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :
    torusDerivList (l ++ [w]) f = torusDerivList l (torusDeriv w f) := by
  simp [torusDerivList, List.map_append, List.prod_append, Module.End.mul_apply]

theorem mul_mem_aux {K A₀ A₁ : Type*} [Field K] (J : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K))
    (W : Submodule K ((A₀ → K) × (A₁ → K))) (n : ℕ) :
    ∀ Q ∈ vanishOrd J W n, ∀ r, r * Q ∈ vanishOrd J W n := by
  induction n with
  | zero =>
    intro Q hQ r l hl _
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hl0
    have := hQ [] le_rfl (by simp)
    simp only [torusDerivList_nil, Module.End.one_apply] at this ⊢
    exact J.mul_mem_left r this
  | succ n ih =>
    intro Q hQ r l hl hW
    rcases l.eq_nil_or_concat with rfl | ⟨L, b, rfl⟩
    · have := hQ [] (Nat.zero_le _) (by simp)
      simp only [torusDerivList_nil, Module.End.one_apply] at this ⊢
      exact J.mul_mem_left r this
    · have hb : b ∈ W := hW b (by simp)
      have hLW : ∀ w ∈ L, w ∈ W := fun w hw => hW w (by simp [hw])
      have hL : L.length ≤ n := by simp at hl; omega
      have hDQ : torusDeriv b Q ∈ vanishOrd J W n := by
        intro L' hL' hL'W
        rw [← torusDerivList_concat]
        exact hQ _ (by simp; omega) (fun w hw => by
          rcases List.mem_append.mp hw with h | h
          · exact hL'W w h
          · simp at h; exact h ▸ hb)
      have hQn : Q ∈ vanishOrd J W n := fun L' hL' hL'W => hQ L' (by omega) hL'W
      rw [List.concat_eq_append, torusDerivList_concat, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, mul_comm Q]
      exact J.add_mem (ih _ hDQ r L hL hLW) (ih _ hQn _ L hL hLW)

theorem torusDerivList_mem_torusIdeal {K A₀ A₁ : Type*} [Field K] (Q : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)
    (hQ : Q ∈ torusIdeal K A₀ A₁) (l : List ((A₀ → K) × (A₁ → K))) :
    torusDerivList l Q ∈ torusIdeal K A₀ A₁ := by
  induction l with
  | nil => simpa using hQ
  | cons w l ih => rw [torusDerivList_cons]; exact (DiazModulus.torusDeriv_mem_torusBox w).2 _ ih

end C13_O6

open DiazModulus C13_O6 in
theorem solution {K A₀ A₁ : Type*} [Field K] (J : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K))
    (W : Submodule K ((A₀ → K) × (A₁ → K))) (t : ℕ) :
    ∃ I : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K), (I : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)) = vanishOrd J W t ∧
      (torusIdeal K A₀ A₁ ≤ J → torusIdeal K A₀ A₁ ≤ I) := by
  let I : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :=
    { carrier := vanishOrd J W t
      add_mem' := fun {a b} ha hb l hl hW => by rw [map_add]; exact J.add_mem (ha l hl hW) (hb l hl hW)
      zero_mem' := fun l _ _ => by rw [map_zero]; exact J.zero_mem
      smul_mem' := fun c x hx => by rw [smul_eq_mul]; exact mul_mem_aux J W t x hx c }
  exact ⟨I, rfl, fun hJ Q hQ l _ _ => hJ (torusDerivList_mem_torusIdeal Q hQ l)⟩
