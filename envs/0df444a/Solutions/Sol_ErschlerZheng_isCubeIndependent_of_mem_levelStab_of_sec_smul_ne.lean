-- Prove2me | solution 1 for ErschlerZheng.isCubeIndependent_of_mem_levelStab_of_sec_smul_ne
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T02:11:08.052471+00:00
-- url     : https://prove2.me/submissions/e6a83f06-f901-4b22-a699-8d60b5c7a837

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

/-! ### The root swap -/

/-- Whether `g` swaps the two vertices of level 1. -/
def rootSwap (g : BinaryTreeAut) : Bool := decide ([false] <• g = [true])

theorem singleton_smul (g : BinaryTreeAut) (x : Bool) :
    [x] <• g = [xor x (rootSwap g)] := by
  have hlen : ∀ y : Bool, ([y] <• g).length = 1 := fun y => length_vertex_smul g [y]
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp (hlen false)
  obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp (hlen true)
  have hne : p ≠ q := by
    intro e
    have : [false] <• g = [true] <• g := by rw [hp, hq, e]
    have := congrArg (fun v => v <• g⁻¹) this
    simp only [vertex_smul_smul_inv] at this
    simp at this
  unfold rootSwap
  cases x
  · rw [hp]
    cases p <;> simp
  · rw [hq, hp]
    cases p <;> cases q <;> simp_all

theorem cons_smul (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    (x :: u) <• g = xor x (rootSwap g) :: (u <• sec g [x]) := by
  have := append_vertex_smul g [x] u
  rw [singleton_smul] at this
  exact this

/-! ### `a` and the generators -/

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Rays: prefixes, shifts, and the action of sections
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace RayBasic

open GrigBasic

theorem ray_ext {x y : Ray} (h : ∀ n, rayPrefix x n = rayPrefix y n) : x = y := by
  funext i
  have hx : i < (rayPrefix x (i + 1)).length := by simp [length_rayPrefix]
  rw [← getElem_rayPrefix x (i + 1) i hx, List.getElem_of_eq (h (i + 1)), getElem_rayPrefix]

theorem rayPrefix_succ (x : Ray) (n : ℕ) :
    rayPrefix x (n + 1) = x 0 :: rayPrefix (shiftRay x 1) n := by
  simp [rayPrefix, List.ofFn_succ, shiftRay]

theorem rayPrefix_add (x : Ray) (n m : ℕ) :
    rayPrefix x (n + m) = rayPrefix x n ++ rayPrefix (shiftRay x n) m := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    by_cases hi : i < n
    · rw [List.getElem_append_left (by rw [length_rayPrefix]; exact hi), getElem_rayPrefix]
    · rw [List.getElem_append_right (by rw [length_rayPrefix]; omega), getElem_rayPrefix]
      simp only [shiftRay, length_rayPrefix]
      congr 1
      omega

theorem shiftRay_smul (g : BinaryTreeAut) (x : Ray) (n : ℕ) :
    shiftRay (x <• g) n = shiftRay x n <• sec g (rayPrefix x n) := by
  apply ray_ext
  intro m
  have h1 : rayPrefix (x <• g) (n + m) =
      (rayPrefix x n <• g) ++ (rayPrefix (shiftRay x n) m <• sec g (rayPrefix x n)) := by
    rw [rayPrefix_smul, rayPrefix_add, append_vertex_smul]
  have h2 : rayPrefix (x <• g) (n + m) =
      rayPrefix (x <• g) n ++ rayPrefix (shiftRay (x <• g) n) m := rayPrefix_add _ _ _
  rw [h2, rayPrefix_smul] at h1
  rw [rayPrefix_smul]
  exact List.append_cancel_left h1

theorem smul_zero (g : BinaryTreeAut) (x : Ray) : (x <• g) 0 = xor (x 0) (rootSwap g) := by
  have h := rayPrefix_smul g x 1
  rw [rayPrefix_succ, rayPrefix_succ] at h
  have h2 : rayPrefix (shiftRay x 1) 0 = [] := by simp [rayPrefix]
  rw [h2, cons_smul] at h
  have := congrArg List.head? h
  simpa using this

theorem one_smul_ray (x : Ray) : x <• (1 : BinaryTreeAut) = x := one_smul _ x

end RayBasic

end ErschlerZheng
end

section
/-!
# A13b: Lemma 5.6 on the binary tree (p. 27)

`g_j` fixes the first `j` digits and flips digit `j` (Lean index): its sections at level `j` swap.
In `x·g_n^{ε_n} ⋯ g_1^{ε_1}` the last factor `g_1^{ε_1}` is the only one that moves digit `1`, so
`ε_1` is read off digit `1`; cancel it and continue with `g_2, …` (the statement holds for every
ray `x`, not only on the orbit of `1^∞`).
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace CubeDev

open GrigBasic RayBasic

/-- `h` fixes every vertex of level `j`. -/
def FixLevel (j : ℕ) (h : BinaryTreeAut) : Prop := ∀ v : List Bool, v.length = j → v <• h = v

theorem FixLevel.mono {j m : ℕ} {h : BinaryTreeAut} (hh : FixLevel m h) (hjm : j ≤ m) :
    FixLevel j h := by
  intro v hv
  set u := v ++ List.replicate (m - j) true
  have hu : u.length = m := by simp [u, hv]; omega
  have hp : v <• h <+: u <• h := (vertex_smul_prefix_iff h v u).2 (List.prefix_append _ _)
  rw [hh u hu, List.prefix_iff_eq_take, length_vertex_smul] at hp
  rw [hp]
  simp [u]

theorem FixLevel.mul {j : ℕ} {g h : BinaryTreeAut} (hg : FixLevel j g) (hh : FixLevel j h) :
    FixLevel j (g * h) := by
  intro v hv; rw [vertex_smul_mul, hg v hv, hh v hv]

theorem FixLevel.one (j : ℕ) : FixLevel j 1 := fun v _ => one_smul _ v

theorem FixLevel.pow {j : ℕ} {h : BinaryTreeAut} (hh : FixLevel j h) (e : ℕ) :
    FixLevel j (h ^ e) := by
  induction e with
  | zero => exact FixLevel.one j
  | succ e ih => rw [pow_succ]; exact ih.mul hh

theorem FixLevel.digit {j : ℕ} {h : BinaryTreeAut} (hh : FixLevel j h) (x : Ray) (i : ℕ)
    (hi : i < j) : (x <• h) i = x i := by
  have e : rayPrefix (x <• h) j = rayPrefix x j := by
    rw [rayPrefix_smul]; exact hh _ (length_rayPrefix x j)
  have h1 : i < (rayPrefix (x <• h) j).length := by rw [length_rayPrefix]; exact hi
  rw [← getElem_rayPrefix (x <• h) j i h1, List.getElem_of_eq e, getElem_rayPrefix]

theorem flip_digit {j : ℕ} {h : BinaryTreeAut} (_hh : FixLevel j h)
    (hs : ∀ v : List Bool, v.length = j → rootSwap (sec h v) = true) (x : Ray) :
    (x <• h) j = !x j := by
  have := congrFun (shiftRay_smul h x j) 0
  simp only [shiftRay, zero_add] at this
  rw [this, smul_zero, hs _ (length_rayPrefix x j)]
  simp [shiftRay]

/-- `g_{a+n}^{ε_{a+n}} ⋯ g_{a+1}^{ε_{a+1}}`. -/
def F (g : ℕ → BinaryTreeAut) (a n : ℕ) (ε : ℕ → ℕ) : BinaryTreeAut :=
  ((List.range n).reverse.map fun i => g (a + i + 1) ^ ε (a + i + 1)).prod

theorem F_succ (g : ℕ → BinaryTreeAut) (a n : ℕ) (ε : ℕ → ℕ) :
    F g a (n + 1) ε = F g (a + 1) n ε * g (a + 1) ^ ε (a + 1) := by
  unfold F
  rw [List.range_succ_eq_map, List.reverse_cons, List.map_append, List.prod_append,
    List.map_reverse, List.map_map, List.map_reverse]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, add_zero]
  congr 3
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [show a + (i + 1) + 1 = a + 1 + i + 1 by omega]

theorem F_fix (g : ℕ → BinaryTreeAut) (hfix : ∀ n, 1 ≤ n → FixLevel n (g n)) (a n : ℕ)
    (ε : ℕ → ℕ) : FixLevel (a + 1) (F g a n ε) := by
  unfold F
  induction n with
  | zero => exact FixLevel.one _
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.map_append, List.prod_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact ((hfix _ (by omega)).pow _ |>.mono (by omega)).mul ih

theorem core (g : ℕ → BinaryTreeAut) (hfix : ∀ n, 1 ≤ n → FixLevel n (g n))
    (hswap : ∀ n, 1 ≤ n → ∀ v : List Bool, v.length = n → rootSwap (sec (g n) v) = true) :
    ∀ (n a : ℕ) (x : Ray) (ε ε' : ℕ → ℕ), (∀ j, a < j → j ≤ a + n → ε j ≤ 1 ∧ ε' j ≤ 1) →
      x <• F g a n ε = x <• F g a n ε' → ∀ j, a < j → j ≤ a + n → ε j = ε' j := by
  intro n
  induction n with
  | zero => intro a x ε ε' _ _ j h1 h2; omega
  | succ n ih =>
    intro a x ε ε' hb he j hj1 hj2
    rw [F_succ, F_succ, MulOpposite.op_mul, MulOpposite.op_mul, mul_smul, mul_smul] at he
    set z := x <• F g (a + 1) n ε
    set z' := x <• F g (a + 1) n ε'
    have hz : z (a + 1) = x (a + 1) := (F_fix g hfix (a + 1) n ε).digit x (a + 1) (by omega)
    have hz' : z' (a + 1) = x (a + 1) := (F_fix g hfix (a + 1) n ε').digit x (a + 1) (by omega)
    have hdig : ∀ (w : Ray) (e : ℕ), e ≤ 1 →
        (w <• g (a + 1) ^ e) (a + 1) = if e = 0 then w (a + 1) else !w (a + 1) := by
      intro w e he1
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he1 with rfl | rfl
      · simp [one_smul_ray]
      · simp only [pow_one, one_ne_zero, if_false]
        exact flip_digit (hfix _ (by omega)) (hswap _ (by omega)) w
    have ha : ε (a + 1) = ε' (a + 1) := by
      have h1 := congrFun he (a + 1)
      change (z <• g (a + 1) ^ ε (a + 1)) (a + 1) = (z' <• g (a + 1) ^ ε' (a + 1)) (a + 1) at h1
      rw [hdig z _ (hb (a + 1) (by omega) (by omega)).1,
        hdig z' _ (hb (a + 1) (by omega) (by omega)).2, hz, hz'] at h1
      have b1 := (hb (a + 1) (by omega) (by omega)).1
      have b2 := (hb (a + 1) (by omega) (by omega)).2
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b1 with e1 | e1 <;>
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b2 with e2 | e2 <;>
        rw [e1, e2] at h1 ⊢ <;> simp at h1 ⊢
    rcases (show j = a + 1 ∨ a + 1 < j by omega) with rfl | hj
    · exact ha
    · rw [ha] at he
      have hzz : z = z' := MulAction.injective (MulOpposite.op (g (a + 1) ^ ε' (a + 1))) he
      exact ih (a + 1) x ε ε' (fun j h1 h2 => hb j (by omega) (by omega)) hzz j hj (by omega)

theorem cubeProd_eq_F (g : ℕ → BinaryTreeAut) (n : ℕ) (ε : ℕ → ℕ) : cubeProd g n ε = F g 0 n ε := by
  unfold cubeProd F
  simp only [zero_add]

end CubeDev

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
set_option linter.unusedSimpArgs false
open ErschlerZheng
open CubeDev GrigBasic in
theorem solution (G : Subgroup Garrido.BinaryTreeAut)
    (g : ℕ → Garrido.BinaryTreeAut) (hg : ∀ n, 1 ≤ n → g n ∈ levelStab G n)
    (hroot : ∀ n, 1 ≤ n → ∀ v : List Bool, v.length = n → ∀ j : Bool, [j] <• sec (g n) v ≠ [j]) :
    IsCubeIndependent (rightOrbit G oneRay) (fun _ => 1) g := by
  have hfix : ∀ n, 1 ≤ n → FixLevel n (g n) := fun n hn v hv =>
    (Subgroup.mem_inf.mp (hg n hn)).2 v hv
  have hswap : ∀ n, 1 ≤ n → ∀ v : List Bool, v.length = n → rootSwap (sec (g n) v) = true := by
    intro n hn v hv
    have := hroot n hn v hv false
    rw [singleton_smul] at this
    cases h : rootSwap (sec (g n) v)
    · rw [h] at this; simp at this
    · rfl
  intro n _ x _ ε ε' hb he j hj1 hj2
  rw [cubeProd_eq_F, cubeProd_eq_F] at he
  exact core g hfix hswap n 0 x ε ε' (fun j h1 h2 => hb j (by omega) (by omega)) he j hj1
    (by omega)
end
