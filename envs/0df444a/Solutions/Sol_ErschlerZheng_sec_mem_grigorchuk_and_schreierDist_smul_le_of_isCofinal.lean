-- Prove2me | solution 1 for ErschlerZheng.sec_mem_grigorchuk_and_schreierDist_smul_le_of_isCofinal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T01:49:17.000684+00:00
-- url     : https://prove2.me/submissions/9c82bb66-1645-48ce-a766-137d1cc49967

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_sec_list_prod
import Theorems.Thm_ErschlerZheng_schreierDist_eq_abs_sub_grayCode_of_isCofinal
import Theorems.Thm_ErschlerZheng_schreierDist_le_two_pow_mul_schreierDist_shiftRay_add_of_isCofinal

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

theorem nil_smul (g : BinaryTreeAut) : ([] : List Bool) <• g = [] :=
  List.eq_nil_of_length_eq_zero (length_vertex_smul g [])

theorem sec_unique {g h : BinaryTreeAut} {v : List Bool}
    (H : ∀ w : List Bool, (v ++ w) <• g = (v <• g) ++ (w <• h)) : sec g v = h := by
  have key : ∀ w : List Bool, w <• sec g v = w <• h := by
    intro w
    have h1 := append_vertex_smul g v w
    rw [H w] at h1
    exact (List.append_cancel_left h1).symm
  have : (sec g v)⁻¹ = h⁻¹ := Subtype.ext (Equiv.ext fun w => key w)
  exact inv_injective this

theorem sec_nil (g : BinaryTreeAut) : sec g [] = g := by
  apply sec_unique
  intro w
  rw [nil_smul]
  rfl

theorem sec_append (g : BinaryTreeAut) (v u : List Bool) :
    sec g (v ++ u) = sec (sec g v) u := by
  apply sec_unique
  intro w
  rw [List.append_assoc, append_vertex_smul, append_vertex_smul, append_vertex_smul]
  simp only [List.append_assoc]

theorem sec_one (v : List Bool) : sec 1 v = 1 := by
  apply sec_unique
  intro w
  rfl

theorem sec_cons (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    sec g (x :: u) = sec (sec g [x]) u := by
  rw [← sec_append]
  rfl

/-! ### The root swap -/

/-! ### `a` and the generators -/

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

theorem grigA_inv : grigA⁻¹ = grigA := inv_eq_of_mul_eq_one_right grigA_mul_self

theorem vertex_smul_grigA (v : List Bool) : v <• grigA = grigAFun v := by
  rw [vertex_smul_def, grigA_inv]
  rfl

theorem sec_grigA (x : Bool) : sec grigA [x] = 1 := by
  apply sec_unique
  intro w
  rw [vertex_smul_grigA, vertex_smul_grigA]
  rfl

theorem sec_grigA_cons (x : Bool) (u : List Bool) : sec grigA (x :: u) = 1 := by
  rw [sec_cons, sec_grigA, sec_one]

theorem gen_mul_self (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ * gen ω γ = 1 :=
  Subtype.ext (Equiv.ext fun w => genFun_involutive ω γ w)

theorem gen_inv (ω : ℕ → Fin 3) (γ : BCD) : (gen ω γ)⁻¹ = gen ω γ :=
  inv_eq_of_mul_eq_one_right (gen_mul_self ω γ)

theorem vertex_smul_gen (ω : ℕ → Fin 3) (γ : BCD) (v : List Bool) :
    v <• gen ω γ = genFun ω γ v := by
  rw [vertex_smul_def, gen_inv]
  rfl

/-- The element `ω_0(γ) ∈ {a, id}`. -/
def letterElt (i : Fin 3) (γ : BCD) : BinaryTreeAut := if letterValue i γ then grigA else 1

theorem sec_gen_false (ω : ℕ → Fin 3) (γ : BCD) :
    sec (gen ω γ) [false] = letterElt (ω 0) γ := by
  apply sec_unique
  intro w
  rw [vertex_smul_gen, vertex_smul_gen]
  unfold letterElt
  by_cases h : letterValue (ω 0) γ
  · simp only [List.cons_append, List.nil_append, genFun, h, if_true]
    rw [vertex_smul_grigA]
    rfl
  · simp only [List.cons_append, List.nil_append, genFun, h]
    rfl

theorem sec_gen_true (ω : ℕ → Fin 3) (γ : BCD) :
    sec (gen ω γ) [true] = gen (shiftSeq ω 1) γ := by
  apply sec_unique
  intro w
  rw [vertex_smul_gen, vertex_smul_gen, vertex_smul_gen]
  simp [genFun]

theorem shiftSeq_shiftSeq (ω : ℕ → Fin 3) (m k : ℕ) :
    shiftSeq (shiftSeq ω m) k = shiftSeq ω (k + m) := by
  funext j
  simp only [shiftSeq]
  congr 1
  omega

theorem shiftSeq_zero (ω : ℕ → Fin 3) : shiftSeq ω 0 = ω := by
  funext j; simp [shiftSeq]

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

/-- `x = x_1 … x_n (𝔰ⁿ x)`. -/
theorem prepend_rayPrefix_shiftRay (x : Ray) (n : ℕ) : prepend (rayPrefix x n) (shiftRay x n) = x := by
  funext i
  unfold prepend
  split_ifs with h
  · rw [getElem_rayPrefix]
  · simp only [shiftRay, length_rayPrefix] at h ⊢
    congr 1; omega

theorem rayPrefix_prepend (u : List Bool) (x : Ray) :
    rayPrefix (prepend u x) u.length = u := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    simp [prepend, h2]

theorem shiftRay_prepend (u : List Bool) (x : Ray) : shiftRay (prepend u x) u.length = x := by
  funext i
  simp [shiftRay, prepend]

/-- `(v x')·g = (v·g)(x'·g_v)`. -/
theorem prepend_smul (g : BinaryTreeAut) (v : List Bool) (x : Ray) :
    prepend v x <• g = prepend (v <• g) (x <• sec g v) := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay (prepend v x <• g) v.length]
  rw [rayPrefix_smul, shiftRay_smul, rayPrefix_prepend, shiftRay_prepend]

theorem one_smul_ray (x : Ray) : x <• (1 : BinaryTreeAut) = x := one_smul _ x

end RayBasic

end ErschlerZheng
end

section
/-!
# The Gray code on finite words, and how the generators move it

For a word `w` of length `N`, `grayList w < 2^N`. The generator `a` changes it by `+1` when `w`
has an even number of zeros and by `-1` otherwise; a generator `γ_ω` either fixes `w` or changes
it by `-1` (even) or `+1` (odd). From every word there is a generator step up (below the top
value `2^N - 1`) and down (above `0`) whose section at `w` is trivial.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace GrayDev

open GrigBasic

end GrayDev

end ErschlerZheng
end

section
/-!
# The Schreier graph of `1^∞` through the Gray code

Rays that are all ones from position `N` on are `prepend w 1^∞` with `|w| = N`; their Gray code
is `grayList w`. A generator moves the Gray code of such a ray by at most one, and from `w` to
`w'` of the same length there is a path of `|ḡ(w) - ḡ(w')|` generators with trivial sections at
the intermediate words, so it carries any tail along unchanged.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace SchreierDev

open GrigBasic RayBasic GrayDev

/-- `x_k = 1` for every `k ⩾ N`. -/
def AllOnesFrom (N : ℕ) (x : Ray) : Prop := ∀ k ≥ N, x k = true

theorem isCofinal_iff (x : Ray) : IsCofinal x ↔ ∃ N, AllOnesFrom N x :=
  Filter.eventually_atTop

theorem AllOnesFrom.mono {N M : ℕ} {x : Ray} (h : AllOnesFrom N x) (hNM : N ≤ M) :
    AllOnesFrom M x := fun k hk => h k (le_trans hNM hk)

theorem rayPrefix_oneRay (n : ℕ) : rayPrefix oneRay n = List.replicate n true := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2; rw [getElem_rayPrefix]; simp [oneRay]

theorem shiftRay_eq_oneRay {N : ℕ} {x : Ray} (h : AllOnesFrom N x) : shiftRay x N = oneRay := by
  funext i; simp only [shiftRay, oneRay]; exact h _ (by omega)

theorem eq_prepend {N : ℕ} {x : Ray} (h : AllOnesFrom N x) :
    x = prepend (rayPrefix x N) oneRay := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay x N]
  rw [shiftRay_eq_oneRay h]

theorem allOnesFrom_prepend (w : List Bool) : AllOnesFrom w.length (prepend w oneRay) := by
  intro k hk
  simp [prepend, oneRay, show ¬ k < w.length by omega]

/-! ### Generators on rays that are eventually all ones -/

theorem genFun_replicate_true (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    genFun ω γ (List.replicate n true) = List.replicate n true := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, genFun, ih]

theorem oneRay_smul_gen (ω : ℕ → Fin 3) (γ : BCD) : oneRay <• gen ω γ = oneRay := by
  apply ray_ext
  intro n
  rw [rayPrefix_smul, rayPrefix_oneRay, vertex_smul_gen, genFun_replicate_true]

theorem sec_gen_append_true (ω : ℕ → Fin 3) (γ : BCD) (u : List Bool) :
    sec (gen ω γ) (u ++ [true]) = 1 ∨
      sec (gen ω γ) (u ++ [true]) = gen (shiftSeq ω (u.length + 1)) γ := by
  induction u generalizing ω with
  | nil =>
    right
    simp only [List.nil_append, sec_gen_true, List.length_nil, zero_add]
  | cons b u ih =>
    cases b
    · left
      rw [List.cons_append, sec_cons, sec_gen_false]
      unfold letterElt
      split_ifs
      · rw [show u ++ [true] = (u ++ [true]).head (by simp) :: (u ++ [true]).tail by simp,
          sec_grigA_cons]
      · exact sec_one _
    · rw [List.cons_append, sec_cons, sec_gen_true]
      rcases ih (shiftSeq ω 1) with h | h
      · left; exact h
      · right; rw [h, shiftSeq_shiftSeq]; simp

theorem oneRay_smul_sec_gens (ω : ℕ → Fin 3) (s : BinaryTreeAut) (hs : s ∈ gens ω)
    (u : List Bool) : oneRay <• sec s (u ++ [true]) = oneRay := by
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [show u ++ [true] = (u ++ [true]).head (by simp) :: (u ++ [true]).tail by simp,
      sec_grigA_cons]
    exact one_smul _ _
  all_goals
    rcases sec_gen_append_true ω _ u with h | h <;> rw [h]
    · exact one_smul _ _
    · exact oneRay_smul_gen _ _

theorem allOnesFrom_smul_gens (ω : ℕ → Fin 3) {s : BinaryTreeAut} (hs : s ∈ gens ω) {N : ℕ}
    {x : Ray} (h : AllOnesFrom N x) : AllOnesFrom (N + 1) (x <• s) := by
  have h1 := h.mono (Nat.le_succ N)
  have hx := eq_prepend h1
  have hw : rayPrefix x (N + 1) = rayPrefix x N ++ [true] := by
    rw [rayPrefix_add, show rayPrefix (shiftRay x N) 1 = [true] by
      simp [rayPrefix, shiftRay, h N le_rfl]]
  rw [hx, prepend_smul, hw, oneRay_smul_sec_gens ω s hs]
  have := allOnesFrom_prepend ((rayPrefix x N ++ [true]) <• s)
  rwa [length_vertex_smul, List.length_append, length_rayPrefix] at this

theorem gens_involutive (ω : ℕ → Fin 3) {s : BinaryTreeAut} (hs : s ∈ gens ω) : s⁻¹ = s := by
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact grigA_inv
  all_goals exact gen_inv _ _

end SchreierDev

end ErschlerZheng
end

section
/-!
# A12: Lemma 7.5, p. 35

`g_v ∈ G_{𝔰ⁿω}` for `|v| = n` (closure induction, sections of products by A4), and
`d(x, x·g) ⩽ 2ⁿ d(𝔰ⁿx, (𝔰ⁿx)·g_v) + 2ⁿ - 1` (A11, since `𝔰ⁿ(x·g) = (𝔰ⁿx)·g_v`), where the last
distance does not depend on the string (A9) and is at most the word length of `g_v`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace Lemma75Dev

open GrigBasic RayBasic SchreierDev

/-- Sections of a product, from (7.17) (A4). -/
theorem sec_mul' (g h : BinaryTreeAut) (v : List Bool) :
    sec (g * h) v = sec g v * sec h (v <• g) := by
  have := sec_list_prod [g, h] v
  simpa using this

theorem sec_inv' (g : BinaryTreeAut) (v : List Bool) : sec g⁻¹ v = (sec g (v <• g⁻¹))⁻¹ := by
  have h1 := sec_mul' g⁻¹ g v
  rw [inv_mul_cancel, sec_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem shiftSeq_add (ω : ℕ → Fin 3) (m : ℕ) : shiftSeq (shiftSeq ω 1) m = shiftSeq ω (m + 1) :=
  shiftSeq_shiftSeq ω 1 m

theorem letterElt_mem (ω : ℕ → Fin 3) (i : Fin 3) (γ : BCD) : letterElt i γ ∈ grigorchuk ω := by
  unfold letterElt
  split_ifs
  · exact Subgroup.subset_closure (by simp [gens])
  · exact Subgroup.one_mem _

theorem sec_gen_mem (ω : ℕ → Fin 3) (γ : BCD) (v : List Bool) :
    sec (gen ω γ) v ∈ grigorchuk (shiftSeq ω v.length) := by
  induction v generalizing ω with
  | nil =>
    rw [sec_nil, List.length_nil, shiftSeq_zero]
    exact Subgroup.subset_closure (gen_mem_gens' ω γ)
  | cons b u ih =>
    rw [sec_cons]
    cases b
    · rw [sec_gen_false]
      cases u with
      | nil => rw [sec_nil]; exact letterElt_mem _ _ _
      | cons c u' =>
        unfold letterElt
        split_ifs
        · rw [sec_grigA_cons]; exact Subgroup.one_mem _
        · rw [sec_one]; exact Subgroup.one_mem _
    · rw [sec_gen_true]
      have := ih (shiftSeq ω 1)
      rw [shiftSeq_add] at this
      rwa [List.length_cons]
where
  gen_mem_gens' (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ ∈ gens ω := by cases γ <;> simp [gens]

theorem sec_grigA_mem (ω : ℕ → Fin 3) (v : List Bool) :
    sec grigA v ∈ grigorchuk (shiftSeq ω v.length) := by
  cases v with
  | nil => rw [sec_nil, List.length_nil, shiftSeq_zero]; exact Subgroup.subset_closure (by simp [gens])
  | cons b u => rw [sec_grigA_cons]; exact Subgroup.one_mem _

theorem sec_mem (ω : ℕ → Fin 3) (g : BinaryTreeAut) (hg : g ∈ grigorchuk ω) :
    ∀ v : List Bool, sec g v ∈ grigorchuk (shiftSeq ω v.length) := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    intro v
    simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact sec_grigA_mem ω v
    all_goals exact sec_gen_mem ω _ v
  | one => intro v; rw [sec_one]; exact Subgroup.one_mem _
  | mul g h _ _ ihg ihh =>
    intro v
    rw [sec_mul']
    refine Subgroup.mul_mem _ (ihg v) ?_
    have := ihh (v <• g)
    rwa [length_vertex_smul] at this
  | inv g _ ihg =>
    intro v
    rw [sec_inv']
    refine Subgroup.inv_mem _ ?_
    have := ihg (v <• g⁻¹)
    rwa [length_vertex_smul] at this

theorem isCofinal_smul (ω : ℕ → Fin 3) (g : BinaryTreeAut) (hg : g ∈ grigorchuk ω) :
    ∀ x, IsCofinal x → IsCofinal (x <• g) := by
  suffices H : (∀ x, IsCofinal x → IsCofinal (x <• g)) ∧ ∀ x, IsCofinal x → IsCofinal (x <• g⁻¹) from
    H.1
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    have key : ∀ x, IsCofinal x → IsCofinal (x <• s) := by
      intro x hx
      obtain ⟨N, hN⟩ := (isCofinal_iff x).mp hx
      exact (isCofinal_iff _).mpr ⟨N + 1, allOnesFrom_smul_gens ω hs hN⟩
    refine ⟨key, ?_⟩
    rw [gens_involutive ω hs]
    exact key
  | one => exact ⟨fun x hx => by rwa [one_smul_ray], fun x hx => by rwa [inv_one, one_smul_ray]⟩
  | mul g h _ _ ihg ihh =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [MulOpposite.op_mul, mul_smul]; exact ihh.1 _ (ihg.1 x hx)
    · rw [mul_inv_rev, MulOpposite.op_mul, mul_smul]; exact ihg.2 _ (ihh.2 x hx)
  | inv g _ ihg => exact ⟨ihg.2, by rw [inv_inv]; exact ihg.1⟩

/-- The subgroup generated by `S` is the union of the balls. -/
theorem exists_mem_wordBall {G : Type*} [Group G] (S : Set G) (g : G)
    (hg : g ∈ Subgroup.closure S) : ∃ n, g ∈ Chou.wordBall S n := by
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨1, [s], by simp, by simp [hs], by simp⟩
  | one => exact ⟨0, [], le_rfl, by simp, rfl⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨m, l, hl, hls, rfl⟩ := ihg
    obtain ⟨n, l', hl', hls', rfl⟩ := ihh
    refine ⟨m + n, l ++ l', by simp; omega, ?_, by simp⟩
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hls x h
    · exact hls' x h
  | inv g _ ihg =>
    obtain ⟨m, l, hl, hls, rfl⟩ := ihg
    refine ⟨m, (l.map (·⁻¹)).reverse, by simp; omega, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_reverse, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rcases hls y hy with h | h
      · right; simpa using h
      · left; exact h
    · rw [List.prod_inv_reverse]

theorem mem_wordBall_wordLength {G : Type*} [Group G] (S : Set G) (g : G)
    (hg : g ∈ Subgroup.closure S) : g ∈ Chou.wordBall S (wordLength S g) := by
  obtain ⟨n, hn⟩ := exists_mem_wordBall S g hg
  exact Nat.sInf_mem (s := {n | g ∈ Chou.wordBall S n}) ⟨n, hn⟩

end Lemma75Dev

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open Lemma75Dev SchreierDev RayBasic GrigBasic in
theorem solution (ω : ℕ → Fin 3)
    (g : Garrido.BinaryTreeAut) (hg : g ∈ grigorchuk ω) (n : ℕ) (x : Ray) (hx : IsCofinal x) :
    sec g (rayPrefix x n) ∈ grigorchuk (shiftSeq ω n) ∧
      schreierDist ω x (x <• g) ≤
        2 ^ n * (wordLength (gens (shiftSeq ω n)) (sec g (rayPrefix x n)) + 1) := by
  have hmem : sec g (rayPrefix x n) ∈ grigorchuk (shiftSeq ω n) := by
    have := sec_mem ω g hg (rayPrefix x n)
    rwa [length_rayPrefix] at this
  refine ⟨hmem, ?_⟩
  set h := sec g (rayPrefix x n)
  have hxg := isCofinal_smul ω g hg x hx
  have hA11 := schreierDist_le_two_pow_mul_schreierDist_shiftRay_add_of_isCofinal ω x (x <• g)
    hx hxg n
  rw [shiftRay_smul] at hA11
  set x' := shiftRay x n
  have hx' : IsCofinal x' := (Filter.tendsto_add_atTop_nat n).eventually hx
  have hx'h : IsCofinal (x' <• h) := isCofinal_smul (shiftSeq ω n) h hmem x' hx'
  -- the distance does not depend on the string (A9)
  have hd : schreierDist ω x' (x' <• h) = schreierDist (shiftSeq ω n) x' (x' <• h) := by
    have e1 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x' (x' <• h) hx' hx'h
    have e2 := schreierDist_eq_abs_sub_grayCode_of_isCofinal (shiftSeq ω n) x' (x' <• h) hx' hx'h
    exact_mod_cast e1.trans e2.symm
  have hwl : schreierDist (shiftSeq ω n) x' (x' <• h) ≤ wordLength (gens (shiftSeq ω n)) h :=
    Nat.sInf_le ⟨h, mem_wordBall_wordLength _ h hmem, rfl⟩
  rw [hd] at hA11
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  calc schreierDist ω x (x <• g)
      ≤ 2 ^ n * schreierDist (shiftSeq ω n) x' (x' <• h) + 2 ^ n - 1 := hA11
    _ ≤ 2 ^ n * wordLength (gens (shiftSeq ω n)) h + 2 ^ n - 1 := by
        have := Nat.mul_le_mul_left (2 ^ n) hwl
        omega
    _ ≤ 2 ^ n * (wordLength (gens (shiftSeq ω n)) h + 1) := by
        rw [mul_add, mul_one]; omega
end
