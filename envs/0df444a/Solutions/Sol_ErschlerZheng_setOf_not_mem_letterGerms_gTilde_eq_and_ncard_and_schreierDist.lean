-- Prove2me | solution 1 for ErschlerZheng.setOf_not_mem_letterGerms_gTilde_eq_and_ncard_and_schreierDist
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T07:51:32.561759+00:00
-- url     : https://prove2.me/submissions/c369a523-cf18-4988-b874-435c3584e64c

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
import Theorems.Thm_ErschlerZheng_sec_evalWord_zetaWord_eq
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_evalFree_zetaFree_congr_and_zetaHat_evalFree_eq_of_tail_ne
import Theorems.Thm_ErschlerZheng_smul_cElt_eq_self_and_sec_cElt_eq
import Theorems.Thm_ErschlerZheng_two_pow_le_schreierDist_oneRay_and_le_of_isCofinal_of_ne
import Theorems.Thm_ErschlerZheng_schreierDist_eq_abs_sub_grayCode_of_isCofinal
import Theorems.Thm_ErschlerZheng_ncard_wSet_and_ncard_vSet_and_getLast_eq_false

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

theorem sec_mul (g h : BinaryTreeAut) (v : List Bool) :
    sec (g * h) v = sec g v * sec h (v <• g) := by
  apply sec_unique
  intro w
  rw [vertex_smul_mul, vertex_smul_mul, append_vertex_smul, append_vertex_smul,
    vertex_smul_mul]

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

theorem rootSwap_mul (g h : BinaryTreeAut) :
    rootSwap (g * h) = xor (rootSwap g) (rootSwap h) := by
  have : [false] <• (g * h) = [xor (rootSwap g) (rootSwap h)] := by
    rw [vertex_smul_mul, singleton_smul g, singleton_smul h]
    simp
  show decide ([false] <• (g * h) = [true]) = _
  rw [this]
  cases rootSwap g <;> cases rootSwap h <;> rfl

theorem rootSwap_one : rootSwap 1 = false := by
  unfold rootSwap; simp

theorem rootSwap_inv (g : BinaryTreeAut) : rootSwap g⁻¹ = rootSwap g := by
  have := rootSwap_mul g g⁻¹
  rw [mul_inv_cancel, rootSwap_one] at this
  cases h1 : rootSwap g <;> cases h2 : rootSwap g⁻¹ <;> simp_all

theorem cons_smul (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    (x :: u) <• g = xor x (rootSwap g) :: (u <• sec g [x]) := by
  have := append_vertex_smul g [x] u
  rw [singleton_smul] at this
  exact this

/-- An automorphism is determined by its root swap and its two sections at level 1. -/
theorem ext_of_rootSwap_sec {g h : BinaryTreeAut} (h0 : rootSwap g = rootSwap h)
    (hf : sec g [false] = sec h [false]) (ht : sec g [true] = sec h [true]) : g = h := by
  have key : ∀ v : List Bool, v <• g = v <• h := by
    intro v
    cases v with
    | nil => rw [nil_smul, nil_smul]
    | cons x u =>
      rw [cons_smul, cons_smul, h0]
      cases x
      · rw [hf]
      · rw [ht]
  have : g⁻¹ = h⁻¹ := Subtype.ext (Equiv.ext fun w => key w)
  exact inv_injective this

theorem sec_inv (g : BinaryTreeAut) (v : List Bool) : sec g⁻¹ v = (sec g (v <• g⁻¹))⁻¹ := by
  have h1 := sec_mul g⁻¹ g v
  rw [inv_mul_cancel, sec_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

/-! ### `a` and the generators -/

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

theorem grigA_inv : grigA⁻¹ = grigA := inv_eq_of_mul_eq_one_right grigA_mul_self

theorem grigA_mul_grigA_mul (x : BinaryTreeAut) : grigA * (grigA * x) = x := by
  rw [← mul_assoc, grigA_mul_self, one_mul]

theorem vertex_smul_grigA (v : List Bool) : v <• grigA = grigAFun v := by
  rw [vertex_smul_def, grigA_inv]
  rfl

theorem rootSwap_grigA : rootSwap grigA = true := by
  unfold rootSwap
  rw [vertex_smul_grigA]
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

theorem rootSwap_gen (ω : ℕ → Fin 3) (γ : BCD) : rootSwap (gen ω γ) = false := by
  unfold rootSwap
  rw [vertex_smul_gen]
  simp [genFun]

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

/-- The Klein four-group relations: the product of two distinct generators among `b, c, d` is
the third. -/
theorem genFun_klein (ω : ℕ → Fin 3) (w : List Bool) :
    genFun ω .b (genFun ω .c w) = genFun ω .d w ∧
    genFun ω .c (genFun ω .d w) = genFun ω .b w ∧
    genFun ω .d (genFun ω .b w) = genFun ω .c w ∧
    genFun ω .c (genFun ω .b w) = genFun ω .d w ∧
    genFun ω .d (genFun ω .c w) = genFun ω .b w ∧
    genFun ω .b (genFun ω .d w) = genFun ω .c w := by
  induction w generalizing ω with
  | nil => simp [genFun]
  | cons x w ih =>
    cases x
    · have h0 : ω 0 = 0 ∨ ω 0 = 1 ∨ ω 0 = 2 := by
        rcases ω 0 with ⟨k, hk⟩
        interval_cases k <;> simp
      rcases h0 with h0 | h0 | h0 <;>
        simp [genFun, letterValue, BCD.killedBy, h0, grigAFun_involutive w]
    · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih (shiftSeq ω 1)
      simp [genFun, a1, a2, a3, a4, a5, a6]

theorem gen_b_mul_c (ω : ℕ → Fin 3) : gen ω .b * gen ω .c = gen ω .d :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).1)
theorem gen_d_mul_b (ω : ℕ → Fin 3) : gen ω .d * gen ω .b = gen ω .c :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).2.2.1)

/-! ### Words -/

theorem evalWord_append (ω : ℕ → Fin 3) (k : ℕ) (u v : List Gen4) :
    evalWord ω k (u ++ v) = evalWord ω k u * evalWord ω k v := by
  simp [evalWord, List.map_append, List.prod_append]

theorem evalWord_nil (ω : ℕ → Fin 3) (k : ℕ) : evalWord ω k [] = 1 := rfl

/-- The value of a pair `aγ` in `G_{𝔰^k ω}`. -/
def pairLetter : APair → BCD
  | .ab => .b
  | .ac => .c
  | .ad => .d

theorem evalWord_toWord (ω : ℕ → Fin 3) (k : ℕ) (p : APair) :
    evalWord ω k p.toWord = grigA * gen (shiftSeq ω k) (pairLetter p) := by
  cases p <;> simp [evalWord, APair.toWord, pairLetter]

theorem evalWord_flatMap_cons (ω : ℕ → Fin 3) (k : ℕ) (p : APair) (w : List APair) :
    evalWord ω k ((p :: w).flatMap APair.toWord) =
      evalWord ω k p.toWord * evalWord ω k (w.flatMap APair.toWord) := by
  rw [List.flatMap_cons, evalWord_append]

theorem count_a_flatMap_toWord (w : List APair) :
    (w.flatMap APair.toWord).count .a = w.length := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rw [List.flatMap_cons, List.count_append, ih]
    cases p <;> simp [APair.toWord] <;> omega

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

theorem sec_gen_cons_true (ω : ℕ → Fin 3) (γ : BCD) (u : List Bool) :
    sec (gen ω γ) (true :: u) = sec (gen (shiftSeq ω 1) γ) u := by
  rw [sec_cons, sec_gen_true]

theorem sec_gen_replicate (ω : ℕ → Fin 3) (γ : BCD) (k : ℕ) (z : List Bool) (hz : z ≠ []) :
    sec (gen ω γ) (List.replicate k true ++ false :: z) = 1 := by
  induction k generalizing ω with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    rw [sec_cons, sec_gen_false]
    obtain ⟨c, z', rfl⟩ := List.exists_cons_of_ne_nil hz
    unfold letterElt
    split_ifs
    · exact sec_grigA_cons c z'
    · exact sec_one _
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, sec_gen_cons_true, ih]

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

theorem rayPrefix_oneRay (n : ℕ) : rayPrefix oneRay n = List.replicate n true := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2; rw [getElem_rayPrefix]; simp [oneRay]

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

end SchreierDev

end ErschlerZheng
end

section
/-!
# Germ calculus (helpers for B2, B5, B6)

Composition of germ equalities and multiplicativity of germs come from B1 (imported).
-/

open scoped RightActions

namespace ErschlerZheng

namespace GermBase

set_option linter.unusedSectionVars false

variable {H : Type*} [Group H] {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X]
  [ContinuousConstSMul Hᵐᵒᵖ X]

theorem rsmul_mul (y : X) (g h : H) : y <• (g * h) = (y <• g) <• h := by
  rw [MulOpposite.op_mul, mul_smul]

theorem rsmul_one (y : X) : y <• (1 : H) = y := by rw [MulOpposite.op_one, one_smul]

theorem rsmul_inv_eq {x : X} {h : H} (hh : x <• h = x) : x <• h⁻¹ = x := by
  conv_lhs => rw [← hh]
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem rsmul_inv_smul (y : X) (h : H) : (y <• h) <• h⁻¹ = y := by
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem germEq_refl (x : X) (g : H) : GermEq x g g := Filter.Eventually.of_forall fun _ => rfl

theorem GermEq.symm' {x : X} {g h : H} (e : GermEq x g h) : GermEq x h g := e.mono fun _ h => h.symm

theorem germEq_comp {x : X} {g₁ g₂ h₁ h₂ : H} (hg : GermEq x g₁ g₂) (hh : GermEq (x <• g₁) h₁ h₂) :
    GermEq x (g₁ * h₁) (g₂ * h₂) :=
  (germEq_mul_and_germ_mul x).1 g₁ g₂ h₁ h₂ hg hh

theorem germ_mul {x : X} {g h : H} (hg : x <• g = x) (hh : x <• h = x) :
    germ x (g * h) = germ x g * germ x h :=
  (germEq_mul_and_germ_mul x).2 g h hg hh

theorem germ_def {x : X} {h : H} (hh : x <• h = x) :
    germ x h = QuotientGroup.mk ⟨h, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top h, hh⟩⟩ := by
  unfold germ; rw [dif_pos hh]

theorem germ_one (x : X) : germ x (1 : H) = 1 := by
  rw [germ_def (rsmul_one x)]
  rfl

theorem germ_eq_iff {x : X} {h h' : H} (hh : x <• h = x) (hh' : x <• h' = x) :
    germ x h = germ x h' ↔ GermEq x h h' := by
  rw [germ_def hh, germ_def hh', QuotientGroup.eq]
  change GermEq x (h⁻¹ * h') 1 ↔ GermEq x h h'
  constructor
  · intro e
    have := germEq_comp (germEq_refl x h) (by rw [hh]; exact e)
    rw [mul_inv_cancel_left, mul_one] at this
    exact GermEq.symm' this
  · intro e
    have := germEq_comp (germEq_refl x h⁻¹) (by rw [rsmul_inv_eq hh]; exact e)
    rw [inv_mul_cancel] at this
    exact GermEq.symm' this

theorem conj_fix {o x : X} {σ h : H} (hσ : o <• σ = x) (hh : x <• h = x) :
    o <• (σ * h * σ⁻¹) = o := by
  rw [rsmul_mul, rsmul_mul, hσ, hh, ← hσ, rsmul_inv_smul]

theorem transport_spec {L : Subgroup H} {x y : X} (h : ∃ σ ∈ L, x <• σ = y) :
    transport L x y ∈ L ∧ x <• transport L x y = y := by
  unfold transport
  exact Classical.epsilon_spec (p := fun σ => σ ∈ L ∧ x <• σ = y) (by
    obtain ⟨σ, h1, h2⟩ := h; exact ⟨σ, h1, h2⟩)

theorem exists_L_of_mem {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) (x : X) {g : H}
    (hg : g ∈ G) : ∃ σ ∈ L, x <• σ = x <• g := by
  have : x <• g ∈ rightOrbit L x := by
    rw [hL.1 x]; exact ⟨g, hg, rfl⟩
  obtain ⟨σ, hσ, e⟩ := this
  exact ⟨σ, hσ, e.symm⟩

theorem exists_L_of_orbit {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) {o x : X}
    (hx : x ∈ rightOrbit G o) : ∃ σ ∈ L, o <• σ = x := by
  have : x ∈ rightOrbit L o := by rw [hL.1 o]; exact hx
  obtain ⟨σ, hσ, e⟩ := this
  exact ⟨σ, hσ, e.symm⟩

end GermBase

end ErschlerZheng
end

section
/-!
# Germs of `G_ω` read from sections along the ray (helpers for B3, B4)

For `k ∈ G_ω ⊔ L` and a ray `x` cofinal with `1^∞`, the sections of `k` along `x` are eventually
the sections along `1^∞` of an element `c ∈ {1, b_ω, c_ω, d_ω}`, i.e. `1` or `γ_{𝔰ⁿω}`; along a ray
not cofinal with `1^∞` they are eventually trivial. Two elements fixing `x` have the same germ at
`x` iff their sections along `x` eventually agree. Orbits and the finitary group come from A2.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ErschlerZheng

namespace GrigGermsDev

open GrigBasic RayBasic GrayDev SchreierDev GermBase

/-! ### Cylinders -/

theorem eventually_rayPrefix_eq (x : Ray) (n : ℕ) :
    ∀ᶠ y in nhds x, rayPrefix y n = rayPrefix x n := by
  have : ∀ᶠ y in nhds x, ∀ i : Fin n, y i = x i := by
    rw [Filter.eventually_all]
    intro i
    exact (continuous_apply (i : ℕ)).continuousAt (x := x)
      ((isOpen_discrete {x i}).mem_nhds rfl)
  filter_upwards [this] with y hy
  simp only [rayPrefix]
  congr 1
  funext i
  exact hy i

theorem exists_cylinder_subset (x : Ray) {U : Set Ray} (hU : U ∈ nhds x) :
    ∃ n, ∀ y : Ray, rayPrefix y n = rayPrefix x n → y ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  obtain ⟨M, hM⟩ := hI.bddAbove
  refine ⟨M + 1, fun y hy => hsub fun i hi => ?_⟩
  have hiM : i < M + 1 := Nat.lt_succ_of_le (hM hi)
  have : y i = x i := by
    have h1 : i < (rayPrefix y (M + 1)).length := by rw [length_rayPrefix]; exact hiM
    rw [← getElem_rayPrefix y (M + 1) i h1, List.getElem_of_eq hy, getElem_rayPrefix]
  rw [this]
  exact mem_of_mem_nhds (ht i)

theorem cyl_smul (k : BinaryTreeAut) (x y : Ray) (n : ℕ) (hy : rayPrefix y n = rayPrefix x n) :
    y <• k = prepend (rayPrefix x n <• k) (shiftRay y n <• sec k (rayPrefix x n)) := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay y n]
  rw [hy, prepend_smul]

theorem germEq_of_sec {x : Ray} {k k' : BinaryTreeAut} {n : ℕ}
    (hv : rayPrefix x n <• k = rayPrefix x n <• k')
    (hs : sec k (rayPrefix x n) = sec k' (rayPrefix x n)) : GermEq x k k' := by
  filter_upwards [eventually_rayPrefix_eq x n] with y hy
  rw [cyl_smul k x y n hy, cyl_smul k' x y n hy, hv, hs]

theorem sec_eq_of_vertex_eq {u : List Bool} {k k' : BinaryTreeAut}
    (H : ∀ w : List Bool, (u ++ w) <• k = (u ++ w) <• k') : sec k u = sec k' u := by
  apply sec_unique
  intro w
  rw [H w, append_vertex_smul, ← (show u <• k = u <• k' by simpa using H [])]

theorem sec_eq_of_germEq {x : Ray} {k k' : BinaryTreeAut} (h : GermEq x k k') :
    ∃ N, ∀ n ≥ N, rayPrefix x n <• k = rayPrefix x n <• k' ∧
      sec k (rayPrefix x n) = sec k' (rayPrefix x n) := by
  obtain ⟨N, hN⟩ := exists_cylinder_subset x h
  refine ⟨N, fun n hn => ?_⟩
  have key : ∀ w : List Bool, (rayPrefix x n ++ w) <• k = (rayPrefix x n ++ w) <• k' := by
    intro w
    set y := prepend (rayPrefix x n ++ w) oneRay
    have hyN : rayPrefix y N = rayPrefix x N := by
      have h1 : rayPrefix y (n + w.length) = rayPrefix x n ++ w := by
        have := rayPrefix_prepend (rayPrefix x n ++ w) oneRay
        simpa [length_rayPrefix] using this
      have h2 : rayPrefix y N = (rayPrefix y (n + w.length)).take N := by
        rw [List.prefix_iff_eq_take.mp (rayPrefix_prefix y (show N ≤ n + w.length by omega))]
        simp [length_rayPrefix]
      rw [h2, h1, List.take_append_of_le_length (by rw [length_rayPrefix]; exact hn)]
      have := List.prefix_iff_eq_take.mp (rayPrefix_prefix x hn)
      rw [length_rayPrefix] at this
      exact this.symm
    have hy := hN y hyN
    have := congrArg (fun z => rayPrefix z (n + w.length)) hy
    simp only [rayPrefix_smul] at this
    have h1 : rayPrefix y (n + w.length) = rayPrefix x n ++ w := by
      have := rayPrefix_prepend (rayPrefix x n ++ w) oneRay
      simpa [length_rayPrefix] using this
    rwa [h1] at this
  exact ⟨by simpa using key [], sec_eq_of_vertex_eq key⟩

/-! ### The set `V = {1, b_ω, c_ω, d_ω}` -/

theorem sec_gen_replicate_true (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    sec (gen ω γ) (List.replicate n true) = gen (shiftSeq ω n) γ := by
  induction n generalizing ω with
  | zero => rw [List.replicate_zero, sec_nil, shiftSeq_zero]
  | succ n ih =>
    rw [List.replicate_succ, sec_cons, sec_gen_true, ih, shiftSeq_shiftSeq]

/-! ### Cofinality classes are preserved (A2) -/

theorem mem_GL_of_G {ω : ℕ → Fin 3} {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) :
    g ∈ grigorchuk ω ⊔ finitary := (le_sup_left : grigorchuk ω ≤ _) hg

theorem mem_GL_of_L {ω : ℕ → Fin 3} {g : BinaryTreeAut} (hg : g ∈ finitary) :
    g ∈ grigorchuk ω ⊔ finitary := (le_sup_right : finitary ≤ _) hg

/-! ### Eventual sections -/

theorem first_zero (x : Ray) (hx : ∃ k, x k = false) :
    ∃ k, x k = false ∧ ∀ j < k, x j = true := by
  classical
  exact ⟨Nat.find hx, Nat.find_spec hx, fun j hj => by simpa using Nat.find_min hx hj⟩

theorem rayPrefix_first_zero' (x : Ray) (k : ℕ) (hk : x k = false) (hmin : ∀ j < k, x j = true) :
    rayPrefix x (k + 1) = List.replicate k true ++ [false] := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    simp only [length_rayPrefix] at h1
    by_cases hi : i < k
    · rw [List.getElem_append_left (by simpa using hi)]; simp [hmin i hi]
    · rw [List.getElem_append_right (by simpa using hi)]
      have : i = k := by omega
      subst this; simp [hk]

theorem rayPrefix_first_zero (x : Ray) (k : ℕ) (hk : x k = false) (hmin : ∀ j < k, x j = true)
    (n : ℕ) (hn : k + 2 ≤ n) :
    ∃ z : List Bool, z ≠ [] ∧ rayPrefix x n = List.replicate k true ++ false :: z := by
  refine ⟨rayPrefix (shiftRay x (k + 1)) (n - (k + 1)), ?_, ?_⟩
  · intro h
    have := congrArg List.length h
    simp [length_rayPrefix] at this
    omega
  · rw [show n = (k + 1) + (n - (k + 1)) by omega, rayPrefix_add, rayPrefix_first_zero' x k hk hmin]
    simp [show k + 1 + (n - (k + 1)) - (k + 1) = n - (k + 1) by omega]

end GrigGermsDev

end ErschlerZheng
end

section
/-!
# B3: Example 3.2 (p. 18)

Germs of `G_ω` at a ray `x` are read from the sections along `x`: two elements fixing `x` have the
same germ iff their sections along `x` eventually agree (`GrigGermsDev`). Along a ray not cofinal
with `1^∞` the sections are eventually trivial; along a cofinal ray they are eventually `1` or
`γ_{𝔰ⁿω}`. Orbits and level transitivity come from A2 and the Gray-code path.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace B3Dev

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev

theorem germ_eq_of_sec' {x : Ray} {k k' : BinaryTreeAut} (hk : x <• k = x) (hk' : x <• k' = x)
    {N : ℕ} (h : ∀ n ≥ N, sec k (rayPrefix x n) = sec k' (rayPrefix x n)) :
    germ x k = germ x k' := by
  rw [germ_eq_iff hk hk']
  refine germEq_of_sec (n := N) ?_ (h N le_rfl)
  rw [← rayPrefix_smul, ← rayPrefix_smul, hk, hk']

theorem sec_eq_of_germ {x : Ray} {k k' : BinaryTreeAut} (hk : x <• k = x) (hk' : x <• k' = x)
    (h : germ x k = germ x k') : ∃ N, ∀ n ≥ N, sec k (rayPrefix x n) = sec k' (rayPrefix x n) := by
  obtain ⟨N, hN⟩ := sec_eq_of_germEq ((germ_eq_iff hk hk').mp h)
  exact ⟨N, fun n hn => (hN n hn).2⟩

theorem one_fix (x : Ray) : x <• (1 : BinaryTreeAut) = x := one_smul_ray x

end B3Dev

end ErschlerZheng
end

section
/-!
# B4: germs read from sections (p. 42, the general-`ω` Fact 4.1)

`(g, x) ∈ ℋ^b` iff the sections of `g` along `x` are eventually `1` or `b_{𝔰ⁿω}` (conjugating by
the finitary transports changes no deep section). If every level-`n` section is in
`{1, a, b_{𝔰ⁿω}}`, that holds along every cofinal ray. Conversely the "bad" vertices (section not
in `{1, a, b_{𝔰^{|v|}ω}}`) form a subtree; if it were infinite, compactness of `∂T` would give a ray
along which every section is bad, while along every ray the sections are eventually good.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace B4Dev

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev B3Dev

theorem sec_gen_along (ω' : ℕ → Fin 3) (γ : BCD) (y : Ray) :
    (∃ N, ∀ m ≥ N, sec (gen ω' γ) (rayPrefix y m) = 1) ∨ y = oneRay := by
  by_cases hz : ∃ k, y k = false
  · left
    obtain ⟨k, hk, hmin⟩ := first_zero y hz
    refine ⟨k + 2, fun m hm => ?_⟩
    obtain ⟨z, hz, e⟩ := rayPrefix_first_zero y k hk hmin m hm
    rw [e, sec_gen_replicate ω' γ k z hz]
  · right
    push Not at hz
    exact funext fun k => by simpa [oneRay] using hz k

/-- Conjugating by a finitary transport does not change deep sections. -/
theorem sec_conj_L {σ k : BinaryTreeAut} (hσ : σ ∈ finitary) {x : Ray} (hσx : oneRay <• σ = x)
    (hk : x <• k = x) :
    ∃ N, ∀ n ≥ N, sec (σ * k * σ⁻¹) (List.replicate n true) = sec k (rayPrefix x n) := by
  obtain ⟨m, hm⟩ := hσ
  refine ⟨m, fun n hn => ?_⟩
  have h1 : sec σ (List.replicate n true) = 1 :=
    sec_eq_one_of_le σ hn hm _ (List.length_replicate)
  have hp : List.replicate n true <• σ = rayPrefix x n := by
    rw [← rayPrefix_oneRay, ← rayPrefix_smul, hσx]
  have hpk : rayPrefix x n <• k = rayPrefix x n := by rw [← rayPrefix_smul, hk]
  have hpσ : rayPrefix x n <• σ⁻¹ = List.replicate n true := by
    rw [← hp, vertex_smul_smul_inv]
  rw [sec_mul, sec_mul, hp, vertex_smul_mul, hp, hpk, sec_inv, hpσ, h1, inv_one, one_mul, mul_one]

theorem sec_mul_L {σ : BinaryTreeAut} (hσ : σ ∈ finitary) (g : BinaryTreeAut) (x : Ray) :
    ∃ N, ∀ n ≥ N, sec (g * σ⁻¹) (rayPrefix x n) = sec g (rayPrefix x n) := by
  obtain ⟨m, hm⟩ := finitary.inv_mem hσ
  refine ⟨m, fun n hn => ?_⟩
  rw [sec_mul, sec_eq_one_of_le σ⁻¹ hn hm _ (by rw [length_vertex_smul, length_rayPrefix]),
    mul_one]

theorem mem_zpowers_sq {G : Type*} [Group G] {θ y : G} (hsq : θ ^ (2 : ℤ) = 1)
    (hy : y ∈ Subgroup.zpowers θ) : y = 1 ∨ y = θ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [zpow_eq_zpow_emod k hsq]
  rcases Int.emod_two_eq k with h | h <;> rw [h]
  · left; exact zpow_zero θ
  · right; exact zpow_one θ

end B4Dev

end ErschlerZheng
end

section
/-!
# Root swap and level-1 sections of products (helpers for A5, A7)
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ZetaDev

open GrigBasic

/-- `g` has root swap `e` and level-1 sections `s0` (at `0`) and `s1` (at `1`). -/
def Dec3 (g : BinaryTreeAut) (e : Bool) (s0 s1 : BinaryTreeAut) : Prop :=
  rootSwap g = e ∧ sec g [false] = s0 ∧ sec g [true] = s1

theorem dec_congr {g : BinaryTreeAut} {e : Bool} {s0 s1 t0 t1 : BinaryTreeAut}
    (h : Dec3 g e s0 s1) (h0 : s0 = t0) (h1 : s1 = t1) : Dec3 g e t0 t1 := by
  subst h0 h1; exact h

theorem dec_mul {g h : BinaryTreeAut} {e f : Bool} {g0 g1 h0 h1 : BinaryTreeAut}
    (hg : Dec3 g e g0 g1) (hh : Dec3 h f h0 h1) :
    Dec3 (g * h) (xor e f) (g0 * (if e then h1 else h0)) (g1 * (if e then h0 else h1)) := by
  obtain ⟨he, hg0, hg1⟩ := hg
  obtain ⟨hf, hh0, hh1⟩ := hh
  refine ⟨by rw [rootSwap_mul, he, hf], ?_, ?_⟩
  · rw [sec_mul, hg0, singleton_smul, he]; cases e <;> simp [hh0, hh1]
  · rw [sec_mul, hg1, singleton_smul, he]; cases e <;> simp [hh0, hh1]

theorem dec_inv {g : BinaryTreeAut} {e : Bool} {g0 g1 : BinaryTreeAut} (hg : Dec3 g e g0 g1) :
    Dec3 g⁻¹ e (if e then g1⁻¹ else g0⁻¹) (if e then g0⁻¹ else g1⁻¹) := by
  obtain ⟨he, hg0, hg1⟩ := hg
  refine ⟨by rw [rootSwap_inv, he], ?_, ?_⟩
  · rw [sec_inv, singleton_smul, rootSwap_inv, he]; cases e <;> simp [hg0, hg1]
  · rw [sec_inv, singleton_smul, rootSwap_inv, he]; cases e <;> simp [hg0, hg1]

theorem dec_one : Dec3 1 false 1 1 := ⟨rootSwap_one, sec_one _, sec_one _⟩

theorem dec_grigA : Dec3 grigA true 1 1 := ⟨rootSwap_grigA, sec_grigA _, sec_grigA _⟩

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨k, hk⟩
  interval_cases k <;> simp

end ZetaDev

end ErschlerZheng
end

section
/-!
# A7: the substitutions act on group elements (p. 15), under the tail hypothesis

Route. By (2.3) (A5, imported), `g = ζ_{ω_n}(w)` evaluated in `G_{𝔰^n ω}` is determined by its
root swap `β(w)` and by `W = w` evaluated in `G_{𝔰^{n+1} ω}`: its level-1 sections are
`(aWa, W)` or `(aW, Wa)`. It remains to see that `β(w)` is a function of `W`. For every level
`k`, `σ_k(g) = Σ_{|v| = k} [g_v swaps level 1] mod 2` is a homomorphism `Aut(T) → ℤ/2`, with
`σ_0(a) = 1`, `σ_{k+1}(a) = 0`, `σ_0(γ_ω) = 0`, `σ_{k+1}(γ_ω) = ω_k(γ)`. The parity `β` counts
the pairs `a κ` with `κ` the generator killed by `ω_n`; under the tail hypothesis it is
`σ_0 + Σ_{j ∈ J} σ_{j+1}` of `W` for a set `J` of one level (where `ω_n` recurs) or two levels
(where the two other letters occur).
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace ZetaHatDev

open GrigBasic ZetaDev

/-! ### Level parities -/

/-- `1` if `g` swaps level 1, else `0`. -/
def bit (g : BinaryTreeAut) : ZMod 2 := if rootSwap g then 1 else 0

theorem bit_mul (g h : BinaryTreeAut) : bit (g * h) = bit g + bit h := by
  unfold bit
  rw [rootSwap_mul]
  cases rootSwap g <;> cases rootSwap h <;> decide

theorem bit_one : bit 1 = 0 := by simp [bit, rootSwap_one]

/-! ### The free-group words -/

theorem evalFree_of (ω : ℕ → Fin 3) (k : ℕ) (p : APair) :
    evalFree ω k (FreeGroup.of p) = evalWord ω k p.toWord := by
  simp [evalFree]

theorem evalFree_prod_map_of (ω : ℕ → Fin 3) (k : ℕ) (u : List APair) :
    evalFree ω k (u.map FreeGroup.of).prod = evalWord ω k (u.flatMap APair.toWord) := by
  induction u with
  | nil => simp [evalWord_nil]
  | cons p u ih => rw [List.map_cons, List.prod_cons, map_mul, ih, evalFree_of,
      evalWord_flatMap_cons]

theorem evalFree_zetaFree_of (ω : ℕ → Fin 3) (n : ℕ) (p : APair) :
    evalFree ω n (zetaFree (ω n) (FreeGroup.of p)) =
      evalWord ω n ((zetaWord (ω n) [p]).flatMap APair.toWord) := by
  rw [show zetaWord (ω n) [p] = zetaPair (ω n) p by simp [zetaWord]]
  simp only [zetaFree, FreeGroup.lift_apply_of]
  exact evalFree_prod_map_of ω n _

/-- (2.3) for free-group words, from (2.3) for single pairs (A5). -/
theorem dec_evalFree (ω : ℕ → Fin 3) (n : ℕ) (w : FreeGroup APair) :
    Dec3 (evalFree ω n (zetaFree (ω n) w)) (rootSwap (evalFree ω n (zetaFree (ω n) w)))
      (grigA * evalFree ω (n + 1) w *
        (if rootSwap (evalFree ω n (zetaFree (ω n) w)) then 1 else grigA))
      (evalFree ω (n + 1) w *
        (if rootSwap (evalFree ω n (zetaFree (ω n) w)) then grigA else 1)) := by
  induction w using FreeGroup.induction_on with
  | C1 =>
    simp only [map_one]
    refine dec_congr dec_one ?_ ?_ <;> simp [rootSwap_one, grigA_mul_self]
  | of p =>
    have hA := sec_evalWord_zetaWord_eq ω n [p]
    have hW : evalWord ω (n + 1) ([p].flatMap APair.toWord) = evalFree ω (n + 1) (FreeGroup.of p) := by
      rw [evalFree_of]; simp
    rw [evalFree_zetaFree_of, ← hW]
    set g := evalWord ω n ((zetaWord (ω n) [p]).flatMap APair.toWord)
    rcases Nat.even_or_odd (((zetaWord (ω n) [p]).flatMap APair.toWord).count .a) with he | ho
    · obtain ⟨hst, h0, h1⟩ := hA.1 he
      have hr : rootSwap g = false := by
        have := (Subgroup.mem_inf.mp hst).2 [false] rfl
        unfold rootSwap
        rw [this]
        decide
      refine ⟨rfl, ?_, ?_⟩ <;> simp [hr, h0, h1]
    · obtain ⟨hsw, h0, h1⟩ := hA.2 ho
      have hr : rootSwap g = true := by unfold rootSwap; rw [hsw]; decide
      refine ⟨rfl, ?_, ?_⟩ <;> simp [hr, h0, h1]
  | inv_of p ih =>
    have := dec_inv ih
    simp only [map_inv, rootSwap_inv] at this ⊢
    refine dec_congr this ?_ ?_ <;>
    · cases rootSwap (evalFree ω n (zetaFree (ω n) (FreeGroup.of p))) <;>
        simp [mul_inv_rev, grigA_inv, mul_assoc]
  | mul x y ihx ihy =>
    have := dec_mul ihx ihy
    simp only [map_mul, rootSwap_mul] at this ⊢
    refine dec_congr this ?_ ?_ <;>
    · cases rootSwap (evalFree ω n (zetaFree (ω n) x)) <;>
        cases rootSwap (evalFree ω n (zetaFree (ω n) y)) <;>
        simp [mul_assoc, grigA_mul_grigA_mul]

/-! ### The parity is a function of the element -/

theorem bodd_length_zetaPair (i : Fin 3) (p : APair) :
    (if Nat.bodd (zetaPair i p).length then (1 : ZMod 2) else 0) =
      if pairLetter p = BCD.killedBy i then 1 else 0 := by
  rcases fin3_cases i with rfl | rfl | rfl <;> cases p <;> rfl

theorem bit_evalFree_zetaFree_of (ω : ℕ → Fin 3) (n : ℕ) (p : APair) :
    bit (evalFree ω n (zetaFree (ω n) (FreeGroup.of p))) =
      if pairLetter p = BCD.killedBy (ω n) then 1 else 0 := by
  rw [← bodd_length_zetaPair, evalFree_zetaFree_of]
  have hd := (dec_evalFree ω n (FreeGroup.of p)).1
  have hA := sec_evalWord_zetaWord_eq ω n [p]
  rw [count_a_flatMap_toWord, show zetaWord (ω n) [p] = zetaPair (ω n) p by simp [zetaWord]] at hA
  rw [show zetaWord (ω n) [p] = zetaPair (ω n) p by simp [zetaWord]]
  unfold bit rootSwap
  rcases Nat.even_or_odd (zetaPair (ω n) p).length with he | ho
  · have hb : Nat.bodd (zetaPair (ω n) p).length = false := by
      have := Nat.mod_two_of_bodd (zetaPair (ω n) p).length
      rw [Nat.even_iff] at he
      cases h : Nat.bodd (zetaPair (ω n) p).length <;> simp_all
    have := (Subgroup.mem_inf.mp (hA.1 he).1).2 [false] rfl
    rw [this, hb]
    decide
  · have hb : Nat.bodd (zetaPair (ω n) p).length = true := by
      have := Nat.mod_two_of_bodd (zetaPair (ω n) p).length
      rw [Nat.odd_iff] at ho
      cases h : Nat.bodd (zetaPair (ω n) p).length <;> simp_all
    rw [(hA.2 ho).1, hb]
    decide

theorem evalFree_zero_mem (ω : ℕ → Fin 3) (w : FreeGroup APair) :
    evalFree ω 0 w ∈ grigorchuk ω := by
  have : (evalFree ω 0).range ≤ grigorchuk ω := by
    apply FreeGroup.range_lift_le
    rintro _ ⟨p, rfl⟩
    show evalWord ω 0 p.toWord ∈ grigorchuk ω
    rw [evalWord_toWord, shiftSeq_zero]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (Subgroup.subset_closure ?_)
    · simp [gens]
    · cases p <;> simp [gens, pairLetter]
  exact this ⟨w, rfl⟩

end ZetaHatDev

open GrigBasic ZetaDev ZetaHatDev

end ErschlerZheng
end

section
/-!
# The index sets `W^n_k` and `V^j_k` (Erschler–Zheng p. 37)

`|W^n_k| = 2^{k/D}` for `D ∣ n`, `D ∣ k`; `|V^j_k| = 2^{k/D}` and every `v ∈ V^j_k` ends with `0`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrW

theorem frM_spec (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (ℓ : ℕ) :
    frM D ω ℓ + 3 ≤ D ∧ ω (ℓ * D + frM D ω ℓ) = 2 ∧ ω (ℓ * D + frM D ω ℓ + 2) = 1 ∧
      (ω (ℓ * D + frM D ω ℓ + 1) = 0 ∨ ω (ℓ * D + frM D ω ℓ + 1) = 1) := by
  have hne : {m | m + 3 ≤ D ∧ ω (ℓ * D + m) = 2 ∧ ω (ℓ * D + m + 2) = 1 ∧
      (ω (ℓ * D + m + 1) = 0 ∨ ω (ℓ * D + m + 1) = 1)}.Nonempty := hω ℓ
  exact Nat.sInf_mem hne

end ConstrW

end ErschlerZheng
end

section
/-!
# Fact 7.6: `ι([γ_{𝔰ⁿω}, a], v)` lies in `G_ω`, with word length at most `2^{n+2}`

The words of the paper's proof (p. 37), built from the bottom: a word `w` read in `G_{𝔰^{ℓ+1}ω}`
is lifted to `G_{𝔰^ℓ ω}` letter by letter, by `a ↦ a y a`, `γ ↦ γ` (to act below `1`) or by
`a ↦ y`, `γ ↦ a γ a` (to act below `0`), where `ω_ℓ(y) = a`. The lift acts as `w` below the chosen
vertex and as `π(w)` below the other one, where `π` sends `a ↦ y_{𝔰^{ℓ+1}ω}`, `γ ↦ ω_ℓ(γ)`.
The invariant that makes `π(w) = 1` is `Kill`: `w` evaluates to `1` under every letter map
`a ↦ z`, `γ ↦ (A if ω_ℓ(γ) = a, else 1)` with `z, A` involutions.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrIota

open GrigBasic ZetaDev

/-! ### `ι` -/

theorem iota_mul (g h : BinaryTreeAut) (u : List Bool) :
    iota g u * iota h u = iota (g * h) u := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  show iotaFun g u (iotaFun h u w) = iotaFun (g * h) u w
  unfold iotaFun
  by_cases hw : u <+: w
  · obtain ⟨t, rfl⟩ := hw
    simp
  · simp [hw]

theorem iota_one (u : List Bool) : iota 1 u = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  show iotaFun 1 u w = w
  unfold iotaFun
  by_cases hw : u <+: w
  · obtain ⟨t, rfl⟩ := hw
    simp
  · simp [hw]

theorem iota_inv (g : BinaryTreeAut) (u : List Bool) : (iota g u)⁻¹ = iota g⁻¹ u := by
  apply inv_eq_of_mul_eq_one_right
  rw [iota_mul, mul_inv_cancel, iota_one]

theorem iota_nil (g : BinaryTreeAut) : iota g [] = g := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  show iotaFun g [] w = _
  simp [iotaFun]

theorem iota_iota (g : BinaryTreeAut) (u v : List Bool) :
    iota (iota g v) u = iota g (u ++ v) := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  show iotaFun (iota g v) u w = iotaFun g (u ++ v) w
  unfold iotaFun
  by_cases hw : u <+: w
  · obtain ⟨t, rfl⟩ := hw
    simp only [List.prefix_append, if_true, List.drop_left', List.prefix_append_right_inj]
    show u ++ iotaFun g v t = _
    unfold iotaFun
    by_cases ht : v <+: t
    · obtain ⟨s, rfl⟩ := ht
      simp
    · simp [ht]
  · have : ¬ u ++ v <+: w := fun h => hw ((List.prefix_append u v).trans h)
    simp [hw, this]

theorem vertex_smul_iota (g : BinaryTreeAut) (u v : List Bool) :
    v <• iota g u = if u <+: v then u ++ (v.drop u.length <• g) else v := by
  rw [vertex_smul_def, iota_inv]
  rfl

theorem append_smul_iota (g : BinaryTreeAut) (u w : List Bool) :
    (u ++ w) <• iota g u = u ++ (w <• g) := by
  rw [vertex_smul_iota, if_pos (List.prefix_append u w)]
  simp

theorem smul_iota_of_not_prefix (g : BinaryTreeAut) (u v : List Bool) (h : ¬ u <+: v) :
    v <• iota g u = v := by
  rw [vertex_smul_iota, if_neg h]

theorem sec_iota_self (g : BinaryTreeAut) (u : List Bool) : sec (iota g u) u = g := by
  apply sec_unique
  intro w
  rw [append_smul_iota]
  have : u <• iota g u = u := by
    have := append_smul_iota g u []
    simpa [nil_smul] using this
  rw [this]

/-- `ι(g, x)` for a first-level vertex `x`: no root swap, section `g` at `x`, `1` at `!x`. -/
theorem dec_iota (g : BinaryTreeAut) (x : Bool) :
    Dec3 (iota g [x]) false (if x then 1 else g) (if x then g else 1) := by
  have h1 : ∀ y : Bool, [y] <• iota g [x] = [y] := by
    intro y
    by_cases hy : y = x
    · subst hy
      have := append_smul_iota g [y] []
      simpa [nil_smul] using this
    · apply smul_iota_of_not_prefix
      simp [Ne.symm hy]
  refine ⟨?_, ?_, ?_⟩
  · unfold rootSwap
    rw [h1]
    simp
  · cases x
    · simpa using sec_iota_self g [false]
    · simp only [if_true]
      apply sec_unique
      intro w
      rw [smul_iota_of_not_prefix _ _ _ (by simp), h1]
      rfl
  · cases x
    · simp only [Bool.false_eq_true, if_false]
      apply sec_unique
      intro w
      rw [smul_iota_of_not_prefix _ _ _ (by simp), h1]
      rfl
    · simpa using sec_iota_self g [true]

/-- The element with sections `g` at `0` and `h` at `1` and no root swap. -/
def pairElt (g h : BinaryTreeAut) : BinaryTreeAut := iota g [false] * iota h [true]

theorem dec_pairElt (g h : BinaryTreeAut) : Dec3 (pairElt g h) false g h := by
  have := dec_mul (dec_iota g false) (dec_iota h true)
  simpa [pairElt] using this

theorem eq_of_dec {g h : BinaryTreeAut} {e : Bool} {s0 s1 : BinaryTreeAut}
    (hg : Dec3 g e s0 s1) (hh : Dec3 h e s0 s1) : g = h :=
  ext_of_rootSwap_sec (hg.1.trans hh.1.symm) (hg.2.1.trans hh.2.1.symm)
    (hg.2.2.trans hh.2.2.symm)

theorem pairElt_mul (g h g' h' : BinaryTreeAut) :
    pairElt g h * pairElt g' h' = pairElt (g * g') (h * h') := by
  apply eq_of_dec (dec_mul (dec_pairElt g h) (dec_pairElt g' h'))
  simpa using dec_pairElt (g * g') (h * h')

theorem pairElt_one : pairElt 1 1 = 1 := by
  simp [pairElt, iota_one]

theorem grigA_conj_pairElt (g h : BinaryTreeAut) :
    grigA * pairElt g h * grigA = pairElt h g := by
  apply eq_of_dec (dec_mul (dec_mul dec_grigA (dec_pairElt g h)) dec_grigA)
  simpa using dec_pairElt h g

theorem gen_eq_pairElt (ω : ℕ → Fin 3) (ℓ : ℕ) (γ : BCD) :
    gen (shiftSeq ω ℓ) γ = pairElt (letterElt (ω ℓ) γ) (gen (shiftSeq ω (ℓ + 1)) γ) := by
  apply eq_of_dec _ (dec_pairElt _ _)
  refine ⟨rootSwap_gen _ _, ?_, ?_⟩
  · rw [sec_gen_false]; simp [shiftSeq]
  · rw [sec_gen_true, shiftSeq_shiftSeq, Nat.add_comm]

/-! ### Words and letter maps -/

/-- The letter `γ` as a letter of `{a, b, c, d}`. -/
def bcdGen : BCD → Gen4
  | .b => .b
  | .c => .c
  | .d => .d

/-- The letter map `a ↦ fa`, `γ ↦ fγ γ`. -/
def lm (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : Gen4 → BinaryTreeAut
  | .a => fa
  | .b => fγ .b
  | .c => fγ .c
  | .d => fγ .d

@[simp] theorem lm_a (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .a = fa := rfl
@[simp] theorem lm_b (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .b = fγ .b := rfl
@[simp] theorem lm_c (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .c = fγ .c := rfl
@[simp] theorem lm_d (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .d = fγ .d := rfl

@[simp] theorem lm_bcdGen (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) (γ : BCD) :
    lm fa fγ (bcdGen γ) = fγ γ := by
  cases γ <;> rfl

/-- The value of a word under a letter map. -/
def evL (φ : Gen4 → BinaryTreeAut) (w : List Gen4) : BinaryTreeAut := (w.map φ).prod

theorem evL_nil (φ : Gen4 → BinaryTreeAut) : evL φ [] = 1 := rfl

theorem evL_cons (φ : Gen4 → BinaryTreeAut) (l : Gen4) (w : List Gen4) :
    evL φ (l :: w) = φ l * evL φ w := by
  simp [evL]

theorem evL_append (φ : Gen4 → BinaryTreeAut) (u w : List Gen4) :
    evL φ (u ++ w) = evL φ u * evL φ w := by
  simp [evL]

theorem evL_flatMap (φ : Gen4 → BinaryTreeAut) (g : Gen4 → List Gen4) (w : List Gen4) :
    evL φ (w.flatMap g) = evL (fun l => evL φ (g l)) w := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [List.flatMap_cons, evL_append, evL_cons, ih]

theorem evL_reverse (φ : Gen4 → BinaryTreeAut) (hφ : ∀ l, φ l * φ l = 1) (w : List Gen4) :
    evL φ w.reverse = (evL φ w)⁻¹ := by
  induction w with
  | nil => simp [evL]
  | cons l w ih =>
    rw [List.reverse_cons, evL_append, ih, evL_cons φ l w, mul_inv_rev]
    congr 1
    rw [evL_cons, evL_nil, mul_one]
    exact (inv_eq_of_mul_eq_one_right (hφ l)).symm

theorem evalWord_eq_evL (ω : ℕ → Fin 3) (k : ℕ) (w : List Gen4) :
    evalWord ω k w = evL (lm grigA (gen (shiftSeq ω k))) w := by
  unfold evalWord evL
  congr 1

theorem evL_congr {φ ψ : Gen4 → BinaryTreeAut} (h : ∀ l, φ l = ψ l) (w : List Gen4) :
    evL φ w = evL ψ w := by
  unfold evL
  congr 1
  exact List.map_congr_left fun l _ => h l

/-- The commutator word `p q p^R q^R` (all letters are involutions). -/
def commW (p q : List Gen4) : List Gen4 := p ++ q ++ p.reverse ++ q.reverse

theorem evL_commW (φ : Gen4 → BinaryTreeAut) (hφ : ∀ l, φ l * φ l = 1) (p q : List Gen4) :
    evL φ (commW p q) = ⁅evL φ p, evL φ q⁆ := by
  rw [commW, evL_append, evL_append, evL_append, evL_reverse φ hφ, evL_reverse φ hφ,
    commutatorElement_def]

/-- The letter map of the invariant: `a ↦ z`, `γ ↦ A` if `e γ`, else `1`. -/
def killMap (z A : BinaryTreeAut) (e : BCD → Bool) : Gen4 → BinaryTreeAut :=
  lm z fun γ => if e γ then A else 1

/-- The invariant: `w` evaluates to `1` under every `killMap z A e` with `z, A` involutions. -/
def Kill (e : BCD → Bool) (w : List Gen4) : Prop :=
  ∀ z A : BinaryTreeAut, z * z = 1 → A * A = 1 → evL (killMap z A e) w = 1

/-! ### The lift -/

/-- The lift of a letter: towards `1` (`x = true`): `a ↦ a y a`, `γ ↦ γ`; towards `0`:
`a ↦ y`, `γ ↦ a γ a`. -/
def liftL (x : Bool) (y : BCD) : Gen4 → List Gen4
  | .a => if x then [.a, bcdGen y, .a] else [bcdGen y]
  | .b => if x then [.b] else [.a, .b, .a]
  | .c => if x then [.c] else [.a, .c, .a]
  | .d => if x then [.d] else [.a, .d, .a]

theorem liftL_palindrome (x : Bool) (y : BCD) (l : Gen4) : (liftL x y l).reverse = liftL x y l := by
  cases l <;> cases x <;> simp [liftL]

theorem flatMap_reverse_of_palindrome (g : Gen4 → List Gen4) (hg : ∀ l, (g l).reverse = g l)
    (w : List Gen4) : w.reverse.flatMap g = (w.flatMap g).reverse := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.reverse_cons, List.flatMap_append, ih]
    simp [hg]

theorem lift_commW (x : Bool) (y : BCD) (p q : List Gen4) :
    (commW p q).flatMap (liftL x y) = commW (p.flatMap (liftL x y)) (q.flatMap (liftL x y)) := by
  simp only [commW, List.flatMap_append]
  rw [flatMap_reverse_of_palindrome _ (liftL_palindrome x y),
    flatMap_reverse_of_palindrome _ (liftL_palindrome x y)]

theorem bcdGen_ne_a (y : BCD) : bcdGen y ≠ .a := by cases y <;> simp [bcdGen]

theorem lift_counts (x : Bool) (y : BCD) (w : List Gen4) :
    (if x then (w.flatMap (liftL x y)).length = 2 * w.count .a + w.length ∧
        (w.flatMap (liftL x y)).count .a = 2 * w.count .a
      else (w.flatMap (liftL x y)).length + 2 * w.count .a = 3 * w.length ∧
        (w.flatMap (liftL x y)).count .a + 2 * w.count .a = 2 * w.length) := by
  have hy : List.count Gen4.a [bcdGen y] = 0 := by
    cases y <;> rfl
  induction w with
  | nil => cases x <;> simp
  | cons l w ih =>
    rw [List.flatMap_cons, List.length_append, List.count_append, List.count_cons,
      List.length_cons]
    cases x <;> cases l <;> simp only [liftL, if_true, Bool.false_eq_true, if_false] at ih ⊢ <;>
      simp [List.count_cons, List.count_nil, hy, bcdGen_ne_a] at ih ⊢ <;> omega

theorem lift_length (x : Bool) (y : BCD) (w : List Gen4) (hw : 2 * w.count .a = w.length) :
    (w.flatMap (liftL x y)).length = 2 * w.length ∧
      2 * (w.flatMap (liftL x y)).count .a = (w.flatMap (liftL x y)).length := by
  have := lift_counts x y w
  cases x
  · simp only [Bool.false_eq_true, if_false] at this; omega
  · simp only [if_true] at this; omega

theorem evL_liftL_true (ω : ℕ → Fin 3) (ℓ : ℕ) (y : BCD) (hy : letterValue (ω ℓ) y = true)
    (l : Gen4) :
    evL (lm grigA (gen (shiftSeq ω ℓ))) (liftL true y l) =
      pairElt (lm (gen (shiftSeq ω (ℓ + 1)) y) (letterElt (ω ℓ)) l)
        (lm grigA (gen (shiftSeq ω (ℓ + 1))) l) := by
  cases l <;> simp only [liftL, if_true, evL_cons, evL_nil, mul_one, lm_a, lm_b, lm_c, lm_d,
    lm_bcdGen]
  · rw [gen_eq_pairElt ω ℓ, ← mul_assoc, grigA_conj_pairElt]
    simp [letterElt, hy]
  all_goals exact gen_eq_pairElt ω ℓ _

theorem evL_liftL_false (ω : ℕ → Fin 3) (ℓ : ℕ) (y : BCD) (hy : letterValue (ω ℓ) y = true)
    (l : Gen4) :
    evL (lm grigA (gen (shiftSeq ω ℓ))) (liftL false y l) =
      pairElt (lm grigA (gen (shiftSeq ω (ℓ + 1)))  l)
        (lm (gen (shiftSeq ω (ℓ + 1)) y) (letterElt (ω ℓ)) l) := by
  cases l <;> simp only [liftL, Bool.false_eq_true, if_false, evL_cons, evL_nil, mul_one, lm_a,
    lm_b, lm_c, lm_d, lm_bcdGen]
  · rw [gen_eq_pairElt ω ℓ]
    simp [letterElt, hy]
  all_goals rw [gen_eq_pairElt ω ℓ, ← mul_assoc, grigA_conj_pairElt]

/-- The lifting identity, towards `1`. -/
theorem evalWord_lift_true (ω : ℕ → Fin 3) (ℓ : ℕ) (y : BCD) (hy : letterValue (ω ℓ) y = true)
    (w : List Gen4) :
    evalWord ω ℓ (w.flatMap (liftL true y)) =
      pairElt (evL (lm (gen (shiftSeq ω (ℓ + 1)) y) (letterElt (ω ℓ))) w)
        (evalWord ω (ℓ + 1) w) := by
  rw [evalWord_eq_evL, evL_flatMap, evalWord_eq_evL]
  induction w with
  | nil => simp [evL, pairElt_one]
  | cons l w ih =>
    rw [evL_cons, ih, evL_cons, evL_cons, ← pairElt_mul, evL_liftL_true ω ℓ y hy]

/-- The lifting identity, towards `0`. -/
theorem evalWord_lift_false (ω : ℕ → Fin 3) (ℓ : ℕ) (y : BCD) (hy : letterValue (ω ℓ) y = true)
    (w : List Gen4) :
    evalWord ω ℓ (w.flatMap (liftL false y)) =
      pairElt (evalWord ω (ℓ + 1) w)
        (evL (lm (gen (shiftSeq ω (ℓ + 1)) y) (letterElt (ω ℓ))) w) := by
  rw [evalWord_eq_evL, evL_flatMap, evalWord_eq_evL]
  induction w with
  | nil => simp [evL, pairElt_one]
  | cons l w ih =>
    rw [evL_cons, ih, evL_cons, evL_cons, ← pairElt_mul, evL_liftL_false ω ℓ y hy]


/-! ### The invariant `Kill` under lifts -/

theorem evL_mem_pair (ψ : Gen4 → BinaryTreeAut) (A : BinaryTreeAut) (hA : A * A = 1)
    (hψ : ∀ l, ψ l = 1 ∨ ψ l = A) (w : List Gen4) : evL ψ w = 1 ∨ evL ψ w = A := by
  induction w with
  | nil => left; rfl
  | cons l w ih =>
    rw [evL_cons]
    rcases hψ l with h | h <;> rcases ih with h' | h' <;> rw [h, h'] <;> simp [hA]

theorem evL_commW_of_pair (ψ : Gen4 → BinaryTreeAut) (A : BinaryTreeAut) (hA : A * A = 1)
    (hψ : ∀ l, ψ l = 1 ∨ ψ l = A) (p q : List Gen4) : evL ψ (commW p q) = 1 := by
  have hinv : ∀ l, ψ l * ψ l = 1 := by
    intro l; rcases hψ l with h | h <;> rw [h]; simp; exact hA
  rw [evL_commW ψ hinv]
  rcases evL_mem_pair ψ A hA hψ p with h | h <;> rcases evL_mem_pair ψ A hA hψ q with h' | h' <;>
    rw [h, h'] <;> simp [commutatorElement_def]

theorem evL_conj (z : BinaryTreeAut) (hz : z * z = 1) (ψ : Gen4 → BinaryTreeAut) (w : List Gen4) :
    evL (fun l => z * ψ l * z) w = z * evL ψ w * z := by
  induction w with
  | nil => simp [evL, hz]
  | cons l w ih =>
    rw [evL_cons, evL_cons, ih]
    calc z * ψ l * z * (z * evL ψ w * z) = z * ψ l * (z * z) * evL ψ w * z := by
          simp only [mul_assoc]
      _ = z * (ψ l * evL ψ w) * z := by rw [hz]; simp only [mul_one, mul_assoc]

theorem kill_lift (e e' : BCD → Bool) (x : Bool) (y : BCD) (p q : List Gen4)
    (h : e' y = false ∨ (e' = e ∧ Kill e (commW p q))) :
    Kill e' ((commW p q).flatMap (liftL x y)) := by
  intro z A hz hA
  have hz' : ∀ X : BinaryTreeAut, z * (z * X) = X := fun X => by rw [← mul_assoc, hz, one_mul]
  rw [evL_flatMap]
  by_cases hy : e' y = true
  · rcases h with h | ⟨rfl, hk⟩
    · rw [hy] at h; exact absurd h (by simp)
    cases x
    · -- towards `0`: `a ↦ A`, `γ ↦ z (A or 1) z`
      have hzAz : z * A * z * (z * A * z) = 1 := by
        calc z * A * z * (z * A * z) = z * A * (z * z) * A * z := by simp only [mul_assoc]
          _ = 1 := by rw [hz, mul_one, mul_assoc z A A, hA, mul_one, hz]
      have key : ∀ l, evL (killMap z A e') (liftL false y l) =
          z * killMap (z * A * z) A e' l * z := by
        intro l
        cases l <;> simp [liftL, killMap, evL_cons, evL_nil, hy, mul_assoc, hz, hz']
      rw [evL_congr key, evL_conj z hz, hk (z * A * z) A hzAz hA]
      simp [hz]
    · have hzAz : z * A * z * (z * A * z) = 1 := by
        calc z * A * z * (z * A * z) = z * A * (z * z) * A * z := by simp only [mul_assoc]
          _ = 1 := by rw [hz, mul_one, mul_assoc z A A, hA, mul_one, hz]
      have key : ∀ l, evL (killMap z A e') (liftL true y l) = killMap (z * A * z) A e' l := by
        intro l
        cases l <;> simp [liftL, killMap, evL_cons, evL_nil, hy, mul_assoc]
      rw [evL_congr key, hk (z * A * z) A hzAz hA]
  · have hy' : e' y = false := by simpa using hy
    cases x
    · have hzAz : z * A * z * (z * A * z) = 1 := by
        calc z * A * z * (z * A * z) = z * A * (z * z) * A * z := by simp only [mul_assoc]
          _ = 1 := by rw [hz, mul_one, mul_assoc z A A, hA, mul_one, hz]
      apply evL_commW_of_pair _ (z * A * z) hzAz
      intro l
      cases l <;> simp only [liftL, killMap, Bool.false_eq_true, if_false, evL_cons, evL_nil,
        mul_one, lm_a, lm_b, lm_c, lm_d, lm_bcdGen, hy'] <;> try (left; rfl)
      all_goals (try split_ifs) <;> simp [hz, hz', mul_assoc]
    · apply evL_commW_of_pair _ A hA
      intro l
      cases l <;> simp only [liftL, killMap, if_true, evL_cons, evL_nil,
        mul_one, lm_a, lm_b, lm_c, lm_d, lm_bcdGen, hy', Bool.false_eq_true, if_false]
      · left; simp [hz]
      all_goals split_ifs <;> simp

/-! ### The words of Fact 7.6 -/

/-- A letter not killed by `i`. -/
def notKilled (i : Fin 3) : BCD := if i = 2 then .c else .b

theorem letterValue_notKilled (i : Fin 3) : letterValue i (notKilled i) = true := by
  revert i; decide

theorem letterValue_killedBy_of_ne (i j : Fin 3) (h : i ≠ j) :
    letterValue j (BCD.killedBy i) = true := by
  revert i j; decide

theorem letterValue_killedBy_self (i : Fin 3) : letterValue i (BCD.killedBy i) = false := by
  revert i; decide

theorem lm_grig_involutive (ω : ℕ → Fin 3) (k : ℕ) (l : Gen4) :
    lm grigA (gen (shiftSeq ω k)) l * lm grigA (gen (shiftSeq ω k)) l = 1 := by
  cases l <;> simp [grigA_mul_self, gen_mul_self]

theorem killMap_involutive (z A : BinaryTreeAut) (e : BCD → Bool) (hz : z * z = 1)
    (hA : A * A = 1) (l : Gen4) : killMap z A e l * killMap z A e l = 1 := by
  cases l <;> simp only [killMap, lm_a, lm_b, lm_c, lm_d] <;> try exact hz
  all_goals split_ifs <;> simp [hA]

theorem exists_word (ω : ℕ → Fin 3) (n : ℕ) (γ : BCD)
    (hγ : 1 ≤ n → letterValue (ω (n - 1)) γ = false) :
    ∀ (v : List Bool) (ℓ : ℕ), ℓ + v.length = n → ∃ w : List Gen4,
      evalWord ω ℓ w = iota ⁅gen (shiftSeq ω n) γ, grigA⁆ v ∧ w.length = 2 ^ (v.length + 2) ∧
      2 * w.count .a = w.length ∧ (∃ p q, w = commW p q) ∧
      (1 ≤ ℓ → Kill (letterValue (ω (ℓ - 1))) w) := by
  intro v
  induction v with
  | nil =>
    intro ℓ hℓ
    simp only [List.length_nil, Nat.add_zero] at hℓ
    subst hℓ
    refine ⟨commW [bcdGen γ] [.a], ?_, by simp [commW], ?_, ⟨_, _, rfl⟩, ?_⟩
    · rw [evalWord_eq_evL, evL_commW _ (lm_grig_involutive ω ℓ), iota_nil]
      simp [evL]
    · simp [commW, List.count_cons, bcdGen_ne_a]
    · intro hℓ z A hz hA
      rw [evL_commW _ (killMap_involutive z A _ hz hA)]
      simp [evL, killMap, hγ hℓ, commutatorElement_def]
  | cons x v ih =>
    intro ℓ hℓ
    simp only [List.length_cons] at hℓ
    obtain ⟨w', hev, hlen, hcount, ⟨p, q, hpq⟩, hkill⟩ := ih (ℓ + 1) (by omega)
    have hk : Kill (letterValue (ω ℓ)) w' := by simpa using hkill (by omega)
    obtain ⟨y, hy, hy'⟩ : ∃ y, letterValue (ω ℓ) y = true ∧
        (1 ≤ ℓ → letterValue (ω (ℓ - 1)) y = false ∨
          letterValue (ω (ℓ - 1)) = letterValue (ω ℓ)) := by
      by_cases h : ω (ℓ - 1) = ω ℓ
      · exact ⟨notKilled (ω ℓ), letterValue_notKilled _, fun _ => Or.inr (by rw [h])⟩
      · exact ⟨BCD.killedBy (ω (ℓ - 1)), letterValue_killedBy_of_ne _ _ h,
          fun _ => Or.inl (letterValue_killedBy_self _)⟩
    have hπ : evL (lm (gen (shiftSeq ω (ℓ + 1)) y) (letterElt (ω ℓ))) w' = 1 :=
      hk _ _ (gen_mul_self _ _) grigA_mul_self
    obtain ⟨hl1, hl2⟩ := lift_length x y w' hcount
    refine ⟨w'.flatMap (liftL x y), ?_, ?_, hl2, ?_, ?_⟩
    · cases x
      · rw [evalWord_lift_false ω ℓ y hy, hπ, hev, pairElt, iota_one, mul_one, iota_iota]
        rfl
      · rw [evalWord_lift_true ω ℓ y hy, hπ, hev, pairElt, iota_one, one_mul, iota_iota]
        rfl
    · rw [hl1, hlen, List.length_cons, pow_succ]; ring
    · exact ⟨_, _, hpq ▸ lift_commW x y p q⟩
    · intro hℓ1
      rw [hpq]
      apply kill_lift (letterValue (ω ℓ)) _ x y p q
      rcases hy' hℓ1 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hpq ▸ hk⟩

end ConstrIota

end ErschlerZheng
end

section
/-!
# The elements `h^v_i` (7.4) (Erschler–Zheng p. 38)

For `v ∈ V^j_k`: its length, the `201`/`211` window at each digit `0`, `h^v_i` in the rigid
stabilizer of `v_1 … v_{i-2}` (Fact 7.6 for the string `𝔰^j ω`), `[b, a]` below `1`, and
`1^∞ · h^v_1 ⋯ h^v_{k'} = v 1^∞`.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrH

open GrigBasic ZetaDev ConstrW ConstrIota RayBasic SchreierDev

/-! ### The positions of the digits `0` of `v ∈ V^j_k` -/

theorem frI_sep (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) {a b : ℕ} (ha : a ∈ frI D ω)
    (hb : b ∈ frI D ω) (hab : a < b) : a + 3 ≤ b := by
  obtain ⟨ℓ1, rfl⟩ := ha
  obtain ⟨ℓ2, rfl⟩ := hb
  have h1 := (frM_spec D ω hω ℓ1).1
  have h2 := (frM_spec D ω hω ℓ2).1
  rcases Nat.lt_trichotomy ℓ1 ℓ2 with h | rfl | h
  · have : (ℓ1 + 1) * D ≤ ℓ2 * D := Nat.mul_le_mul_right D h
    have : (ℓ1 + 1) * D = ℓ1 * D + D := by ring
    omega
  · omega
  · have : (ℓ2 + 1) * D ≤ ℓ1 * D := Nat.mul_le_mul_right D h
    have : (ℓ2 + 1) * D = ℓ2 * D + D := by ring
    omega

theorem window_of_mem_frI (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) {s : ℕ}
    (hs : s ∈ frI D ω) :
    3 ≤ s ∧ ω (s - 3) = 2 ∧ (ω (s - 2) = 0 ∨ ω (s - 2) = 1) ∧ ω (s - 1) = 1 := by
  obtain ⟨ℓ, rfl⟩ := hs
  obtain ⟨-, h2, h3, h4⟩ := frM_spec D ω hω ℓ
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [show ℓ * D + frM D ω ℓ + 3 - 3 = ℓ * D + frM D ω ℓ by omega]; exact h2
  · rw [show ℓ * D + frM D ω ℓ + 3 - 2 = ℓ * D + frM D ω ℓ + 1 by omega]; exact h4
  · rw [show ℓ * D + frM D ω ℓ + 3 - 1 = ℓ * D + frM D ω ℓ + 2 by omega]; exact h3

theorem length_of_mem_vSet (D : ℕ) (ω : ℕ → Fin 3) (j k : ℕ) (v : List Bool)
    (hv : v ∈ vSet D ω j k) :
    v.length = D - j % D + k + frM D ω (ellIndex D k j) + 3 := by
  obtain ⟨u, ⟨hu, -⟩, rfl⟩ := hv
  simp [hu]
  omega

theorem getElem_of_mem_vSet (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j k : ℕ)
    (hk : D ∣ k) (v : List Bool) (hv : v ∈ vSet D ω j k) (t : ℕ) (ht : t < v.length)
    (hf : v[t] = false) : D - j % D ≤ t ∧ j + (t + 1) ∈ frI D ω := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  have hjD : j % D < D := Nat.mod_lt _ (by omega)
  have hjj : j % D ≤ j := Nat.mod_le _ _
  obtain ⟨u, ⟨hu, hu2⟩, rfl⟩ := hv
  simp only [List.append_assoc] at ht hf
  simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at ht
  by_cases h1 : t < D - j % D
  · rw [List.getElem_append_left (by simp; omega)] at hf
    simp at hf
  push Not at h1
  rw [List.getElem_append_right (by simp; omega)] at hf
  simp only [List.length_replicate] at hf
  by_cases h2 : t - (D - j % D) < k
  · rw [List.getElem_append_left (by simp [hu]; omega)] at hf
    refine ⟨h1, ?_⟩
    by_contra hnot
    have := hu2 (t - (D - j % D)) (by rw [hu]; exact h2)
      (by
        have e : j + D - j % D + (t - (D - j % D) + 1) = j + (t + 1) := by omega
        rw [e]; exact hnot)
    rw [this] at hf
    exact Bool.noConfusion hf
  push Not at h2
  rw [List.getElem_append_right (by simp [hu]; omega)] at hf
  simp only [hu] at hf
  by_cases h3 : t - (D - j % D) - k < frM D ω (ellIndex D k j) + 2
  · rw [List.getElem_append_left (by simp; omega)] at hf
    simp at hf
  refine ⟨h1, ⟨ellIndex D k j, ?_⟩⟩
  have hlast : t = D - j % D + k + frM D ω (ellIndex D k j) + 2 := by omega
  have hdiv : D ∣ j + D - j % D + k := by
    have h1 : j + D - j % D = D * (j / D) + D := by
      have := Nat.div_add_mod j D
      omega
    rw [h1]
    exact Dvd.dvd.add (Dvd.dvd.add (Dvd.intro _ rfl) (dvd_refl D)) hk
  have hell : ellIndex D k j * D = j + D - j % D + k := by
    unfold ellIndex
    exact Nat.div_mul_cancel hdiv
  rw [hell, hlast]
  omega

/-! ### `[b, a]` below `1` -/

theorem dec_comm_b (ω : ℕ → Fin 3) (hb : letterValue (ω 0) .b = true) :
    Dec3 ⁅gen ω .b, grigA⁆ false (grigA * gen (shiftSeq ω 1) .b) (gen (shiftSeq ω 1) .b * grigA) := by
  have hg : Dec3 (gen ω .b) false grigA (gen (shiftSeq ω 1) .b) := by
    refine ⟨rootSwap_gen _ _, ?_, sec_gen_true _ _⟩
    rw [sec_gen_false]; simp [letterElt, hb]
  rw [commutatorElement_def, gen_inv, grigA_inv]
  have := dec_mul (dec_mul (dec_mul hg dec_grigA) hg) dec_grigA
  simpa [mul_assoc] using this

theorem prepend_append (u w : List Bool) (x : Ray) :
    prepend (u ++ w) x = prepend u (prepend w x) := by
  funext i
  unfold prepend
  by_cases h1 : i < u.length
  · rw [dif_pos (by simp; omega), dif_pos h1, List.getElem_append_left h1]
  · rw [dif_neg h1]
    by_cases h2 : i < u.length + w.length
    · rw [dif_pos (by simpa using h2), dif_pos (by omega), List.getElem_append_right (by omega)]
    · rw [dif_neg (by simpa using h2), dif_neg (by omega)]
      congr 1
      simp; omega

/-! ### The milestone -/

theorem hElt_of_false (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) (t : ℕ) (ht : t < v.length)
    (hf : v[t] = false) :
    hElt ω j v (t + 1) = iota ⁅gen (shiftSeq ω (j + (t + 1) - 2)) .b, grigA⁆ (v.take (t + 1 - 2)) := by
  have : v.getD (t + 1 - 1) true = false := by
    rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ ht, hf]
  unfold hElt
  rw [this]
  simp

theorem hElt_of_true (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) (t : ℕ) (ht : t < v.length)
    (hf : v[t] = true) : hElt ω j v (t + 1) = 1 := by
  have : v.getD (t + 1 - 1) true = true := by
    rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ ht, hf]
  unfold hElt
  rw [this]
  simp

end ConstrH

end ErschlerZheng
end

section
/-!
# Lemma 7.9 (corrected) and its printed failure (Erschler–Zheng p. 39)

`a𝔠^v_j = a H⁻¹ c H` is the value of the explicit even-length word `a U^R c U` (`U` a word for
`H = h^v_1 ⋯ h^v_{k'}`, from Fact 7.6), hence of a free-group word `w` over `{ab, ac, ad}`
(pair the letters: `x y = (a x)⁻¹ (a y)`). The parity character `χ_κ` (number of `aκ` letters
mod 2) satisfies `χ_κ ∘ ζ_i = χ_{κ_i}` (`κ_i` the letter killed by `i`), and the root swap of
`ζ_i(u)` evaluated is `χ_{κ_i}(u)` (A5). So every stage of `ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{j-1}}(w)`
has root swap `χ_{κ_{j-1}}(w)`: `0` when `ω_{j-1} ≠ 1` (even numbers of `b` and `d`), `1` when
`ω_{j-1} = 1` (odd number of `c`). With (2.3) this gives Lemma 7.9 and its failure.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrG

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH

/-! ### Words for `hProd` and `a𝔠` -/

theorem evalWord_shift_zero (ω : ℕ → Fin 3) (j : ℕ) (u : List Gen4) :
    evalWord (shiftSeq ω j) 0 u = evalWord ω j u := by
  rw [evalWord_eq_evL, evalWord_eq_evL, shiftSeq_zero]

theorem exists_word_prod (ω : ℕ → Fin 3) (j : ℕ) (l : List BinaryTreeAut)
    (hl : ∀ x ∈ l, ∃ u, evalWord ω j u = x) : ∃ U, evalWord ω j U = l.prod := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x l ih =>
    obtain ⟨u, hu⟩ := hl x (by simp)
    obtain ⟨U, hU⟩ := ih (fun y hy => hl y (by simp [hy]))
    exact ⟨u ++ U, by rw [evalWord_append, hu, hU, List.prod_cons]⟩

theorem exists_word_hProd (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j k : ℕ) (hk : D ∣ k)
    (v : List Bool) (hv : v ∈ vSet D ω j k) : ∃ U, evalWord ω j U = hProd ω j v := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  apply exists_word_prod
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  have ht' : t < v.length := List.mem_range.mp ht
  cases hvt : v[t]
  · obtain ⟨h1, hI⟩ := getElem_of_mem_vSet D ω hω j k hk v hv t ht' hvt
    have ht1 : 1 ≤ t := by have := Nat.mod_lt j (show 0 < D by omega); omega
    obtain ⟨-, w1, -, -⟩ := window_of_mem_frI D ω hω hI
    obtain ⟨u, hu, -⟩ := exists_word (shiftSeq ω j) (t + 1 - 2) .b
      (by
        intro _
        simp only [shiftSeq]
        rw [show t + 1 - 2 - 1 + j = j + (t + 1) - 3 by omega, w1]
        decide)
      (v.take (t + 1 - 2)) 0 (by simp; omega)
    refine ⟨u, ?_⟩
    rw [← evalWord_shift_zero, hu, hElt_of_false ω j v t ht' hvt]
    rw [shiftSeq_shiftSeq, show t + 1 - 2 + j = j + (t + 1) - 2 by omega]
  · exact ⟨[], by rw [hElt_of_true ω j v t ht' hvt]; rfl⟩

theorem evalWord_reverse (ω : ℕ → Fin 3) (j : ℕ) (U : List Gen4) :
    evalWord ω j U.reverse = (evalWord ω j U)⁻¹ := by
  rw [evalWord_eq_evL, evalWord_eq_evL, evL_reverse _ (lm_grig_involutive ω j)]

/-- The word `a U^R c U` for `a𝔠^v_j`. -/
def acWord (U : List Gen4) : List Gen4 := [.a] ++ U.reverse ++ [.c] ++ U

theorem evalWord_acWord (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) (U : List Gen4)
    (hU : evalWord ω j U = hProd ω j v) :
    evalWord ω j (acWord U) = grigA * cElt ω j v := by
  unfold acWord cElt
  rw [evalWord_append, evalWord_append, evalWord_append, evalWord_reverse, hU]
  simp [evalWord, mul_assoc]

/-! ### Free-group words from even-length words -/

/-- The free-group element with value `a x`. -/
def lt : Gen4 → FreeGroup APair
  | .a => 1
  | .b => .of .ab
  | .c => .of .ac
  | .d => .of .ad

/-- Pair the letters: `x y ↦ (a x)⁻¹ (a y)`. -/
def conv : List Gen4 → FreeGroup APair
  | x :: y :: rest => (lt x)⁻¹ * lt y * conv rest
  | _ => 1

theorem evalFree_lt (ω : ℕ → Fin 3) (k : ℕ) (x : Gen4) :
    evalFree ω k (lt x) = grigA * lm grigA (gen (shiftSeq ω k)) x := by
  cases x
  · simp [lt, grigA_mul_self]
  all_goals simp [lt, evalFree_of, evalWord_toWord, pairLetter]

theorem evalFree_conv (ω : ℕ → Fin 3) (k : ℕ) :
    ∀ n (w : List Gen4), w.length = 2 * n → evalFree ω k (conv w) = evalWord ω k w := by
  intro n
  induction n with
  | zero =>
    intro w hw
    have : w = [] := List.length_eq_zero_iff.mp (by simpa using hw)
    subst this; rfl
  | succ n ih =>
    intro w hw
    match w, hw with
    | x :: y :: rest, hw =>
      simp only [List.length_cons] at hw
      rw [conv, map_mul, map_mul, map_inv, ih rest (by omega), evalFree_lt, evalFree_lt,
        evalWord_eq_evL, evalWord_eq_evL, evL_cons, evL_cons, mul_inv_rev, grigA_inv]
      have hx := lm_grig_involutive ω k x
      have hxi : (lm grigA (gen (shiftSeq ω k)) x)⁻¹ = lm grigA (gen (shiftSeq ω k)) x :=
        inv_eq_of_mul_eq_one_right hx
      rw [hxi]
      simp only [mul_assoc, grigA_mul_grigA_mul]

/-- The parity of the number of letters `aκ`. -/
def chi (κ : BCD) : FreeGroup APair →* Multiplicative (ZMod 2) :=
  FreeGroup.lift fun p => Multiplicative.ofAdd (if pairLetter p = κ then 1 else 0)

theorem chi_lt (κ : BCD) (x : Gen4) :
    chi κ (lt x) = Multiplicative.ofAdd (if x = bcdGen κ then 1 else 0) := by
  cases x <;> cases κ <;> simp [lt, chi, pairLetter, bcdGen] <;> rfl

theorem chi_conv (κ : BCD) :
    ∀ n (w : List Gen4), w.length = 2 * n →
      chi κ (conv w) = Multiplicative.ofAdd ((w.count (bcdGen κ) : ℕ) : ZMod 2) := by
  intro n
  induction n with
  | zero =>
    intro w hw
    have : w = [] := List.length_eq_zero_iff.mp (by simpa using hw)
    subst this; rfl
  | succ n ih =>
    intro w hw
    match w, hw with
    | x :: y :: rest, hw =>
      simp only [List.length_cons] at hw
      rw [conv, map_mul, map_mul, map_inv, ih rest (by omega), chi_lt, chi_lt,
        List.count_cons, List.count_cons]
      rw [← ofAdd_neg, ← ofAdd_add, ← ofAdd_add]
      congr 1
      have hneg : ∀ z : ZMod 2, -z = z := by decide
      rw [hneg]
      split_ifs <;> simp_all <;> push_cast <;> ring

/-! ### The parity character and the substitutions -/

/-- The root-swap bit as a homomorphism. -/
def bitHom : BinaryTreeAut →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (bit g)
  map_one' := by simp [bit_one]
  map_mul' g h := by simp [bit_mul, ofAdd_add]

theorem bit_evalFree_zetaFree (ω : ℕ → Fin 3) (m : ℕ) (u : FreeGroup APair) :
    Multiplicative.ofAdd (bit (evalFree ω m (zetaFree (ω m) u))) =
      chi (BCD.killedBy (ω m)) u := by
  have : bitHom.comp ((evalFree ω m).comp (zetaFree (ω m))) = chi (BCD.killedBy (ω m)) := by
    apply FreeGroup.ext_hom
    intro p
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    show Multiplicative.ofAdd (bit (evalFree ω m (zetaFree (ω m) (FreeGroup.of p)))) = _
    rw [bit_evalFree_zetaFree_of]
    simp [chi]
  exact DFunLike.congr_fun this u

theorem chi_zetaFree (κ : BCD) (i : Fin 3) (u : FreeGroup APair) :
    chi κ (zetaFree i u) = chi (BCD.killedBy i) u := by
  have : (chi κ).comp (zetaFree i) = chi (BCD.killedBy i) := by
    apply FreeGroup.ext_hom
    intro p
    simp only [MonoidHom.coe_comp, Function.comp_apply, zetaFree, FreeGroup.lift_apply_of]
    rcases fin3_cases i with rfl | rfl | rfl <;> cases p <;> cases κ <;>
      simp [zetaPair, chi, pairLetter, BCD.killedBy, ← ofAdd_add] <;> decide
  exact DFunLike.congr_fun this u

/-- `ζ_{ω_m} ∘ ⋯ ∘ ζ_{ω_{m+r-1}}`. -/
def zfold (ω : ℕ → Fin 3) : ℕ → ℕ → FreeGroup APair → FreeGroup APair
  | _, 0, w => w
  | m, r + 1, w => zetaFree (ω m) (zfold ω (m + 1) r w)

theorem foldr_range'_eq (ω : ℕ → Fin 3) (w : FreeGroup APair) :
    ∀ r m, (List.range' m r).foldr (fun k w => zetaFree (ω k) w) w = zfold ω m r w := by
  intro r
  induction r with
  | zero => intro m; rfl
  | succ r ih => intro m; rw [List.range'_succ, List.foldr_cons, ih]; rfl

theorem chi_zfold (ω : ℕ → Fin 3) (w : FreeGroup APair) :
    ∀ r m κ, chi κ (zfold ω m (r + 1) w) = chi (BCD.killedBy (ω (m + r))) w := by
  intro r
  induction r with
  | zero => intro m κ; simp [zfold, chi_zetaFree]
  | succ r ih =>
    intro m κ
    rw [zfold, chi_zetaFree, ih (m + 1), show m + 1 + r = m + (r + 1) by omega]

/-- The bit of every stage. -/
theorem bit_zfold (ω : ℕ → Fin 3) (w : FreeGroup APair) (r m : ℕ) :
    Multiplicative.ofAdd (bit (evalFree ω m (zfold ω m (r + 1) w))) =
      chi (BCD.killedBy (ω (m + r))) w := by
  rw [zfold, bit_evalFree_zetaFree]
  cases r with
  | zero => rfl
  | succ r => rw [chi_zfold, show m + 1 + r = m + (r + 1) by omega]

theorem rootSwap_eq_of_bit {g : BinaryTreeAut} (h : Multiplicative.ofAdd (bit g) = 1) :
    rootSwap g = false := by
  unfold bit at h
  cases hg : rootSwap g
  · rfl
  · rw [hg] at h; exact absurd h (by decide)

/-! ### The structure of `g̃` -/

/-- `g` fixes level `r` and its sections there are `W` or `a W a`. -/
def Good (W : BinaryTreeAut) (r : ℕ) (g : BinaryTreeAut) : Prop :=
  ∀ x : List Bool, x.length = r → x <• g = x ∧ (sec g x = W ∨ sec g x = grigA * W * grigA)

theorem good_conj (W : BinaryTreeAut) (r : ℕ) (g : BinaryTreeAut) (hg : Good W r g) :
    Good W r (grigA * g * grigA) := by
  intro x hx
  cases x with
  | nil =>
    have := (hg [] hx).2
    rw [sec_nil] at this ⊢
    refine ⟨nil_smul _, ?_⟩
    rcases this with h | h
    · right; rw [h]
    · left; rw [h]
      simp only [← mul_assoc, grigA_mul_self, one_mul]
      rw [mul_assoc, grigA_mul_self, mul_one]
  | cons z x' =>
    have h1 := hg ((!z) :: x') (by simpa using hx)
    have hza : (z :: x') <• grigA = ((!z) :: x') := by
      rw [vertex_smul_grigA]; rfl
    have hza' : ((!z) :: x') <• grigA = (z :: x') := by
      rw [vertex_smul_grigA]; simp [grigAFun]
    refine ⟨?_, ?_⟩
    · rw [vertex_smul_mul, vertex_smul_mul, hza, h1.1, hza']
    · rw [sec_mul, sec_mul, sec_grigA_cons, hza, one_mul, vertex_smul_mul, hza, h1.1,
        sec_grigA_cons, mul_one]
      exact h1.2

theorem good_zfold (ω : ℕ → Fin 3) (j : ℕ) (w : FreeGroup APair)
    (hκ : chi (BCD.killedBy (ω (j - 1))) w = 1) :
    ∀ r m, m + r = j → Good (evalFree ω j w) r (evalFree ω m (zfold ω m r w)) := by
  intro r
  induction r with
  | zero =>
    intro m hm x hx
    rw [List.length_eq_zero_iff.mp hx, sec_nil]
    subst hm
    exact ⟨nil_smul _, Or.inl rfl⟩
  | succ r ih =>
    intro m hm
    have hg' := ih (m + 1) (by omega)
    set u := zfold ω (m + 1) r w
    have hswap : rootSwap (evalFree ω m (zetaFree (ω m) u)) = false := by
      apply rootSwap_eq_of_bit
      have := bit_zfold ω w r m
      rw [zfold] at this
      rw [this, show m + r = j - 1 by omega, hκ]
    obtain ⟨-, h0, h1⟩ := dec_evalFree ω m u
    rw [hswap] at h0 h1
    simp only [Bool.false_eq_true, if_false, mul_one] at h0 h1
    have hgood0 := good_conj _ r _ hg'
    intro x hx
    obtain ⟨y, x', rfl⟩ : ∃ y x', x = y :: x' := by
      cases x with
      | nil => simp at hx
      | cons y x' => exact ⟨y, x', rfl⟩
    have hx' : x'.length = r := by simpa using hx
    have hz : zfold ω m (r + 1) w = zetaFree (ω m) u := rfl
    rw [hz]
    cases y
    · obtain ⟨a1, a2⟩ := hgood0 x' hx'
      refine ⟨?_, ?_⟩
      · rw [cons_smul, hswap, h0, a1]; rfl
      · rw [sec_cons, h0]; exact a2
    · obtain ⟨a1, a2⟩ := hg' x' hx'
      refine ⟨?_, ?_⟩
      · rw [cons_smul, hswap, h1, a1]; rfl
      · rw [sec_cons, h1]; exact a2

/-! ### The free word for `a𝔠` and the tail condition -/

theorem tail_of_fr (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ) (i : Fin 3) :
    ∃ m, k < m ∧ ω m ≠ i := by
  obtain ⟨m, hm, h2, h1, -⟩ := hω (k + 1)
  have hD : 1 ≤ D := by omega
  have : k + 1 ≤ (k + 1) * D := Nat.le_mul_of_pos_right _ hD
  by_cases hi : i = 2
  · exact ⟨(k + 1) * D + m + 2, by omega, by rw [h1, hi]; decide⟩
  · exact ⟨(k + 1) * D + m, by omega, by rw [h2]; exact Ne.symm hi⟩

theorem ofAdd_two (x : ZMod 2) : Multiplicative.ofAdd x * Multiplicative.ofAdd x = 1 := by
  rw [← ofAdd_add]
  have : x + x = 0 := by fin_cases x <;> decide
  rw [this]; rfl

theorem exists_free_word (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j k : ℕ) (hk : D ∣ k)
    (v : List Bool) (hv : v ∈ vSet D ω j k) :
    ∃ w : FreeGroup APair, evalFree ω j w = grigA * cElt ω j v ∧
      chi .b w = 1 ∧ chi .d w = 1 ∧ chi .c w = Multiplicative.ofAdd 1 := by
  obtain ⟨U, hU⟩ := exists_word_hProd D ω hω j k hk v hv
  have hlen : (acWord U).length = 2 * (U.length + 1) := by simp [acWord]; ring
  refine ⟨conv (acWord U), ?_, ?_, ?_, ?_⟩
  · rw [evalFree_conv ω j _ _ hlen, evalWord_acWord ω j v U hU]
  all_goals
    rw [chi_conv _ _ _ hlen]
    simp only [acWord, List.count_append, List.count_reverse, List.count_cons, List.count_nil,
      bcdGen]
    simp
  · exact ofAdd_two _
  · exact ofAdd_two _
  · rw [mul_comm (Multiplicative.ofAdd _) (Multiplicative.ofAdd 1), mul_assoc, ofAdd_two,
      mul_one]

theorem gTilde_eq (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j : ℕ) (hj : 1 ≤ j)
    (v : List Bool) (w : FreeGroup APair) (hw : evalFree ω j w = grigA * cElt ω j v) :
    gTilde ω j v = evalFree ω 0 (zfold ω 0 j w) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have := (evalFree_zetaFree_congr_and_zetaHat_evalFree_eq_of_tail_ne ω n
    (fun i _ => tail_of_fr D ω hω n i)).2.2.2 0 (Nat.zero_le n)
      (fun k _ _ i _ => tail_of_fr D ω hω k i) w
  rw [List.Ico.zero_bot] at this
  unfold gTilde
  rw [← hw, this, List.range_eq_range', foldr_range'_eq]

/-! ### The printed claim fails at `ω = (201)^∞`, `D = 3`, `j = 3`, `k = 3` -/

end ConstrG

end ErschlerZheng
end

section
/-!
# The sequence `g_n` of (7.1) (Erschler–Zheng p. 35)

`g_n = ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{n-1}}(aγ)` with `γ = c` if `ω_{n-1} = 2`, else `b`: the letter `aγ`
has `χ_{κ_{n-1}} = 0`, so every substitution stage fixes level 1 (`ConstrG`), `g_n ∈ St(L_n)` with
sections `aγ` or `γa` at level `n`; cube independence is Lemma 5.6 (A13b); the germs are read from
the sections at level `n + 1`, which lie in `{1, a, γ_{𝔰^{n+1}ω}}`, with B4 (for `⟨c⟩`, B4 applied to
the string with the letters `1` and `2` exchanged, whose `b` is `c_ω`).
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrSeq

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG

/-! ### `g_n` as a substituted free-group word -/

/-! ### Exchanging the letters `1` and `2` -/

/-! ### Generators that differ -/

theorem sec_gen_replicate_true' (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    sec (gen ω γ) (List.replicate n true) = gen (shiftSeq ω n) γ := by
  induction n generalizing ω with
  | zero => rw [List.replicate_zero, sec_nil, shiftSeq_zero]
  | succ n ih =>
    rw [List.replicate_succ, sec_cons, sec_gen_true, ih, shiftSeq_shiftSeq]

theorem sec_gen_one_zero (ω : ℕ → Fin 3) (γ : BCD) (m : ℕ) :
    sec (gen ω γ) (List.replicate m true ++ [false]) = letterElt (ω m) γ := by
  rw [sec_append, sec_gen_replicate_true', sec_gen_false]
  simp [shiftSeq]

theorem grigA_ne_one : grigA ≠ 1 := by
  intro h
  have := rootSwap_grigA
  rw [h, rootSwap_one] at this
  exact Bool.noConfusion this

theorem letterValue_of_letterElt_eq {i : Fin 3} {γ γ' : BCD}
    (h : letterElt i γ = letterElt i γ') : letterValue i γ = letterValue i γ' := by
  unfold letterElt at h
  cases h1 : letterValue i γ <;> cases h2 : letterValue i γ' <;> simp_all
  · exact grigA_ne_one h.symm
  · exact grigA_ne_one h

theorem gen_c_not_mem (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (L : ℕ) :
    gen (shiftSeq ω L) .c ∉ ({1, grigA, gen (shiftSeq ω L) .b} : Set BinaryTreeAut) := by
  intro hmem
  rcases hmem with h | h | h
  · obtain ⟨m, hm, hne⟩ := tail_of_fr D ω hω L 1
    have := sec_gen_one_zero (shiftSeq ω L) .c (m - L)
    rw [h, sec_one] at this
    have hv : letterValue ((shiftSeq ω L) (m - L)) .c = false := by
      unfold letterElt at this
      split_ifs at this with hh
      · exact absurd this.symm grigA_ne_one
      · simpa using hh
    simp only [shiftSeq, show m - L + L = m by omega] at hv
    revert hv hne
    generalize ω m = i
    revert i
    decide
  · have h1 := rootSwap_gen (shiftSeq ω L) .c
    rw [h, rootSwap_grigA] at h1
    exact Bool.noConfusion h1
  · obtain ⟨m, hm, hne⟩ := tail_of_fr D ω hω L 0
    have h1 := sec_gen_one_zero (shiftSeq ω L) .c (m - L)
    have h2 := sec_gen_one_zero (shiftSeq ω L) .b (m - L)
    rw [h] at h1
    have hv := letterValue_of_letterElt_eq (h2.symm.trans h1)
    simp only [shiftSeq, show m - L + L = m by omega] at hv
    revert hv hne
    generalize ω m = i
    revert i
    decide

/-! ### The milestone -/

end ConstrSeq

end ErschlerZheng
end

section
/-!
# `B_j`: the points where `g_j` has a germ outside `ℋ^b`, for `ω_{j-1} = 2` (p. 55)

Pointwise germ criterion (from the proof of B4): for `g ∈ G_ω` and `x` in the orbit of `1^∞`,
`(g, x) ∈ ℋ^b` iff the sections of `g` along `x` are eventually `1` or eventually `b_{𝔰ⁿω}`.
The section of `g_j` at `u ∈ L_j` is `ac_{𝔰^jω}` if `u` has an even number of zeros and `ca`
otherwise; so along `x` the sections of `g_j` are eventually those of `c_{𝔰^jω}` along `𝔰^j x`
(first digit flipped in the even case), which are eventually `1` unless that ray is `1^∞`, and are
`c_{𝔰ⁿω} ∉ {1, b_{𝔰ⁿω}}` if it is.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrBj

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev B3Dev B4Dev ZetaDev ZetaHatDev
  ConstrIota ConstrG ConstrSeq

/-! ### The pointwise criterion -/

theorem mem_letterGerms_b_iff (ω : ℕ → Fin 3) (g : BinaryTreeAut) (hg : g ∈ grigorchuk ω)
    (x : Ray) (hx : x ∈ orbitOne ω) :
    (g, x) ∈ letterGerms ω .b ↔ (∃ N, ∀ n ≥ N, sec g (rayPrefix x n) = 1) ∨
      (∃ N, ∀ n ≥ N, sec g (rayPrefix x n) = gen (shiftSeq ω n) .b) := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
  have hL : IsAuxiliary (X := Ray) (grigorchuk ω) finitary := hA2.2.2 ω
  have hbo := oneRay_smul_gen ω .b
  have hsq : germ oneRay (gen ω .b) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← germ_mul hbo hbo, gen_mul_self, germ_one]
  have hgGL : g ∈ grigorchuk ω ⊔ finitary := mem_GL_of_G hg
  constructor
  · intro hmem
    obtain ⟨-, -, hmem⟩ := hmem
    dsimp only at hmem
    obtain ⟨hσL, hσ⟩ := transport_spec (exists_L_of_mem hL x hg)
    set σ := transport finitary x (x <• g)
    obtain ⟨h, hhGL, hhx, hhe, hho⟩ := hmem
    obtain ⟨hρL, hρ⟩ := transport_spec (exists_L_of_orbit hL hx)
    set ρ := transport finitary oneRay x
    have hk : x <• (g * σ⁻¹) = x := by rw [rsmul_mul, ← hσ, rsmul_inv_smul]
    have hK : oneRay <• (ρ * h * ρ⁻¹) = oneRay := conj_fix hρ hhx
    obtain ⟨N1, hN1⟩ := sec_conj_L hρL hρ hhx
    obtain ⟨N2, hN2⟩ := sec_eq_of_germ hhx hk hhe
    obtain ⟨N3, hN3⟩ := sec_mul_L hσL g x
    rcases mem_zpowers_sq hsq hho with e | e
    · obtain ⟨N4, hN4⟩ := sec_eq_of_germ hK (one_fix oneRay) (e.trans (germ_one _).symm)
      refine Or.inl ⟨max (max N1 N2) (max N3 N4), fun n hn => ?_⟩
      rw [← hN3 _ (by omega), ← hN2 _ (by omega), ← hN1 _ (by omega), ← rayPrefix_oneRay,
        hN4 _ (by omega), sec_one]
    · obtain ⟨N4, hN4⟩ := sec_eq_of_germ hK hbo e
      refine Or.inr ⟨max (max N1 N2) (max N3 N4), fun n hn => ?_⟩
      rw [← hN3 _ (by omega), ← hN2 _ (by omega), ← hN1 _ (by omega), ← rayPrefix_oneRay,
        hN4 _ (by omega), rayPrefix_oneRay, sec_gen_replicate_true]
  · intro hN
    obtain ⟨hσL, hσ⟩ := transport_spec (exists_L_of_mem hL x hg)
    set σ := transport finitary x (x <• g)
    obtain ⟨hρL, hρ⟩ := transport_spec (exists_L_of_orbit hL hx)
    set ρ := transport finitary oneRay x
    have hk : x <• (g * σ⁻¹) = x := by rw [rsmul_mul, ← hσ, rsmul_inv_smul]
    have hkGL : g * σ⁻¹ ∈ grigorchuk ω ⊔ finitary :=
      Subgroup.mul_mem _ hgGL (mem_GL_of_L (finitary.inv_mem hσL))
    refine ⟨hg, hx, g * σ⁻¹, hkGL, hk, rfl, ?_⟩
    have hK : oneRay <• (ρ * (g * σ⁻¹) * ρ⁻¹) = oneRay := conj_fix hρ hk
    obtain ⟨N1, hN1⟩ := sec_conj_L hρL hρ hk
    obtain ⟨N3, hN3⟩ := sec_mul_L hσL g x
    rcases hN with ⟨N, hN⟩ | ⟨N, hN⟩
    · have : germ oneRay (ρ * (g * σ⁻¹) * ρ⁻¹) = 1 := by
        rw [← germ_one oneRay]
        exact germ_eq_of_sec' hK (one_fix oneRay) (N := max N (max N1 N3)) fun n hn => by
          rw [rayPrefix_oneRay, hN1 n (by omega), hN3 n (by omega), hN n (by omega), sec_one]
      rw [this]; exact Subgroup.one_mem _
    · have : germ oneRay (ρ * (g * σ⁻¹) * ρ⁻¹) = germ oneRay (gen ω .b) :=
        germ_eq_of_sec' hK hbo (N := max N (max N1 N3)) fun n hn => by
          rw [rayPrefix_oneRay, hN1 n (by omega), hN3 n (by omega), hN n (by omega),
            sec_gen_replicate_true]
      rw [this]; exact Subgroup.mem_zpowers _

/-! ### The sections of `g_j` at level `j`, by parity -/

theorem sec_zfold_parity (ω : ℕ → Fin 3) (j : ℕ) (w : FreeGroup APair)
    (hκ : chi (BCD.killedBy (ω (j - 1))) w = 1) :
    ∀ r m, m + r = j → ∀ u : List Bool, u.length = r →
      sec (evalFree ω m (zfold ω m r w)) u =
        if Even (u.count false) then evalFree ω j w else grigA * evalFree ω j w * grigA := by
  intro r
  induction r with
  | zero =>
    intro m hm u hu
    rw [List.length_eq_zero_iff.mp hu, sec_nil]
    subst hm; simp; rfl
  | succ r ih =>
    intro m hm u hu
    have hg' := good_zfold ω j w hκ r (m + 1) (by omega)
    set u' := zfold ω (m + 1) r w
    have hswap : rootSwap (evalFree ω m (zetaFree (ω m) u')) = false := by
      apply rootSwap_eq_of_bit
      have := bit_zfold ω w r m
      rw [zfold] at this
      rw [this, show m + r = j - 1 by omega, hκ]
    obtain ⟨-, h0, h1⟩ := dec_evalFree ω m u'
    rw [hswap] at h0 h1
    simp only [Bool.false_eq_true, if_false, mul_one] at h0 h1
    have hz : zfold ω m (r + 1) w = zetaFree (ω m) u' := rfl
    rw [hz]
    obtain ⟨y, x', rfl⟩ : ∃ y x', u = y :: x' := by
      cases u with
      | nil => simp at hu
      | cons y x' => exact ⟨y, x', rfl⟩
    have hx' : x'.length = r := by simpa using hu
    cases y
    · rw [sec_cons _ false x', h0]
      cases x' with
      | nil =>
        have hr : r = 0 := by simpa using hx'.symm
        subst hr
        rw [sec_nil]
        simp only [List.count_singleton_self, Nat.not_even_one, if_false]
        subst hm
        rfl
      | cons z x'' =>
        have hfix := (hg' ((!z) :: x'') (by simpa using hx')).1
        have hza : (z :: x'') <• grigA = ((!z) :: x'') := by
          rw [vertex_smul_grigA]; rfl
        rw [sec_mul, sec_mul, sec_grigA_cons, hza, one_mul, vertex_smul_mul, hza, hfix,
          sec_grigA_cons, mul_one, ih (m + 1) (by omega) _ (by simpa using hx')]
        congr 1
        apply propext
        cases z <;> simp [List.count_cons, Nat.even_add_one, parity_simps]
    · rw [sec_cons _ true x', h1, ih (m + 1) (by omega) _ hx']
      simp [List.count_cons]

/-! ### The milestone -/

end ConstrBj

end ErschlerZheng
end

section
/-!
# Lemma 7.7: the sections of `𝔠^v_j` along the path `v` (Erschler–Zheng p. 38)

For a string `ω` and a word `v`, `kProd ω v = k_1 ⋯ k_{|v|}` with `k_i = 1` if `v_i = 1`,
`k_1 = a` if `v_1 = 0`, and `k_i = ι([b_{𝔰^{i-2}ω}, a], v_1 … v_{i-2})` if `v_i = 0`, `i ⩾ 2`;
`qElt ω v = kProd⁻¹ c_ω kProd`. When `v_1 = 1`, `hProd ω j v = kProd (𝔰^j ω) v` and
`cElt ω j v = qElt (𝔰^j ω) v`. One level down:
`qElt ω (1 :: v') = (s, qElt (𝔰ω) v')` and `qElt ω (0 :: v') = (qElt (𝔰ω) v', ω_0(c))`, where
`s = b a ω_0(c) a b` (`b = b_{𝔰ω}`) if `v'` starts with `0`, and `s = ω_0(c)` otherwise.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrC

open GrigBasic ZetaDev ConstrW ConstrIota ConstrH

/-- `k_i`. -/
def kElt (ω : ℕ → Fin 3) (v : List Bool) (i : ℕ) : BinaryTreeAut :=
  if v.getD (i - 1) true then 1
  else if i = 1 then grigA else iota ⁅gen (shiftSeq ω (i - 2)) .b, grigA⁆ (v.take (i - 2))

/-- `k_1 ⋯ k_{|v|}`. -/
def kProd (ω : ℕ → Fin 3) (v : List Bool) : BinaryTreeAut :=
  ((List.range v.length).map fun i => kElt ω v (i + 1)).prod

/-- `k_2 ⋯ k_{|v|}`. -/
def tailProd (ω : ℕ → Fin 3) (v : List Bool) : BinaryTreeAut :=
  ((List.range (v.length - 1)).map fun i => kElt ω v (i + 2)).prod

/-- `kProd⁻¹ c_ω kProd`. -/
def qElt (ω : ℕ → Fin 3) (v : List Bool) : BinaryTreeAut :=
  (kProd ω v)⁻¹ * gen ω .c * kProd ω v

theorem kProd_eq (ω : ℕ → Fin 3) (v : List Bool) : kProd ω v = kElt ω v 1 * tailProd ω v := by
  unfold kProd tailProd
  cases v with
  | nil => simp [kElt]
  | cons x v' =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp [List.map_map, Function.comp_def]

theorem iota_list_prod (l : List BinaryTreeAut) (u : List Bool) :
    iota l.prod u = (l.map fun g => iota g u).prod := by
  induction l with
  | nil => simp [iota_one]
  | cons g l ih => rw [List.prod_cons, ← iota_mul, ih, List.map_cons, List.prod_cons]

theorem kElt_cons_add_three (ω : ℕ → Fin 3) (x : Bool) (v' : List Bool) (i : ℕ) :
    kElt ω (x :: v') (i + 3) = iota (kElt (shiftSeq ω 1) v' (i + 2)) [x] := by
  unfold kElt
  have h1 : (x :: v').getD (i + 3 - 1) true = v'.getD (i + 2 - 1) true := by
    simp
  rw [h1, if_neg (show i + 3 ≠ 1 by omega), if_neg (show i + 2 ≠ 1 by omega)]
  split_ifs with h
  · rw [iota_one]
  · have e1 : shiftSeq ω (i + 3 - 2) = shiftSeq (shiftSeq ω 1) (i + 2 - 2) := by
      rw [shiftSeq_shiftSeq]; congr 1
    rw [e1, iota_iota]
    congr 1

theorem tailProd_cons (ω : ℕ → Fin 3) (x : Bool) (v' : List Bool) :
    tailProd ω (x :: v') = kElt ω (x :: v') 2 * iota (tailProd (shiftSeq ω 1) v') [x] := by
  unfold tailProd
  cases v' with
  | nil => simp [kElt, iota_one]
  | cons y v'' =>
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, iota_list_prod]
    congr 1
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    exact kElt_cons_add_three ω x (y :: v'') i

theorem kElt_one (ω : ℕ → Fin 3) (v : List Bool) :
    kElt ω v 1 = if v.head? = some false then grigA else 1 := by
  unfold kElt
  cases v with
  | nil => simp
  | cons x v => cases x <;> simp

theorem kElt_two (ω : ℕ → Fin 3) (x : Bool) (v' : List Bool) :
    kElt ω (x :: v') 2 = if v'.head? = some false then ⁅gen ω .b, grigA⁆ else 1 := by
  unfold kElt
  cases v' with
  | nil => simp
  | cons y v'' => cases y <;> simp [iota_nil, shiftSeq_zero]

theorem pairElt_inv (g h : BinaryTreeAut) : (pairElt g h)⁻¹ = pairElt g⁻¹ h⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [pairElt_mul, mul_inv_cancel, mul_inv_cancel, pairElt_one]

theorem iota_true_eq (g : BinaryTreeAut) : iota g [true] = pairElt 1 g := by
  simp [pairElt, iota_one]

theorem iota_false_eq (g : BinaryTreeAut) : iota g [false] = pairElt g 1 := by
  simp [pairElt, iota_one]

theorem gen_c_eq (ω : ℕ → Fin 3) :
    gen ω .c = pairElt (letterElt (ω 0) .c) (gen (shiftSeq ω 1) .c) := by
  have := gen_eq_pairElt ω 0 .c
  simpa [shiftSeq_zero] using this

theorem comm_b_eq (ω : ℕ → Fin 3) (hb : letterValue (ω 0) .b = true) :
    ⁅gen ω .b, grigA⁆ = pairElt (grigA * gen (shiftSeq ω 1) .b) (gen (shiftSeq ω 1) .b * grigA) :=
  eq_of_dec (dec_comm_b ω hb) (dec_pairElt _ _)

theorem b_conj_c (ω : ℕ → Fin 3) : gen ω .b * gen ω .c * gen ω .b = gen ω .c := by
  rw [gen_b_mul_c, gen_d_mul_b]

/-- The section off the path at depth `i + 1`. -/
def sSib (ω : ℕ → Fin 3) (v : List Bool) (i : ℕ) : BinaryTreeAut :=
  if v.getD i true = true ∧ v.getD (i + 1) true = false then
    gen (shiftSeq ω (i + 1)) .b * grigA * letterElt (ω i) .c * grigA * gen (shiftSeq ω (i + 1)) .b
  else letterElt (ω i) .c

theorem sSib_succ (ω : ℕ → Fin 3) (x : Bool) (v' : List Bool) (i : ℕ) :
    sSib ω (x :: v') (i + 1) = sSib (shiftSeq ω 1) v' i := by
  unfold sSib
  simp only [List.getD_cons_succ]
  rw [shiftSeq_shiftSeq]
  rfl

theorem pairElt_conj (g h e c : BinaryTreeAut) :
    (pairElt g h)⁻¹ * pairElt e c * pairElt g h = pairElt (g⁻¹ * e * g) (h⁻¹ * c * h) := by
  rw [pairElt_inv, pairElt_mul, pairElt_mul]

theorem conj_mul (g P C : BinaryTreeAut) : (g * P)⁻¹ * C * (g * P) = P⁻¹ * (g⁻¹ * C * g) * P := by
  group

/-- One level down. -/
theorem qElt_cons (ω : ℕ → Fin 3) (x : Bool) (v' : List Bool)
    (h1 : x = false → v'.head? ≠ some false)
    (h2 : x = true → v'.head? = some false → letterValue (ω 0) .b = true) :
    qElt ω (x :: v') = if x then pairElt (sSib ω (x :: v') 0) (qElt (shiftSeq ω 1) v')
      else pairElt (qElt (shiftSeq ω 1) v') (letterElt (ω 0) .c) := by
  have hk := kProd_eq ω (x :: v')
  have hk' := kProd_eq (shiftSeq ω 1) v'
  rw [tailProd_cons, ← mul_assoc] at hk
  unfold qElt
  rw [hk, hk', gen_c_eq ω, kElt_one, kElt_two, kElt_one]
  generalize tailProd (shiftSeq ω 1) v' = T
  cases x
  · have hh : v'.head? ≠ some false := h1 rfl
    have e1 : (if (false :: v').head? = some false then grigA else 1) = grigA := by simp
    rw [e1, if_neg hh, if_neg hh, mul_one, one_mul, iota_false_eq, conj_mul, grigA_inv,
      grigA_conj_pairElt, pairElt_conj]
    simp
  · have e1 : (if (true :: v').head? = some false then grigA else 1) = 1 := by simp
    rw [e1, one_mul, if_pos rfl]
    by_cases hh : v'.head? = some false
    · have hb := h2 rfl hh
      rw [if_pos hh, if_pos hh, comm_b_eq ω hb, iota_true_eq, pairElt_mul, pairElt_conj]
      have hv0 : v'.getD 0 true = false := by
        cases v' with
        | nil => simp at hh
        | cons y v'' => simp at hh; simp [hh]
      congr 1
      · simp only [sSib, List.getD_cons_zero, List.getD_cons_succ, hv0, and_self, if_true,
          Nat.zero_add, mul_one, mul_inv_rev, gen_inv, grigA_inv, mul_assoc]
      · simp only [mul_inv_rev, gen_inv, grigA_inv, mul_assoc]
        rw [← mul_assoc (gen (shiftSeq ω 1) .b) (gen (shiftSeq ω 1) .c),
          ← mul_assoc (gen (shiftSeq ω 1) .b * gen (shiftSeq ω 1) .c), b_conj_c]
    · rw [if_neg hh, if_neg hh]
      simp only [one_mul, mul_one]
      rw [iota_true_eq, pairElt_conj]
      have hv0 : ¬ (v'[0]?.getD true = false) := by
        cases v' with
        | nil => simp
        | cons y v'' => cases y <;> simp_all
      simp only [sSib, List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add]
      rw [List.getD_eq_getElem?_getD, if_neg (by simp [hv0])]
      simp

theorem qElt_spec : ∀ (v : List Bool) (ω : ℕ → Fin 3),
    (∀ i (h : i + 1 < v.length), v[i] = false → v[i + 1] = true) →
    (∀ i (h : i + 1 < v.length), v[i + 1] = false → letterValue (ω i) .b = true) →
    v <• qElt ω v = v ∧
      (∀ i (hi : i < v.length), sec (qElt ω v) (v.take i ++ [!v[i]]) = sSib ω v i) ∧
      sec (qElt ω v) v = gen (shiftSeq ω v.length) .c := by
  intro v
  induction v with
  | nil =>
    intro ω _ _
    refine ⟨nil_smul _, fun i hi => absurd hi (by simp), ?_⟩
    simp [qElt, kProd, sec_nil, shiftSeq_zero]
  | cons x v' ih =>
    intro ω H1 H2
    have H1' : ∀ i (h : i + 1 < v'.length), v'[i] = false → v'[i + 1] = true := by
      intro i h hf
      exact H1 (i + 1) (by simp; omega) hf
    have H2' : ∀ i (h : i + 1 < v'.length), v'[i + 1] = false →
        letterValue ((shiftSeq ω 1) i) .b = true := by
      intro i h hf
      exact H2 (i + 1) (by simp; omega) hf
    obtain ⟨ih1, ih2, ih3⟩ := ih (shiftSeq ω 1) H1' H2'
    have hq := qElt_cons ω x v'
      (by
        rintro rfl hh
        cases v' with
        | nil => simp at hh
        | cons y v'' =>
          simp at hh
          have := H1 0 (by simp) rfl
          simp [hh] at this)
      (by
        rintro rfl hh
        cases v' with
        | nil => simp at hh
        | cons y v'' =>
          simp at hh
          exact H2 0 (by simp) (by simp [hh]))
    have hsec : sec (qElt ω (x :: v')) [x] = qElt (shiftSeq ω 1) v' := by
      rw [hq]; cases x <;> simp [(dec_pairElt _ _).2.1, (dec_pairElt _ _).2.2]
    have hswap : rootSwap (qElt ω (x :: v')) = false := by
      rw [hq]; cases x <;> simp [(dec_pairElt _ _).1]
    refine ⟨?_, ?_, ?_⟩
    · rw [cons_smul, hswap, hsec, ih1]; simp
    · intro i hi
      cases i with
      | zero =>
        simp only [List.take_zero, List.nil_append, List.getElem_cons_zero]
        rw [hq]
        cases x
        · simp [(dec_pairElt _ _).2.2, sSib]
        · simp [(dec_pairElt _ _).2.1]
      | succ i =>
        simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
        rw [sec_cons, hsec, ih2 i (by simpa using hi), sSib_succ]
    · rw [sec_cons, hsec, ih3, shiftSeq_shiftSeq]
      simp [Nat.add_comm]

/-! ### The milestone -/

theorem hProd_eq_kProd (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) (hv : v.getD 0 true = true) :
    hProd ω j v = kProd (shiftSeq ω j) v := by
  unfold hProd kProd
  congr 1
  apply List.map_congr_left
  intro i _
  unfold hElt kElt
  simp only [Nat.add_sub_cancel]
  split_ifs with h1 h2
  · rfl
  · have : i = 0 := by omega
    subst this
    exact absurd hv h1
  · rw [shiftSeq_shiftSeq, show j + (i + 1) - 2 = i + 1 - 2 + j by omega]

theorem cElt_eq_qElt (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) (hv : v.getD 0 true = true) :
    cElt ω j v = qElt (shiftSeq ω j) v := by
  unfold cElt qElt
  rw [hProd_eq_kProd ω j v hv]

end ConstrC

end ErschlerZheng
end

section
/-!
# Fact 7.14: on level `n + D + 1`, every element of `𝔉_{j,n}` acts as `g_j` (p. 44)

`g̃^v_j` and `g_j` are `ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{j-1}}` of `a𝔠^v_j` and `ac_{𝔰^jω}`; both fix level `j`, and
at each vertex of level `j` their sections are `(a𝔠, ac)` or `(𝔠a, ca)` (`goodPair_zfold`). If `v`
begins with `1^p`, then `𝔠^v_j = qElt (𝔰^jω) v` and `c = qElt (𝔰^jω) 1^{|v|}` agree on level `p + 1`
(`qElt_agree`, one level at a time with `qElt_cons`); here `p = n - j + D`.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrFact714

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC

/-- No two consecutive zeros. -/
def H1 (v : List Bool) : Prop := ∀ i (h : i + 1 < v.length), v[i] = false → v[i + 1] = true

/-- `b` is not killed just before a zero. -/
def H2 (ω : ℕ → Fin 3) (v : List Bool) : Prop :=
  ∀ i (h : i + 1 < v.length), v[i + 1] = false → letterValue (ω i) .b = true

theorem vSet_props (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j k : ℕ) (hk : D ∣ k)
    (v : List Bool) (hv : v ∈ vSet D ω j k) :
    v.getD 0 true = true ∧ H1 v ∧ H2 (shiftSeq ω j) v := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  have hzero : ∀ t (ht : t < v.length), v[t] = false → j + (t + 1) ∈ frI D ω :=
    fun t ht hf => (getElem_of_mem_vSet D ω hω j k hk v hv t ht hf).2
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, -, rfl⟩ := hv
    have : 0 < D - j % D := by have := Nat.mod_lt j (show 0 < D by omega); omega
    obtain ⟨m, hm⟩ : ∃ m, D - j % D = m + 1 := ⟨D - j % D - 1, by omega⟩
    rw [hm]
    simp [List.replicate_succ]
  · intro i h hf
    by_contra hne
    have hf' : v[i + 1] = false := by simpa using hne
    have := frI_sep D ω hω (hzero i (by omega) hf) (hzero (i + 1) h hf') (by omega)
    omega
  · intro i h hf
    obtain ⟨-, -, hw, -⟩ := window_of_mem_frI D ω hω (hzero (i + 1) h hf)
    rw [show j + (i + 1 + 1) - 2 = j + i by omega] at hw
    simp only [shiftSeq]
    rw [Nat.add_comm i j]
    rcases hw with hw | hw <;> rw [hw] <;> decide

/-! ### `|1^∞ ∧ v|` -/

/-! ### Two substitution stacks side by side -/

/-! ### The milestone -/

end ConstrFact714

end ErschlerZheng
end

section
/-!
# (7.7): the index set of `𝔉_{j,n}`, injectivity of `v ↦ g̃^v_j`, and `|𝔉_{j,n}|` (p. 40)

Injectivity: the section of `g̃^v_j` at `1^j` is `a𝔠^v_j`, and `v ↦ 𝔠^v_j` is injective: where two
words first differ, one element has the path section `qElt` (no root swap, `≠ 1`) and the other a
sibling section (`1`, or one that swaps level 1). The count: the prefix `1^{n-j+D}` fixes the first
`n - j + j̄` digits of `u ∈ W^{j+D-j̄}_{2k_n}`, a multiple of `D`.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrF8

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC
  ConstrFact714

/-! ### Clause 1 -/

/-! ### Injectivity of `v ↦ 𝔠^v_j` -/

/-! ### The section of `g̃^v_j` at `1^j` -/

/-! ### The count -/

end ConstrF8

end ErschlerZheng
end

section
/-!
# Remark 7.8: `𝔠^v_j` fixes `1^∞` and every vertex `1^m 0` (Erschler–Zheng p. 39)

From Lemma 7.7: with `d` the position of the first digit `0` of `v`, `𝔠^v_j` fixes the prefixes
of `v` and their siblings, and has trivial section at `1^{d+1}`, the sibling at depth `d + 1`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrRemark78

open GrigBasic RayBasic ConstrH

end ConstrRemark78

end ErschlerZheng
end

section
/-!
# Lemma 7.16: displacement by `g̃^v_j` (Erschler–Zheng p. 44)

`p = n - j + D`. Every `v` in the index set of `𝔉_{j,n}` begins with `1^{p+2}`: `j + p + 1 = n + D + 1`
and `n + D + 2` are `≡ 1, 2 (mod D)`, never in `I_ω`. At the vertex `x_1…x_j` the sections of
`(g̃, g_j)` are `(a𝔠, ac)` or `(𝔠a, ca)`; let `w = 𝔰^j x` (resp. `(𝔰^j x)·a`).
If `|𝔰^{j+1}x ∧ 𝔰v| < p`, `w` leaves `1^∞` at depth `⩽ p + 1`, where `𝔠` and `c` have the same
sections, so `x·g̃ = x·g_j` and Lemma 7.5 at level `j` gives `2^j·3`. Otherwise Lemma 7.5 at the
level where `w` leaves `v` (a section `1`, `a` or `bab`) or at `v` itself (`c`).
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrLemma716

open GrigBasic RayBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC
  ConstrFact714 ConstrF8 ConstrRemark78

/-! ### Word lengths -/

/-! ### Common prefixes -/

/-! ### `v` begins with `1^{p+2}` -/

/-! ### `qElt` on a ray leaving the path -/

/-! ### The milestone -/

end ConstrLemma716

end ErschlerZheng
end

section
/-!
# (7.16): the points where `g̃^v_j` has a germ outside `ℋ^b` (Erschler–Zheng pp. 45–46)

As for `B_j` (`ConstrBj`), with `𝔠 = 𝔠^v_j` in place of `c`: the section of `g̃` at `u ∈ L_j` is
`a𝔠` (even number of zeros in `u`) or `𝔠a`, so along `x` the sections are eventually those of `𝔠`
along the effective ray `x'` below level `j`. Along `v1^∞` these are `c_{𝔰ⁿω}`; along any other
ray they are eventually `1` or `b_{𝔰ⁿω}` (leaving `v` at a sibling with section `1`, `a` or `bab`, or
following `v` and leaving `1^∞` afterwards). So the bad points are the `p (𝔰v) 1^∞`, `|p| = j + 1`
with an odd number of zeros: `2^j` of them, with last zero at `j + |v|` (Fact 7.3).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrG6

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev B3Dev B4Dev ZetaDev ZetaHatDev
  ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC ConstrFact714 ConstrF8 ConstrRemark78
  ConstrBj ConstrLemma716

/-- Eventually `1` or eventually `b_{𝔰^{s}ω}` along a ray, for a family of sections. -/
def EvGood (ω : ℕ → Fin 3) (f : ℕ → BinaryTreeAut) : Prop :=
  (∃ N, ∀ t ≥ N, f t = 1) ∨ (∃ N, ∀ t ≥ N, f t = gen (shiftSeq ω t) .b)

theorem evGood_shift (ω : ℕ → Fin 3) (g : BinaryTreeAut) (z : Ray) (L : ℕ)
    (h : EvGood (shiftSeq ω L) fun s => sec (sec g (rayPrefix z L)) (rayPrefix (shiftRay z L) s)) :
    EvGood ω fun t => sec g (rayPrefix z t) := by
  have hsplit : ∀ t ≥ L, sec g (rayPrefix z t) =
      sec (sec g (rayPrefix z L)) (rayPrefix (shiftRay z L) (t - L)) := by
    intro t ht
    rw [show t = L + (t - L) by omega, rayPrefix_add, sec_append]
    simp
  rcases h with ⟨N, hN⟩ | ⟨N, hN⟩
  · left
    refine ⟨N + L, fun t ht => ?_⟩
    have := hN (t - L) (by omega)
    beta_reduce at this ⊢
    rw [hsplit t (by omega), this]
  · right
    refine ⟨N + L, fun t ht => ?_⟩
    have := hN (t - L) (by omega)
    beta_reduce at this ⊢
    rw [hsplit t (by omega), this, shiftSeq_shiftSeq, show t - L + L = t by omega]

/-- Sections of `b a b` along any ray are eventually `1` or `b`. -/
theorem evGood_bab (ω : ℕ → Fin 3) (r : Ray) :
    EvGood ω fun s => sec (gen ω .b * grigA * gen ω .b) (rayPrefix r s) := by
  have hs : ∀ s ≥ 1, sec (gen ω .b * grigA * gen ω .b) (rayPrefix r s) =
      sec (gen ω .b) (rayPrefix r s) * sec (gen ω .b) (rayPrefix (r <• gen ω .b <• grigA) s) := by
    intro s hs
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hA : sec grigA (rayPrefix r (s' + 1) <• gen ω .b) = 1 := by
      rw [rayPrefix_succ, cons_smul]; exact sec_grigA_cons _ _
    rw [sec_mul, sec_mul, hA, mul_one, vertex_smul_mul, rayPrefix_smul, rayPrefix_smul]
  rcases sec_gen_along ω .b r with ⟨N1, h1⟩ | h1 <;>
    rcases sec_gen_along ω .b (r <• gen ω .b <• grigA) with ⟨N2, h2⟩ | h2
  · left; refine ⟨N1 + N2 + 1, fun t ht => ?_⟩
    beta_reduce
    rw [hs t (by omega), h1 t (by omega), h2 t (by omega), one_mul]
  · right; refine ⟨N1 + 1, fun t ht => ?_⟩
    beta_reduce
    rw [hs t (by omega), h1 t (by omega), h2, rayPrefix_oneRay, sec_gen_replicate_true, one_mul]
  · right; refine ⟨N2 + 1, fun t ht => ?_⟩
    beta_reduce
    rw [hs t (by omega), h2 t (by omega), h1, rayPrefix_oneRay, sec_gen_replicate_true, mul_one]
  · left; refine ⟨1, fun t ht => ?_⟩
    beta_reduce
    rw [hs t (by omega), h2, h1, rayPrefix_oneRay, sec_gen_replicate_true, gen_mul_self]

theorem evGood_sSib (ω : ℕ → Fin 3) (v : List Bool) (i : ℕ) (r : Ray) :
    EvGood (shiftSeq ω (i + 1)) fun s => sec (sSib ω v i) (rayPrefix r s) := by
  unfold sSib letterElt
  split_ifs
  · have e : gen (shiftSeq ω (i + 1)) .b * grigA * grigA * grigA * gen (shiftSeq ω (i + 1)) .b =
        gen (shiftSeq ω (i + 1)) .b * grigA * gen (shiftSeq ω (i + 1)) .b := by
      simp [mul_assoc, grigA_mul_grigA_mul]
    rw [e]; exact evGood_bab _ r
  · have e : gen (shiftSeq ω (i + 1)) .b * grigA * 1 * grigA * gen (shiftSeq ω (i + 1)) .b = 1 := by
      simp [mul_assoc, grigA_mul_grigA_mul, gen_mul_self]
    rw [e]; left; exact ⟨0, fun t _ => by beta_reduce; exact sec_one _⟩
  · left; refine ⟨1, fun t ht => ?_⟩
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    beta_reduce
    rw [rayPrefix_succ, sec_grigA_cons]
  · left; exact ⟨0, fun t _ => by beta_reduce; exact sec_one _⟩

/-- Sections of `qElt ω v` along a ray other than `v1^∞` are eventually `1` or `b`. -/
theorem evGood_qElt (ω : ℕ → Fin 3) (v : List Bool) (hv1 : H1 v) (hv2 : H2 ω v) (z : Ray)
    (hz : z ≠ prepend v oneRay) : EvGood ω fun t => sec (qElt ω v) (rayPrefix z t) := by
  obtain ⟨s1, s2, s3⟩ := qElt_spec v ω hv1 hv2
  by_cases hleave : ∃ i, ∃ hi : i < v.length, z i ≠ v[i]
  · classical
    obtain ⟨i, ⟨hi, hzi⟩, hmin⟩ : ∃ i, (∃ hi : i < v.length, z i ≠ v[i]) ∧
        ∀ t < i, ¬ ∃ ht : t < v.length, z t ≠ v[t] :=
      ⟨Nat.find hleave, Nat.find_spec hleave, fun t ht => Nat.find_min hleave ht⟩
    have hbefore : ∀ t < i, ∀ ht : t < v.length, z t = v[t] := by
      intro t htm ht
      by_contra hne
      exact hmin t htm ⟨ht, hne⟩
    have hzi' : z i = !v[i] := by revert hzi; cases z i <;> cases v[i] <;> simp
    have hpre : rayPrefix z (i + 1) = v.take i ++ [!v[i]] := by
      apply List.ext_getElem
      · simp [length_rayPrefix]; omega
      · intro t h1 h2
        rw [getElem_rayPrefix]
        simp only [length_rayPrefix] at h1
        by_cases ht : t < i
        · rw [List.getElem_append_left (by simp only [List.length_take]; omega), List.getElem_take,
            hbefore t ht]
        · have : t = i := by omega
          subst this
          rw [List.getElem_append_right (by simp only [List.length_take]; omega)]
          simp only [List.length_take, min_eq_left (le_of_lt hi), Nat.sub_self,
            List.getElem_cons_zero, hzi']
    apply evGood_shift ω _ z (i + 1)
    rw [hpre, s2 i hi]
    exact evGood_sSib ω v i _
  · push Not at hleave
    have hpre : rayPrefix z v.length = v := by
      apply List.ext_getElem
      · simp [length_rayPrefix]
      · intro t h1 h2; rw [getElem_rayPrefix, hleave t h2]
    apply evGood_shift ω _ z v.length
    rw [hpre, s3]
    rcases sec_gen_along (shiftSeq ω v.length) .c (shiftRay z v.length) with ⟨N, hN⟩ | h
    · left; exact ⟨N, fun t ht => by beta_reduce; exact hN t ht⟩
    · exfalso; apply hz
      rw [← prepend_rayPrefix_shiftRay z v.length, hpre, h]

end ConstrG6

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open ErschlerZheng.ConstrG6
open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev B3Dev B4Dev ZetaDev ZetaHatDev
  ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC ConstrFact714 ConstrF8 ConstrRemark78
  ConstrBj ConstrLemma716
theorem solution (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n, D ∣ n → ∀ j, 1 ≤ j → ω (j - 1) = 2 → n < j + k n →
      j ≤ n → ∀ v ∈ vSet D ω j (2 * k n), n - j + D ≤ commonPrefixLength v oneRay →
        {x | x ∈ orbitOne ω ∧ (gTilde ω j v, x) ∉ letterGerms ω .b} =
            {x | ∃ p : List Bool, p.length = j + 1 ∧ Odd (j + 1 + p.count true) ∧
              x = prepend (p ++ (v.drop 1).take (D - j % D + 2 * k n - 1) ++
                List.replicate (frM D ω (ellIndex D (2 * k n) j) + 2) true ++ [false]) oneRay} ∧
          {x | x ∈ orbitOne ω ∧ (gTilde ω j v, x) ∉ letterGerms ω .b}.ncard = 2 ^ j ∧
          ∀ x ∈ {x | x ∈ orbitOne ω ∧ (gTilde ω j v, x) ∉ letterGerms ω .b},
            c * 2 ^ (j + 2 * k n) ≤ (schreierDist ω oneRay x : ℝ) ∧
              (schreierDist ω oneRay x : ℝ) ≤ C * 2 ^ (j + 2 * k n) := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
  have horb : ∀ x : Ray, x ∈ orbitOne ω ↔ ∀ᶠ n in Filter.atTop, x n = oneRay n := by
    intro x
    unfold orbitOne
    rw [(hA2.2.1 ω oneRay).1]
    rfl
  refine ⟨1, by norm_num, (2 : ℝ) ^ (2 * D), by positivity, ?_⟩
  intro n hn j hj1 hj hjn hjn' v hv hv'
  have hkn := hk.2 n (by omega) hn
  have h2k : D ∣ 2 * k n := Dvd.dvd.mul_left hkn.2 2
  obtain ⟨hv0, hv1, hv2⟩ := vSet_props D ω hω j _ h2k v hv
  have hlen := length_of_mem_vSet D ω j _ v hv
  have hm := (frM_spec D ω hω (ellIndex D (2 * k n) j)).1
  have hjD : j % D < D := Nat.mod_lt _ (by omega)
  have hv0' : v[0]'(by omega) = true := by
    rw [List.getD_eq_getElem _ _ (by omega)] at hv0; exact hv0
  obtain ⟨w1, hw1, hb1, -, -⟩ := exists_free_word D ω hω j (2 * k n) h2k v hv
  have hg1 := gTilde_eq D ω hω j hj1 v w1 hw1
  have hκ1 : chi (BCD.killedBy (ω (j - 1))) w1 = 1 := by rw [hj]; exact hb1
  have hmemG : gTilde ω j v ∈ grigorchuk ω := by rw [hg1]; exact evalFree_zero_mem ω _
  set 𝔠 := cElt ω j v
  have hq : 𝔠 = qElt (shiftSeq ω j) v := cElt_eq_qElt ω j v hv0
  -- the sections at level `j`, by parity
  have hpar : ∀ u : List Bool, u.length = j → sec (gTilde ω j v) u =
      if Even (u.count false) then grigA * 𝔠 else 𝔠 * grigA := by
    intro u hu
    rw [hg1, sec_zfold_parity ω j w1 hκ1 j 0 (by omega) u hu, hw1]
    split_ifs
    · rfl
    · simp [mul_assoc, grigA_mul_grigA_mul]
  let x' : Ray → Ray := fun x i =>
    if i = 0 ∧ Even ((rayPrefix x j).count false) then !x j else x (i + j)
  have hsecx : ∀ x : Ray, ∀ n ≥ j + 1, sec (gTilde ω j v) (rayPrefix x n) =
      sec 𝔠 (rayPrefix (x' x) (n - j)) := by
    intro x n hn
    obtain ⟨t, rfl⟩ : ∃ t, n = j + (t + 1) := ⟨n - j - 1, by omega⟩
    rw [rayPrefix_add, sec_append, hpar _ (length_rayPrefix _ _),
      show j + (t + 1) - j = t + 1 by omega, rayPrefix_succ, rayPrefix_succ]
    have hsh : shiftRay (x' x) 1 = shiftRay (shiftRay x j) 1 := by
      funext i; simp [x', shiftRay, Nat.add_comm, Nat.add_left_comm]
    rw [hsh]
    split_ifs with he
    · rw [sec_mul, sec_grigA_cons, one_mul]
      congr 1
      rw [vertex_smul_grigA]
      simp [grigAFun, x', he, shiftRay]
    · rw [sec_mul, cons_smul, sec_grigA_cons, mul_one]
      congr 1
      simp [x', he, shiftRay]
  have hrp : ∀ t ≥ v.length, rayPrefix (prepend v oneRay) t = v ++ List.replicate (t - v.length) true := by
    intro t ht
    apply List.ext_getElem
    · simp [length_rayPrefix]; omega
    · intro i h1 h2
      rw [getElem_rayPrefix]
      by_cases hi : i < v.length
      · rw [List.getElem_append_left hi]; simp [prepend, hi]
      · rw [List.getElem_append_right (by omega)]; simp [prepend, hi, oneRay]
  -- `(g̃, x) ∉ ℋ^b` iff the effective ray is `v1^∞`
  have hkey : ∀ x ∈ orbitOne ω, ((gTilde ω j v, x) ∉ letterGerms ω .b ↔
      x' x = prepend v oneRay) := by
    intro x hx
    rw [mem_letterGerms_b_iff ω _ hmemG x hx]
    constructor
    · intro hnot
      by_contra hne
      apply hnot
      rcases evGood_qElt (shiftSeq ω j) v hv1 hv2 (x' x) hne with ⟨N, hN⟩ | ⟨N, hN⟩
      · left; refine ⟨N + j + 1, fun n hn => ?_⟩
        have := hN (n - j) (by omega)
        beta_reduce at this
        rw [hsecx x n (by omega), hq, this]
      · right; refine ⟨N + j + 1, fun n hn => ?_⟩
        have := hN (n - j) (by omega)
        beta_reduce at this
        rw [hsecx x n (by omega), hq, this, shiftSeq_shiftSeq, show n - j + j = n by omega]
    · intro h hin
      have s3 : sec (qElt (shiftSeq ω j) v) v = gen (shiftSeq (shiftSeq ω j) v.length) .c := by
        rw [← hq, shiftSeq_shiftSeq, Nat.add_comm]
        exact (smul_cElt_eq_self_and_sec_cElt_eq D ω hω j (2 * k n) h2k v hv).2.2.2
      have hc : ∀ n ≥ j + v.length + 1, sec (gTilde ω j v) (rayPrefix x n) =
          gen (shiftSeq ω n) .c := by
        intro n hn
        rw [hsecx x n (by omega), h, hrp _ (by omega), sec_append, hq, s3,
          sec_gen_replicate_true', shiftSeq_shiftSeq, shiftSeq_shiftSeq]
        congr 2; omega
      rcases hin with ⟨N, hN⟩ | ⟨N, hN⟩
      · apply gen_c_not_mem D ω hω (N + j + v.length + 1)
        rw [← hc _ (by omega), hN _ (by omega)]; simp
      · apply gen_c_not_mem D ω hω (N + j + v.length + 1)
        rw [← hc _ (by omega), hN _ (by omega)]; simp
  -- the tail of the bad rays is `𝔰v`
  have hT : (v.drop 1).take (D - j % D + 2 * k n - 1) ++
      List.replicate (frM D ω (ellIndex D (2 * k n) j) + 2) true ++ [false] = v.drop 1 := by
    obtain ⟨u, ⟨hu, -⟩, hveq⟩ := hv
    obtain ⟨d, hd⟩ : ∃ d, D - j % D = d + 1 := ⟨D - j % D - 1, by omega⟩
    rw [hveq, hd, List.replicate_succ]
    simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.append_assoc]
    rw [show d + 1 + 2 * k n - 1 = (List.replicate d true).length + 2 * k n by simp,
      List.take_append, List.take_of_length_le (by simp), Nat.add_sub_cancel_left,
      List.take_left' hu]
    simp

  -- the set
  have hset : {x | x ∈ orbitOne ω ∧ (gTilde ω j v, x) ∉ letterGerms ω .b} =
      {x | ∃ p : List Bool, p.length = j + 1 ∧ Odd (j + 1 + p.count true) ∧
        x = prepend (p ++ v.drop 1) oneRay} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hnot⟩
      have h1 := (hkey x hx).mp hnot
      refine ⟨rayPrefix x (j + 1), length_rayPrefix _ _, ?_, ?_⟩
      · have h0 := congrFun h1 0
        simp only [x', prepend] at h0
        rw [dif_pos (by omega), hv0'] at h0
        rw [rayPrefix_add, List.count_append]
        have hs1 : rayPrefix (shiftRay x j) 1 = [x j] := by simp [rayPrefix, shiftRay]
        rw [hs1]
        have hc1 : (rayPrefix x j).count true + (rayPrefix x j).count false = j := by
          rw [List.count_true_add_count_false, length_rayPrefix]
        by_cases he : Even ((rayPrefix x j).count false)
        · simp only [true_and, he, if_true] at h0
          have hxj : x j = false := by simpa using h0
          rw [hxj]
          simp
          rw [Nat.odd_iff]; rw [Nat.even_iff] at he; omega
        · simp only [he, and_false, if_false, Nat.zero_add] at h0
          rw [h0]
          simp
          rw [Nat.odd_iff]; rw [Nat.not_even_iff] at he; omega
      · have hshift : shiftRay x (j + 1) = prepend (v.drop 1) oneRay := by
          funext i
          have := congrFun h1 (i + 1)
          simp only [x'] at this
          rw [if_neg (by omega)] at this
          simp only [shiftRay]
          rw [show i + (j + 1) = i + 1 + j by omega, this]
          obtain ⟨b, t, hbt⟩ : ∃ b t, v = b :: t := by
            cases v with
            | nil => simp at hlen
            | cons b t => exact ⟨b, t, rfl⟩
          rw [hbt]
          simp only [prepend, List.length_cons, List.drop_succ_cons, List.drop_zero]
          by_cases hi : i < t.length
          · rw [dif_pos (by omega), dif_pos hi]; rfl
          · rw [dif_neg (by omega), dif_neg hi]; congr 1; omega
        conv_lhs => rw [← prepend_rayPrefix_shiftRay x (j + 1), hshift]
        rw [prepend_append]
    · rintro ⟨p, hp, hodd, rfl⟩
      have hx : prepend (p ++ v.drop 1) oneRay ∈ orbitOne ω := by
        rw [horb]
        refine Filter.eventually_atTop.mpr ⟨(p ++ v.drop 1).length, fun n hn => ?_⟩
        unfold prepend
        rw [dif_neg (by omega)]
        rfl
      refine ⟨hx, (hkey _ hx).mpr ?_⟩
      have hpre : rayPrefix (prepend (p ++ v.drop 1) oneRay) j = p.take j := by
        apply List.ext_getElem
        · simp [length_rayPrefix, hp]
        · intro i h1 h2
          rw [getElem_rayPrefix]
          simp only [length_rayPrefix] at h1
          unfold prepend
          rw [dif_pos (by simp; omega), List.getElem_append_left (by omega), List.getElem_take]
      have hpj : prepend (p ++ v.drop 1) oneRay j = p[j]'(by omega) := by
        unfold prepend
        rw [dif_pos (by simp; omega), List.getElem_append_left (by omega)]
      funext i
      simp only [x']
      by_cases h0 : i = 0
      · subst h0
        simp only [Nat.zero_add, true_and]
        rw [hpre, hpj]
        have hsplit : p = p.take j ++ [p[j]'(by omega)] := by
          conv_lhs => rw [← List.take_append_drop j p]
          congr 1
          rw [List.drop_eq_getElem_cons (by omega)]
          simp [List.drop_eq_nil_of_le (show p.length ≤ j + 1 by omega)]
        have hc1 : p.count true + p.count false = j + 1 := by
          rw [List.count_true_add_count_false, hp]
        rw [hsplit] at hodd hc1
        simp only [List.count_append] at hodd hc1
        have hpv : prepend v oneRay 0 = true := by simp [prepend, hv0', show 0 < v.length by omega]
        rw [hpv]
        revert hodd hc1
        generalize p[j]'(by omega) = e
        generalize (p.take j).count true = a
        generalize (p.take j).count false = b
        intro hodd hc1
        cases e <;> simp [Nat.odd_iff, Nat.even_iff] at hodd hc1 ⊢ <;> omega
      · rw [if_neg (by tauto)]
        simp only [prepend]
        by_cases hiv : i < v.length
        · rw [dif_pos (by simp [hp]; omega), dif_pos hiv, List.getElem_append_right (by omega),
            List.getElem_drop]
          congr 1; omega
        · rw [dif_neg (by simp [hp]; omega), dif_neg hiv]
          simp [oneRay]
  have hT' : ∀ p : List Bool, p ++ (v.drop 1).take (D - j % D + 2 * k n - 1) ++
      List.replicate (frM D ω (ellIndex D (2 * k n) j) + 2) true ++ [false] = p ++ v.drop 1 := by
    intro p; rw [List.append_assoc, List.append_assoc, ← List.append_assoc _ _ [false], hT]
  have hset2 : {x | ∃ p : List Bool, p.length = j + 1 ∧ Odd (j + 1 + p.count true) ∧
      x = prepend (p ++ (v.drop 1).take (D - j % D + 2 * k n - 1) ++
        List.replicate (frM D ω (ellIndex D (2 * k n) j) + 2) true ++ [false]) oneRay} =
      {x | ∃ p : List Bool, p.length = j + 1 ∧ Odd (j + 1 + p.count true) ∧
        x = prepend (p ++ v.drop 1) oneRay} := by
    ext x; simp only [Set.mem_setOf_eq, hT']
  refine ⟨hset.trans hset2.symm, ?_, ?_⟩
  · -- the count
    rw [hset]
    have himg : {x | ∃ p : List Bool, p.length = j + 1 ∧ Odd (j + 1 + p.count true) ∧
        x = prepend (p ++ v.drop 1) oneRay} = (fun p => prepend (p ++ v.drop 1) oneRay) ''
          {p : List Bool | p.length = j + 1 ∧ Odd (j + 1 + p.count true)} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨p, h1, h2, rfl⟩; exact ⟨p, ⟨h1, h2⟩, rfl⟩
      · rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨p, h1, h2, rfl⟩
    rw [himg, Set.InjOn.ncard_image]
    · have hP : {p : List Bool | p.length = j + 1 ∧ Odd (j + 1 + p.count true)} =
          (fun q => q ++ [decide (Even (j + 1 + q.count true))]) '' {q | q.length = j} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_image]
        constructor
        · rintro ⟨hp, hodd⟩
          refine ⟨p.take j, by simp; omega, ?_⟩
          have hsplit : p = p.take j ++ [p[j]'(by omega)] := by
            conv_lhs => rw [← List.take_append_drop j p]
            congr 1
            rw [List.drop_eq_getElem_cons (by omega)]
            simp [List.drop_eq_nil_of_le (show p.length ≤ j + 1 by omega)]
          conv_rhs => rw [hsplit]
          congr 2
          rw [hsplit, List.count_append] at hodd
          revert hodd
          generalize p[j]'(by omega) = e
          cases e <;> simp [Nat.odd_iff, Nat.even_iff] <;> omega
        · rintro ⟨q, hq, rfl⟩
          refine ⟨by simp [hq], ?_⟩
          rw [List.count_append]
          by_cases he : Even (j + 1 + q.count true)
          · simp only [he, decide_true, List.count_singleton_self]
            rw [Nat.odd_iff]; rw [Nat.even_iff] at he; omega
          · simp only [he, decide_false]
            simp only [List.count_cons, List.count_nil]
            simp
            rw [Nat.odd_iff]; rw [Nat.not_even_iff] at he; omega
      rw [hP, Set.InjOn.ncard_image]
      · rw [← Nat.card_coe_set_eq]
        have : Nat.card ↥{q : List Bool | q.length = j} = Nat.card (List.Vector Bool j) := rfl
        rw [this, Nat.card_eq_fintype_card, card_vector, Fintype.card_bool]
      · intro q1 hq1 q2 hq2 h
        have := congrArg (List.take j) h
        simp only [Set.mem_setOf_eq] at hq1 hq2
        simpa [List.take_append_of_le_length, hq1, hq2] using this
    · intro p1 hp1 p2 hp2 h
      simp only [Set.mem_setOf_eq] at hp1 hp2
      have := congrArg (fun y => rayPrefix y (j + 1)) h
      simp only [prepend_append] at this
      rwa [← hp1.1, rayPrefix_prepend, hp1.1, ← hp2.1, rayPrefix_prepend] at this
  · -- the distances (Fact 7.3)
    rw [hset]
    rintro x ⟨p, hp, -, rfl⟩
    set L := p ++ v.drop 1 with hL
    have hLlen : L.length = j + v.length := by simp [hL, hp]; omega
    have hvlast : v[v.length - 1]'(by omega) = false := by
      have hgl := ((ncard_wSet_and_ncard_vSet_and_getLast_eq_false D ω hω).2 j _ h2k).2 v hv
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hgl
      simpa using hgl
    have hLlast : L[L.length - 1]'(by omega) = false := by
      simp only [hL]
      rw [List.getElem_append_right (by simp; omega), List.getElem_drop]
      rw [← hvlast]; congr 1; simp; omega
    have hx0 : prepend L oneRay (L.length - 1) = false := by
      unfold prepend; rw [dif_pos (by omega)]; exact hLlast
    have hmax : maxZeroIndex (prepend L oneRay) = L.length := by
      unfold maxZeroIndex
      apply IsGreatest.csSup_eq
      refine ⟨⟨by omega, hx0⟩, fun m ⟨hm1, hm2⟩ => ?_⟩
      by_contra hlt
      unfold prepend at hm2
      rw [dif_neg (by omega)] at hm2
      exact Bool.noConfusion hm2
    have hcof : IsCofinal (prepend L oneRay) :=
      Filter.eventually_atTop.mpr ⟨L.length, fun m hm => by
        unfold prepend; rw [dif_neg (by omega)]; rfl⟩
    have hne : prepend L oneRay ≠ oneRay := by
      intro h; rw [h] at hx0; exact Bool.noConfusion hx0
    have hcof1 : IsCofinal oneRay := Filter.Eventually.of_forall fun _ => rfl
    obtain ⟨d1, d2⟩ := two_pow_le_schreierDist_oneRay_and_le_of_isCofinal_of_ne ω _ hcof hne
    have hsymm : schreierDist ω oneRay (prepend L oneRay) = schreierDist ω (prepend L oneRay) oneRay := by
      have e1 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω oneRay (prepend L oneRay) hcof1 hcof
      have e2 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω (prepend L oneRay) oneRay hcof hcof1
      have : (schreierDist ω oneRay (prepend L oneRay) : ℤ) =
          schreierDist ω (prepend L oneRay) oneRay := by rw [e1, e2, abs_sub_comm]
      exact_mod_cast this
    rw [hsymm, hmax, hLlen] at *
    rw [hmax, hLlen] at d1 d2
    constructor
    · have : 2 ^ (j + 2 * k n) ≤ schreierDist ω (prepend L oneRay) oneRay :=
        le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) d1
      rw [one_mul]; exact_mod_cast this
    · have : schreierDist ω (prepend L oneRay) oneRay ≤ 2 ^ (2 * D) * 2 ^ (j + 2 * k n) := by
        refine d2.trans (le_trans (Nat.sub_le _ _) ?_)
        rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast this
end
