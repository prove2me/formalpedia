-- Prove2me | solution 1 for ErschlerZheng.not_forall_tsum_f_schreierDist_div_card_le_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T12:44:17.333385+00:00
-- url     : https://prove2.me/submissions/7666e26c-31e3-4f41-a21b-67b420fde9c3

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_smul_cElt_eq_self_and_sec_cElt_eq
import Theorems.Thm_ErschlerZheng_exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem

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

theorem cons_smul (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    (x :: u) <• g = xor x (rootSwap g) :: (u <• sec g [x]) := by
  have := append_vertex_smul g [x] u
  rw [singleton_smul] at this
  exact this

theorem sec_inv (g : BinaryTreeAut) (v : List Bool) : sec g⁻¹ v = (sec g (v <• g⁻¹))⁻¹ := by
  have h1 := sec_mul g⁻¹ g v
  rw [inv_mul_cancel, sec_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

/-! ### `a` and the generators -/

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

theorem grigA_inv : grigA⁻¹ = grigA := inv_eq_of_mul_eq_one_right grigA_mul_self

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
theorem gen_c_mul_d (ω : ℕ → Fin 3) : gen ω .c * gen ω .d = gen ω .b :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).2.1)
theorem gen_d_mul_b (ω : ℕ → Fin 3) : gen ω .d * gen ω .b = gen ω .c :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).2.2.1)
theorem gen_c_mul_b (ω : ℕ → Fin 3) : gen ω .c * gen ω .b = gen ω .d :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).2.2.2.1)
theorem gen_d_mul_c (ω : ℕ → Fin 3) : gen ω .d * gen ω .c = gen ω .b :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).2.2.2.2.1)
theorem gen_b_mul_d (ω : ℕ → Fin 3) : gen ω .b * gen ω .d = gen ω .c :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).2.2.2.2.2)

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

theorem genFun_replicate (ω : ℕ → Fin 3) (γ : BCD) (k : ℕ) (z : List Bool) :
    genFun ω γ (List.replicate k true ++ false :: z) =
      List.replicate k true ++ false :: (if letterValue (ω k) γ then grigAFun z else z) := by
  induction k generalizing ω with
  | zero => simp [genFun]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, genFun, ih]
    simp only [shiftSeq]
    rfl

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

/-! ### Eventual sections -/

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

theorem sec_eq_of_germ {x : Ray} {k k' : BinaryTreeAut} (hk : x <• k = x) (hk' : x <• k' = x)
    (h : germ x k = germ x k') : ∃ N, ∀ n ≥ N, sec k (rayPrefix x n) = sec k' (rayPrefix x n) := by
  obtain ⟨N, hN⟩ := sec_eq_of_germEq ((germ_eq_iff hk hk').mp h)
  exact ⟨N, fun n hn => (hN n hn).2⟩

theorem one_fix (x : Ray) : x <• (1 : BinaryTreeAut) = x := one_smul_ray x

theorem gen_ne_one_of_exists (ω : ℕ → Fin 3) (γ : BCD) (h : ∃ j, letterValue (ω j) γ = true) :
    gen ω γ ≠ 1 := by
  obtain ⟨j, hj⟩ := h
  intro e
  have := congrArg (fun g => (List.replicate j true ++ [false, false]) <• g) e
  rw [vertex_smul_gen, show List.replicate j true ++ [false, false] =
    List.replicate j true ++ false :: [false] from rfl, genFun_replicate, hj] at this
  simp only [↓reduceIte, one_smul_ray] at this
  rw [show (List.replicate j true ++ [false, false]) <• (1 : BinaryTreeAut) =
    List.replicate j true ++ [false, false] from one_smul _ _] at this
  have := List.append_cancel_left this
  simp [grigAFun] at this

theorem eq_of_letterValue_false (i : Fin 3) (γ : BCD) (h : letterValue i γ = false) :
    γ = BCD.killedBy i := by
  simpa [letterValue] using h

theorem killedBy_inj {i j : Fin 3} (h : BCD.killedBy i = BCD.killedBy j) : i = j := by
  rcases ZetaFin.fin3 i with rfl | rfl | rfl <;> rcases ZetaFin.fin3 j with rfl | rfl | rfl <;>
    first | rfl | exact absurd h (by decide)
where
  ZetaFin.fin3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
    rcases i with ⟨k, hk⟩; interval_cases k <;> simp

/-- Not eventually constant: every letter is non-trivial on every tail. -/
theorem gen_shift_ne_one (ω : ℕ → Fin 3) (hω : ¬ ∃ i : Fin 3, ∀ᶠ k in Filter.atTop, ω k = i)
    (γ : BCD) (n : ℕ) : gen (shiftSeq ω n) γ ≠ 1 := by
  apply gen_ne_one_of_exists
  by_contra hcon
  push Not at hcon
  -- every letter from `n` on kills `γ`
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, BCD.killedBy i = γ := by
    cases γ
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  apply hω
  refine ⟨i, Filter.eventually_atTop.mpr ⟨n, fun k hk => ?_⟩⟩
  have := hcon (k - n)
  simp only [shiftSeq, show k - n + n = k by omega, Bool.not_eq_true] at this
  have e := eq_of_letterValue_false _ _ this
  rw [← hi] at e
  exact (killedBy_inj e).symm

theorem gen_shift_inj (ω : ℕ → Fin 3) (hω : ¬ ∃ i : Fin 3, ∀ᶠ k in Filter.atTop, ω k = i)
    {γ γ' : BCD} (n : ℕ) (h : gen (shiftSeq ω n) γ = gen (shiftSeq ω n) γ') : γ = γ' := by
  by_contra hne
  have hmul : gen (shiftSeq ω n) γ * gen (shiftSeq ω n) γ' = 1 := by rw [h, gen_mul_self]
  cases γ <;> cases γ' <;> simp at hne
  · rw [gen_b_mul_c] at hmul; exact gen_shift_ne_one ω hω _ n hmul
  · rw [gen_b_mul_d] at hmul; exact gen_shift_ne_one ω hω _ n hmul
  · rw [gen_c_mul_b] at hmul; exact gen_shift_ne_one ω hω _ n hmul
  · rw [gen_c_mul_d] at hmul; exact gen_shift_ne_one ω hω _ n hmul
  · rw [gen_d_mul_b] at hmul; exact gen_shift_ne_one ω hω _ n hmul
  · rw [gen_d_mul_c] at hmul; exact gen_shift_ne_one ω hω _ n hmul

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
# Proposition 7.12 as stated fails for `υ̌_n` (prover 3, item 3)

The bound of Proposition 7.12 is uniform in `f`, and `f(0)` is free (only `f ⩾ 0`, `f`
non-increasing on `[0, ∞)` and the ratio condition on `[1, ∞)` are asked). The term `x = o = 1^∞`
of the sum is `f(0) · υ̌_n{g : (g, o) ∉ ℋ^b}`. For `υ_n` that mass is `0` (every factor `γ_j` acts at a
point whose first `j + 1` digits are `1`, where its germ is good). For `υ̌_n` it is not: with
`D = 3`, `ω = (201)^∞`, `k ≡ 3`, `n = 6`, the element `g_1 = a c a c` is `θ_6(e_1, γ)` for every `γ`, so
`υ̌_6(g_1⁻¹) = υ_6(g_1) ⩾ 2⁻⁶`, and the sections of `g_1⁻¹ = c a c a` along `1^∞` are `c_{𝔰ⁿω}`
(`n ⩾ 2`), so `(g_1⁻¹, o) ∉ ℋ^b`. Taking `f = 1` on `(0, ∞)` and `f(0) = M` large contradicts the
`υ̌` inequality.

The sum is a genuine (summable) sum: every `g ∈ G_ω` has only finitely many points where its
sections are not eventually `1` or `b_{𝔰ⁿω}` (closure induction: generators have at most `1^∞`), and
`υ̌_6` has finite support.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErschlerZheng

namespace P3P712Dev

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev B3Dev B4Dev

/-! ### Germs read from sections, point by point -/

/-- The sections of `g` along `x` are eventually `1`, or eventually `b_{𝔰ⁿω}`. -/
def GoodAt (ω : ℕ → Fin 3) (g : BinaryTreeAut) (x : Ray) : Prop :=
  ∃ N, (∀ n ≥ N, sec g (rayPrefix x n) = 1) ∨
    (∀ n ≥ N, sec g (rayPrefix x n) = gen (shiftSeq ω n) .b)

/-- A germ in `ℋ^b` has good sections (as in B4). -/
theorem goodAt_of_mem (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) {x : Ray}
    (hx : x ∈ orbitOne ω) (hmem : (g, x) ∈ letterGerms ω .b) : GoodAt ω g x := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
  have hL : IsAuxiliary (X := Ray) (grigorchuk ω) finitary := hA2.2.2 ω
  have hbo := oneRay_smul_gen ω .b
  have hsq : germ oneRay (gen ω .b) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← germ_mul hbo hbo, gen_mul_self, germ_one]
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
    refine ⟨max (max N1 N2) (max N3 N4), Or.inl fun n hn => ?_⟩
    rw [← hN3 _ (by omega), ← hN2 _ (by omega), ← hN1 _ (by omega), ← rayPrefix_oneRay,
      hN4 _ (by omega), sec_one]
  · obtain ⟨N4, hN4⟩ := sec_eq_of_germ hK hbo e
    refine ⟨max (max N1 N2) (max N3 N4), Or.inr fun n hn => ?_⟩
    rw [← hN3 _ (by omega), ← hN2 _ (by omega), ← hN1 _ (by omega), ← rayPrefix_oneRay,
      hN4 _ (by omega), rayPrefix_oneRay, sec_gen_replicate_true]

/-! ### The witness: `D = 3`, `ω = (201)^∞`, `k ≡ 3`, `n = 6` -/

/-- `ω = (201)^∞`. -/
def ω₁ : ℕ → Fin 3 := fun i => if i % 3 = 0 then 2 else if i % 3 = 1 then 0 else 1

/-- `k_n = 3`. -/
def k₁ : ℕ → ℕ := fun _ => 3

theorem satisfiesFr_ω₁ : SatisfiesFr 3 ω₁ := by
  intro k
  have h0 : (k * 3 + 0) % 3 = 0 := by omega
  have h1 : (k * 3 + 0 + 1) % 3 = 1 := by omega
  have h2 : (k * 3 + 0 + 2) % 3 = 2 := by omega
  refine ⟨0, by norm_num, ?_, ?_, Or.inl ?_⟩
  · simp only [ω₁, h0, if_true]
  · simp only [ω₁, h2]; rfl
  · simp only [ω₁, h1]; rfl

theorem not_eventually_const_ω₁ : ¬ ∃ i : Fin 3, ∀ᶠ k in Filter.atTop, ω₁ k = i := by
  rintro ⟨i, hi⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hi
  have e1 := hN (3 * N) (by omega)
  have e2 := hN (3 * N + 1) (by omega)
  have h0 : 3 * N % 3 = 0 := by omega
  have h1 : (3 * N + 1) % 3 = 1 := by omega
  simp only [ω₁, h0, h1, if_true] at e1 e2
  rw [← e2] at e1
  exact absurd e1 (by decide)

theorem admissible_k₁ : IsAdmissibleSeq 3 k₁ :=
  ⟨monotone_const, fun _ _ _ => ⟨by norm_num [k₁], dvd_refl 3⟩⟩

theorem sec_grigA_ne_nil {v : List Bool} (hv : v ≠ []) : sec grigA v = 1 := by
  obtain ⟨y, u, rfl⟩ := List.exists_cons_of_ne_nil hv
  exact sec_grigA_cons y u

/-! ### `Λ_n` is finite; `Λ_6` is non-empty -/

theorem finite_vSet (D : ℕ) (ω : ℕ → Fin 3) (j k : ℕ) : (vSet D ω j k).Finite := by
  apply Set.Finite.subset ((List.finite_length_eq Bool k).image fun u =>
    List.replicate (D - j % D) true ++ u ++ List.replicate (frM D ω (ellIndex D k j) + 2) true ++
      [false])
  rintro v ⟨u, hu, rfl⟩
  exact ⟨u, hu.1, rfl⟩

theorem finite_fSet (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (j n : ℕ) : (fSet D ω k j n).Finite := by
  unfold fSet
  split_ifs
  · apply Set.Finite.subset ((finite_vSet D ω j (2 * k n)).image (gTilde ω j))
    rintro g ⟨v, hv, -, rfl⟩
    exact ⟨v, hv, rfl⟩
  · exact Set.finite_singleton _

theorem cpl_cons_true (u : List Bool) :
    commonPrefixLength (true :: u) oneRay = commonPrefixLength u oneRay + 1 := by
  simp [commonPrefixLength, rayPrefix_oneRay, List.replicate_succ, List.takeWhile_cons]

theorem cpl_replicate_append (N : ℕ) (w : List Bool) :
    N ≤ commonPrefixLength (List.replicate N true ++ w) oneRay := by
  induction N with
  | zero => exact Nat.zero_le _
  | succ N ih =>
    rw [List.replicate_succ, List.cons_append, cpl_cons_true]
    omega

theorem nonempty_fSet (i : Fin 6) : (fSet 3 ω₁ k₁ (i + 1) 6).Nonempty := by
  unfold fSet
  split_ifs with h
  · set m := frM 3 ω₁ (ellIndex 3 (2 * k₁ 6) (i + 1))
    set v := List.replicate (3 - (i + 1) % 3) true ++ List.replicate (2 * k₁ 6) true ++
      List.replicate (m + 2) true ++ [false]
    refine ⟨gTilde ω₁ (i + 1) v, v, ⟨List.replicate (2 * k₁ 6) true, ⟨by simp, ?_⟩, rfl⟩, ?_, rfl⟩
    · intro j hj _; simp
    · have : v = List.replicate (3 - (i + 1) % 3 + 2 * k₁ 6) true ++
          (List.replicate (m + 2) true ++ [false]) := by
        simp only [v, List.replicate_add, List.append_assoc]
      rw [this]
      refine le_trans ?_ (cpl_replicate_append _ _)
      have := i.2
      simp only [k₁]
      omega
  · exact Set.singleton_nonempty _

instance (i : Fin 6) : Finite (fSet 3 ω₁ k₁ (i + 1) 6) := (finite_fSet _ _ _ _ _).to_subtype

instance : Finite (LambdaN 3 ω₁ k₁ 6) := inferInstance

instance : Nonempty (fProd 3 ω₁ k₁ 6) :=
  ⟨fun i => ⟨(nonempty_fSet i).some, (nonempty_fSet i).some_mem⟩⟩

/-! ### `υ_6(g_1) ⩾ 2⁻⁶` -/

/-! ### Finite support and summability -/

end P3P712Dev

end ErschlerZheng
end

section
/-!
# Lemma 7.21 (i) as printed fails for negative `f`

Witness: `D = 3`, `ω = (201)^∞`, `k ≡ 3`, `n = 6`, `j = 4`, `v = 1^{2+6+m+2}0`, `f ≡ -1`. The left side
is `-1`, the right side `-1 - 3^{1+2/3}·2^{-4/3} < -1`. A bad point `x` of `g̃^v_4` exists: the section
of `g̃^v_4` at `1^4` is `a𝔠` or `𝔠a` (Lemma 7.9), `𝔠` fixes `v` with section `c_{𝔰^{4+|v|}ω}` there
(Lemma 7.7), so along `1^4 v 1^∞` (resp. `1^4 v' 1^∞`, `v'` = `v` with its first digit flipped) the
sections of `g̃^v_4` are eventually `c_{𝔰^mω}`, neither `1` nor `b_{𝔰^mω}`.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace ErschlerZheng

namespace P3I1FDev

open GrigBasic RayBasic SchreierDev GermBase GrigGermsDev B3Dev P3P712Dev

/-- `v = 1^{2+6+m+2} 0`. -/
noncomputable def v₀ : List Bool :=
  List.replicate (3 - 4 % 3) true ++ List.replicate (2 * k₁ 6) true ++
    List.replicate (frM 3 ω₁ (ellIndex 3 (2 * k₁ 6) 4) + 2) true ++ [false]

theorem v₀_mem : v₀ ∈ vSet 3 ω₁ 4 (2 * k₁ 6) :=
  ⟨List.replicate (2 * k₁ 6) true, ⟨by simp, fun i hi _ => by simp⟩, rfl⟩

theorem v₀_cpl : 6 - 4 + 3 ≤ commonPrefixLength v₀ oneRay := by
  have : v₀ = List.replicate (3 - 4 % 3 + 2 * k₁ 6) true ++
      (List.replicate (frM 3 ω₁ (ellIndex 3 (2 * k₁ 6) 4) + 2) true ++ [false]) := by
    simp only [v₀, List.replicate_add, List.append_assoc]
  rw [this]
  refine le_trans ?_ (cpl_replicate_append _ _)
  simp [k₁]

theorem v₀_cons : ∃ w, v₀ = true :: w := ⟨_, rfl⟩

theorem rayPrefix_prepend_oneRay (u : List Bool) (i : ℕ) :
    rayPrefix (prepend u oneRay) (u.length + i) = u ++ List.replicate i true := by
  rw [rayPrefix_add, rayPrefix_prepend, shiftRay_prepend, rayPrefix_oneRay]

theorem prepend_mem_orbitOne (ω : ℕ → Fin 3) (u : List Bool) : prepend u oneRay ∈ orbitOne ω := by
  have := (isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary.2.1 ω oneRay).1
  show prepend u oneRay ∈ rightOrbit (grigorchuk ω) oneRay
  rw [this]
  refine Filter.eventually_atTop.mpr ⟨u.length, fun i hi => ?_⟩
  simp [prepend, show ¬ i < u.length by omega, oneRay]

theorem not_goodAt_of_sec {g : BinaryTreeAut} {x : Ray} {L : ℕ}
    (h : ∀ i, sec g (rayPrefix x (L + i)) = gen (shiftSeq ω₁ (L + i)) .c) : ¬ GoodAt ω₁ g x := by
  rintro ⟨N, hN⟩
  have e := h N
  rcases hN with hN | hN
  · rw [hN (L + N) (by omega)] at e
    exact gen_shift_ne_one ω₁ not_eventually_const_ω₁ .c (L + N) e.symm
  · rw [hN (L + N) (by omega)] at e
    exact absurd (gen_shift_inj ω₁ not_eventually_const_ω₁ (L + N) e) (by decide)

/-- A bad point of `g̃^{v₀}_4`. -/
theorem exists_bad : ∃ x ∈ orbitOne ω₁, (gTilde ω₁ 4 v₀, x) ∉ letterGerms ω₁ .b := by
  have hk : 3 ∣ 2 * k₁ 6 := ⟨2, by simp [k₁]⟩
  have h79 := exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem 3 ω₁ satisfiesFr_ω₁ 4
    (by norm_num) (2 * k₁ 6) hk v₀ v₀_mem
  have hG : gTilde ω₁ 4 v₀ ∈ grigorchuk ω₁ := h79.2.1
  have hsec := (h79.2.2 (by decide)).2 (List.replicate 4 true) (by simp)
  have h77 := smul_cElt_eq_self_and_sec_cElt_eq 3 ω₁ satisfiesFr_ω₁ 4 (2 * k₁ 6) hk v₀ v₀_mem
  have hcv : sec (cElt ω₁ 4 v₀) v₀ = gen (shiftSeq ω₁ (4 + v₀.length)) .c := h77.2.2.2
  have hsecc : ∀ i, sec (cElt ω₁ 4 v₀) (v₀ ++ List.replicate i true) =
      gen (shiftSeq ω₁ (4 + v₀.length + i)) .c := by
    intro i
    rw [sec_append, hcv, sec_gen_replicate_true, shiftSeq_shiftSeq]
    congr 2; omega
  have hlen : ∀ (w : List Bool) (g : BinaryTreeAut), w ≠ [] → w <• g ≠ [] := fun w g hw h => by
    have := length_vertex_smul g w
    rw [h] at this
    exact hw (List.eq_nil_of_length_eq_zero this.symm)
  obtain ⟨w, hw⟩ := v₀_cons
  rcases hsec with hs | hs
  · -- section `a𝔠`: the bad point is `1^4 (0 w) 1^∞`
    set u := List.replicate 4 true ++ (false :: w)
    refine ⟨prepend u oneRay, prepend_mem_orbitOne ω₁ u, fun hmem => ?_⟩
    refine not_goodAt_of_sec (L := u.length) (fun i => ?_) (goodAt_of_mem ω₁ hG
      (prepend_mem_orbitOne ω₁ u) hmem)
    rw [rayPrefix_prepend_oneRay, show u ++ List.replicate i true =
      List.replicate 4 true ++ ((false :: w) ++ List.replicate i true) by simp [u],
      sec_append, hs, sec_mul, sec_grigA_ne_nil (by simp), one_mul]
    have : ((false :: w) ++ List.replicate i true) <• grigA = v₀ ++ List.replicate i true := by
      rw [List.cons_append, cons_smul, rootSwap_grigA, sec_grigA, MulOpposite.op_one, one_smul,
        hw]
      rfl
    rw [this, hsecc]
    congr 2
    simp [u, hw]; omega
  · -- section `𝔠a`: the bad point is `1^4 v 1^∞`
    set u := List.replicate 4 true ++ v₀
    refine ⟨prepend u oneRay, prepend_mem_orbitOne ω₁ u, fun hmem => ?_⟩
    refine not_goodAt_of_sec (L := u.length) (fun i => ?_) (goodAt_of_mem ω₁ hG
      (prepend_mem_orbitOne ω₁ u) hmem)
    rw [rayPrefix_prepend_oneRay, show u ++ List.replicate i true =
      List.replicate 4 true ++ (v₀ ++ List.replicate i true) by simp [u],
      sec_append, hs, sec_mul, sec_grigA_ne_nil (hlen _ _ (by simp [hw])), mul_one, hsecc]
    congr 2
    simp [u]; omega

end P3I1FDev

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open ErschlerZheng
open P3I1FDev P3P712Dev in
theorem solution :
    ¬ ∀ (D : ℕ) (ω : ℕ → Fin 3), SatisfiesFr D ω → ∀ k : ℕ → ℕ, IsAdmissibleSeq D k →
      ∀ n, D ∣ n → ∀ j, 1 ≤ j → ω (j - 1) = 2 → n < j + k n → j ≤ n →
      ∀ v ∈ vSet D ω j (2 * k n), n - j + D ≤ commonPrefixLength v oneRay →
      ∀ f : ℝ → ℝ, Antitone f → ∀ x ∈ orbitOne ω, (gTilde ω j v, x) ∉ letterGerms ω .b →
        (∑' p : LambdaN D ω k n, f (schreierDist ω oneRay
            (x <• (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map fun i =>
              ((p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat)⁻¹).prod))) /
            Nat.card (LambdaN D ω k n) ≤
          f (2 ^ (j + 2 * k n)) +
            f (2 ^ (n + D)) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
              (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n)) := by
  intro H
  obtain ⟨x, hx, hbad⟩ := exists_bad
  have h := H 3 ω₁ satisfiesFr_ω₁ k₁ admissible_k₁ 6 (by norm_num) 4 (by norm_num) rfl
    (by simp [k₁]) (by norm_num) v₀ v₀_mem v₀_cpl (fun _ => -1) antitone_const x hx hbad
  haveI : Fintype (LambdaN 3 ω₁ k₁ 6) := Fintype.ofFinite _
  have hcard : (0 : ℝ) < Nat.card (LambdaN 3 ω₁ k₁ 6) := by exact_mod_cast Nat.card_pos
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card,
    mul_neg_one, neg_div, div_self hcard.ne'] at h
  have hpos : 0 < ((k₁ 6 : ℕ) : ℝ) ^ (1 + 2 / ((3 : ℕ) : ℝ)) *
      (2 : ℝ) ^ (-(1 / ((3 : ℕ) : ℝ)) * (((4 : ℕ) : ℝ) + 2 * (k₁ 6 : ℕ) - ((6 : ℕ) : ℝ))) := by
    apply mul_pos
    · apply Real.rpow_pos_of_pos; simp [k₁]
    · apply Real.rpow_pos_of_pos; norm_num
  nlinarith
end
