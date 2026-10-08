-- Prove2me | solution 1 for ErschlerZheng.not_forall_tsum_f_mul_mass_upsilonCheck_not_mem_letterGerms_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T12:44:17.506213+00:00
-- url     : https://prove2.me/submissions/0658ebcc-144c-4a8c-91aa-fca03b75d863

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
import Definitions.Def_ErschlerZheng_Construction

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

theorem genFun_replicate (ω : ℕ → Fin 3) (γ : BCD) (k : ℕ) (z : List Bool) :
    genFun ω γ (List.replicate k true ++ false :: z) =
      List.replicate k true ++ false :: (if letterValue (ω k) γ then grigAFun z else z) := by
  induction k generalizing ω with
  | zero => simp [genFun]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, genFun, ih]
    simp only [shiftSeq]
    rfl

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

theorem goodAt_mul (ω : ℕ → Fin 3) {g h : BinaryTreeAut} {x : Ray} (hg : GoodAt ω g x)
    (hh : GoodAt ω h (x <• g)) : GoodAt ω (g * h) x := by
  obtain ⟨N, hN⟩ := hg
  obtain ⟨M, hM⟩ := hh
  have e : ∀ n, sec (g * h) (rayPrefix x n) =
      sec g (rayPrefix x n) * sec h (rayPrefix (x <• g) n) := fun n => by
    rw [sec_mul, rayPrefix_smul]
  refine ⟨max N M, ?_⟩
  rcases hN with hN | hN <;> rcases hM with hM | hM
  · exact Or.inl fun n hn => by rw [e, hN n (by omega), hM n (by omega), one_mul]
  · exact Or.inr fun n hn => by rw [e, hN n (by omega), hM n (by omega), one_mul]
  · exact Or.inr fun n hn => by rw [e, hN n (by omega), hM n (by omega), mul_one]
  · exact Or.inl fun n hn => by rw [e, hN n (by omega), hM n (by omega), gen_mul_self]

theorem goodAt_inv (ω : ℕ → Fin 3) {g : BinaryTreeAut} {x : Ray} (hg : GoodAt ω g x) :
    GoodAt ω g⁻¹ (x <• g) := by
  obtain ⟨N, hN⟩ := hg
  have e : ∀ n, sec g⁻¹ (rayPrefix (x <• g) n) = (sec g (rayPrefix x n))⁻¹ := fun n => by
    rw [sec_inv, rayPrefix_smul, vertex_smul_smul_inv]
  refine ⟨N, ?_⟩
  rcases hN with hN | hN
  · exact Or.inl fun n hn => by rw [e, hN n hn, inv_one]
  · exact Or.inr fun n hn => by rw [e, hN n hn, gen_inv]

theorem goodAt_one (ω : ℕ → Fin 3) (x : Ray) : GoodAt ω 1 x :=
  ⟨0, Or.inl fun n _ => sec_one _⟩

theorem goodAt_grigA (ω : ℕ → Fin 3) (x : Ray) : GoodAt ω grigA x := by
  refine ⟨1, Or.inl fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : rayPrefix x (m + 1) = x 0 :: rayPrefix (shiftRay x 1) m := by
    simp [rayPrefix, List.ofFn_succ, shiftRay]
  rw [this, sec_grigA_cons]

theorem goodAt_gen (ω : ℕ → Fin 3) (γ : BCD) {x : Ray} (hx : x ≠ oneRay) :
    GoodAt ω (gen ω γ) x := by
  rcases sec_gen_along ω γ x with ⟨N, hN⟩ | h
  · exact ⟨N, Or.inl hN⟩
  · exact absurd h hx

theorem goodAt_gen_b (ω : ℕ → Fin 3) (x : Ray) : GoodAt ω (gen ω .b) x := by
  by_cases hx : x = oneRay
  · subst hx
    exact ⟨0, Or.inr fun n _ => by rw [rayPrefix_oneRay, sec_gen_replicate_true]⟩
  · exact goodAt_gen ω .b hx

/-- Every element of `G_ω` has sections eventually `1` or `b` along all but finitely many rays. -/
theorem finite_not_goodAt (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) :
    {x | ¬ GoodAt ω g x}.Finite := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · simp [goodAt_grigA]
    · simp [goodAt_gen_b]
    · refine (Set.finite_singleton oneRay).subset fun x hx => ?_
      by_contra h
      exact hx (goodAt_gen ω .c h)
    · refine (Set.finite_singleton oneRay).subset fun x hx => ?_
      by_contra h
      exact hx (goodAt_gen ω .d h)
  | one => simp [goodAt_one]
  | mul g h _ _ ihg ihh =>
    refine (ihg.union (ihh.image fun y => y <• g⁻¹)).subset fun x hx => ?_
    by_cases h1 : GoodAt ω g x
    · right
      refine ⟨x <• g, fun h2 => hx (goodAt_mul ω h1 h2), ?_⟩
      exact rsmul_inv_smul x g
    · exact Or.inl h1
  | inv g _ ihg =>
    refine (ihg.image fun y => y <• g).subset fun x hx => ?_
    refine ⟨x <• g⁻¹, fun h2 => hx ?_, ?_⟩
    · have := goodAt_inv ω h2
      rwa [← rsmul_mul, inv_mul_cancel, rsmul_one] at this
    · show (x <• g⁻¹) <• g = x
      rw [← rsmul_mul, inv_mul_cancel, rsmul_one]

/-- Good sections give a germ in `ℋ^b` (as in B4). -/
theorem mem_of_goodAt (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) {x : Ray}
    (hx : x ∈ orbitOne ω) (hG : GoodAt ω g x) : (g, x) ∈ letterGerms ω .b := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
  have hL : IsAuxiliary (X := Ray) (grigorchuk ω) finitary := hA2.2.2 ω
  have hbo := oneRay_smul_gen ω .b
  have hgGL : g ∈ grigorchuk ω ⊔ finitary := mem_GL_of_G hg
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
  obtain ⟨N, hN⟩ := hG
  rcases hN with hN | hN
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

theorem seqG_one : seqG ω₁ 1 = grigA * gen ω₁ .c * grigA * gen ω₁ .c := by
  have h0 : ω₁ 0 = 2 := rfl
  simp [seqG, h0, zetaWord, zetaPair, evalWord, APair.toWord, shiftSeq_zero, mul_assoc]

theorem seqG_one_mem : seqG ω₁ 1 ∈ grigorchuk ω₁ := by
  have ha : grigA ∈ grigorchuk ω₁ := Subgroup.subset_closure (by simp [gens])
  have hc : gen ω₁ .c ∈ grigorchuk ω₁ := Subgroup.subset_closure (by simp [gens])
  rw [seqG_one]
  exact mul_mem (mul_mem (mul_mem ha hc) ha) hc

theorem sec_grigA_ne_nil {v : List Bool} (hv : v ≠ []) : sec grigA v = 1 := by
  obtain ⟨y, u, rfl⟩ := List.exists_cons_of_ne_nil hv
  exact sec_grigA_cons y u

theorem sec_seqG_one_inv (m : ℕ) :
    sec (seqG ω₁ 1)⁻¹ (List.replicate (m + 2) true) = gen (shiftSeq ω₁ (m + 2)) .c := by
  have hinv : (seqG ω₁ 1)⁻¹ = gen ω₁ .c * grigA * gen ω₁ .c * grigA := by
    rw [seqG_one]; simp [mul_inv_rev, gen_inv, grigA_inv, mul_assoc]
  set v := List.replicate (m + 2) true
  have hv : v ≠ [] := by simp [v]
  have hlen : ∀ g : BinaryTreeAut, v <• g ≠ [] := fun g h => by
    have := length_vertex_smul g v
    rw [h] at this; simp [v] at this
  have hvc : v <• gen ω₁ .c = v := by rw [vertex_smul_gen, genFun_replicate_true]
  have hva : v <• grigA = false :: List.replicate (m + 1) true := by
    show (true :: List.replicate (m + 1) true) <• grigA = _
    rw [cons_smul, rootSwap_grigA, sec_grigA, MulOpposite.op_one, one_smul]
    rfl
  have hl : letterElt (ω₁ 0) .c = grigA := by
    simp [letterElt, letterValue, ω₁, BCD.killedBy]
  rw [hinv, sec_mul, sec_grigA_ne_nil (hlen _), mul_one, sec_mul, vertex_smul_mul, hvc, hva,
    sec_cons, sec_gen_false, hl, List.replicate_succ, sec_grigA_cons, mul_one, sec_mul,
    sec_grigA_ne_nil (hlen _), mul_one, sec_gen_replicate_true]

theorem not_goodAt_seqG_one_inv : ¬ GoodAt ω₁ (seqG ω₁ 1)⁻¹ oneRay := by
  rintro ⟨N, hN⟩
  have e := sec_seqG_one_inv N
  rw [← rayPrefix_oneRay] at e
  rcases hN with hN | hN
  · rw [hN (N + 2) (by omega)] at e
    exact gen_shift_ne_one ω₁ not_eventually_const_ω₁ .c (N + 2) e.symm
  · rw [hN (N + 2) (by omega)] at e
    exact absurd (gen_shift_inj ω₁ not_eventually_const_ω₁ (N + 2) e) (by decide)

theorem oneRay_mem_orbitOne (ω : ℕ → Fin 3) : oneRay ∈ orbitOne ω :=
  ⟨1, Subgroup.one_mem _, (one_smul _ _).symm⟩

theorem seqG_one_inv_not_mem : ((seqG ω₁ 1)⁻¹, oneRay) ∉ letterGerms ω₁ .b := fun h =>
  not_goodAt_seqG_one_inv (goodAt_of_mem ω₁ (inv_mem seqG_one_mem) (oneRay_mem_orbitOne ω₁) h)

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

/-- `ε = e_1` (only the paper's first coordinate is `1`). -/
def e₀ : Fin 6 → Bool := fun i => decide (i.val = 0)

theorem theta_e₀ (γ : fProd 3 ω₁ k₁ 6) : theta 3 ω₁ k₁ 6 (e₀, γ) = (γ 0 : BinaryTreeAut) := by
  simp [theta, List.ofFn_succ, e₀, Fin.rev]

theorem γ0_eq (γ : fProd 3 ω₁ k₁ 6) : (γ 0 : BinaryTreeAut) = seqG ω₁ 1 := by
  have h : (γ 0 : BinaryTreeAut) ∈ fSet 3 ω₁ k₁ 1 6 := (γ 0).2
  have hS : fSet 3 ω₁ k₁ 1 6 = {seqG ω₁ 1} := by
    unfold fSet
    rw [if_neg (by simp [k₁])]
  rw [hS] at h
  exact h

theorem upsilon_seqG_one_ge : (1 : ℝ) / 64 ≤ upsilon 3 ω₁ k₁ 6 (seqG ω₁ 1) := by
  unfold upsilon
  have hinj : Function.Injective (fun γ : fProd 3 ω₁ k₁ 6 =>
      (⟨(e₀, γ), by rw [theta_e₀, γ0_eq]⟩ : {p : LambdaN 3 ω₁ k₁ 6 // theta 3 ω₁ k₁ 6 p = seqG ω₁ 1})) := by
    intro γ γ' h
    have := congrArg (fun q => q.1.2) h
    simpa using this
  have hle := Nat.card_le_card_of_injective _ hinj
  have hcard : Nat.card (LambdaN 3 ω₁ k₁ 6) = 64 * Nat.card (fProd 3 ω₁ k₁ 6) := by
    rw [Nat.card_prod, Nat.card_fun]; simp
  have hpos : 0 < Nat.card (fProd 3 ω₁ k₁ 6) := Nat.card_pos
  rw [hcard, Nat.cast_mul, le_div_iff₀ (by positivity)]
  have : (Nat.card (fProd 3 ω₁ k₁ 6) : ℝ) ≤
      Nat.card {p : LambdaN 3 ω₁ k₁ 6 // theta 3 ω₁ k₁ 6 p = seqG ω₁ 1} := by exact_mod_cast hle
  push_cast
  linarith

/-! ### Finite support and summability -/

theorem finite_support_upsilonCheck :
    {g : grigorchuk ω₁ | upsilonCheck 3 ω₁ k₁ 6 g ≠ 0}.Finite := by
  apply Set.Finite.subset ((Set.finite_range (theta 3 ω₁ k₁ 6)).preimage
    (Set.injOn_of_injective (inv_injective.comp Subtype.val_injective)))
  intro g hg
  simp only [Set.mem_ofPred_eq, upsilonCheck, upsilon] at hg
  simp only [Set.mem_preimage, Function.comp, Set.mem_range]
  by_contra hne
  push Not at hne
  apply hg
  have : IsEmpty {p : LambdaN 3 ω₁ k₁ 6 // theta 3 ω₁ k₁ 6 p = (g : BinaryTreeAut)⁻¹} :=
    ⟨fun p => hne p.1 p.2⟩
  rw [Nat.card_of_isEmpty]; simp

theorem upsilonCheck_nonneg (g : BinaryTreeAut) : 0 ≤ upsilonCheck 3 ω₁ k₁ 6 g := by
  unfold upsilonCheck upsilon; positivity

theorem summable_mass (x : Ray) :
    Summable fun g : grigorchuk ω₁ => {g : grigorchuk ω₁ |
      ((g : BinaryTreeAut), x) ∉ letterGerms ω₁ .b}.indicator
        (fun g : grigorchuk ω₁ => upsilonCheck 3 ω₁ k₁ 6 g) g := by
  apply summable_of_hasFiniteSupport
  apply finite_support_upsilonCheck.subset
  intro g hg
  simp only [Function.mem_support, Set.indicator] at hg
  split_ifs at hg with h
  · exact hg
  · exact absurd rfl hg

theorem mass_nonneg (x : Ray) :
    0 ≤ mass (fun g : grigorchuk ω₁ => upsilonCheck 3 ω₁ k₁ 6 g)
      {g | ((g : BinaryTreeAut), x) ∉ letterGerms ω₁ .b} := by
  unfold mass
  exact tsum_nonneg fun g => Set.indicator_nonneg
    (f := fun g : grigorchuk ω₁ => upsilonCheck 3 ω₁ k₁ 6 g) (fun g _ => upsilonCheck_nonneg _) g

theorem mass_ne_zero {x : orbitOne ω₁}
    (h : mass (fun g : grigorchuk ω₁ => upsilonCheck 3 ω₁ k₁ 6 g)
      {g | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω₁ .b} ≠ 0) :
    ∃ g ∈ {g : grigorchuk ω₁ | upsilonCheck 3 ω₁ k₁ 6 g ≠ 0}, ¬ GoodAt ω₁ g x := by
  by_contra hne
  push Not at hne
  apply h
  unfold mass
  convert tsum_zero with g
  by_cases hb : ((g : BinaryTreeAut), (x : Ray)) ∈ letterGerms ω₁ .b
  · simp [Set.indicator, hb]
  · rw [Set.indicator_of_mem (show g ∈ {g : grigorchuk ω₁ |
      ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω₁ .b} from hb)]
    by_contra hu
    exact hb (mem_of_goodAt ω₁ g.2 x.2 (hne g hu))

theorem summable_sum (f : ℝ → ℝ) :
    Summable fun x : orbitOne ω₁ => f (schreierDist ω₁ oneRay x) *
      mass (fun g : grigorchuk ω₁ => upsilonCheck 3 ω₁ k₁ 6 g)
        {g | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω₁ .b} := by
  apply summable_of_hasFiniteSupport
  have hfin : (⋃ g ∈ {g : grigorchuk ω₁ | upsilonCheck 3 ω₁ k₁ 6 g ≠ 0},
      {x : Ray | ¬ GoodAt ω₁ g x}).Finite :=
    finite_support_upsilonCheck.biUnion fun g _ => finite_not_goodAt ω₁ g.2
  apply (hfin.preimage Subtype.val_injective.injOn).subset
  intro x hx
  simp only [Function.mem_support] at hx
  obtain ⟨g, hg, hbad⟩ := mass_ne_zero (right_ne_zero_of_mul hx)
  simp only [Set.mem_preimage, Set.mem_iUnion]
  exact ⟨g, hg, hbad⟩

theorem schreierDist_self (ω : ℕ → Fin 3) : schreierDist ω oneRay oneRay = 0 := by
  unfold schreierDist
  apply Nat.sInf_eq_zero.mpr
  left
  refine ⟨1, ⟨[], by simp, by simp, by simp⟩, (one_smul _ _).symm⟩

/-- The mass of `υ̌_6` on the elements with a bad germ at `1^∞` is at least `2⁻⁶`. -/
theorem mass_oneRay_ge :
    (1 : ℝ) / 64 ≤ mass (fun g : grigorchuk ω₁ => upsilonCheck 3 ω₁ k₁ 6 g)
      {g | ((g : BinaryTreeAut), oneRay) ∉ letterGerms ω₁ .b} := by
  set g₀ : grigorchuk ω₁ := ⟨(seqG ω₁ 1)⁻¹, inv_mem seqG_one_mem⟩
  have hterm : {g : grigorchuk ω₁ | ((g : BinaryTreeAut), oneRay) ∉ letterGerms ω₁ .b}.indicator
      (fun g : grigorchuk ω₁ => upsilonCheck 3 ω₁ k₁ 6 g) g₀ = upsilon 3 ω₁ k₁ 6 (seqG ω₁ 1) := by
    rw [Set.indicator_of_mem (show g₀ ∈ _ from seqG_one_inv_not_mem)]
    simp [g₀, upsilonCheck]
  unfold mass
  refine le_trans upsilon_seqG_one_ge (le_of_eq_of_le hterm.symm ?_)
  exact (summable_mass oneRay).le_tsum g₀ fun g _ => Set.indicator_nonneg
    (f := fun g : grigorchuk ω₁ => upsilonCheck 3 ω₁ k₁ 6 g) (fun g _ => upsilonCheck_nonneg _) g

end P3P712Dev

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open ErschlerZheng
open P3P712Dev in
/-- The `υ̌_n` half of Proposition 7.12 as printed fails (the new F-statement). -/
theorem solution :
    ¬ ∀ (D : ℕ) (ω : ℕ → Fin 3), SatisfiesFr D ω → ∀ k : ℕ → ℕ, IsAdmissibleSeq D k →
      ∀ D' : ℝ, (D : ℝ) < D' →
      ∃ C : ℝ, ∀ f : ℝ → ℝ, (∀ s, 0 ≤ s → 0 ≤ f s) → AntitoneOn f (Set.Ici 0) →
        (∀ s, 1 ≤ s → (2 : ℝ) ^ (-1 / D') ≤ f (2 * s) / f s) → ∀ n, D ∣ n →
          ∑' x : orbitOne ω, f (schreierDist ω oneRay x) *
              mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
                {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} ≤
            C * 2 ^ n * f (2 ^ (n + 2 * k n)) := by
  intro H
  obtain ⟨C, hC⟩ := H 3 ω₁ satisfiesFr_ω₁ k₁ admissible_k₁ 4 (by norm_num)
  set M : ℝ := 64 * (|C| * 64 + 1) with hM
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith [abs_nonneg C]
  set f : ℝ → ℝ := fun s => if s ≤ 0 then M else 1 with hf
  have hf0 : ∀ s, 0 ≤ s → 0 ≤ f s := fun s _ => by
    simp only [hf]; split_ifs <;> linarith
  have hfa : AntitoneOn f (Set.Ici 0) := by
    intro a ha b hb hab
    simp only [hf, Set.mem_Ici] at ha hb ⊢
    split_ifs <;> linarith
  have hfr : ∀ s, 1 ≤ s → (2 : ℝ) ^ (-1 / (4 : ℝ)) ≤ f (2 * s) / f s := by
    intro s hs
    have h1 : ¬ 2 * s ≤ 0 := by linarith
    have h2 : ¬ s ≤ 0 := by linarith
    simp only [hf, h1, h2, if_false, div_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hB := hC f hf0 hfa hfr 6 (by norm_num)
  -- the right-hand side
  have hR : f (2 ^ (6 + 2 * k₁ 6)) = 1 := by
    have : ¬ (2 : ℝ) ^ (6 + 2 * k₁ 6) ≤ 0 := not_le.mpr (by positivity)
    simp only [hf, this, if_false]
  rw [hR, mul_one] at hB
  -- the term `x = 1^∞`
  set o : orbitOne ω₁ := ⟨oneRay, oneRay_mem_orbitOne ω₁⟩
  have hterm := (summable_sum f).le_tsum o fun x _ =>
    mul_nonneg (hf0 _ (Nat.cast_nonneg _)) (mass_nonneg x)
  have ho : f (schreierDist ω₁ oneRay (o : Ray)) = M := by
    simp only [o, schreierDist_self, Nat.cast_zero, hf, le_refl, if_true]
  rw [ho] at hterm
  have hmass := mass_oneRay_ge
  have : M * (1 / 64) ≤ C * 2 ^ 6 := by
    refine le_trans ?_ (le_trans hterm hB)
    exact mul_le_mul_of_nonneg_left hmass (by linarith)
  have hC' : C ≤ |C| := le_abs_self C
  rw [hM] at this
  nlinarith
end
