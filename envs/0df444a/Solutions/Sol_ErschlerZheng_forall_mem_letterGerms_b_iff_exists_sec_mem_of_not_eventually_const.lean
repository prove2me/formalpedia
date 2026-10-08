-- Prove2me | solution 1 for ErschlerZheng.forall_mem_letterGerms_b_iff_exists_sec_mem_of_not_eventually_const
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T03:25:49.529983+00:00
-- url     : https://prove2.me/submissions/9491c241-81b1-4b7c-9505-fd2de1194016

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary

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

/-- `{1, b_ω, c_ω, d_ω}`. -/
def V (ω : ℕ → Fin 3) : Set BinaryTreeAut := {c | c = 1 ∨ ∃ γ, c = gen ω γ}

theorem one_mem_V (ω : ℕ → Fin 3) : (1 : BinaryTreeAut) ∈ V ω := Or.inl rfl

theorem gen_mem_V (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ ∈ V ω := Or.inr ⟨γ, rfl⟩

theorem gen_mul_gen_mem (ω : ℕ → Fin 3) (γ γ' : BCD) : gen ω γ * gen ω γ' ∈ V ω := by
  cases γ <;> cases γ'
  · rw [gen_mul_self]; exact one_mem_V ω
  · rw [gen_b_mul_c]; exact gen_mem_V ω _
  · rw [gen_b_mul_d]; exact gen_mem_V ω _
  · rw [gen_c_mul_b]; exact gen_mem_V ω _
  · rw [gen_mul_self]; exact one_mem_V ω
  · rw [gen_c_mul_d]; exact gen_mem_V ω _
  · rw [gen_d_mul_b]; exact gen_mem_V ω _
  · rw [gen_d_mul_c]; exact gen_mem_V ω _
  · rw [gen_mul_self]; exact one_mem_V ω

theorem V_mul {ω : ℕ → Fin 3} {c c' : BinaryTreeAut} (hc : c ∈ V ω) (hc' : c' ∈ V ω) :
    c * c' ∈ V ω := by
  rcases hc with rfl | ⟨γ, rfl⟩
  · rwa [one_mul]
  · rcases hc' with rfl | ⟨γ', rfl⟩
    · rw [mul_one]; exact gen_mem_V ω γ
    · exact gen_mul_gen_mem ω γ γ'

theorem V_fix {ω : ℕ → Fin 3} {c : BinaryTreeAut} (hc : c ∈ V ω) (n : ℕ) :
    List.replicate n true <• c = List.replicate n true := by
  rcases hc with rfl | ⟨γ, rfl⟩
  · exact one_smul _ _
  · rw [vertex_smul_gen, genFun_replicate_true]

theorem sec_V_mul {ω : ℕ → Fin 3} {c c' : BinaryTreeAut} (hc : c ∈ V ω) (n : ℕ) :
    sec (c * c') (List.replicate n true) =
      sec c (List.replicate n true) * sec c' (List.replicate n true) := by
  rw [sec_mul, V_fix hc]

theorem sec_gen_replicate_true (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    sec (gen ω γ) (List.replicate n true) = gen (shiftSeq ω n) γ := by
  induction n generalizing ω with
  | zero => rw [List.replicate_zero, sec_nil, shiftSeq_zero]
  | succ n ih =>
    rw [List.replicate_succ, sec_cons, sec_gen_true, ih, shiftSeq_shiftSeq]

/-! ### Cofinality classes are preserved (A2) -/

/-- Eventual agreement of rays. -/
def Cof (x y : Ray) : Prop := ∀ᶠ n in Filter.atTop, y n = x n

theorem cof_symm {x y : Ray} (h : Cof x y) : Cof y x := h.mono fun _ h => h.symm

theorem cof_trans {x y z : Ray} (h1 : Cof x y) (h2 : Cof y z) : Cof x z :=
  (h1.and h2).mono fun _ h => h.2.trans h.1

theorem cof_smul_GL (ω : ℕ → Fin 3) {k : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary) (x : Ray) :
    Cof x (x <• k) := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary.2.1 ω
  suffices H : ∀ x, Cof x (x <• k) from H x
  rw [Subgroup.sup_eq_closure] at hk
  induction hk using Subgroup.closure_induction with
  | mem s hs =>
    intro x
    rcases hs with hs | hs
    · have : x <• s ∈ rightOrbit (grigorchuk ω) x := ⟨s, hs, rfl⟩
      rw [(hA2 x).1] at this; exact this
    · have : x <• s ∈ rightOrbit finitary x := ⟨s, hs, rfl⟩
      rw [(hA2 x).2] at this; exact this
  | one => intro x; rw [one_smul_ray]; exact Filter.Eventually.of_forall fun _ => rfl
  | mul g h _ _ ihg ihh =>
    intro x
    rw [MulOpposite.op_mul, mul_smul]
    exact cof_trans (ihg x) (ihh _)
  | inv g _ ihg =>
    intro x
    have := ihg (x <• g⁻¹)
    have e : (x <• g⁻¹) <• g = x := by
      rw [← mul_smul, ← MulOpposite.op_mul, inv_mul_cancel, MulOpposite.op_one, one_smul]
    rw [e] at this
    exact cof_symm this

theorem isCofinal_iff_cof (x : Ray) : IsCofinal x ↔ Cof x oneRay :=
  ⟨fun h => h.mono fun _ h => h.symm, fun h => h.mono fun _ h => h.symm⟩

theorem isCofinal_smul_GL (ω : ℕ → Fin 3) {k : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary)
    {x : Ray} (hx : IsCofinal x) : IsCofinal (x <• k) := by
  rw [isCofinal_iff_cof] at hx ⊢
  exact cof_trans (cof_symm (cof_smul_GL ω hk x)) hx

theorem not_isCofinal_smul_GL (ω : ℕ → Fin 3) {k : BinaryTreeAut}
    (hk : k ∈ grigorchuk ω ⊔ finitary) {x : Ray} (hx : ¬ IsCofinal x) : ¬ IsCofinal (x <• k) := by
  rw [isCofinal_iff_cof] at hx ⊢
  exact fun h => hx (cof_trans (cof_smul_GL ω hk x) h)

theorem mem_GL_of_G {ω : ℕ → Fin 3} {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) :
    g ∈ grigorchuk ω ⊔ finitary := (le_sup_left : grigorchuk ω ≤ _) hg

theorem mem_GL_of_L {ω : ℕ → Fin 3} {g : BinaryTreeAut} (hg : g ∈ finitary) :
    g ∈ grigorchuk ω ⊔ finitary := (le_sup_right : finitary ≤ _) hg

/-! ### Eventual sections -/

/-- Along a cofinal ray, the sections of `k` are eventually those of some `c ∈ V` along `1^∞`. -/
def ESc (ω : ℕ → Fin 3) (k : BinaryTreeAut) : Prop :=
  ∀ x : Ray, IsCofinal x → ∃ N, ∃ c ∈ V ω, ∀ n ≥ N,
    sec k (rayPrefix x n) = sec c (List.replicate n true)

/-- Along a ray not cofinal with `1^∞`, the sections of `k` are eventually trivial. -/
def ESn (k : BinaryTreeAut) : Prop :=
  ∀ x : Ray, ¬ IsCofinal x → ∃ N, ∀ n ≥ N, sec k (rayPrefix x n) = 1

theorem ESc_mul (ω : ℕ → Fin 3) {k k' : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary)
    (h1 : ESc ω k) (h2 : ESc ω k') : ESc ω (k * k') := by
  intro x hx
  obtain ⟨N, c, hc, hN⟩ := h1 x hx
  obtain ⟨N', c', hc', hN'⟩ := h2 (x <• k) (isCofinal_smul_GL ω hk hx)
  refine ⟨max N N', c * c', V_mul hc hc', fun n hn => ?_⟩
  rw [sec_mul, ← rayPrefix_smul, hN n (le_of_max_le_left hn), hN' n (le_of_max_le_right hn),
    sec_V_mul hc]

theorem ESc_inv (ω : ℕ → Fin 3) {k : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary)
    (h1 : ESc ω k) : ESc ω k⁻¹ := by
  intro x hx
  obtain ⟨N, c, hc, hN⟩ := h1 (x <• k⁻¹) (isCofinal_smul_GL ω (Subgroup.inv_mem _ hk) hx)
  refine ⟨N, c, hc, fun n hn => ?_⟩
  rw [sec_inv, ← rayPrefix_smul, hN n hn]
  apply inv_eq_of_mul_eq_one_right
  rcases hc with rfl | ⟨γ, rfl⟩
  · rw [sec_one, one_mul]
  · rw [sec_gen_replicate_true, gen_mul_self]

theorem ESn_mul (ω : ℕ → Fin 3) {k k' : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary)
    (h1 : ESn k) (h2 : ESn k') : ESn (k * k') := by
  intro x hx
  obtain ⟨N, hN⟩ := h1 x hx
  obtain ⟨N', hN'⟩ := h2 (x <• k) (not_isCofinal_smul_GL ω hk hx)
  refine ⟨max N N', fun n hn => ?_⟩
  rw [sec_mul, ← rayPrefix_smul, hN n (le_of_max_le_left hn), hN' n (le_of_max_le_right hn),
    one_mul]

theorem ESn_inv (ω : ℕ → Fin 3) {k : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary)
    (h1 : ESn k) : ESn k⁻¹ := by
  intro x hx
  obtain ⟨N, hN⟩ := h1 (x <• k⁻¹) (not_isCofinal_smul_GL ω (Subgroup.inv_mem _ hk) hx)
  refine ⟨N, fun n hn => ?_⟩
  rw [sec_inv, ← rayPrefix_smul, hN n hn, inv_one]

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

theorem ES_gen (ω : ℕ → Fin 3) (γ : BCD) : ESc ω (gen ω γ) ∧ ESn (gen ω γ) := by
  have hzero : ∀ x : Ray, (∃ k, x k = false) → ∃ N, ∀ n ≥ N, sec (gen ω γ) (rayPrefix x n) = 1 := by
    intro x hx
    obtain ⟨k, hk, hmin⟩ := first_zero x hx
    refine ⟨k + 2, fun n hn => ?_⟩
    obtain ⟨z, hz, e⟩ := rayPrefix_first_zero x k hk hmin n hn
    rw [e, sec_gen_replicate ω γ k z hz]
  constructor
  · intro x hx
    by_cases hz : ∃ k, x k = false
    · obtain ⟨N, hN⟩ := hzero x hz
      exact ⟨N, 1, one_mem_V ω, fun n hn => by rw [hN n hn, sec_one]⟩
    · push Not at hz
      have hxo : x = oneRay := funext fun k => by simpa [oneRay] using hz k
      refine ⟨0, gen ω γ, gen_mem_V ω γ, fun n _ => ?_⟩
      rw [hxo, rayPrefix_oneRay]
  · intro x hx
    apply hzero x
    by_contra h
    push Not at h
    apply hx
    exact Filter.Eventually.of_forall fun k => by simpa using h k

theorem ES_grigA (ω : ℕ → Fin 3) : ESc ω grigA ∧ ESn grigA := by
  have h : ∀ x : Ray, ∀ n ≥ 1, sec grigA (rayPrefix x n) = 1 := by
    intro x n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [rayPrefix_succ, sec_grigA_cons]
  exact ⟨fun x _ => ⟨1, 1, one_mem_V ω, fun n hn => by rw [h x n hn, sec_one]⟩,
    fun x _ => ⟨1, h x⟩⟩

theorem ES_finitary (ω : ℕ → Fin 3) {f : BinaryTreeAut} (hf : f ∈ finitary) :
    ESc ω f ∧ ESn f := by
  obtain ⟨m, hm⟩ := hf
  have h : ∀ x : Ray, ∀ n ≥ m, sec f (rayPrefix x n) = 1 := fun x n hn =>
    sec_eq_one_of_le f hn hm _ (length_rayPrefix x n)
  exact ⟨fun x _ => ⟨m, 1, one_mem_V ω, fun n hn => by rw [h x n hn, sec_one]⟩,
    fun x _ => ⟨m, h x⟩⟩

theorem ES_G (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) : ESc ω g ∧ ESn g := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ES_grigA ω
    all_goals exact ES_gen ω _
  | one => exact ES_finitary ω (Subgroup.one_mem _)
  | mul g h hg _ ihg ihh =>
    exact ⟨ESc_mul ω (mem_GL_of_G hg) ihg.1 ihh.1, ESn_mul ω (mem_GL_of_G hg) ihg.2 ihh.2⟩
  | inv g hg ihg =>
    exact ⟨ESc_inv ω (mem_GL_of_G hg) ihg.1, ESn_inv ω (mem_GL_of_G hg) ihg.2⟩

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

/-- `g_v ∈ {1, a, b_{𝔰^{|v|}ω}}`. -/
def Good (ω : ℕ → Fin 3) (g : BinaryTreeAut) (v : List Bool) : Prop :=
  sec g v = 1 ∨ sec g v = grigA ∨ sec g v = gen (shiftSeq ω v.length) .b

theorem good_child (ω : ℕ → Fin 3) (g : BinaryTreeAut) (v : List Bool) (b : Bool)
    (h : Good ω g v) : Good ω g (v ++ [b]) := by
  unfold Good at h ⊢
  rw [sec_append]
  rcases h with h | h | h <;> rw [h]
  · left; exact sec_one _
  · left; exact sec_grigA b
  · cases b
    · rw [sec_gen_false]
      unfold letterElt
      split_ifs
      · right; left; rfl
      · left; rfl
    · right; right
      rw [sec_gen_true, shiftSeq_shiftSeq, List.length_append, List.length_singleton,
        Nat.add_comm]

theorem isOpen_prefix (n : ℕ) (P : List Bool → Prop) : IsOpen {x : Ray | P (rayPrefix x n)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  filter_upwards [eventually_rayPrefix_eq x n] with y hy
  show P (rayPrefix y n)
  rw [hy]; exact hx

/-- If the sections along every ray are eventually good, some level is good everywhere. -/
theorem exists_level_good (ω : ℕ → Fin 3) (g : BinaryTreeAut)
    (hev : ∀ x : Ray, ∃ N, Good ω g (rayPrefix x N)) :
    ∃ n, ∀ v : List Bool, v.length = n → Good ω g v := by
  set B : ℕ → Set Ray := fun n => {x | ¬ Good ω g (rayPrefix x n)} with hB
  have hmono : ∀ i, B (i + 1) ⊆ B i := by
    intro i x hx hgood
    apply hx
    rw [rayPrefix_add]
    have : rayPrefix (shiftRay x i) 1 = [x i] := by simp [rayPrefix, shiftRay]
    rw [this]
    exact good_child ω g _ _ hgood
  have hclosed : ∀ i, IsClosed (B i) := by
    intro i
    have : B i = {x : Ray | Good ω g (rayPrefix x i)}ᶜ := by ext x; simp [hB]
    rw [this]
    exact (isOpen_prefix i _).isClosed_compl
  by_contra hcon
  push Not at hcon
  have hne : ∀ i, (B i).Nonempty := by
    intro i
    obtain ⟨v, hv, hbad⟩ := hcon i
    refine ⟨prepend v oneRay, ?_⟩
    show ¬ Good ω g (rayPrefix (prepend v oneRay) i)
    rw [← hv, rayPrefix_prepend]
    exact hbad
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed B hmono hne
    (hclosed 0).isCompact hclosed
  obtain ⟨N, hN⟩ := hev x
  exact (Set.mem_iInter.mp hx N) hN

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
open scoped RightActions
open Garrido
set_option linter.unusedSimpArgs false
open ErschlerZheng
open B4Dev B3Dev GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev in
theorem solution (ω : ℕ → Fin 3)
    (_hω : ¬ ∃ i : Fin 3, ∀ᶠ k in Filter.atTop, ω k = i) (g : Garrido.BinaryTreeAut)
    (hg : g ∈ grigorchuk ω) :
    (∀ x ∈ orbitOne ω, (g, x) ∈ letterGerms ω .b) ↔
      ∃ n, ∀ v : List Bool, v.length = n →
        sec g v ∈ ({1, Garrido.grigA, gen (shiftSeq ω n) .b} : Set Garrido.BinaryTreeAut) := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
  have hL : IsAuxiliary (X := Ray) (grigorchuk ω) finitary := hA2.2.2 ω
  have horb : ∀ x : Ray, x ∈ orbitOne ω ↔ IsCofinal x := by
    intro x
    unfold orbitOne
    rw [(hA2.2.1 ω oneRay).1]
    rfl
  have hbo := oneRay_smul_gen ω .b
  have hsq : germ oneRay (gen ω .b) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← germ_mul hbo hbo, gen_mul_self, germ_one]
  have hgGL : g ∈ grigorchuk ω ⊔ finitary := mem_GL_of_G hg
  constructor
  · -- sections along every ray are eventually good, then compactness
    intro hall
    obtain ⟨n, hn⟩ := exists_level_good ω g (fun x => by
      by_cases hx : IsCofinal x
      · obtain ⟨-, -, hmem⟩ := hall x ((horb x).mpr hx)
        dsimp only at hmem
        obtain ⟨hσL, hσ⟩ := transport_spec (exists_L_of_mem hL x hg)
        set σ := transport finitary x (x <• g)
        obtain ⟨h, hhGL, hhx, hhe, hho⟩ := hmem
        obtain ⟨hρL, hρ⟩ := transport_spec (exists_L_of_orbit hL ((horb x).mpr hx))
        set ρ := transport finitary oneRay x
        have hk : x <• (g * σ⁻¹) = x := by rw [rsmul_mul, ← hσ, rsmul_inv_smul]
        have hK : oneRay <• (ρ * h * ρ⁻¹) = oneRay := conj_fix hρ hhx
        obtain ⟨N1, hN1⟩ := sec_conj_L hρL hρ hhx
        obtain ⟨N2, hN2⟩ := sec_eq_of_germ hhx hk hhe
        obtain ⟨N3, hN3⟩ := sec_mul_L hσL g x
        rcases mem_zpowers_sq hsq hho with e | e
        · obtain ⟨N4, hN4⟩ := sec_eq_of_germ hK (one_fix oneRay) (e.trans (germ_one _).symm)
          refine ⟨max (max N1 N2) (max N3 N4), Or.inl ?_⟩
          rw [← hN3 _ (by omega), ← hN2 _ (by omega), ← hN1 _ (by omega), ← rayPrefix_oneRay,
            hN4 _ (by omega), sec_one]
        · obtain ⟨N4, hN4⟩ := sec_eq_of_germ hK hbo e
          refine ⟨max (max N1 N2) (max N3 N4), Or.inr (Or.inr ?_)⟩
          rw [← hN3 _ (by omega), ← hN2 _ (by omega), ← hN1 _ (by omega), ← rayPrefix_oneRay,
            hN4 _ (by omega), rayPrefix_oneRay, sec_gen_replicate_true, length_rayPrefix]
      · obtain ⟨N, hN⟩ := (ES_G ω hg).2 x hx
        exact ⟨N, Or.inl (hN N le_rfl)⟩)
    refine ⟨n, fun v hv => ?_⟩
    rcases hn v hv with h | h | h
    · rw [h]; exact Set.mem_insert _ _
    · rw [h]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · rw [h, hv]; exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  · -- from good sections at one level
    rintro ⟨n₀, hn₀⟩ x hx
    have hxc := (horb x).mp hx
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
    -- the sections of `g` along `x` from level `n₀` on
    have hs := hn₀ (rayPrefix x n₀) (length_rayPrefix x n₀)
    have hsplit : ∀ n ≥ n₀, sec g (rayPrefix x n) =
        sec (sec g (rayPrefix x n₀)) (rayPrefix (shiftRay x n₀) (n - n₀)) := by
      intro n hn
      rw [show n = n₀ + (n - n₀) by omega, rayPrefix_add, sec_append]
      simp
    have hgoal : ∀ N : ℕ, (∀ n ≥ N, sec g (rayPrefix x n) = 1) ∨
        (∀ n ≥ N, sec g (rayPrefix x n) = gen (shiftSeq ω n) .b) →
        germ oneRay (ρ * (g * σ⁻¹) * ρ⁻¹) ∈ germLetterSubgroup ω .b := by
      intro N hN
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
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with h | h | h
    · exact hgoal n₀ (Or.inl fun n hn => by rw [hsplit n hn, h, sec_one])
    · refine hgoal (n₀ + 1) (Or.inl fun n hn => ?_)
      rw [hsplit n (by omega), h]
      obtain ⟨m, hm⟩ : ∃ m, n - n₀ = m + 1 := ⟨n - n₀ - 1, by omega⟩
      rw [hm, rayPrefix_succ, sec_grigA_cons]
    · rcases sec_gen_along (shiftSeq ω n₀) .b (shiftRay x n₀) with ⟨N, hN⟩ | hy
      · exact hgoal (n₀ + N) (Or.inl fun n hn => by
          rw [hsplit n (by omega), h, hN (n - n₀) (by omega)])
      · exact hgoal n₀ (Or.inr fun n hn => by
          rw [hsplit n hn, h, hy, rayPrefix_oneRay, sec_gen_replicate_true, shiftSeq_shiftSeq,
            show n - n₀ + n₀ = n by omega])
end
