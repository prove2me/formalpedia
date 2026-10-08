-- Prove2me | solution 1 for ErschlerZheng.sec_gen_nil_and_cons_false_smul_and_germ_eq_one_and_hasGermAt_iff_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.594643+00:00
-- url     : https://prove2.me/submissions/64d2f7c3-b308-4758-9e0f-50cc944bbc67

import Mathlib
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
import Definitions.Def_ErschlerZheng_Grigorchuk

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

theorem germEq_refl (x : X) (g : H) : GermEq x g g := Filter.Eventually.of_forall fun _ => rfl

theorem GermEq.symm' {x : X} {g h : H} (e : GermEq x g h) : GermEq x h g := e.mono fun _ h => h.symm

theorem germEq_comp {x : X} {g₁ g₂ h₁ h₂ : H} (hg : GermEq x g₁ g₂) (hh : GermEq (x <• g₁) h₁ h₂) :
    GermEq x (g₁ * h₁) (g₂ * h₂) :=
  (germEq_mul_and_germ_mul x).1 g₁ g₂ h₁ h₂ hg hh

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

end GermBase

end ErschlerZheng
end

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

/-- Whether `g` swaps the two vertices of level 1. -/
def rootSwap (g : BinaryTreeAut) : Bool := decide ([false] <• g = [true])

theorem rootSwap_one : rootSwap 1 = false := by
  unfold rootSwap; simp

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

theorem shiftRay_zero (x : Ray) : shiftRay x 0 = x := rfl

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
# New germ items: the condition `x = x₁ … xₙ 1^∞` in `HasGermAt`, and the choice of `σ` in (3.3)

1. For `ω₀ = 0`, the generator `d_ω` is its own section at the empty prefix, fixes every vertex
   below `0`, has trivial germ at `01^∞`, and has a `d`-germ at `01^∞` in the sense of
   `HasGermAt` exactly when all but finitely many letters of `ω` are `0`.
2. When the isotropy group of `L` at `x` is trivial, `germConfig L g x` is the germ of `gσ⁻¹` at
   `x` for every `σ ∈ L` with `x·σ = x·g`, not only for the chosen `transport L x (x·g)`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace NewGerms

open GrigBasic RayBasic GermBase

/-! ### Cylinders and sections (as in `GrigGermsDev`, whose module imports an unrelated stub) -/

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

/-- Two automorphisms agreeing on a vertex `x₁ … xₙ` of `x` and with equal sections there agree
near `x`. -/
theorem germEq_of_sec {x : Ray} {k k' : BinaryTreeAut} {n : ℕ}
    (hv : rayPrefix x n <• k = rayPrefix x n <• k')
    (hs : sec k (rayPrefix x n) = sec k' (rayPrefix x n)) : GermEq x k k' := by
  filter_upwards [eventually_rayPrefix_eq x n] with y hy
  have e : ∀ k : BinaryTreeAut,
      y <• k = prepend (rayPrefix x n <• k) (shiftRay y n <• sec k (rayPrefix x n)) := by
    intro k
    conv_lhs => rw [← prepend_rayPrefix_shiftRay y n]
    rw [hy, prepend_smul]
  rw [e k, e k', hv, hs]

theorem sec_gen_replicate_true (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    sec (gen ω γ) (List.replicate n true) = gen (shiftSeq ω n) γ := by
  induction n generalizing ω with
  | zero => rw [List.replicate_zero, sec_nil, shiftSeq_zero]
  | succ n ih =>
    rw [List.replicate_succ, sec_cons, sec_gen_true, ih, shiftSeq_shiftSeq]

/-! ### Item 1 -/

/-- The letter `i` vanishes on `d` exactly when `i = 0`. -/
theorem letterValue_d_eq_false_iff (i : Fin 3) : letterValue i .d = false ↔ i = 0 := by
  fin_cases i <;> decide

/-- `d_ω` acts trivially on the tree when every letter of `ω` is `0`. -/
theorem gen_d_eq_one_of_forall_eq_zero {ω : ℕ → Fin 3} (h : ∀ k, ω k = 0) : gen ω .d = 1 := by
  have key : ∀ (ω : ℕ → Fin 3), (∀ k, ω k = 0) → ∀ w : List Bool, genFun ω .d w = w := by
    intro ω h w
    induction w generalizing ω with
    | nil => rfl
    | cons b w ih =>
      cases b
      · have h0 : letterValue (ω 0) .d = false := (letterValue_d_eq_false_iff _).mpr (h 0)
        simp [genFun, h0]
      · simp only [genFun]
        rw [ih (shiftSeq ω 1) (fun k => h (k + 1))]
  exact Subtype.ext (Equiv.ext fun w => key ω h w)

/-- Conversely, if `d_ω` acts trivially then every letter of `ω` is `0`. -/
theorem forall_eq_zero_of_gen_d_eq_one {ω : ℕ → Fin 3} (h : gen ω .d = 1) (k : ℕ) : ω k = 0 := by
  have h1 := sec_gen_replicate_true ω .d k
  rw [h, sec_one] at h1
  have h2 := sec_gen_false (shiftSeq ω k) .d
  rw [← h1, sec_one] at h2
  have h3 : shiftSeq ω k 0 = ω k := by simp [shiftSeq]
  rw [h3] at h2
  by_contra hk
  have hv : letterValue (ω k) .d = true := by
    cases hl : letterValue (ω k) .d
    · exact absurd ((letterValue_d_eq_false_iff _).mp hl) hk
    · rfl
  unfold letterElt at h2
  rw [if_pos hv] at h2
  have := rootSwap_grigA
  rw [← h2, rootSwap_one] at this
  exact Bool.false_ne_true this

/-- For `ω₀ = 0`, the section of `d_ω` at `0` is trivial. -/
theorem sec_gen_d_false {ω : ℕ → Fin 3} (hω : ω 0 = 0) : sec (gen ω .d) [false] = 1 := by
  rw [sec_gen_false]
  unfold letterElt
  rw [if_neg (by rw [(letterValue_d_eq_false_iff _).mpr hω]; decide)]

/-- For `ω₀ = 0`, the section of `d_ω` at every vertex below `0` is trivial. -/
theorem sec_gen_d_cons_false {ω : ℕ → Fin 3} (hω : ω 0 = 0) (u : List Bool) :
    sec (gen ω .d) (false :: u) = 1 := by
  rw [sec_cons, sec_gen_d_false hω, sec_one]

theorem cons_false_smul_gen_d {ω : ℕ → Fin 3} (hω : ω 0 = 0) (v : List Bool) :
    (false :: v) <• gen ω .d = false :: v := by
  rw [vertex_smul_gen]
  have h0 : letterValue (ω 0) .d = false := (letterValue_d_eq_false_iff _).mpr hω
  simp [genFun, h0]

theorem prepend_false_oneRay_zero : prepend [false] oneRay 0 = false := rfl

theorem shiftRay_prepend_false_oneRay (n : ℕ) : shiftRay (prepend [false] oneRay) (n + 1) = oneRay := by
  funext i
  simp [shiftRay, prepend, oneRay]

theorem rayPrefix_prepend_false_oneRay (n : ℕ) :
    rayPrefix (prepend [false] oneRay) (n + 1) = false :: rayPrefix oneRay n := by
  rw [rayPrefix_succ, prepend_false_oneRay_zero]
  have : shiftRay (prepend [false] oneRay) 1 = oneRay := shiftRay_prepend_false_oneRay 0
  rw [this]

theorem prepend_false_oneRay_smul_gen_d {ω : ℕ → Fin 3} (hω : ω 0 = 0) :
    prepend [false] oneRay <• gen ω .d = prepend [false] oneRay := by
  rw [prepend_smul, cons_false_smul_gen_d hω [], sec_gen_d_false hω, one_smul_ray]

theorem germ_prepend_false_oneRay_gen_d {ω : ℕ → Fin 3} (hω : ω 0 = 0) :
    germ (prepend [false] oneRay) (gen ω .d) = 1 := by
  have hfix := prepend_false_oneRay_smul_gen_d hω
  rw [← germ_one (prepend [false] oneRay), germ_eq_iff hfix (rsmul_one _)]
  apply germEq_of_sec (n := 1)
  · rw [rayPrefix_prepend_false_oneRay 0]
    rw [cons_false_smul_gen_d hω]
    rfl
  · rw [rayPrefix_prepend_false_oneRay 0, sec_gen_d_cons_false hω, sec_one]

theorem hasGermAt_prepend_false_oneRay_gen_d_iff {ω : ℕ → Fin 3} (hω : ω 0 = 0) :
    HasGermAt ω .d (gen ω .d) (prepend [false] oneRay) ↔ ∀ᶠ k in Filter.atTop, ω k = 0 := by
  constructor
  · rintro ⟨n, hshift, hsec⟩
    cases n with
    | zero =>
      have := congrFun hshift 0
      rw [shiftRay_zero, prepend_false_oneRay_zero] at this
      exact absurd this (by simp [oneRay])
    | succ m =>
      rw [rayPrefix_prepend_false_oneRay, sec_gen_d_cons_false hω] at hsec
      have h := forall_eq_zero_of_gen_d_eq_one hsec.symm
      rw [Filter.eventually_atTop]
      refine ⟨m + 1, fun k hk => ?_⟩
      have := h (k - (m + 1))
      simp only [shiftSeq] at this
      rwa [Nat.sub_add_cancel hk] at this
  · intro h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
    refine ⟨N + 1, shiftRay_prepend_false_oneRay N, ?_⟩
    rw [rayPrefix_prepend_false_oneRay, sec_gen_d_cons_false hω]
    symm
    exact gen_d_eq_one_of_forall_eq_zero fun k => hN _ (by omega)

end NewGerms

/-! ### Item 2 -/

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open NewGerms in
theorem solution
    (ω : ℕ → Fin 3) (hω : ω 0 = 0) :
    sec (gen ω .d) [] = gen (shiftSeq ω 0) .d ∧
      (∀ v : List Bool, (false :: v) <• gen ω .d = false :: v) ∧
      germ (prepend [false] oneRay) (gen ω .d) = 1 ∧
      (HasGermAt ω .d (gen ω .d) (prepend [false] oneRay) ↔
        ∀ᶠ k in Filter.atTop, ω k = 0) := by
  refine ⟨?_, cons_false_smul_gen_d hω, germ_prepend_false_oneRay_gen_d hω,
    hasGermAt_prepend_false_oneRay_gen_d_iff hω⟩
  rw [GrigBasic.sec_nil, GrigBasic.shiftSeq_zero]
end
