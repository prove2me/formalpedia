-- Prove2me | solution 1 for ErschlerZheng.length_and_hElt_mem_rist_and_oneRay_smul_hProd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T04:47:21.998211+00:00
-- url     : https://prove2.me/submissions/aa4725c9-e0a8-4f33-a07c-5d8ddadfe660

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
import Definitions.Def_ErschlerZheng_Grigorchuk

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

/-! ### Words -/

end GrigBasic

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

theorem dec_mul {g h : BinaryTreeAut} {e f : Bool} {g0 g1 h0 h1 : BinaryTreeAut}
    (hg : Dec3 g e g0 g1) (hh : Dec3 h f h0 h1) :
    Dec3 (g * h) (xor e f) (g0 * (if e then h1 else h0)) (g1 * (if e then h0 else h1)) := by
  obtain ⟨he, hg0, hg1⟩ := hg
  obtain ⟨hf, hh0, hh1⟩ := hh
  refine ⟨by rw [rootSwap_mul, he, hf], ?_, ?_⟩
  · rw [sec_mul, hg0, singleton_smul, he]; cases e <;> simp [hh0, hh1]
  · rw [sec_mul, hg1, singleton_smul, he]; cases e <;> simp [hh0, hh1]

theorem dec_grigA : Dec3 grigA true 1 1 := ⟨rootSwap_grigA, sec_grigA _, sec_grigA _⟩

end ZetaDev

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

theorem iota_mem_rist (K : Subgroup BinaryTreeAut) (g : BinaryTreeAut) (u : List Bool)
    (hK : iota g u ∈ K) : iota g u ∈ rist K u :=
  ⟨hK, fun v hv => smul_iota_of_not_prefix g u v hv⟩

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

theorem evalWord_mem_wordBall (ω : ℕ → Fin 3) (w : List Gen4) :
    evalWord ω 0 w ∈ Chou.wordBall (gens ω) w.length := by
  refine ⟨w.map (lm grigA (gen (shiftSeq ω 0))), by simp, ?_, ?_⟩
  · intro g hg
    left
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hg
    rw [shiftSeq_zero]
    cases l <;> simp [gens]
  · rw [evalWord_eq_evL]; rfl

theorem mem_grigorchuk_of_mem_wordBall (ω : ℕ → Fin 3) (g : BinaryTreeAut) (m : ℕ)
    (hg : g ∈ Chou.wordBall (gens ω) m) : g ∈ grigorchuk ω := by
  obtain ⟨l, _, hl, rfl⟩ := hg
  apply Subgroup.list_prod_mem
  intro x hx
  rcases hl x hx with h | h
  · exact Subgroup.subset_closure h
  · have := Subgroup.subset_closure (k := gens ω) h
    simpa using (grigorchuk ω).inv_mem this

theorem wordLength_le_of_mem_wordBall (ω : ℕ → Fin 3) (g : BinaryTreeAut) (m : ℕ)
    (hg : g ∈ Chou.wordBall (gens ω) m) : wordLength (gens ω) g ≤ m :=
  Nat.sInf_le hg

/-- Fact 7.6 for every `n` (at `n = 0` no condition on `γ`) and every string. -/
theorem iota_comm_mem_and_wordLength_le (ω : ℕ → Fin 3) (n : ℕ) (γ : BCD)
    (hγ : 1 ≤ n → letterValue (ω (n - 1)) γ = false) (v : List Bool) (hv : v.length = n) :
    iota ⁅gen (shiftSeq ω n) γ, grigA⁆ v ∈ grigorchuk ω ∧
      wordLength (gens ω) (iota ⁅gen (shiftSeq ω n) γ, grigA⁆ v) ≤ 2 ^ (n + 2) := by
  obtain ⟨w, hev, hlen, -⟩ := exists_word ω n γ hγ v 0 (by omega)
  have hb := evalWord_mem_wordBall ω w
  rw [hev, hlen, hv] at hb
  exact ⟨mem_grigorchuk_of_mem_wordBall ω _ _ hb, wordLength_le_of_mem_wordBall ω _ _ hb⟩

end ConstrIota

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

theorem ray_smul_mul (g h : BinaryTreeAut) (x : Ray) : x <• (g * h) = (x <• g) <• h := by
  rw [MulOpposite.op_mul, mul_smul]

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

theorem prepend_true_oneRay : prepend [true] oneRay = oneRay := by
  funext i
  unfold prepend oneRay
  split_ifs <;> simp_all

theorem prepend_nil (x : Ray) : prepend [] x = x := by
  funext i; simp [prepend]

theorem prepend_smul_iota (g : BinaryTreeAut) (u : List Bool) (x : Ray) :
    prepend u x <• iota g u = prepend u (x <• g) := by
  rw [prepend_smul, sec_iota_self]
  congr 1
  have := append_smul_iota g u []
  simpa [nil_smul] using this

theorem oneRay_smul_grigA : oneRay <• grigA = prepend [false] oneRay := by
  conv_lhs => rw [← prepend_true_oneRay]
  rw [prepend_smul, sec_grigA, one_smul_ray]
  congr 1

theorem oneRay_smul_comm_b (ω : ℕ → Fin 3) (hb : letterValue (ω 0) .b = true) :
    oneRay <• ⁅gen ω .b, grigA⁆ = prepend [true, false] oneRay := by
  obtain ⟨h0, -, h1⟩ := dec_comm_b ω hb
  conv_lhs => rw [← prepend_true_oneRay]
  rw [prepend_smul, h1, singleton_smul, h0, ray_smul_mul, oneRay_smul_gen, oneRay_smul_grigA,
    ← prepend_append]
  rfl

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

theorem take_succ_eq (v : List Bool) (t : ℕ) (ht : t < v.length) :
    v.take (t + 1) = v.take t ++ [v[t]] := by
  rw [List.take_succ, List.getElem?_eq_getElem ht]
  rfl

end ConstrH

end ErschlerZheng
end

section
open scoped RightActions commutatorElement
open Garrido
open ErschlerZheng
open ErschlerZheng.ConstrH
open GrigBasic ZetaDev ConstrW ConstrIota RayBasic SchreierDev
theorem solution (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (j k : ℕ) (hk : D ∣ k) (v : List Bool) (hv : v ∈ vSet D ω j k) :
    v.length = D - j % D + k + frM D ω (ellIndex D k j) + 3 ∧
    (∀ i, 1 ≤ i → v[i - 1]? = some false →
      (ω (j + i - 3) = 2 ∧ (ω (j + i - 2) = 0 ∨ ω (j + i - 2) = 1) ∧ ω (j + i - 1) = 1) ∧
      hElt ω j v i ∈ rist (grigorchuk (shiftSeq ω j)) (v.take (i - 2)) ∧
      [true] <• ⁅gen (shiftSeq ω (j + i - 2)) .b, Garrido.grigA⁆ = [true] ∧
      sec ⁅gen (shiftSeq ω (j + i - 2)) .b, Garrido.grigA⁆ [true] =
        gen (shiftSeq ω (j + i - 1)) .b * Garrido.grigA) ∧
    oneRay <• hProd ω j v = prepend v oneRay := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  have hjD : j % D < D := Nat.mod_lt _ (by omega)
  -- the digits `0`
  have hzero : ∀ t (ht : t < v.length), v[t] = false →
      1 ≤ t ∧ v[t - 1]'(by omega) = true ∧ j + (t + 1) ∈ frI D ω := by
    intro t ht hf
    obtain ⟨h1, h2⟩ := getElem_of_mem_vSet D ω hω j k hk v hv t ht hf
    refine ⟨by omega, ?_, h2⟩
    by_contra hne
    have hf' : v[t - 1]'(by omega) = false := by simpa using hne
    obtain ⟨-, h3⟩ := getElem_of_mem_vSet D ω hω j k hk v hv (t - 1) (by omega) hf'
    have := frI_sep D ω hω h3 h2 (by omega)
    omega
  have hb : ∀ t (ht : t < v.length), v[t] = false →
      letterValue ((shiftSeq ω (j + (t + 1) - 2)) 0) .b = true := by
    intro t ht hf
    obtain ⟨-, -, hI⟩ := hzero t ht hf
    obtain ⟨-, -, h, -⟩ := window_of_mem_frI D ω hω hI
    simp only [shiftSeq, Nat.zero_add]
    rcases h with h | h <;> rw [h] <;> decide
  refine ⟨length_of_mem_vSet D ω j k v hv, ?_, ?_⟩
  · intro i hi hvi
    obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hvi
    have ht : t < v.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hvi; simp at hvi
    have hf : v[t] = false := by rw [List.getElem?_eq_getElem ht] at hvi; simpa using hvi
    obtain ⟨ht1, -, hI⟩ := hzero t ht hf
    obtain ⟨-, w1, w2, w3⟩ := window_of_mem_frI D ω hω hI
    refine ⟨⟨w1, w2, w3⟩, ?_, ?_, ?_⟩
    · rw [hElt_of_false ω j v t ht hf]
      apply iota_mem_rist
      have hshift : shiftSeq ω (j + (t + 1) - 2) = shiftSeq (shiftSeq ω j) (t + 1 - 2) := by
        rw [shiftSeq_shiftSeq]; congr 1; omega
      rw [hshift]
      refine (iota_comm_mem_and_wordLength_le (shiftSeq ω j) (t + 1 - 2) .b ?_ _ ?_).1
      · intro _
        simp only [shiftSeq]
        rw [show t + 1 - 2 - 1 + j = j + (t + 1) - 3 by omega, w1]
        decide
      · simp; omega
    · obtain ⟨h0, -, -⟩ := dec_comm_b _ (hb t ht hf)
      rw [singleton_smul, h0]; rfl
    · obtain ⟨-, -, h1⟩ := dec_comm_b _ (hb t ht hf)
      rw [h1, shiftSeq_shiftSeq]
      congr 3
      omega
  · -- `1^∞ · h_1 ⋯ h_t = v_1 … v_t 1^∞`
    have key : ∀ t ≤ v.length,
        oneRay <• ((List.range t).map fun i => hElt ω j v (i + 1)).prod =
          prepend (v.take t) oneRay := by
      intro t
      induction t with
      | zero => intro _; simp [prepend_nil]
      | succ t ih =>
        intro ht
        rw [List.range_succ, List.map_append, List.prod_append, ray_smul_mul, ih (by omega)]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        rw [take_succ_eq v t (by omega)]
        cases hvt : v[t]'(by omega)
        · obtain ⟨ht1, hprev, -⟩ := hzero t (by omega) hvt
          rw [hElt_of_false ω j v t (by omega) hvt]
          have htake : v.take t = v.take (t + 1 - 2) ++ [true] := by
            have e : t + 1 - 2 = t - 1 := by omega
            rw [e]
            conv_lhs => rw [show t = (t - 1) + 1 by omega]
            rw [take_succ_eq v (t - 1) (by omega), hprev]
          rw [htake, prepend_append, prepend_true_oneRay, prepend_smul_iota,
            oneRay_smul_comm_b _ (hb t (by omega) hvt), ← prepend_append]
          simp
        · rw [hElt_of_true ω j v t (by omega) hvt, one_smul_ray, prepend_append,
            prepend_true_oneRay]
    have := key v.length le_rfl
    rw [List.take_length] at this
    exact this
end
