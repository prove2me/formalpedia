-- Prove2me | solution 1 for ErschlerZheng.orbitKernel_upsilon_eq_and_boundarySize_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T07:17:27.429577+00:00
-- url     : https://prove2.me/submissions/6cc7deec-7e15-4b97-a227-e561566fff45

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_vertex_smul_eq_smul_seqG_of_mem_fSet
import Theorems.Thm_ErschlerZheng_seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms
import Definitions.Def_MarkovChain_HeatKernels
import Theorems.Thm_ErschlerZheng_fst_eq_of_smul_theta_eq
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

theorem rootSwap_gen (ω : ℕ → Fin 3) (γ : BCD) : rootSwap (gen ω γ) = false := by
  unfold rootSwap
  rw [vertex_smul_gen]
  simp [genFun]

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

/-! ### The free-group words -/

/-! ### The parity is a function of the element -/

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

/-! ### The lift -/


/-! ### The invariant `Kill` under lifts -/

/-! ### The words of Fact 7.6 -/

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

/-! ### Generators on rays that are eventually all ones -/

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

theorem length_of_mem_vSet (D : ℕ) (ω : ℕ → Fin 3) (j k : ℕ) (v : List Bool)
    (hv : v ∈ vSet D ω j k) :
    v.length = D - j % D + k + frM D ω (ellIndex D k j) + 3 := by
  obtain ⟨u, ⟨hu, -⟩, rfl⟩ := hv
  simp [hu]
  omega

/-! ### `[b, a]` below `1` -/

/-! ### The milestone -/

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

/-! ### Free-group words from even-length words -/

/-! ### The parity character and the substitutions -/

/-! ### The structure of `g̃` -/

/-! ### The free word for `a𝔠` and the tail condition -/

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

/-! ### The milestone -/

end ConstrSeq

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

/-! ### The milestone -/

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

/-! ### `|1^∞ ∧ v|` -/

theorem take_of_le_commonPrefixLength (v : List Bool) (p : ℕ)
    (h : p ≤ commonPrefixLength v oneRay) : p ≤ v.length ∧ v.take p = List.replicate p true := by
  unfold commonPrefixLength at h
  have hro : rayPrefix oneRay v.length = List.replicate v.length true := by
    apply List.ext_getElem <;> simp [rayPrefix, oneRay]
  rw [hro] at h
  set l := (v.zip (List.replicate v.length true)).takeWhile fun p => p.1 = p.2
  have hpre : l <+: v.zip (List.replicate v.length true) := List.takeWhile_prefix _
  have hl : l.length ≤ v.length := by
    have := hpre.length_le; simpa using this
  refine ⟨by omega, ?_⟩
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_replicate]
    have hi : i < l.length := by simp at h2; omega
    have hmem : l[i] ∈ l := List.getElem_mem hi
    have hP := List.mem_takeWhile_imp hmem
    have heq : l[i] = (v.zip (List.replicate v.length true))[i]'(by
        have := hpre.length_le; omega) := hpre.getElem hi
    rw [heq] at hP
    simpa using hP

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

theorem le_length_takeWhile {α : Type*} (P : α → Bool) :
    ∀ (p : ℕ) (l : List α) (hl : p ≤ l.length), (∀ i (h : i < p), P (l[i]'(by omega)) = true) →
      p ≤ (l.takeWhile P).length := by
  intro p
  induction p with
  | zero => intros; exact Nat.zero_le _
  | succ p ih =>
    intro l hl h
    cases l with
    | nil => simp at hl
    | cons a l =>
      have h0 : P a = true := h 0 (by omega)
      rw [List.takeWhile_cons, if_pos h0]
      simp only [List.length_cons, Nat.add_le_add_iff_right]
      exact ih l (by simpa using hl) (fun i hi => h (i + 1) (by omega))

theorem le_commonPrefixLength_iff (v : List Bool) (p : ℕ) :
    p ≤ commonPrefixLength v oneRay ↔ List.replicate p true <+: v := by
  constructor
  · intro h
    obtain ⟨hl, ht⟩ := take_of_le_commonPrefixLength v p h
    rw [List.prefix_iff_eq_take, List.length_replicate, ht]
  · intro h
    have hl : p ≤ v.length := by simpa using h.length_le
    have ht : v.take p = List.replicate p true := by
      rw [List.prefix_iff_eq_take, List.length_replicate] at h; exact h.symm
    unfold commonPrefixLength
    apply le_length_takeWhile _ p _ (by simp [length_rayPrefix]; omega)
    intro i hi
    simp only [List.getElem_zip, decide_eq_true_eq]
    have h1 : v[i]'(by omega) = true := by
      have := congrArg (fun l : List Bool => l[i]?) ht
      simp only [List.getElem?_take, show i < p from hi, if_true,
        List.getElem?_replicate, if_true] at this
      rw [List.getElem?_eq_getElem (by omega)] at this
      simpa using this
    rw [h1, getElem_rayPrefix]
    rfl

/-! ### Injectivity of `v ↦ 𝔠^v_j` -/

/-! ### The section of `g̃^v_j` at `1^j` -/

/-! ### The count -/

end ConstrF8

end ErschlerZheng
end

section
/-!
# Lemma 7.15: on level `n + D + 1`, `x·θ_n(ε, γ)` determines `ε` (Erschler–Zheng p. 44)

By Fact 7.14 every `γ_i ∈ 𝔉_{i,n}` acts on level `n + D + 1` as `g_i`, so `x·θ_n(ε, γ) =
x·g_n^{ε_n} ⋯ g_1^{ε_1}` there. Each `g_k` fixes the first `k` digits and flips digit `k + 1`
(it fixes level `k` and its sections there swap level 1, (7.1)); so digit `2` of the result is
`x_2 + ε_1`, and peeling off `g_1^{ε_1}` the argument repeats.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrLemma715

open GrigBasic

theorem ofFn_rev {α : Type*} (n : ℕ) (f : Fin n → α) :
    List.ofFn (fun i => f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    congr 1
    ext
    simp [Fin.rev]
    omega

/-- Lists of factors that act alike on level `N` have products that act alike there. -/
theorem prod_smul_eq (N : ℕ) : ∀ (l1 l2 : List BinaryTreeAut), l1.length = l2.length →
    (∀ i (h1 : i < l1.length) (h2 : i < l2.length) (w : List Bool), w.length = N →
      w <• l1[i] = w <• l2[i]) →
    ∀ z : List Bool, z.length = N → z <• l1.prod = z <• l2.prod := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 hl _ z _
    rw [List.length_nil] at hl
    rw [List.eq_nil_of_length_eq_zero hl.symm]
  | cons a l1 ih =>
    intro l2 hl h z hz
    cases l2 with
    | nil => simp at hl
    | cons b l2 =>
      have h0 : z <• a = z <• b := h 0 (by simp) (by simp) z hz
      rw [List.prod_cons, List.prod_cons, vertex_smul_mul, vertex_smul_mul, h0]
      exact ih l2 (by simpa using hl) (fun i h1 h2 w hw => h (i + 1) (by simpa using h1)
        (by simpa using h2) w hw) _ (by rw [length_vertex_smul, hz])

/-- The factors `g_{s+1}^{e_0}, g_{s+2}^{e_1}, …`. -/
def facs (g : ℕ → BinaryTreeAut) : ℕ → List Bool → List BinaryTreeAut
  | _, [] => []
  | s, b :: e => g (s + 1) ^ b.toNat :: facs g (s + 1) e

theorem ofFn_eq_facs (g : ℕ → BinaryTreeAut) : ∀ (n s : ℕ) (e : Fin n → Bool),
    List.ofFn (fun i : Fin n => g (s + i + 1) ^ (e i).toNat) = facs g s (List.ofFn e) := by
  intro n
  induction n with
  | zero => intro s e; rfl
  | succ n ih =>
    intro s e
    rw [List.ofFn_succ, List.ofFn_succ, facs]
    congr 1
    rw [← ih (s + 1) (fun i => e i.succ)]
    congr 1
    funext i
    simp only [Fin.val_succ]
    congr 2
    omega

/-- A family `g_k` fixing level `k` with sections there that swap level 1. -/
structure Flips (g : ℕ → BinaryTreeAut) : Prop where
  fix : ∀ k, 1 ≤ k → ∀ v : List Bool, v.length = k → v <• g k = v
  swap : ∀ k, 1 ≤ k → ∀ v : List Bool, v.length = k → rootSwap (sec (g k) v) = true

theorem fix_take {g : BinaryTreeAut} {k : ℕ} (hg : ∀ v : List Bool, v.length = k → v <• g = v)
    (z : List Bool) (hz : k ≤ z.length) : (z <• g).take k = z.take k := by
  have h := append_vertex_smul g (z.take k) (z.drop k)
  rw [List.take_append_drop, hg (z.take k) (by simp; omega)] at h
  rw [h, List.take_left' (by simp; omega)]

/-- All factors `g_k`, `k ⩾ s + 1`, fix the first `s + 1` digits. -/
theorem facs_take (g : ℕ → BinaryTreeAut) (hg : Flips g) :
    ∀ (e : List Bool) (s : ℕ) (z : List Bool), s + e.length ≤ z.length →
      (z <• (facs g s e).reverse.prod).take (s + 1) = z.take (s + 1) ∧
        (z <• (facs g s e).reverse.prod).length = z.length := by
  intro e
  induction e with
  | nil => intro s z _; simp [facs]
  | cons b e ih =>
    intro s z hz
    simp only [facs, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      vertex_smul_mul]
    obtain ⟨h1, h2⟩ := ih (s + 1) z (by simp at hz; omega)
    set y := z <• (facs g (s + 1) e).reverse.prod
    refine ⟨?_, by rw [length_vertex_smul, h2]⟩
    have hy : (y <• g (s + 1) ^ b.toNat).take (s + 1) = y.take (s + 1) := by
      cases b
      · simp
      · simp only [Bool.toNat_true, pow_one]
        exact fix_take (hg.fix (s + 1) (by omega)) y (by simp at hz; omega)
    rw [hy]
    have := congrArg (List.take (s + 1)) h1
    simpa [List.take_take] using this

/-- `g_{s+1}` flips digit `s + 1` (Lean index). -/
theorem flip_digit (g : ℕ → BinaryTreeAut) (hg : Flips g) (s : ℕ) (y : List Bool)
    (hy : s + 2 ≤ y.length) :
    (y <• g (s + 1))[s + 1]'(by rw [length_vertex_smul]; omega) = !y[s + 1] := by
  have h := append_vertex_smul (g (s + 1)) (y.take (s + 1)) (y.drop (s + 1))
  rw [List.take_append_drop, hg.fix (s + 1) (by omega) (y.take (s + 1)) (by simp; omega)] at h
  have hd : y.drop (s + 1) = y[s + 1] :: y.drop (s + 2) := by
    rw [List.drop_eq_getElem_cons (by omega)]
  rw [hd, cons_smul, hg.swap (s + 1) (by omega) (y.take (s + 1)) (by simp; omega)] at h
  have key : (y <• g (s + 1))[s + 1]? = some (!y[s + 1]) := by
    rw [h, List.getElem?_append_right (by simp only [List.length_take]; omega), List.length_take,
      min_eq_left (by omega), Nat.sub_self, List.getElem?_cons_zero, Bool.xor_true]
  rw [List.getElem?_eq_getElem (by rw [length_vertex_smul]; omega)] at key
  exact Option.some.inj key

theorem facs_inj (g : ℕ → BinaryTreeAut) (hg : Flips g) :
    ∀ (e e' : List Bool) (s : ℕ), e.length = e'.length → ∀ z : List Bool,
      s + e.length + 1 ≤ z.length →
      z <• (facs g s e).reverse.prod = z <• (facs g s e').reverse.prod → e = e' := by
  intro e
  induction e with
  | nil =>
    intro e' s hl
    have : e' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst this; intros; rfl
  | cons b e ih =>
    intro e' s hl z hz heq
    cases e' with
    | nil => simp at hl
    | cons b' e' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [facs, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
        vertex_smul_mul] at heq
      obtain ⟨t1, l1⟩ := facs_take g hg e (s + 1) z (by simp at hz; omega)
      obtain ⟨t2, l2⟩ := facs_take g hg e' (s + 1) z (by simp at hz; omega)
      set y := z <• (facs g (s + 1) e).reverse.prod
      set y' := z <• (facs g (s + 1) e').reverse.prod
      have hlen : s + 2 ≤ z.length := by simp at hz; omega
      -- digit `s + 1` of `y` and `y'` is that of `z`
      have hdy : ∀ (x : List Bool) (hx : x.take (s + 2) = z.take (s + 2)) (hxl : x.length = z.length),
          x[s + 1]'(by omega) = z[s + 1]'(by omega) := by
        intro x hx hxl
        have := congrArg (fun l : List Bool => l[s + 1]?) hx
        simp only [List.getElem?_take] at this
        simp only [show s + 1 < s + 2 by omega, if_true] at this
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
        simpa using this
      have hb : b = b' := by
        have key : ∀ (x : List Bool) (c : Bool) (hx : x.take (s + 2) = z.take (s + 2))
            (hxl : x.length = z.length),
            (x <• g (s + 1) ^ c.toNat)[s + 1]'(by rw [length_vertex_smul]; omega) =
              xor (z[s + 1]'(by omega)) c := by
          intro x c hx hxl
          cases c
          · simp only [Bool.toNat_false, pow_zero, Bool.xor_false]
            have : x <• (1 : BinaryTreeAut) = x := one_smul _ x
            simp only [this]
            exact hdy x hx hxl
          · simp only [Bool.toNat_true, pow_one]
            rw [flip_digit g hg s x (by omega), hdy x hx hxl]
            simp
        have e1 := key y b t1 l1
        have e2 := key y' b' t2 l2
        have := congrArg (fun l : List Bool => l[s + 1]?) heq
        rw [List.getElem?_eq_getElem (by rw [length_vertex_smul]; omega),
          List.getElem?_eq_getElem (by rw [length_vertex_smul]; omega), e1, e2] at this
        simp only [Option.some.injEq] at this
        revert this
        generalize z[s + 1]'(by omega) = c
        cases b <;> cases b' <;> cases c <;> decide
      subst hb
      have heq' : y = y' := by
        have := congrArg (fun x => x <• (g (s + 1) ^ b.toNat)⁻¹) heq
        simpa only [vertex_smul_smul_inv] using this
      rw [ih e' (s + 1) hl z (by simp at hz; omega) heq']

theorem flips_seqG (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) : Flips (seqG ω) := by
  obtain ⟨h1, -, -⟩ := seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω
  refine ⟨fun k hk v hv => (h1 k hk).1.2 v hv, fun k hk v hv => ?_⟩
  have hW : ∀ x : Gen4, x ≠ .a → rootSwap (evalWord ω k [.a, x]) = true := by
    intro x hx
    cases x <;> simp_all [evalWord, rootSwap_mul, rootSwap_grigA, rootSwap_gen]
  have hW' := hW (if ω (k - 1) = 2 then .c else .b) (by split_ifs <;> simp)
  rcases (h1 k hk).2 v hv with h | h <;> rw [h]
  · exact hW'
  · rw [rootSwap_mul, rootSwap_mul, rootSwap_grigA, hW']; rfl

end ConstrLemma715

end ErschlerZheng
end

section
/-!
# The kernels of `υ_n` on `L_n` and the isoperimetric bound (Erschler–Zheng p. 48)
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrG9

open GrigBasic ConstrW ConstrH ConstrF8 ConstrLemma715

/-! ### `𝔉_{j,n}` and `Λ_n` are finite and non-empty -/

theorem vSet_finite (D : ℕ) (ω : ℕ → Fin 3) (j k : ℕ) : (vSet D ω j k).Finite :=
  (List.finite_length_eq Bool (D - j % D + k + frM D ω (ellIndex D k j) + 3)).subset
    fun v hv => length_of_mem_vSet D ω j k v hv

theorem fSet_finite (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (j n : ℕ) : (fSet D ω k j n).Finite := by
  unfold fSet
  split_ifs
  · apply ((vSet_finite D ω j (2 * k n)).image (gTilde ω j)).subset
    rintro g ⟨v, hv, -, rfl⟩
    exact ⟨v, hv, rfl⟩
  · exact Set.finite_singleton _

theorem fSet_nonempty (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j) :
    (fSet D ω k j n).Nonempty := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  unfold fSet
  split_ifs with hc
  · obtain ⟨-, hjn, hjn'⟩ := hc
    have hkn := hk.2 n (by omega) hn
    have hkD : D ≤ k n := Nat.le_of_dvd hkn.1 hkn.2
    set m := frM D ω (ellIndex D (2 * k n) j)
    set v0 := List.replicate (D - j % D) true ++ List.replicate (2 * k n) true ++
      List.replicate (m + 2) true ++ [false]
    have hv0 : v0 ∈ vSet D ω j (2 * k n) :=
      ⟨List.replicate (2 * k n) true, ⟨by simp, fun i hi _ => by simp⟩, rfl⟩
    have hjD : j % D < D := Nat.mod_lt _ (by omega)
    have hpre : List.replicate (n - j + D) true <+: v0 := by
      have e : v0 = List.replicate (n - j + D) true ++
          (List.replicate (D - j % D + 2 * k n + (m + 2) - (n - j + D)) true ++ [false]) := by
        simp only [v0, ← List.append_assoc, ← List.replicate_add]
        congr 2
        omega
      rw [e]; exact List.prefix_append _ _
    exact ⟨_, v0, hv0, (le_commonPrefixLength_iff v0 _).2 hpre, rfl⟩
  · exact Set.singleton_nonempty _

theorem fSet_subset (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j) :
    fSet D ω k j n ⊆ grigorchuk ω := by
  intro γ hγ
  unfold fSet at hγ
  split_ifs at hγ with hc
  · obtain ⟨v, hv, -, rfl⟩ := hγ
    have hkn := hk.2 n (by omega) hn
    exact (exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem D ω hω j hj1 (2 * k n)
      (Dvd.dvd.mul_left hkn.2 2) v hv).2.1
  · rw [Set.mem_singleton_iff.mp hγ]
    exact ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).1 j hj1).1.1

theorem finite_fProd (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) : Finite (fProd D ω k n) := by
  have : ∀ i : Fin n, Finite ↥(fSet D ω k (i + 1) n) := fun i => (fSet_finite D ω k _ n).to_subtype
  exact Pi.finite

theorem nonempty_fProd (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) : Nonempty (fProd D ω k n) :=
  ⟨fun i => ⟨_, (fSet_nonempty D ω hω k hk n hn (i + 1) (by omega)).some_mem⟩⟩

theorem theta_mem (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (p : LambdaN D ω k n) :
    theta D ω k n p ∈ grigorchuk ω := by
  unfold theta
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact Subgroup.pow_mem _ (fSet_subset D ω hω k hk n hn _ (by omega) (p.2 i.rev).2) _

/-! ### Injectivity in `ε` on rays (Lemma 7.15) -/

theorem smul_theta_injective (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (x : Ray) (γ : fProd D ω k n) :
    Function.Injective fun e : Fin n → Bool => x <• theta D ω k n (e, γ) := by
  intro e e' h
  have h1 := congrArg (fun y => rayPrefix y (n + D + 1)) h
  simp only [rayPrefix_smul] at h1
  exact fst_eq_of_smul_theta_eq D ω hω k hk n hn _ (length_rayPrefix _ _) (e, γ) (e', γ) h1

theorem smul_theta_inv_injective (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (x : Ray) (γ : fProd D ω k n) :
    Function.Injective fun e : Fin n → Bool => x <• (theta D ω k n (e, γ))⁻¹ := by
  intro e e' h
  simp only at h
  set z := x <• (theta D ω k n (e, γ))⁻¹
  have h1 : z <• theta D ω k n (e, γ) = x := by
    simp only [z, ← MulOpposite.op_mul, ← mul_smul, inv_mul_cancel]
    rw [show MulOpposite.op (1 : BinaryTreeAut) = 1 from rfl, one_smul]
  have h2 : z <• theta D ω k n (e', γ) = x := by
    rw [h]
    simp only [← MulOpposite.op_mul, ← mul_smul, inv_mul_cancel]
    rw [show MulOpposite.op (1 : BinaryTreeAut) = 1 from rfl, one_smul]
  exact smul_theta_injective D ω hω k hk n hn z γ (h1.trans h2.symm)


/-! ### Clause 2 -/

open Classical in
theorem upsilon_eq_sum (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) [Fintype (LambdaN D ω k n)]
    (g : BinaryTreeAut) :
    upsilon D ω k n g = ∑ p : LambdaN D ω k n,
      if theta D ω k n p = g then (1 / (Nat.card (LambdaN D ω k n) : ℝ)) else 0 := by
  unfold upsilon
  rw [Nat.card_eq_fintype_card (α := {p // theta D ω k n p = g}), Fintype.card_subtype,
    Finset.card_filter]
  push_cast
  rw [Finset.sum_div]
  congr 1; funext p; split_ifs <;> simp

theorem tsum_point {β : Type*} [DecidableEq β] (b : β) (c : ℝ) (P : β → Prop) [DecidablePred P] :
    ∑' g : β, (if g = b then (if P g then c else 0) else 0) = if P b then c else 0 := by
  rw [tsum_eq_single b]
  · simp
  · intro g hg; simp [hg]

theorem summable_point {β : Type*} [DecidableEq β] (b : β) (f : β → ℝ) :
    Summable fun g : β => if g = b then f g else 0 := by
  apply summable_of_ne_finset_zero (s := {b})
  intro g hg
  simp only [Finset.mem_singleton] at hg
  simp [hg]

theorem clause2 (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (hn1 : 1 ≤ n) :
    ∀ U : Finset (orbitOne ω), U.Nonempty → U.card ≤ 2 ^ (n - 1) →
      (1 : ℝ) / 2 ≤
        MarkovChain.boundarySize
          (orbitKernel (grigorchuk ω) (fun g => (upsilon D ω k n g + upsilonCheck D ω k n g) / 2)
            oneRay) (fun _ => 1) U / U.card := by
  classical
  intro U hU hUc
  haveI := finite_fProd D ω k n
  haveI := nonempty_fProd D ω hω k hk n hn
  letI : Fintype (fProd D ω k n) := Fintype.ofFinite _
  set Λ := LambdaN D ω k n
  set N := Nat.card Λ with hN
  have hNpos : 0 < N := Nat.card_pos
  have hNF : N = 2 ^ n * Fintype.card (fProd D ω k n) := by
    rw [hN, Nat.card_eq_fintype_card]
    simp only [Λ, LambdaN, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  set K := grigorchuk ω
  let gp : Λ → K := fun p => ⟨theta D ω k n p, theta_mem D ω hω k hk n hn p⟩
  let gq : Λ → K := fun p => ⟨(theta D ω k n p)⁻¹, K.inv_mem (theta_mem D ω hω k hk n hn p)⟩
  set c : ℝ := 1 / (2 * N)
  -- the kernel as a finite sum
  have hw : ∀ g : K, (upsilon D ω k n g + upsilonCheck D ω k n g) / 2 =
      ∑ p : Λ, ((if g = gp p then c else 0) + (if g = gq p then c else 0)) := by
    intro g
    unfold upsilonCheck
    rw [upsilon_eq_sum, upsilon_eq_sum, ← Finset.sum_add_distrib, Finset.sum_div,
      Finset.sum_congr rfl]
    intro p _
    have e1 : (theta D ω k n p = (g : BinaryTreeAut)) ↔ g = gp p := by
      constructor
      · intro h; apply Subtype.ext; exact h.symm
      · intro h; rw [h]
    have e2 : (theta D ω k n p = (g : BinaryTreeAut)⁻¹) ↔ g = gq p := by
      constructor
      · intro h; apply Subtype.ext; show (g : BinaryTreeAut) = (theta D ω k n p)⁻¹; rw [h, inv_inv]
      · intro h; rw [h]; show theta D ω k n p = ((theta D ω k n p)⁻¹)⁻¹; rw [inv_inv]
    simp only [e1, e2, c]
    split_ifs <;> ring
  have hP : ∀ x y : orbitOne ω, orbitKernel K (fun g => (upsilon D ω k n g +
      upsilonCheck D ω k n g) / 2) oneRay x y = ∑ p : Λ,
        ((if (x : Ray) <• (gp p : BinaryTreeAut) = y then c else 0) +
          (if (x : Ray) <• (gq p : BinaryTreeAut) = y then c else 0)) := by
    intro x y
    unfold orbitKernel
    simp only [hw]
    have : ∀ g : K, (if (x : Ray) <• (g : BinaryTreeAut) = y then
        ∑ p : Λ, ((if g = gp p then c else 0) + (if g = gq p then c else 0)) else 0) =
        ∑ p : Λ, ((if g = gp p then (if (x : Ray) <• (g : BinaryTreeAut) = y then c else 0)
          else 0) + (if g = gq p then (if (x : Ray) <• (g : BinaryTreeAut) = y then c else 0)
          else 0)) := by
      intro g
      split_ifs with h <;> simp [h]
    simp only [this]
    rw [Summable.tsum_finsetSum (fun p _ => (summable_point _ _).add (summable_point _ _))]
    apply Finset.sum_congr rfl
    intro p _
    rw [Summable.tsum_add (summable_point _ _) (summable_point _ _), tsum_point, tsum_point]
  -- from each point at least half of the mass leaves `U`
  have horb : ∀ (x : orbitOne ω) (g : K), (x : Ray) <• (g : BinaryTreeAut) ∈ orbitOne ω := by
    rintro ⟨x, k0, hk0, rfl⟩ g
    refine ⟨k0 * g, K.mul_mem hk0 g.2, ?_⟩
    rw [MulOpposite.op_mul, mul_smul]
  have hout : ∀ x : orbitOne ω, (1 : ℝ) / 2 ≤
      ∑' y : {y // y ∉ U}, (1 : ℝ) * orbitKernel K (fun g => (upsilon D ω k n g +
        upsilonCheck D ω k n g) / 2) oneRay x y := by
    intro x
    simp only [one_mul, hP]
    have hpt : ∀ g : K, ∑' y : {y // y ∉ U},
        (if (x : Ray) <• (g : BinaryTreeAut) = ((y : orbitOne ω) : Ray) then c else 0) =
        if (⟨_, horb x g⟩ : orbitOne ω) ∈ U then 0 else c := by
      intro g
      by_cases hg : (⟨_, horb x g⟩ : orbitOne ω) ∈ U
      · rw [if_pos hg]
        have : ∀ y : {y // y ∉ U},
            (if (x : Ray) <• (g : BinaryTreeAut) = ((y : orbitOne ω) : Ray) then c else 0) = 0 := by
          intro y
          rw [if_neg]
          intro h
          apply y.2
          have : (y : orbitOne ω) = ⟨_, horb x g⟩ := Subtype.ext h.symm
          rw [this]; exact hg
        simp only [this, tsum_zero]
      · rw [if_neg hg, tsum_eq_single ⟨⟨_, horb x g⟩, hg⟩]
        · simp
        · intro y hy
          rw [if_neg]
          intro h
          apply hy
          apply Subtype.ext; apply Subtype.ext; exact h.symm
    have hsum1 : ∀ g : K, Summable fun y : {y // y ∉ U} =>
        (if (x : Ray) <• (g : BinaryTreeAut) = ((y : orbitOne ω) : Ray) then c else 0) := by
      intro g
      apply summable_of_finite_support
      apply Set.Subsingleton.finite
      intro y1 h1 y2 h2
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at h1 h2
      apply Subtype.ext; apply Subtype.ext
      exact h1.1.symm.trans h2.1
    rw [Summable.tsum_finsetSum (fun p _ => (hsum1 _).add (hsum1 _))]
    simp only [Summable.tsum_add (hsum1 _) (hsum1 _), hpt, Finset.sum_add_distrib]
    -- counting
    have hcount : ∀ f : Λ → K, (∀ γ : fProd D ω k n, Function.Injective fun e : Fin n → Bool =>
        (x : Ray) <• (f (e, γ) : BinaryTreeAut)) →
        (1 : ℝ) / 4 ≤ c * ((Finset.univ.filter fun p : Λ =>
          (⟨_, horb x (f p)⟩ : orbitOne ω) ∉ U).card : ℝ) := by
      intro f hinj
      have hin : ∀ γ : fProd D ω k n, (Finset.univ.filter fun e : Fin n → Bool =>
          (⟨_, horb x (f (e, γ))⟩ : orbitOne ω) ∈ U).card ≤ U.card := by
        intro γ
        apply Finset.card_le_card_of_injOn (fun e => (⟨_, horb x (f (e, γ))⟩ : orbitOne ω))
        · intro e he; simpa using he
        · intro e1 _ e2 _ h
          apply hinj γ
          have := congrArg Subtype.val h
          simpa using this
      have hsplit : (Finset.univ.filter fun p : Λ => (⟨_, horb x (f p)⟩ : orbitOne ω) ∈ U).card =
          ∑ γ : fProd D ω k n, (Finset.univ.filter fun e : Fin n → Bool =>
            (⟨_, horb x (f (e, γ))⟩ : orbitOne ω) ∈ U).card := by
        rw [Finset.card_filter, Fintype.sum_prod_type_right]
        apply Finset.sum_congr rfl; intro γ _; rw [Finset.card_filter]
      have hle : (Finset.univ.filter fun p : Λ => (⟨_, horb x (f p)⟩ : orbitOne ω) ∈ U).card ≤
          Fintype.card (fProd D ω k n) * 2 ^ (n - 1) := by
        rw [hsplit]
        calc ∑ γ : fProd D ω k n, (Finset.univ.filter fun e : Fin n → Bool =>
              (⟨_, horb x (f (e, γ))⟩ : orbitOne ω) ∈ U).card
            ≤ ∑ γ : fProd D ω k n, 2 ^ (n - 1) :=
              Finset.sum_le_sum fun γ _ => (hin γ).trans hUc
          _ = _ := by simp
      have htot := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset Λ)) (fun p : Λ => (⟨_, horb x (f p)⟩ : orbitOne ω) ∈ U)
      rw [Finset.card_univ] at htot
      have hN' : Fintype.card Λ = N := by rw [hN, Nat.card_eq_fintype_card]
      have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hge : N ≤ 2 * (Finset.univ.filter fun p : Λ =>
          (⟨_, horb x (f p)⟩ : orbitOne ω) ∉ U).card := by
        rw [hNF] at hN'
        nlinarith [hle, htot, hN', h2]
      have hc : c * (N : ℝ) = 1 / 2 := by
        simp only [c]; field_simp
      have hge' : (N : ℝ) ≤ 2 * ((Finset.univ.filter fun p : Λ =>
          (⟨_, horb x (f p)⟩ : orbitOne ω) ∉ U).card : ℝ) := by exact_mod_cast hge
      have hcpos : 0 ≤ c := by simp only [c]; positivity
      nlinarith [hge', hcpos, hc]
    have h1 := hcount gp (fun γ => by
      intro e e' h
      exact smul_theta_injective D ω hω k hk n hn x γ h)
    have h2 := hcount gq (fun γ => by
      intro e e' h
      exact smul_theta_inv_injective D ω hω k hk n hn x γ h)
    have e1 : ∀ f : Λ → K, ∑ p : Λ, (if (⟨_, horb x (f p)⟩ : orbitOne ω) ∈ U then (0 : ℝ) else c) =
        c * ((Finset.univ.filter fun p : Λ => (⟨_, horb x (f p)⟩ : orbitOne ω) ∉ U).card : ℝ) := by
      intro f
      rw [Finset.card_filter]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> simp
    rw [e1, e1]
    have hc : c * (N : ℝ) = 1 / 2 := by simp only [c]; field_simp
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    nlinarith [h1, h2, hc]
  -- the boundary
  unfold MarkovChain.boundarySize
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  rw [le_div_iff₀ hUpos]
  calc 1 / 2 * (U.card : ℝ) = ∑ x ∈ U, (1 : ℝ) / 2 := by simp; ring
    _ ≤ _ := Finset.sum_le_sum fun x _ => hout x


/-! ### Clause 1 -/

/-- `ε ∈ {0,1}^n` as exponents `ℕ → ℕ` (index `i ∈ [1, n]`). -/
def epsOf {n : ℕ} (e : Fin n → Bool) (i : ℕ) : ℕ :=
  if h : 1 ≤ i ∧ i ≤ n then (e ⟨i - 1, by omega⟩).toNat else 0

/-- `g_n^{ε_n} ⋯ g_1^{ε_1}`. -/
def cB (ω : ℕ → Fin 3) {n : ℕ} (e : Fin n → Bool) : BinaryTreeAut := cubeProd (seqG ω) n (epsOf e)

theorem range_map_eq_ofFn {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn fun i : Fin n => f i := by
  apply List.ext_getElem <;> simp

theorem cB_eq (ω : ℕ → Fin 3) {n : ℕ} (e : Fin n → Bool) :
    cB ω e = (List.ofFn fun i : Fin n => seqG ω (i.rev + 1) ^ (e i.rev).toNat).prod := by
  unfold cB cubeProd
  rw [List.map_reverse, range_map_eq_ofFn, ← ofFn_rev]
  congr 1
  congr 1
  funext i
  congr 2
  unfold epsOf
  rw [dif_pos (by constructor <;> omega)]
  congr 2

theorem cB_eq_facs (ω : ℕ → Fin 3) {n : ℕ} (e : Fin n → Bool) :
    cB ω e = (facs (seqG ω) 0 (List.ofFn e)).reverse.prod := by
  rw [cB_eq, show (List.ofFn fun i : Fin n => seqG ω (↑i.rev + 1) ^ (e i.rev).toNat) =
      (List.ofFn fun i : Fin n => seqG ω (↑i + 1) ^ (e i).toNat).reverse from
        ofFn_rev n (fun i : Fin n => seqG ω (↑i + 1) ^ (e i).toNat),
    ← ofFn_eq_facs (seqG ω) n 0 e]
  congr 3
  funext i
  simp

theorem cB_injective (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (n : ℕ) :
    Function.Injective (cB ω (n := n)) := by
  intro e e' h
  have := facs_inj (seqG ω) (flips_seqG D ω hω) (List.ofFn e) (List.ofFn e') 0 (by simp)
    (List.replicate (n + 1) true) (by simp)
    (by rw [← cB_eq_facs, ← cB_eq_facs, h])
  exact List.ofFn_injective this

theorem quasiCubicSet_eq (ω : ℕ → Fin 3) (n : ℕ) :
    quasiCubicSet (seqG ω) (fun _ => 1) n = Set.range (cB ω (n := n)) := by
  ext h
  constructor
  · rintro ⟨ε, hε, rfl⟩
    refine ⟨fun i => decide (ε (i + 1) = 1), ?_⟩
    unfold cB cubeProd
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' : i < n := by simpa using hi
    congr 1
    unfold epsOf
    rw [dif_pos (by omega)]
    have := hε (i + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl
  · rintro ⟨e, rfl⟩
    refine ⟨epsOf e, fun i h1 h2 => ?_, rfl⟩
    unfold epsOf
    split_ifs
    · cases e _ <;> simp
    · omega

theorem cB_mem (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) {n : ℕ} (e : Fin n → Bool) :
    cB ω e ∈ grigorchuk ω := by
  rw [cB_eq]
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact Subgroup.pow_mem _ ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).1
    _ (by omega)).1.1 _

theorem restrict_level (g h : BinaryTreeAut) (N : ℕ)
    (hgh : ∀ u : List Bool, u.length = N → u <• g = u <• h) (x : List Bool) (hx : x.length ≤ N) :
    x <• g = x <• h := by
  have e := hgh (x ++ List.replicate (N - x.length) true) (by simp; omega)
  rw [append_vertex_smul, append_vertex_smul] at e
  have := congrArg (List.take x.length) e
  simpa [List.take_left' (length_vertex_smul _ _)] using this

/-- On level `n`, `θ_n(ε, γ)` acts as `g_n^{ε_n} ⋯ g_1^{ε_1}`. -/
theorem smul_theta_eq_cB (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (p : LambdaN D ω k n) (x : List Bool)
    (hx : x.length = n) : x <• theta D ω k n p = x <• cB ω p.1 := by
  apply restrict_level _ _ (n + D + 1) _ x (by omega)
  intro z hz
  unfold theta
  rw [cB_eq]
  apply prod_smul_eq (n + D + 1) _ _ (by simp) _ z hz
  intro i h1 h2 w hw
  simp only [List.getElem_ofFn]
  cases p.1 (Fin.rev ⟨i, by simpa using h1⟩)
  · simp
  · simp only [Bool.toNat_true, pow_one]
    set γ := p.2 (Fin.rev ⟨i, by simpa using h1⟩)
    by_cases hc : ω (↑(Fin.rev (⟨i, by simpa using h1⟩ : Fin n)) + 1 - 1) = 2 ∧
        n < ↑(Fin.rev (⟨i, by simpa using h1⟩ : Fin n)) + 1 + k n ∧
        ↑(Fin.rev (⟨i, by simpa using h1⟩ : Fin n)) + 1 ≤ n
    · exact vertex_smul_eq_smul_seqG_of_mem_fSet D ω hω k hk n hn _ (by omega) hc.1 hc.2.1
        hc.2.2 γ γ.2 w hw
    · obtain ⟨g, hg⟩ := γ
      unfold fSet at hg
      rw [if_neg hc] at hg
      show w <• g = _
      rw [Set.mem_singleton_iff.mp hg]

/-- Clause 1 on the level: for words `x, y` with `x` of length `n`, `υ_n` and `u_{F_n}` give
the same mass to `{g : x·g = y}`. -/
theorem clause1_level (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (x y : List Bool) (hxl : x.length = n) :
    ∑' g : grigorchuk ω, (if x <• (g : Garrido.BinaryTreeAut) = y then upsilon D ω k n g else 0) =
      ∑' g : grigorchuk ω, (if x <• (g : Garrido.BinaryTreeAut) = y then
        uniformMeasure (quasiCubicSet (seqG ω) (fun _ => 1) n) (g : Garrido.BinaryTreeAut)
        else 0) := by
  classical
  haveI := finite_fProd D ω k n
  haveI := nonempty_fProd D ω hω k hk n hn
  letI : Fintype (fProd D ω k n) := Fintype.ofFinite _
  set Λ := LambdaN D ω k n
  set N := Nat.card Λ with hN
  have hNF : N = 2 ^ n * Fintype.card (fProd D ω k n) := by
    rw [hN, Nat.card_eq_fintype_card]
    simp only [Λ, LambdaN, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hFpos : 0 < Fintype.card (fProd D ω k n) := Fintype.card_pos
  set K := grigorchuk ω
  let gp : Λ → K := fun p => ⟨theta D ω k n p, theta_mem D ω hω k hk n hn p⟩
  let gc : (Fin n → Bool) → K := fun e => ⟨cB ω e, cB_mem D ω hω e⟩
  have hυ : ∀ g : K, upsilon D ω k n g = ∑ p : Λ, (if g = gp p then (1 / (N : ℝ)) else 0) := by
    intro g
    rw [upsilon_eq_sum]
    apply Finset.sum_congr rfl
    intro p _
    have e1 : (theta D ω k n p = (g : BinaryTreeAut)) ↔ g = gp p := by
      constructor
      · intro h; apply Subtype.ext; exact h.symm
      · intro h; rw [h]
    simp only [e1]
    rfl
  have hcard : Nat.card ↥(quasiCubicSet (seqG ω) (fun _ => 1) n) = 2 ^ n := by
    rw [quasiCubicSet_eq, Nat.card_range_of_injective (cB_injective D ω hω n)]
    simp
  have hu : ∀ g : K, uniformMeasure (quasiCubicSet (seqG ω) (fun _ => 1) n) (g : BinaryTreeAut) =
      ∑ e : Fin n → Bool, (if g = gc e then (1 / (2 : ℝ) ^ n) else 0) := by
    intro g
    unfold uniformMeasure
    rw [hcard]
    by_cases hg : (g : BinaryTreeAut) ∈ quasiCubicSet (seqG ω) (fun _ => 1) n
    · rw [if_pos hg]
      rw [quasiCubicSet_eq] at hg
      obtain ⟨e0, he0⟩ := hg
      rw [Finset.sum_eq_single e0]
      · rw [if_pos (Subtype.ext he0.symm)]; push_cast; ring
      · intro e _ hne
        rw [if_neg]
        intro h
        apply hne
        have h1 : (g : BinaryTreeAut) = cB ω e := congrArg Subtype.val h
        exact cB_injective D ω hω n (h1.symm.trans he0.symm)
      · simp
    · rw [if_neg hg]
      symm
      apply Finset.sum_eq_zero
      intro e _
      rw [if_neg]
      intro h
      apply hg
      rw [h, quasiCubicSet_eq]
      exact ⟨e, rfl⟩
  have hL : ∀ g : K, (if x <• (g : BinaryTreeAut) = y then upsilon D ω k n g else 0) =
      ∑ p : Λ, (if g = gp p then (if x <• (g : BinaryTreeAut) = y then
        (1 / (N : ℝ)) else 0) else 0) := by
    intro g
    rw [hυ]
    split_ifs with h <;> simp [h]
  have hR : ∀ g : K, (if x <• (g : BinaryTreeAut) = y then
      uniformMeasure (quasiCubicSet (seqG ω) (fun _ => 1) n) (g : BinaryTreeAut) else 0) =
      ∑ e : Fin n → Bool, (if g = gc e then (if x <• (g : BinaryTreeAut) = y then
        (1 / (2 : ℝ) ^ n) else 0) else 0) := by
    intro g
    rw [hu]
    split_ifs with h <;> simp [h]
  simp only [hL, hR]
  rw [Summable.tsum_finsetSum (fun p _ => summable_point _ _),
    Summable.tsum_finsetSum (fun e _ => summable_point _ _)]
  simp only [tsum_point]
  -- compare the two finite sums
  rw [Fintype.sum_prod_type]
  have hθ : ∀ (e : Fin n → Bool) (γ : fProd D ω k n),
      (x <• ((gp (e, γ) : K) : BinaryTreeAut) = y) ↔
        (x <• ((gc e : K) : BinaryTreeAut) = y) := by
    intro e γ
    show x <• theta D ω k n (e, γ) = y ↔ x <• cB ω e = y
    rw [smul_theta_eq_cB D ω hω k hk n hn (e, γ) x hxl]
  simp only [hθ]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  split_ifs
  · rw [hNF]; push_cast
    have : (Fintype.card (fProd D ω k n) : ℝ) ≠ 0 := by exact_mod_cast hFpos.ne'
    field_simp
  · simp

theorem clause1 (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) :
    orbitKernel (grigorchuk ω) (fun g => upsilon D ω k n g) (List.replicate n true) =
      orbitKernel (grigorchuk ω)
        (fun g =>
          uniformMeasure (quasiCubicSet (seqG ω) (fun _ => 1) n) (g : Garrido.BinaryTreeAut))
        (List.replicate n true) := by
  funext x y
  have hxl : (x : List Bool).length = n := by
    obtain ⟨k0, -, hk0⟩ := x.2
    rw [hk0, length_vertex_smul]; simp
  unfold orbitKernel
  convert clause1_level D ω hω k hk n hn x y hxl using 4

end ConstrG9

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open ErschlerZheng.ConstrG9
open GrigBasic ConstrW ConstrH ConstrF8 ConstrLemma715
theorem solution (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n)
    (hn1 : 1 ≤ n) :
    orbitKernel (grigorchuk ω) (fun g => upsilon D ω k n g) (List.replicate n true) =
      orbitKernel (grigorchuk ω)
        (fun g =>
          uniformMeasure (quasiCubicSet (seqG ω) (fun _ => 1) n) (g : Garrido.BinaryTreeAut))
        (List.replicate n true) ∧
    (∀ x y : List Bool, x.length = n → y.length = n →
      ∑' g : grigorchuk ω, (if x <• (g : Garrido.BinaryTreeAut) = y then upsilon D ω k n g else 0) =
        ∑' g : grigorchuk ω, (if x <• (g : Garrido.BinaryTreeAut) = y then
          uniformMeasure (quasiCubicSet (seqG ω) (fun _ => 1) n) (g : Garrido.BinaryTreeAut)
          else 0)) ∧
    ∀ U : Finset (orbitOne ω), U.Nonempty → U.card ≤ 2 ^ (n - 1) →
      (1 : ℝ) / 2 ≤
        MarkovChain.boundarySize
          (orbitKernel (grigorchuk ω) (fun g => (upsilon D ω k n g + upsilonCheck D ω k n g) / 2)
            oneRay) (fun _ => 1) U / U.card :=
  ⟨clause1 D ω hω k hk n hn, fun x y hx _ => clause1_level D ω hω k hk n hn x y hx,
    clause2 D ω hω k hk n hn hn1⟩
end
