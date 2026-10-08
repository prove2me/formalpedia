-- Prove2me | solution 1 for ErschlerZheng.schreierDist_smul_le_of_mem_fSet_and_smul_theta_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T06:27:46.928886+00:00
-- url     : https://prove2.me/submissions/1180f61d-2e1a-4dc0-a03c-0742d3d423dc

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_schreierDist_smul_gTilde_le
import Theorems.Thm_ErschlerZheng_seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms
import Theorems.Thm_ErschlerZheng_exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem
import Theorems.Thm_ErschlerZheng_sec_mem_grigorchuk_and_schreierDist_smul_le_of_isCofinal
import Theorems.Thm_ErschlerZheng_schreierDist_eq_abs_sub_grayCode_of_isCofinal
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary

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

/-! ### The root swap -/

/-! ### `a` and the generators -/

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
# The maximal displacements (Erschler–Zheng p. 45)

On the levels of `𝔉_{j,n}` made of `g̃^v_j`: Lemma 7.16, with `|𝔰^{j+1}x ∧ 𝔰v| ⩽ |v| - 1 ⩽
2k_n + 2D - 1`. On the levels `{g_j}`: Lemma 7.5 at level `j`, the sections of `g_j` there having
word length `2`. The product `θ_n(ε, γ)`: the triangle inequality along the intermediate points
(`d_𝒮` is a difference of Gray codes on the orbit, A9) and `Σ_{i ⩽ n} 2^{i+C} < 2^{n+C+1}`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrDisp

open ConstrW ConstrH

theorem ofFn_rev' {α : Type*} (n : ℕ) (f : Fin n → α) :
    List.ofFn (fun i => f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    congr 1
    ext
    simp [Fin.rev]
    omega

theorem sum_pow (K : ℕ) : ∀ n : ℕ, (List.ofFn fun i : Fin n => 2 ^ (i + 1 + K)).sum + 2 ^ (K + 1) =
    2 ^ (n + K + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.sum_append]
    simp only [Fin.coe_castSucc, Fin.val_last, List.sum_cons, List.sum_nil, add_zero]
    rw [add_right_comm, ih, show n + 1 + K + 1 = (n + K + 1) + 1 by omega, pow_succ,
      show n + 1 + K = n + K + 1 by omega]
    ring

theorem cofinal_of_orbit (ω : ℕ → Fin 3) (x : Ray) (hx : x ∈ orbitOne ω) : IsCofinal x := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
  have : x ∈ rightOrbit (grigorchuk ω) oneRay := hx
  rw [(hA2.2.1 ω oneRay).1] at this
  exact this

theorem orbit_smul (ω : ℕ → Fin 3) (x : Ray) (hx : x ∈ orbitOne ω) (g : BinaryTreeAut)
    (hg : g ∈ grigorchuk ω) : x <• g ∈ orbitOne ω := by
  obtain ⟨k, hk, rfl⟩ := hx
  refine ⟨k * g, Subgroup.mul_mem _ hk hg, ?_⟩
  rw [MulOpposite.op_mul, mul_smul]

theorem dist_triangle (ω : ℕ → Fin 3) (x y z : Ray) (hx : IsCofinal x) (hy : IsCofinal y)
    (hz : IsCofinal z) : schreierDist ω x z ≤ schreierDist ω x y + schreierDist ω y z := by
  have h1 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x z hx hz
  have h2 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x y hx hy
  have h3 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω y z hy hz
  have : (schreierDist ω x z : ℤ) ≤ schreierDist ω x y + schreierDist ω y z := by
    rw [h1, h2, h3]
    exact abs_sub_le _ _ _
  exact_mod_cast this

theorem dist_self (ω : ℕ → Fin 3) (x : Ray) (hx : IsCofinal x) : schreierDist ω x x = 0 := by
  have h := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x x hx hx
  simp at h
  exact_mod_cast h

/-- The displacement of a product, along the intermediate points. -/
theorem dist_prod (ω : ℕ → Fin 3) : ∀ (l : List BinaryTreeAut) (b : List ℕ), l.length = b.length →
    (∀ i (h1 : i < l.length) (h2 : i < b.length), l[i] ∈ grigorchuk ω ∧
      ∀ y ∈ orbitOne ω, schreierDist ω y (y <• l[i]) ≤ b[i]) →
    ∀ x ∈ orbitOne ω, schreierDist ω x (x <• l.prod) ≤ b.sum := by
  intro l
  induction l with
  | nil =>
    intro b hb _ x hx
    simp only [List.prod_nil]
    rw [show x <• (1 : BinaryTreeAut) = x from one_smul _ x, dist_self ω x (cofinal_of_orbit ω x hx)]
    exact Nat.zero_le _
  | cons g l ih =>
    intro b hb h x hx
    cases b with
    | nil => simp at hb
    | cons c b =>
      obtain ⟨hg, hgb⟩ := h 0 (by simp) (by simp)
      have hxg := orbit_smul ω x hx g hg
      have hl : l.prod ∈ grigorchuk ω := by
        apply Subgroup.list_prod_mem
        intro s hs
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
        exact (h (i + 1) (by simp; omega) (by simp at hb; simp; omega)).1
      have hrest := ih b (by simpa using hb) (fun i h1 h2 => h (i + 1) (by simpa using h1)
        (by simpa using h2)) (x <• g) hxg
      rw [List.prod_cons, List.sum_cons, MulOpposite.op_mul, mul_smul]
      have hxgl := orbit_smul ω _ hxg _ hl
      refine (dist_triangle ω x (x <• g) _ (cofinal_of_orbit ω x hx)
        (cofinal_of_orbit ω _ hxg) (cofinal_of_orbit ω _ hxgl)).trans ?_
      exact Nat.add_le_add (hgb x hx) (by simpa [MulOpposite.op_mul, mul_smul] using hrest)

theorem wordLength_le_of_list (ω : ℕ → Fin 3) (l : List BinaryTreeAut) (hl : ∀ s ∈ l, s ∈ gens ω) :
    wordLength (gens ω) l.prod ≤ l.length :=
  Nat.sInf_le ⟨l, le_rfl, fun s hs => Or.inl (hl s hs), rfl⟩

end ConstrDisp

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open ErschlerZheng.ConstrDisp
open ConstrW ConstrH
theorem solution (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) :
    (∀ j, 1 ≤ j → j ≤ n → ∀ γ ∈ fSet D ω k j n, ∀ x ∈ orbitOne ω,
        schreierDist ω x (x <• γ) ≤ 2 ^ (j + 2 * k n + 2 * D + 4)) ∧
    ∀ x ∈ orbitOne ω, ∀ p : LambdaN D ω k n,
      schreierDist ω x (x <• theta D ω k n p) ≤ 2 ^ (n + 2 * k n + 2 * D + 5) := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  obtain ⟨hF1, -, -⟩ := seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω
  -- membership and the bound, level by level
  have hlev : ∀ j, 1 ≤ j → j ≤ n → ∀ γ ∈ fSet D ω k j n, γ ∈ grigorchuk ω ∧ ∀ x ∈ orbitOne ω,
      schreierDist ω x (x <• γ) ≤ 2 ^ (j + 2 * k n + 2 * D + 4) := by
    intro j hj1 hjn γ hγ
    unfold fSet at hγ
    split_ifs at hγ with hc
    · obtain ⟨hj, hjn1, hjn'⟩ := hc
      obtain ⟨v, hv, hpre, rfl⟩ := hγ
      have hkn := hk.2 n (by omega) hn
      have h2k : D ∣ 2 * k n := Dvd.dvd.mul_left hkn.2 2
      have hmem := (exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem D ω hω j hj1
        (2 * k n) h2k v hv).2.1
      refine ⟨hmem, fun x hx => ?_⟩
      obtain ⟨c1, c2⟩ := schreierDist_smul_gTilde_le D ω hω k hk n hn j hj1 hj hjn1 hjn' v hv hpre
        x hx
      have hvl := length_of_mem_vSet D ω j _ v hv
      have hm := (frM_spec D ω hω (ellIndex D (2 * k n) j)).1
      by_cases h : n - j + D ≤ commonPrefixLength (v.drop 1) (shiftRay x (j + 1))
      · refine (c1 h).trans (Nat.pow_le_pow_right (by norm_num) ?_)
        have hcp : commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) ≤ (v.drop 1).length := by
          unfold commonPrefixLength
          have := (List.takeWhile_prefix (p := fun p : Bool × Bool => decide (p.1 = p.2))
            (l := (v.drop 1).zip (rayPrefix (shiftRay x (j + 1)) (v.drop 1).length))).length_le
          simp [length_rayPrefix] at this
          simpa using this
        rw [List.length_drop] at hcp
        omega
      · exact (c2 (by omega)).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    · rw [Set.mem_singleton_iff.mp hγ]
      obtain ⟨hst, hsec⟩ := hF1 j hj1
      refine ⟨hst.1, fun x hx => ?_⟩
      have hA := (sec_mem_grigorchuk_and_schreierDist_smul_le_of_isCofinal ω (seqG ω j) hst.1 j x
        (cofinal_of_orbit ω x hx)).2
      refine hA.trans ?_
      have hl : wordLength (gens (shiftSeq ω j)) (sec (seqG ω j) (rayPrefix x j)) ≤ 2 := by
        have ha : grigA ∈ gens (shiftSeq ω j) := by simp [gens]
        have key : ∀ γ : BCD, wordLength (gens (shiftSeq ω j)) (grigA * gen (shiftSeq ω j) γ) ≤ 2 ∧
            wordLength (gens (shiftSeq ω j)) (grigA * (grigA * gen (shiftSeq ω j) γ) * grigA) ≤ 2 := by
          intro γ
          have hγ : gen (shiftSeq ω j) γ ∈ gens (shiftSeq ω j) := by cases γ <;> simp [gens]
          constructor
          · have := wordLength_le_of_list (shiftSeq ω j) [grigA, gen (shiftSeq ω j) γ]
              (by simp [ha, hγ])
            simpa using this
          · have := wordLength_le_of_list (shiftSeq ω j) [gen (shiftSeq ω j) γ, grigA]
              (by simp [ha, hγ])
            rw [← mul_assoc grigA grigA, show grigA * grigA = 1 from
              Subtype.ext (Equiv.ext fun w => grigAFun_involutive w), one_mul]
            simpa using this
        rcases hsec (rayPrefix x j) (length_rayPrefix _ _) with h | h <;> rw [h] <;> split_ifs <;>
          simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
            mul_one] <;>
          first | exact (key .c).1 | exact (key .c).2 | exact (key .b).1 | exact (key .b).2
      calc 2 ^ j * (wordLength (gens (shiftSeq ω j)) (sec (seqG ω j) (rayPrefix x j)) + 1)
          ≤ 2 ^ j * 2 ^ 2 := by gcongr; norm_num; omega
        _ = 2 ^ (j + 2) := (pow_add 2 j 2).symm
        _ ≤ 2 ^ (j + 2 * k n + 2 * D + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨fun j hj1 hjn γ hγ x hx => (hlev j hj1 hjn γ hγ).2 x hx, fun x hx p => ?_⟩
  -- the product
  unfold theta
  set C := 2 * k n + 2 * D + 4
  have hb := dist_prod ω (List.ofFn fun i : Fin n => (p.2 i.rev : BinaryTreeAut) ^ (p.1 i.rev).toNat)
    (List.ofFn fun i : Fin n => 2 ^ (i.rev + 1 + C)) (by simp)
    (by
      intro i h1 h2
      simp only [List.getElem_ofFn]
      have hγ := (p.2 (Fin.rev ⟨i, by simpa using h1⟩)).2
      have hlv := hlev _ (by omega) (by omega) _ hγ
      cases p.1 (Fin.rev ⟨i, by simpa using h1⟩)
      · refine ⟨Subgroup.one_mem _, fun y hy => ?_⟩
        simp only [Bool.toNat_false, pow_zero]
        rw [show y <• (1 : BinaryTreeAut) = y from one_smul _ y,
          dist_self ω y (cofinal_of_orbit ω y hy)]
        exact Nat.zero_le _
      · simp only [Bool.toNat_true, pow_one]
        refine ⟨hlv.1, fun y hy => (hlv.2 y hy).trans (le_of_eq ?_)⟩
        congr 1; ring)
    x hx
  refine hb.trans ?_
  have e := ofFn_rev' n (fun i : Fin n => 2 ^ (i.val + 1 + C))
  rw [e, List.sum_reverse]
  have := sum_pow C n
  calc (List.ofFn fun i : Fin n => 2 ^ (i.val + 1 + C)).sum
      ≤ (List.ofFn fun i : Fin n => 2 ^ (i.val + 1 + C)).sum + 2 ^ (C + 1) := Nat.le_add_right _ _
    _ = 2 ^ (n + C + 1) := this
    _ = 2 ^ (n + 2 * k n + 2 * D + 5) := by congr 1; omega
end
