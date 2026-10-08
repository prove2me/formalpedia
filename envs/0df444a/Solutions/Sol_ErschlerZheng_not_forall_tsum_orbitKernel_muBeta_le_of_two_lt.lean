-- Prove2me | solution 1 for ErschlerZheng.not_forall_tsum_orbitKernel_muBeta_le_of_two_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T12:44:17.253832+00:00
-- url     : https://prove2.me/submissions/e7ee4af7-e94c-47ab-af0c-d01f11715941

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_schreierDist_eq_abs_sub_grayCode_of_isCofinal

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

theorem sec_unique {g h : BinaryTreeAut} {v : List Bool}
    (H : ∀ w : List Bool, (v ++ w) <• g = (v <• g) ++ (w <• h)) : sec g v = h := by
  have key : ∀ w : List Bool, w <• sec g v = w <• h := by
    intro w
    have h1 := append_vertex_smul g v w
    rw [H w] at h1
    exact (List.append_cancel_left h1).symm
  have : (sec g v)⁻¹ = h⁻¹ := Subtype.ext (Equiv.ext fun w => key w)
  exact inv_injective this

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

theorem grayList_cons (b : Bool) (v : List Bool) :
    grayList (b :: v) = (b :: v).count false % 2 + 2 * grayList v := rfl

theorem grayList_append_true (w : List Bool) : grayList (w ++ [true]) = grayList w := by
  induction w with
  | nil => simp [grayList]
  | cons b v ih =>
    rw [List.cons_append, grayList_cons, grayList_cons, ih]
    simp [List.count_cons, List.count_append]

theorem grayList_append_replicate (w : List Bool) (m : ℕ) :
    grayList (w ++ List.replicate m true) = grayList w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ', ← List.append_assoc, grayList_append_true, ih]

/-- The move of `a`. -/
theorem grayList_grigAFun (w : List Bool) (hw : w ≠ []) :
    (grayList (grigAFun w) : ℤ) = grayList w + (if w.count false % 2 = 0 then 1 else -1) ∧
      (grigAFun w).count false % 2 ≠ w.count false % 2 := by
  obtain ⟨b, v, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [grigAFun, grayList_cons]
  cases b <;> simp [List.count_cons] <;> split_ifs <;> omega

/-- The move of `γ_ω`: identity, or a step of `∓1` that flips the parity of the zeros. -/
theorem grayList_genFun (ω : ℕ → Fin 3) (γ : BCD) (w : List Bool) :
    genFun ω γ w = w ∨
      ((genFun ω γ w).count false % 2 ≠ w.count false % 2 ∧
        (grayList (genFun ω γ w) : ℤ) = grayList w + (if w.count false % 2 = 0 then -1 else 1)) := by
  induction w generalizing ω with
  | nil => left; rfl
  | cons b v ih =>
    cases b
    · by_cases hl : letterValue (ω 0) γ
      · by_cases hv : v = []
        · left; subst hv; simp [genFun, hl, grigAFun]
        · right
          have ha := grayList_grigAFun v hv
          simp only [genFun, hl, if_true, grayList_cons]
          simp only [List.count_cons] at ha ⊢
          simp at ha ⊢
          omega
      · left; simp [genFun, hl]
    · rcases ih (shiftSeq ω 1) with h | ⟨h1, h2⟩
      · left; simp [genFun, h]
      · right
        simp only [genFun, grayList_cons]
        simp only [List.count_cons] at h1 h2 ⊢
        simp at h1 h2 ⊢
        omega

theorem grigA_mem_gens (ω : ℕ → Fin 3) : grigA ∈ gens ω := by simp [gens]

theorem gen_mem_gens (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ ∈ gens ω := by
  cases γ <;> simp [gens]

/-- Every generator moves the Gray code by at most one. -/
theorem grayList_smul_gens (ω : ℕ → Fin 3) (w : List Bool) (s : BinaryTreeAut) (hs : s ∈ gens ω) :
    (grayList (w <• s) : ℤ) - grayList w ∈ ({-1, 0, 1} : Set ℤ) := by
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [vertex_smul_grigA]
    by_cases hw : w = []
    · subst hw; simp [grigAFun]
    · have := (grayList_grigAFun w hw).1
      split_ifs at this <;> simp [this]
  all_goals
    rw [vertex_smul_gen]
  · rcases grayList_genFun ω .b w with h | ⟨_, h2⟩
    · simp [h]
    · split_ifs at h2 <;> simp [h2]
  · rcases grayList_genFun ω .c w with h | ⟨_, h2⟩
    · simp [h]
    · split_ifs at h2 <;> simp [h2]
  · rcases grayList_genFun ω .d w with h | ⟨_, h2⟩
    · simp [h]
    · split_ifs at h2 <;> simp [h2]

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

theorem grayCode_eq {N : ℕ} {x : Ray} (h : AllOnesFrom N x) :
    grayCode x = grayList (rayPrefix x N) := by
  unfold grayCode
  set M := maxZeroIndex x with hM
  have hMdef : M = sSup {k | 1 ≤ k ∧ x (k - 1) = false} := rfl
  have hbdd : ∀ k ∈ {k | 1 ≤ k ∧ x (k - 1) = false}, k ≤ N := by
    rintro k ⟨hk1, hk⟩
    by_contra hc
    have := h (k - 1) (by omega)
    rw [this] at hk
    exact Bool.noConfusion hk
  have hMN : M ≤ N := csSup_le' hbdd
  have hones : AllOnesFrom M x := by
    intro k hk
    by_contra hc
    have hmem : k + 1 ∈ {k | 1 ≤ k ∧ x (k - 1) = false} := by
      refine ⟨by omega, ?_⟩
      simpa using hc
    have := le_csSup ⟨N, hbdd⟩ hmem
    rw [← hMdef] at this
    omega
  have hsplit : rayPrefix x N = rayPrefix x M ++ List.replicate (N - M) true := by
    rw [show N = M + (N - M) by omega, rayPrefix_add, shiftRay_eq_oneRay hones,
      rayPrefix_oneRay]
    simp
  rw [hsplit, grayList_append_replicate]

theorem grayCode_oneRay : grayCode oneRay = 0 := by
  rw [grayCode_eq (N := 0) (x := oneRay) (fun k _ => rfl)]
  rfl

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

theorem gray_smul_gens (ω : ℕ → Fin 3) {s : BinaryTreeAut} (hs : s ∈ gens ω) {N : ℕ} {x : Ray}
    (h : AllOnesFrom N x) :
    (grayCode (x <• s) : ℤ) - grayCode x ∈ ({-1, 0, 1} : Set ℤ) := by
  rw [grayCode_eq (allOnesFrom_smul_gens ω hs h), grayCode_eq (h.mono (Nat.le_succ N)),
    rayPrefix_smul]
  exact grayList_smul_gens ω _ s hs

theorem ray_smul_list_cons (x : Ray) (s : BinaryTreeAut) (l : List BinaryTreeAut) :
    x <• (s :: l).prod = (x <• s) <• l.prod := by
  rw [List.prod_cons, MulOpposite.op_mul, mul_smul]

/-- Along a path of generators, the Gray code moves by at most the length. -/
theorem gray_path_le (ω : ℕ → Fin 3) :
    ∀ (l : List BinaryTreeAut), (∀ s ∈ l, s ∈ gens ω) → ∀ (N : ℕ) (x : Ray), AllOnesFrom N x →
      |(grayCode (x <• l.prod) : ℤ) - grayCode x| ≤ l.length ∧
        AllOnesFrom (N + l.length) (x <• l.prod)
  | [], _, N, x, h => by simp [h]
  | s :: l, hl, N, x, h => by
    have hs : s ∈ gens ω := hl s (by simp)
    have h1 := allOnesFrom_smul_gens ω hs h
    obtain ⟨ih1, ih2⟩ := gray_path_le ω l (fun t ht => hl t (by simp [ht])) (N + 1) (x <• s) h1
    have hstep := gray_smul_gens ω hs h
    rw [ray_smul_list_cons]
    refine ⟨?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using ih2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hstep
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [abs_le] at ih1 ⊢
    constructor <;> rcases hstep with e | e | e <;> linarith [ih1.1, ih1.2]

end SchreierDev

end ErschlerZheng
end

section
/-!
# Kernel library for the Markov heat-kernel package

Substochastic kernels on a type `X` (no countability needed): non-negative entries, summable rows
with sums at most one. Their powers `stepProb`, Chapman–Kolmogorov, symmetry of powers, column
sums, and Poisson series facts used by the heat kernel.
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

variable [DecidableEq X]

/-! ## The heat kernel -/

end MarkovHK
end

section
/-!
# Near and far parts of a kernel; `uniformize` of a substochastic kernel (shared by H6 and H8)
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

variable [DecidableEq X]

end MarkovHK
end

section
/-!
# Orbit kernels of `μ_β` and `υ_n` as Markov kernels (helpers for Proposition 7.19, prover 6)

* `G_ω` and the orbit `1^∞·G_ω` are countable.
* For `ν ⩾ 0` summable on a subgroup `K`, the rows of `P_ν` sum to `Σ ν`; `P_ν` is a transition
  kernel when `ν` is a probability, and symmetric when `ν` is.
* `υ_n` restricted to `G_ω` is a sub-probability, so `P_{(υ_n + υ̌_n)/2}` is substochastic.
* `μ_β ⩾ C_β 2^{-nβ} (υ_n + υ̌_n)/2` pointwise, for `n ⩾ 1`, `D ∣ n`.
* `μ_β` is symmetric; `k_n = A⌊log₂ n⌋` is admissible and eventually `⩽ n` (copied from prover 5's
  `P5Goal`, which is still being edited).
-/

open scoped RightActions
open DurrettProbability MarkovChain

namespace ErschlerZheng

namespace P6Dev

open GrigBasic Garrido Filter

set_option linter.unusedSectionVars false

/-! ### Countability -/

lemma gens_finite (ω : ℕ → Fin 3) : (gens ω).Finite := by
  unfold gens
  exact (((Set.finite_singleton _).insert _).insert _).insert _

instance countable_grigorchuk (ω : ℕ → Fin 3) : Countable (grigorchuk ω) := by
  have hT : (gens ω ∪ (gens ω)⁻¹).Countable :=
    ((gens_finite ω).union (gens_finite ω).inv).countable
  have hc : ((grigorchuk ω : Subgroup BinaryTreeAut) : Set BinaryTreeAut).Countable := by
    have h1 : ((grigorchuk ω : Subgroup BinaryTreeAut) : Set BinaryTreeAut) =
        (Submonoid.closure (gens ω ∪ (gens ω)⁻¹) : Set BinaryTreeAut) := by
      unfold grigorchuk
      rw [← Subgroup.closure_toSubmonoid]
      rfl
    rw [h1, Submonoid.closure_eq_image_prod]
    have : Countable (gens ω ∪ (gens ω)⁻¹ : Set BinaryTreeAut) := hT.to_subtype
    have h2 : {l : List BinaryTreeAut | ∀ x ∈ l, x ∈ gens ω ∪ (gens ω)⁻¹} ⊆
        Set.range (fun l : List (gens ω ∪ (gens ω)⁻¹ : Set BinaryTreeAut) =>
          l.map Subtype.val) := by
      intro l hl
      refine ⟨l.attach.map fun x => ⟨x.1, hl x.1 x.2⟩, ?_⟩
      simp [List.map_attach_eq_pmap]
    exact ((Set.countable_range _).mono h2).image _
  exact hc.to_subtype

instance countable_orbitOne (ω : ℕ → Fin 3) : Countable (orbitOne ω) := by
  have : (orbitOne ω).Countable := by
    have h : orbitOne ω ⊆ Set.range (fun g : grigorchuk ω => oneRay <• (g : BinaryTreeAut)) := by
      rintro y ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    exact (Set.countable_range _).mono h
  exact this.to_subtype

/-! ### Orbit kernels -/

section Orbit

variable {H : Type*} [Group H] {X : Type*} [MulAction Hᵐᵒᵖ X] (K : Subgroup H)

lemma orbitKernel_nonneg' {ν : K → ℝ} (hν : ∀ g, 0 ≤ ν g) (o : X) (x y : rightOrbit K o) :
    0 ≤ orbitKernel K ν o x y := by
  classical
  unfold orbitKernel
  exact tsum_nonneg fun g => by split_ifs <;> simp [hν g]

/-- The rows of `P_ν` sum to `Σ ν`. -/
lemma hasSum_orbitKernel_row {ν : K → ℝ} (hν : ∀ g, 0 ≤ ν g) (hs : Summable ν) (o : X)
    (x : rightOrbit K o) : HasSum (fun y => orbitKernel K ν o x y) (∑' g, ν g) := by
  classical
  -- the point `x·g` of the orbit
  let act : K → rightOrbit K o := fun g => ⟨(x : X) <• (g : H), by
    obtain ⟨k, hk, hx⟩ := x.2
    refine ⟨k * g, K.mul_mem hk g.2, ?_⟩
    rw [hx, MulOpposite.op_mul, mul_smul]⟩
  let F : rightOrbit K o × K → ℝ := fun p => if (x : X) <• (p.2 : H) = p.1 then ν p.2 else 0
  have hinj : Function.Injective (fun g : K => (act g, g)) := fun a b h => (Prod.mk.inj h).2
  have hF : HasSum F (∑' g, ν g) := by
    have hcomp : F ∘ (fun g : K => (act g, g)) = ν := by
      funext g; simp [F, act]
    have hsupp : ∀ p ∉ Set.range (fun g : K => (act g, g)), F p = 0 := by
      rintro ⟨y, g⟩ hp
      simp only [F]
      split_ifs with h
      · exact absurd ⟨g, by
          simp only [Prod.mk.injEq, and_true]
          exact Subtype.ext h⟩ hp
      · rfl
    rw [← hinj.hasSum_iff hsupp, hcomp]
    exact hs.hasSum
  refine hF.prod_fiberwise fun y => ?_
  show HasSum (fun g : K => if (x : X) <• (g : H) = y then ν g else 0) (orbitKernel K ν o x y)
  unfold orbitKernel
  refine Summable.hasSum ?_
  refine Summable.of_nonneg_of_le (fun g => by split_ifs <;> simp [hν g]) (fun g => ?_) hs
  split_ifs
  · exact le_rfl
  · exact hν g

end Orbit

/-! ### The measures `υ_n` on `G_ω` -/

lemma upsilon_nonneg (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (g : BinaryTreeAut) :
    0 ≤ upsilon D ω k n g :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- `Σ_{g ∈ s} υ_n(e g) ⩽ 1` for an injective `e`. -/
lemma sum_upsilon_le {ι : Type*} (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ)
    (e : ι → BinaryTreeAut) (he : Function.Injective e) (s : Finset ι) :
    ∑ g ∈ s, upsilon D ω k n (e g) ≤ 1 := by
  classical
  unfold upsilon
  rw [← Finset.sum_div]
  by_cases h0 : Nat.card (LambdaN D ω k n) = 0
  · simp [h0]
  have hfin : Finite (LambdaN D ω k n) := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero h0)).2
  letI : Fintype (LambdaN D ω k n) := Fintype.ofFinite _
  have hpos : (0 : ℝ) < Nat.card (LambdaN D ω k n) := by exact_mod_cast Nat.pos_of_ne_zero h0
  rw [div_le_one hpos]
  have key : ∑ g ∈ s, Nat.card {p : LambdaN D ω k n // theta D ω k n p = e g} ≤
      Nat.card (LambdaN D ω k n) := by
    simp_rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← Finset.card_biUnion]
    · exact Finset.card_le_univ _
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hpa hpb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpa hpb
      exact hab (he (hpa.symm.trans hpb))
  exact_mod_cast key

lemma upsilon_le_one (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (g : BinaryTreeAut) :
    upsilon D ω k n g ≤ 1 := by
  have := sum_upsilon_le D ω k n (fun _ : Unit => g) (fun _ _ _ => rfl) {()}
  simpa using this

/-- `ν_n = (υ_n + υ̌_n)/2` on `G_ω`. -/
noncomputable def nuN (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) : grigorchuk ω → ℝ :=
  fun g => (upsilon D ω k n g + upsilonCheck D ω k n g) / 2

lemma sum_nuN_le (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (s : Finset (grigorchuk ω)) :
    ∑ g ∈ s, nuN D ω k n g ≤ 1 := by
  unfold nuN upsilonCheck
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have h1 := sum_upsilon_le D ω k n (fun g : grigorchuk ω => (g : BinaryTreeAut))
    Subtype.val_injective s
  have h2 := sum_upsilon_le D ω k n (fun g : grigorchuk ω => (g : BinaryTreeAut)⁻¹)
    (fun a b h => Subtype.val_injective (inv_injective h)) s
  try simp only at h1 h2
  linarith

/-! ### `μ_β` dominates its `n`-th component -/

lemma rpow_neg_mul_eq (β : ℝ) (m : ℕ) : (2 : ℝ) ^ (-((m : ℝ) * β)) = ((2 : ℝ) ^ (-β)) ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1; ring

lemma summable_two_rpow (β : ℝ) (hβ : 0 < β) :
    Summable (fun m : ℕ => (2 : ℝ) ^ (-((m : ℝ) * β))) := by
  simp_rw [rpow_neg_mul_eq]
  exact summable_geometric_of_lt_one (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))

lemma summable_normSeries (D : ℕ) (β : ℝ) (hβ : 0 < β) :
    Summable (fun m : ℕ => if 1 ≤ m ∧ D ∣ m then (2 : ℝ) ^ (-((m : ℝ) * β)) else 0) :=
  Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
    (fun m => by split_ifs <;> [exact le_rfl; positivity]) (summable_two_rpow β hβ)

lemma normConst_pos (D : ℕ) (β : ℝ) (hβ : 0 < β) (hD : 1 ≤ D) : 0 < normConst D β := by
  unfold normConst
  have : 0 < ∑' m : ℕ, if 1 ≤ m ∧ D ∣ m then (2 : ℝ) ^ (-((m : ℝ) * β)) else 0 :=
    (summable_normSeries D β hβ).tsum_pos (fun m => by split_ifs <;> positivity) D
      (by rw [if_pos ⟨hD, dvd_refl D⟩]; positivity)
  positivity

lemma summable_muBeta_series (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) (hβ : 0 < β)
    (hD : 1 ≤ D) (g : grigorchuk ω) :
    Summable (fun m : ℕ => if 1 ≤ m ∧ D ∣ m then
      normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) *
        (upsilon D ω k m g + upsilonCheck D ω k m g) else 0) := by
  have hC := (normConst_pos D β hβ hD).le
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    ((summable_two_rpow β hβ).mul_left (normConst D β * 2))
  · split_ifs
    · exact mul_nonneg (mul_nonneg hC (by positivity))
        (add_nonneg (upsilon_nonneg _ _ _ _ _) (upsilon_nonneg _ _ _ _ _))
    · exact le_rfl
  · split_ifs
    · have h1 := upsilon_le_one D ω k m g
      have h2 := upsilon_le_one D ω k m (g : BinaryTreeAut)⁻¹
      have h0 : 0 ≤ normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) := mul_nonneg hC (by positivity)
      unfold upsilonCheck
      calc normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) *
            (upsilon D ω k m g + upsilon D ω k m (g : BinaryTreeAut)⁻¹)
          ≤ normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) * 2 :=
            mul_le_mul_of_nonneg_left (by linarith) h0
        _ = normConst D β * 2 * (2 : ℝ) ^ (-((m : ℝ) * β)) := by ring
    · positivity

lemma uniformMeasure_nonneg {G : Type*} (F : Set G) (g : G) : 0 ≤ uniformMeasure F g := by
  classical
  unfold uniformMeasure
  split_ifs <;> positivity

/-- `C_β 2^{-nβ} ν_n ⩽ μ_β`. -/
lemma mul_nuN_le_muBeta (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) (hβ : 0 < β) (hD : 1 ≤ D)
    (n : ℕ) (hn : 1 ≤ n) (hDn : D ∣ n) (g : grigorchuk ω) :
    normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) * nuN D ω k n g ≤ muBeta D ω k β g := by
  have hs := summable_muBeta_series D ω k β hβ hD g
  have hC := (normConst_pos D β hβ hD).le
  have hle := hs.le_tsum n (fun m _ => by
    split_ifs
    · exact mul_nonneg (mul_nonneg hC (by positivity))
        (add_nonneg (upsilon_nonneg _ _ _ _ _) (upsilon_nonneg _ _ _ _ _))
    · exact le_rfl)
  rw [if_pos ⟨hn, hDn⟩] at hle
  unfold muBeta nuN
  have hu := uniformMeasure_nonneg (genSet ω) g
  nlinarith

lemma muBeta_nonneg (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) (hβ : 0 < β) (hD : 1 ≤ D)
    (g : grigorchuk ω) : 0 ≤ muBeta D ω k β g := by
  have hC := (normConst_pos D β hβ hD).le
  unfold muBeta
  have := uniformMeasure_nonneg (genSet ω) g
  have : 0 ≤ ∑' m : ℕ, if 1 ≤ m ∧ D ∣ m then
      normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) *
        (upsilon D ω k m g + upsilonCheck D ω k m g) else 0 :=
    tsum_nonneg fun m => by
      split_ifs
      · exact mul_nonneg (mul_nonneg hC (by positivity))
          (add_nonneg (upsilon_nonneg _ _ _ _ _) (upsilon_nonneg _ _ _ _ _))
      · exact le_rfl
  positivity

/-! ### Symmetry of `μ_β` and the parameters (after prover 5's `P5Goal`) -/

lemma isAdmissibleSeq_kLog (D A : ℕ) (hD : 3 ≤ D) (hDA : D ∣ A) (hA : 0 < A) :
    IsAdmissibleSeq D (kLog A) := by
  refine ⟨fun m n hmn => Nat.mul_le_mul_left A (Nat.log_mono_right hmn), fun n hn hDn => ?_⟩
  have hnD : D ≤ n := Nat.le_of_dvd hn hDn
  have hlog : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
  exact ⟨Nat.mul_pos hA hlog, Dvd.dvd.mul_right hDA _⟩

end P6Dev

end ErschlerZheng
end

section
/-!
# Proposition 7.18 for radii just above 2 (group `p718small`)

For `D = 3`, `ω = (201)^∞`, `β = 9/10`, `A = 3`:

1. the truncated second moment `Σ_{d(x,y) ⩽ r} d(x,y)² P(x,y)` at `x = 1^∞` is at least
   `μ_β(a) > 0` for every `r ⩾ 1` (the term `y = 1^∞·a`, at distance `1`), while
   `C r^{2-β} (log₂ r)^{…} (log₂ log₂ r)^{1+1/D}` tends to `0` as `r → 2⁺`;
2. the tail `Σ_{d(x,y) ⩾ r} P(x,y)` at `x = 1^∞` is at least `μ_β(g_2) > 0` for `r ⩽ 8` (the term
   `y = 1^∞·g_2 = 11001^∞`, at distance `8`), and `g_2 = θ_3(e_2, γ)` for every `γ ∈ 𝔉_3`, while
   `C r^{-β} (log₂ r)^{…} (log₂ log₂ r)^{1+1/D}` tends to `0` as `r → 2⁺`.

The radii used are `r = 2^{2^t}` with `0 < t ⩽ 1`, where `log₂ r = 2^t` and `log₂ log₂ r = t`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace NewP718Small

open GrigBasic SchreierDev GrayDev

/-! ### Summability of `μ_β` -/

theorem genSet_finite (ω : ℕ → Fin 3) : (genSet ω).Finite :=
  (P6Dev.gens_finite ω).preimage Subtype.val_injective.injOn

theorem summable_uniformMeasure_genSet (ω : ℕ → Fin 3) :
    Summable (uniformMeasure (genSet ω)) := by
  classical
  refine summable_of_ne_finset_zero (s := (genSet_finite ω).toFinset) fun g hg => ?_
  rw [Set.Finite.mem_toFinset] at hg
  simp [uniformMeasure, hg]

theorem summable_muBeta (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) (hβ : 0 < β) (hD : 1 ≤ D) :
    Summable (muBeta D ω k β) := by
  classical
  have hC := (P6Dev.normConst_pos D β hβ hD).le
  set a : ℕ → grigorchuk ω → ℝ := fun m g => if 1 ≤ m ∧ D ∣ m then
      normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) *
        (upsilon D ω k m g + upsilonCheck D ω k m g) else 0 with ha
  have ha0 : ∀ m g, 0 ≤ a m g := fun m g => by
    simp only [ha]
    split_ifs
    · exact mul_nonneg (mul_nonneg hC (by positivity))
        (add_nonneg (P6Dev.upsilon_nonneg _ _ _ _ _) (P6Dev.upsilon_nonneg _ _ _ _ _))
    · exact le_rfl
  have hT : Summable (fun g => ∑' m, a m g) := by
    refine summable_of_sum_le (c := ∑' m : ℕ, 2 * normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)))
      (fun g => tsum_nonneg fun m => ha0 m g) (fun s => ?_)
    rw [← Summable.tsum_finsetSum (fun g _ => P6Dev.summable_muBeta_series D ω k β hβ hD g)]
    refine Summable.tsum_le_tsum (fun m => ?_)
      (summable_sum fun g _ => P6Dev.summable_muBeta_series D ω k β hβ hD g)
      ((P6Dev.summable_two_rpow β hβ).mul_left _)
    split_ifs
    · rw [← Finset.mul_sum]
      have h1 := P6Dev.sum_nuN_le D ω k m s
      unfold P6Dev.nuN at h1
      rw [← Finset.sum_div, div_le_one two_pos] at h1
      calc normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) *
            ∑ g ∈ s, (upsilon D ω k m g + upsilonCheck D ω k m g)
          ≤ normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) * 2 :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hC (by positivity))
        _ = 2 * normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) := by ring
    · have h0 : (0 : ℝ) ≤ 2 * normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) := by positivity
      simpa using h0
  have e : muBeta D ω k β =
      fun g => (1 / 2) * uniformMeasure (genSet ω) g + (1 / 2) * ∑' m, a m g := rfl
  rw [e]
  exact ((summable_uniformMeasure_genSet ω).mul_left _).add (hT.mul_left _)

/-! ### `P(x, x·g) ⩾ μ(g)` -/

theorem le_orbitKernel {ω : ℕ → Fin 3} {μ : grigorchuk ω → ℝ} (hμ : ∀ g, 0 ≤ μ g)
    (hs : Summable μ) (x y : orbitOne ω) (g : grigorchuk ω)
    (hy : (y : Ray) = (x : Ray) <• (g : BinaryTreeAut)) :
    μ g ≤ orbitKernel (grigorchuk ω) μ oneRay x y := by
  classical
  unfold orbitKernel
  have hnn : ∀ h : grigorchuk ω,
      0 ≤ (if (x : Ray) <• (h : BinaryTreeAut) = (y : Ray) then μ h else 0) := fun h => by
    split_ifs
    · exact hμ h
    · exact le_rfl
  have hf : Summable (fun h : grigorchuk ω =>
      if (x : Ray) <• (h : BinaryTreeAut) = (y : Ray) then μ h else 0) :=
    Summable.of_nonneg_of_le hnn (fun h => by
      split_ifs
      · exact le_rfl
      · exact hμ h) hs
  have := hf.le_tsum g (fun h _ => hnn h)
  rwa [if_pos hy.symm] at this

/-! ### `μ_β(a) > 0` -/

/-! ### Words of `G_ω` as paths of generators -/

/-- The letters of `evalWord ω 0`. -/
def letterAut (ω : ℕ → Fin 3) : Gen4 → BinaryTreeAut
  | .a => grigA
  | .b => gen ω .b
  | .c => gen ω .c
  | .d => gen ω .d

theorem evalWord_zero_eq (ω : ℕ → Fin 3) (w : List Gen4) :
    evalWord ω 0 w = (w.map (letterAut ω)).prod := by
  unfold evalWord
  congr 2

theorem letterAut_mem_gens (ω : ℕ → Fin 3) (l : Gen4) : letterAut ω l ∈ gens ω := by
  cases l
  · exact grigA_mem_gens ω
  · exact gen_mem_gens ω _
  · exact gen_mem_gens ω _
  · exact gen_mem_gens ω _

theorem evalWord_zero_mem (ω : ℕ → Fin 3) (w : List Gen4) : evalWord ω 0 w ∈ grigorchuk ω := by
  rw [evalWord_zero_eq]
  apply Subgroup.list_prod_mem
  intro s hs
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hs
  exact Subgroup.subset_closure (letterAut_mem_gens ω l)

/-- `1^∞·w` is all ones from position `|w|` on, and its Gray code is that of the first `|w|`
digits. -/
theorem grayCode_oneRay_smul_evalWord (ω : ℕ → Fin 3) (w : List Gen4) :
    grayCode (oneRay <• evalWord ω 0 w) =
      grayList (List.replicate w.length true <• evalWord ω 0 w) := by
  have h := (gray_path_le ω (w.map (letterAut ω))
    (fun s hs => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hs
      exact letterAut_mem_gens ω l) 0 oneRay (fun _ _ => rfl)).2
  rw [List.length_map, zero_add, ← evalWord_zero_eq] at h
  rw [grayCode_eq h, rayPrefix_smul, rayPrefix_oneRay]

theorem isCofinal_oneRay_smul_evalWord (ω : ℕ → Fin 3) (w : List Gen4) :
    IsCofinal (oneRay <• evalWord ω 0 w) := by
  have h := (gray_path_le ω (w.map (letterAut ω))
    (fun s hs => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hs
      exact letterAut_mem_gens ω l) 0 oneRay (fun _ _ => rfl)).2
  rw [← evalWord_zero_eq] at h
  exact (isCofinal_iff _).2 ⟨_, h⟩

theorem isCofinal_oneRay : IsCofinal oneRay := (isCofinal_iff _).2 ⟨0, fun _ _ => rfl⟩

/-- The Schreier distance from `1^∞` to `1^∞·w`. -/
theorem schreierDist_oneRay_smul_evalWord (ω : ℕ → Fin 3) (w : List Gen4) :
    schreierDist ω oneRay (oneRay <• evalWord ω 0 w) =
      grayList (List.replicate w.length true <• evalWord ω 0 w) := by
  have h := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω oneRay (oneRay <• evalWord ω 0 w) isCofinal_oneRay
    (isCofinal_oneRay_smul_evalWord ω w)
  rw [grayCode_oneRay, grayCode_oneRay_smul_evalWord] at h
  simp only [Nat.cast_zero, zero_sub, abs_neg, Nat.abs_cast] at h
  exact_mod_cast h

/-! ### The instance: `D = 3`, `ω = (201)^∞`, `β = 9/10`, `A = 3` -/

/-- `ω = (201)^∞`. -/
def ω₁ : ℕ → Fin 3 := fun i => if i % 3 = 0 then 2 else if i % 3 = 1 then 0 else 1

theorem satisfiesFr_ω₁ : SatisfiesFr 3 ω₁ := by
  intro k
  have h0 : (k * 3 + 0) % 3 = 0 := by omega
  have h1 : (k * 3 + 0 + 1) % 3 = 1 := by omega
  have h2 : (k * 3 + 0 + 2) % 3 = 2 := by omega
  refine ⟨0, by norm_num, ?_, ?_, Or.inl ?_⟩
  · simp only [ω₁, h0, if_true]
  · simp only [ω₁, h2]; rfl
  · simp only [ω₁, h1]; rfl

/-- `1^∞` as a point of the orbit. -/
def o₁ : orbitOne ω₁ := ⟨oneRay, 1, Subgroup.one_mem _, (one_smul _ _).symm⟩

/-- The point `1^∞·g` of the orbit. -/
def ptOf (g : grigorchuk ω₁) : orbitOne ω₁ := ⟨oneRay <• (g : BinaryTreeAut), g, g.2, rfl⟩

/-! ### `g_2` and `υ_3(g_2) > 0` -/

theorem seqG_two : seqG ω₁ 2 = evalWord ω₁ 0 [.a, .c, .a, .b, .a, .d, .a, .c, .a, .b, .a, .d] :=
  rfl

theorem schreierDist_seqG_two : schreierDist ω₁ oneRay (oneRay <• seqG ω₁ 2) = 8 := by
  rw [seqG_two, schreierDist_oneRay_smul_evalWord]
  decide

/-- `g_2` as an element of `G_ω`. -/
def g2Elt : grigorchuk ω₁ := ⟨seqG ω₁ 2, by rw [seqG_two]; exact evalWord_zero_mem ω₁ _⟩

theorem admissible_kLog : IsAdmissibleSeq 3 (kLog 3) :=
  P6Dev.isAdmissibleSeq_kLog 3 3 le_rfl (dvd_refl 3) (by norm_num)

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
  simp [commonPrefixLength, rayPrefix_oneRay, List.replicate_succ]

theorem cpl_replicate_append (N : ℕ) (w : List Bool) :
    N ≤ commonPrefixLength (List.replicate N true ++ w) oneRay := by
  induction N with
  | zero => exact Nat.zero_le _
  | succ N ih =>
    rw [List.replicate_succ, List.cons_append, cpl_cons_true]
    omega

theorem nonempty_fSet (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
    (n : ℕ) (hn : D ∣ n) (hn1 : 1 ≤ n) (i : ℕ) : (fSet D ω k (i + 1) n).Nonempty := by
  unfold fSet
  split_ifs with hc
  · have hkn := hk.2 n hn1 hn
    have hD : 0 < D := Nat.pos_of_ne_zero (fun h => by subst h; simp at hn; omega)
    have hDk : D ≤ k n := Nat.le_of_dvd hkn.1 hkn.2
    have hmod : (i + 1) % D < D := Nat.mod_lt _ hD
    set m := frM D ω (ellIndex D (2 * k n) (i + 1))
    set v := List.replicate (D - (i + 1) % D) true ++ List.replicate (2 * k n) true ++
      List.replicate (m + 2) true ++ [false]
    refine ⟨gTilde ω (i + 1) v, v, ⟨List.replicate (2 * k n) true, ⟨by simp, ?_⟩, rfl⟩, ?_, rfl⟩
    · intro j hj _; simp
    · have : v = List.replicate (D - (i + 1) % D + 2 * k n) true ++
          (List.replicate (m + 2) true ++ [false]) := by
        simp only [v, List.replicate_add, List.append_assoc]
      rw [this]
      refine le_trans ?_ (cpl_replicate_append _ _)
      have := hc.2.1
      omega
  · exact Set.singleton_nonempty _

instance (i : Fin 3) : Finite (fSet 3 ω₁ (kLog 3) (i + 1) 3) :=
  (finite_fSet _ _ _ _ _).to_subtype

instance : Finite (LambdaN 3 ω₁ (kLog 3) 3) := inferInstance

instance : Nonempty (fProd 3 ω₁ (kLog 3) 3) :=
  ⟨fun i => ⟨(nonempty_fSet 3 ω₁ (kLog 3) admissible_kLog 3 (dvd_refl 3) (by norm_num) i).some,
    (nonempty_fSet 3 ω₁ (kLog 3) admissible_kLog 3 (dvd_refl 3) (by norm_num) i).some_mem⟩⟩

/-- `ε = e_2` (only the paper's second coordinate is `1`). -/
def e₁ : Fin 3 → Bool := fun i => decide (i.val = 1)

theorem theta_e₁ (γ : fProd 3 ω₁ (kLog 3) 3) :
    theta 3 ω₁ (kLog 3) 3 (e₁, γ) = (γ 1 : BinaryTreeAut) := by
  simp [theta, List.ofFn_succ, e₁, Fin.rev]

theorem γ1_eq (γ : fProd 3 ω₁ (kLog 3) 3) : (γ 1 : BinaryTreeAut) = seqG ω₁ 2 := by
  have h : (γ 1 : BinaryTreeAut) ∈ fSet 3 ω₁ (kLog 3) 2 3 := (γ 1).2
  have hS : fSet 3 ω₁ (kLog 3) 2 3 = {seqG ω₁ 2} := by
    unfold fSet
    rw [if_neg (by simp [ω₁])]
  rw [hS] at h
  exact h

theorem upsilon_seqG_two_pos : 0 < upsilon 3 ω₁ (kLog 3) 3 (seqG ω₁ 2) := by
  unfold upsilon
  have γ : fProd 3 ω₁ (kLog 3) 3 := Classical.arbitrary _
  have hne : Nonempty {p : LambdaN 3 ω₁ (kLog 3) 3 // theta 3 ω₁ (kLog 3) 3 p = seqG ω₁ 2} :=
    ⟨⟨(e₁, γ), by rw [theta_e₁, γ1_eq]⟩⟩
  have h1 : 0 < Nat.card {p : LambdaN 3 ω₁ (kLog 3) 3 // theta 3 ω₁ (kLog 3) 3 p = seqG ω₁ 2} :=
    Nat.card_pos
  have h2 : 0 < Nat.card (LambdaN 3 ω₁ (kLog 3) 3) := Nat.card_pos
  have h1' : (0 : ℝ) < Nat.card {p : LambdaN 3 ω₁ (kLog 3) 3 //
      theta 3 ω₁ (kLog 3) 3 p = seqG ω₁ 2} := by exact_mod_cast h1
  have h2' : (0 : ℝ) < Nat.card (LambdaN 3 ω₁ (kLog 3) 3) := by exact_mod_cast h2
  exact div_pos h1' h2'

theorem muBeta_g2Elt_pos : 0 < muBeta 3 ω₁ (kLog 3) (9 / 10) g2Elt := by
  have hle := P6Dev.mul_nuN_le_muBeta 3 ω₁ (kLog 3) (9 / 10) (by norm_num) (by norm_num) 3
    (by norm_num) (dvd_refl 3) g2Elt
  have hC := P6Dev.normConst_pos 3 (9 / 10) (by norm_num) (by norm_num)
  have hν : 0 < P6Dev.nuN 3 ω₁ (kLog 3) 3 g2Elt := by
    unfold P6Dev.nuN
    have := upsilon_seqG_two_pos
    have h' := P6Dev.upsilon_nonneg 3 ω₁ (kLog 3) 3 ((g2Elt : BinaryTreeAut)⁻¹)
    unfold upsilonCheck
    have e : ((g2Elt : grigorchuk ω₁) : BinaryTreeAut) = seqG ω₁ 2 := rfl
    rw [e] at h' ⊢
    linarith
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(((3 : ℕ) : ℝ) * (9 / 10))) := by positivity
  have := mul_pos (mul_pos hC h2) hν
  linarith

/-! ### The right sides tend to `0` as `r → 2⁺` -/

theorem exists_rhs_lt (C c : ℝ) (hc : 0 < c) (p e₁ e₂ : ℝ)
    (hp : ∀ r : ℝ, 2 ≤ r → r ≤ 4 → r ^ p ≤ 16) (he₁ : 0 ≤ e₁) (he₁' : e₁ ≤ 4) (he₂ : 1 ≤ e₂) :
    ∃ r : ℝ, 2 < r ∧ r ≤ 4 ∧
      C * r ^ p * Real.logb 2 r ^ e₁ * Real.logb 2 (Real.logb 2 r) ^ e₂ < c := by
  -- `r = 2^{2^t}`
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      2 < (2 : ℝ) ^ ((2 : ℝ) ^ t) ∧ (2 : ℝ) ^ ((2 : ℝ) ^ t) ≤ 4 ∧
      Real.logb 2 ((2 : ℝ) ^ ((2 : ℝ) ^ t)) = (2 : ℝ) ^ t ∧
      Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ ((2 : ℝ) ^ t))) = t := by
    intro t ht0 ht1
    have h1 : 1 < (2 : ℝ) ^ t := Real.one_lt_rpow (by norm_num) ht0
    have h2 : (2 : ℝ) ^ t ≤ 2 := by
      calc (2 : ℝ) ^ t ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) ht1
        _ = 2 := Real.rpow_one 2
    have hl : Real.logb 2 ((2 : ℝ) ^ ((2 : ℝ) ^ t)) = (2 : ℝ) ^ t :=
      Real.logb_rpow (by norm_num) (by norm_num)
    refine ⟨?_, ?_, hl, ?_⟩
    · calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ < (2 : ℝ) ^ ((2 : ℝ) ^ t) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
    · calc (2 : ℝ) ^ ((2 : ℝ) ^ t) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
        _ = 4 := by norm_num
    · rw [hl, Real.logb_rpow (by norm_num) (by norm_num)]
  by_cases hC : C ≤ 0
  · obtain ⟨h2, h4, hl, hll⟩ := key 1 one_pos le_rfl
    refine ⟨_, h2, h4, ?_⟩
    rw [hll, hl]
    have : 0 ≤ ((2 : ℝ) ^ ((2 : ℝ) ^ (1 : ℝ))) ^ p * ((2 : ℝ) ^ (1 : ℝ)) ^ e₁ * (1 : ℝ) ^ e₂ := by
      positivity
    have : C * ((2 : ℝ) ^ ((2 : ℝ) ^ (1 : ℝ))) ^ p * ((2 : ℝ) ^ (1 : ℝ)) ^ e₁ * (1 : ℝ) ^ e₂ ≤ 0 := by
      have e : C * ((2 : ℝ) ^ ((2 : ℝ) ^ (1 : ℝ))) ^ p * ((2 : ℝ) ^ (1 : ℝ)) ^ e₁ * (1 : ℝ) ^ e₂ =
          C * (((2 : ℝ) ^ ((2 : ℝ) ^ (1 : ℝ))) ^ p * ((2 : ℝ) ^ (1 : ℝ)) ^ e₁ * (1 : ℝ) ^ e₂) := by
        ring
      rw [e]
      exact mul_nonpos_of_nonpos_of_nonneg hC this
    linarith
  push Not at hC
  set t := min 1 (c / (512 * C)) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htc : t ≤ c / (512 * C) := min_le_right _ _
  obtain ⟨h2, h4, hl, hll⟩ := key t ht0 ht1
  set r := (2 : ℝ) ^ ((2 : ℝ) ^ t)
  refine ⟨r, h2, h4, ?_⟩
  rw [hll, hl]
  have hrp : r ^ p ≤ 16 := hp r h2.le h4
  have hrp0 : 0 ≤ r ^ p := by positivity
  have he : ((2 : ℝ) ^ t) ^ e₁ ≤ 16 := by
    rw [← Real.rpow_mul (by norm_num)]
    calc (2 : ℝ) ^ (t * e₁) ≤ (2 : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ = 16 := by norm_num
  have he0 : 0 ≤ ((2 : ℝ) ^ t) ^ e₁ := by positivity
  have htt : t ^ e₂ ≤ t := by
    calc t ^ e₂ ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 he₂
      _ = t := Real.rpow_one t
  have htt0 : 0 ≤ t ^ e₂ := by positivity
  have hprod : r ^ p * ((2 : ℝ) ^ t) ^ e₁ * t ^ e₂ ≤ 16 * 16 * t := by
    have := mul_le_mul hrp he he0 (by norm_num)
    exact mul_le_mul this htt htt0 (by norm_num)
  have hct : 512 * C * t ≤ c := by
    rw [le_div_iff₀ (by positivity)] at htc
    linarith
  calc C * r ^ p * ((2 : ℝ) ^ t) ^ e₁ * t ^ e₂ = C * (r ^ p * ((2 : ℝ) ^ t) ^ e₁ * t ^ e₂) := by
        ring
    _ ≤ C * (16 * 16 * t) := mul_le_mul_of_nonneg_left hprod hC.le
    _ < c := by nlinarith

/-! ### The left sides -/

theorem muBeta_nonneg₁ (g : grigorchuk ω₁) : 0 ≤ muBeta 3 ω₁ (kLog 3) (9 / 10) g :=
  P6Dev.muBeta_nonneg 3 ω₁ (kLog 3) (9 / 10) (by norm_num) (by norm_num) g

theorem summable_muBeta₁ : Summable (muBeta 3 ω₁ (kLog 3) (9 / 10)) :=
  summable_muBeta 3 ω₁ (kLog 3) (9 / 10) (by norm_num) (by norm_num)

theorem summable_row₁ (x : orbitOne ω₁) :
    Summable (fun y => orbitKernel (grigorchuk ω₁) (muBeta 3 ω₁ (kLog 3) (9 / 10)) oneRay x y) :=
  (P6Dev.hasSum_orbitKernel_row (grigorchuk ω₁) muBeta_nonneg₁ summable_muBeta₁ oneRay x).summable

theorem orbitKernel_nonneg₁ (x y : orbitOne ω₁) :
    0 ≤ orbitKernel (grigorchuk ω₁) (muBeta 3 ω₁ (kLog 3) (9 / 10)) oneRay x y :=
  P6Dev.orbitKernel_nonneg' (grigorchuk ω₁) muBeta_nonneg₁ oneRay x y

/-- The tail at `1^∞` is at least `μ_β(g_2)` for `r ⩽ 8`. -/
theorem muBeta_g2Elt_le_tsum (r : ℝ) (hr : r ≤ 8) :
    muBeta 3 ω₁ (kLog 3) (9 / 10) g2Elt ≤
      ∑' y : orbitOne ω₁,
        (if r ≤ orbitDist ω₁ o₁ y then
          orbitKernel (grigorchuk ω₁) (muBeta 3 ω₁ (kLog 3) (9 / 10)) oneRay o₁ y else 0) := by
  set P := orbitKernel (grigorchuk ω₁) (muBeta 3 ω₁ (kLog 3) (9 / 10)) oneRay
  have hnn : ∀ y, 0 ≤ (if r ≤ orbitDist ω₁ o₁ y then P o₁ y else 0) := fun y => by
    split_ifs
    · exact orbitKernel_nonneg₁ _ _
    · exact le_rfl
  have hf : Summable (fun y => if r ≤ orbitDist ω₁ o₁ y then P o₁ y else 0) := by
    refine Summable.of_nonneg_of_le hnn (fun y => ?_) (summable_row₁ o₁)
    split_ifs
    · exact le_rfl
    · exact orbitKernel_nonneg₁ _ _
  have hd : orbitDist ω₁ o₁ (ptOf g2Elt) = 8 := by
    show ((schreierDist ω₁ oneRay (oneRay <• seqG ω₁ 2) : ℕ) : ℝ) = 8
    rw [schreierDist_seqG_two]
    norm_num
  have hle := hf.le_tsum (ptOf g2Elt) (fun y _ => hnn y)
  rw [if_pos (by rw [hd]; exact hr)] at hle
  exact (le_orbitKernel muBeta_nonneg₁ summable_muBeta₁ o₁ (ptOf g2Elt) g2Elt rfl).trans hle

end NewP718Small

open NewP718Small

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open NewP718Small
theorem solution :
    ¬ ∀ (D : ℕ) (ω : ℕ → Fin 3), SatisfiesFr D ω → ∀ β : ℝ, 1 - 1 / (D : ℝ) < β → β < 1 →
      ∀ A : ℕ, 0 < A → D ∣ A →
      ∃ C : ℝ, ∀ x : orbitOne ω, ∀ r : ℝ, 2 < r →
        ∑' y : orbitOne ω,
            (if r ≤ orbitDist ω x y then
              orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay x y else 0) ≤
          C * r ^ (-β) * Real.logb 2 r ^ (2 * (A : ℝ) * (β - 1 / (D : ℝ))) *
            Real.logb 2 (Real.logb 2 r) ^ (1 + 1 / (D : ℝ)) := by
  intro h
  obtain ⟨C, hC⟩ := h 3 ω₁ satisfiesFr_ω₁ (9 / 10) (by norm_num) (by norm_num) 3 (by norm_num)
    (dvd_refl 3)
  obtain ⟨r, hr2, hr4, hlt⟩ := exists_rhs_lt C _ muBeta_g2Elt_pos (-(9 / 10))
    (2 * ((3 : ℕ) : ℝ) * (9 / 10 - 1 / ((3 : ℕ) : ℝ))) (1 + 1 / ((3 : ℕ) : ℝ))
    (fun r h2 h4 => by
      have : r ^ (-(9 / 10) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      linarith)
    (by norm_num) (by norm_num) (by norm_num)
  have h1 := hC o₁ r hr2
  have h2 := muBeta_g2Elt_le_tsum r (by linarith)
  linarith
end
