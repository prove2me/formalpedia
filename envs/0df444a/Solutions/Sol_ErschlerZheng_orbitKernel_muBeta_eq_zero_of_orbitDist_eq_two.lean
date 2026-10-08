-- Prove2me | solution 1 for ErschlerZheng.orbitKernel_muBeta_eq_zero_of_orbitDist_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T12:44:17.402982+00:00
-- url     : https://prove2.me/submissions/52eabc82-f13e-4e2e-9ce8-c41e5bcd79c4

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem
import Theorems.Thm_ErschlerZheng_seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms
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

theorem singleton_rayPrefix (x : Ray) : rayPrefix x 1 = [x 0] := by
  simp [rayPrefix]

theorem shiftRay_smul_one (g : BinaryTreeAut) (x : Ray) :
    shiftRay (x <• g) 1 = shiftRay x 1 <• sec g [x 0] := by
  rw [shiftRay_smul, singleton_rayPrefix]

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

theorem mem_wordBall_of_list (ω : ℕ → Fin 3) (l : List BinaryTreeAut) (hl : ∀ s ∈ l, s ∈ gens ω) :
    l.prod ∈ Chou.wordBall (gens ω) l.length :=
  ⟨l, le_rfl, fun s hs => Or.inl (hl s hs), rfl⟩

end SchreierDev

end ErschlerZheng
end

section
/-!
# A2: `L` is locally finite; `G_ω`- and `L`-orbits are cofinality classes; `L` is auxiliary (p. 18)

- `G_ω`-orbits: generators change finitely many digits; conversely the Gray-code path at level `N`
  (whose sections at the intermediate words are trivial) carries any common tail along.
- `L`-orbits: finitary elements fix the tail beyond their level; conversely the digit-flip
  automorphism `D_p` (flip the digits where `p` is true) is finitary when `p` is eventually false.
- Local finiteness: a finite subset of `L` lies in the subgroup `K_N` of elements with trivial
  sections at level `N`, which embeds in the maps of level `N` to itself.
- Trivial isotropy: a finitary `h` fixing `x` fixes every `y` with the same first `N` digits.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace OrbitsDev

open GrigBasic RayBasic GrayDev SchreierDev

/-- Eventual agreement of rays. -/
def Cof (x y : Ray) : Prop := ∀ᶠ n in Filter.atTop, y n = x n

theorem cof_refl (x : Ray) : Cof x x := Filter.Eventually.of_forall fun _ => rfl

theorem cof_symm {x y : Ray} (h : Cof x y) : Cof y x := h.mono fun _ h => h.symm

theorem cof_trans {x y z : Ray} (h1 : Cof x y) (h2 : Cof y z) : Cof x z :=
  (h1.and h2).mono fun _ h => h.2.trans h.1

theorem cof_of_shiftRay_eq {x y : Ray} {N : ℕ} (h : shiftRay y N = shiftRay x N) : Cof x y := by
  rw [Cof, Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have := congrFun h (n - N)
  simpa [shiftRay, show n - N + N = n by omega] using this

/-! ### `G_ω`-orbits -/

theorem cof_smul_gens (ω : ℕ → Fin 3) {s : BinaryTreeAut} (hs : s ∈ gens ω) (x : Ray) :
    Cof x (x <• s) := by
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · apply cof_of_shiftRay_eq (N := 1)
    rw [shiftRay_smul_one, sec_grigA, one_smul_ray]
  all_goals
    classical
    by_cases hz : ∃ k, x k = false
    · have hk : x (Nat.find hz) = false := Nat.find_spec hz
      have hmin : ∀ j < Nat.find hz, x j = true := fun j hj => by
        have := Nat.find_min hz hj
        simpa using this
      apply cof_of_shiftRay_eq (N := Nat.find hz + 2)
      rw [shiftRay_smul]
      have hpre : rayPrefix x (Nat.find hz + 2) =
          List.replicate (Nat.find hz) true ++ false :: [x (Nat.find hz + 1)] := by
        apply List.ext_getElem
        · simp [length_rayPrefix]
        · intro i h1 h2
          rw [getElem_rayPrefix]
          simp only [length_rayPrefix] at h1
          by_cases hi : i < Nat.find hz
          · rw [List.getElem_append_left (by simpa using hi)]
            simp [hmin i hi]
          · rw [List.getElem_append_right (by simpa using hi)]
            simp only [List.length_replicate]
            rcases (show i = Nat.find hz ∨ i = Nat.find hz + 1 by omega) with e | e
            · subst e; simp [hk]
            · subst e; simp
      rw [hpre, sec_gen_replicate _ _ _ _ (by simp), one_smul_ray]
    · push Not at hz
      have hx : x = oneRay := funext fun k => by simpa [oneRay] using hz k
      rw [hx, oneRay_smul_gen]
      exact cof_refl _

theorem cof_smul_of_mem (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) (x : Ray) :
    Cof x (x <• g) := by
  suffices H : ∀ x, Cof x (x <• g) from H x
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact cof_smul_gens ω hs
  | one => intro x; rw [one_smul_ray]; exact cof_refl x
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

/-! ### The digit-flip automorphisms -/

/-! ### `L`-orbits -/

/-! ### Local finiteness -/

/-! ### Trivial isotropy of `L` -/

end OrbitsDev

end ErschlerZheng
end

section
/-!
# `P_{μ_β}` vanishes at Schreier distance 2 (group `p718small`, optional item)

Every element of `𝔉_{j,n}` (`j ⩾ 1`) fixes the first level: `g_j` by Lemma 7.6 (milestone
`seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms`) and `g̃^v_j` with `ω_{j-1} = 2` by
Lemma 7.9 (milestone `exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem`). So every `θ_n(λ)`
fixes the first level, and `μ_β` is carried by `S ∪ St(1)`. An element `g` fixing the first level
moves a ray `bv1^∞` to `bv'1^∞`, and the Gray codes `2ḡ(v) + ((e + ḡ(v)) mod 2)` and
`2ḡ(v') + ((e + ḡ(v')) mod 2)` (`e = 1` if `b = 0`) never differ by exactly `2`; a generator moves
a ray by at most `1`. So no element of the support of `μ_β` moves a point of `1^∞·G_ω` by exactly
`2`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace NewP718SmallZero

open GrigBasic SchreierDev GrayDev

/-! ### Root swaps -/

theorem rootSwap_eq_false_of_mem_levelStab {K : Subgroup BinaryTreeAut} {n : ℕ} (hn : 1 ≤ n)
    {g : BinaryTreeAut} (hg : g ∈ levelStab K n) : rootSwap g = false := by
  have h := hg.2 (false :: List.replicate (n - 1) false) (by simp; omega)
  rw [cons_smul] at h
  simpa using (List.cons.inj h).1

theorem rootSwap_eq_false_of_mem_fSet (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj : 1 ≤ j)
    {γ : BinaryTreeAut} (hγ : γ ∈ fSet D ω k j n) : rootSwap γ = false := by
  unfold fSet at hγ
  split_ifs at hγ with hc
  · obtain ⟨v, hv, -, rfl⟩ := hγ
    obtain ⟨h2, hjn, hjn'⟩ := hc
    have hkn := hk.2 n (by omega) hn
    have h := (exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem D ω hω j hj (2 * k n)
      (Dvd.dvd.mul_left hkn.2 2) v hv).2.2 (by rw [h2]; decide)
    exact rootSwap_eq_false_of_mem_levelStab hj h.1
  · rw [Set.mem_singleton_iff.mp hγ]
    exact rootSwap_eq_false_of_mem_levelStab hj
      ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).1 j hj).1

theorem rootSwap_list_prod (l : List BinaryTreeAut) (hl : ∀ g ∈ l, rootSwap g = false) :
    rootSwap l.prod = false := by
  induction l with
  | nil => exact rootSwap_one
  | cons g l ih =>
    rw [List.prod_cons, rootSwap_mul, hl g (by simp), ih (fun h hh => hl h (by simp [hh]))]
    rfl

theorem rootSwap_pow (g : BinaryTreeAut) (hg : rootSwap g = false) (m : ℕ) :
    rootSwap (g ^ m) = false := by
  induction m with
  | zero => rw [pow_zero]; exact rootSwap_one
  | succ m ih => rw [pow_succ, rootSwap_mul, ih, hg]; rfl

theorem rootSwap_theta (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (p : LambdaN D ω k n) :
    rootSwap (theta D ω k n p) = false := by
  unfold theta
  apply rootSwap_list_prod
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact rootSwap_pow _ (rootSwap_eq_false_of_mem_fSet D ω hω k hk n hn _ (by omega)
    (p.2 i.rev).2) _

theorem upsilon_eq_zero (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (g : BinaryTreeAut) (hg : rootSwap g = true) :
    upsilon D ω k n g = 0 := by
  unfold upsilon
  have : IsEmpty {p : LambdaN D ω k n // theta D ω k n p = g} := ⟨fun p => by
    have := rootSwap_theta D ω hω k hk n hn p.1
    rw [p.2, hg] at this
    exact Bool.noConfusion this⟩
  rw [Nat.card_of_isEmpty, Nat.cast_zero, zero_div]

/-- `μ_β` vanishes outside `S ∪ St(1)`. -/
theorem muBeta_eq_zero (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (β : ℝ) (g : grigorchuk ω) (hS : g ∉ genSet ω)
    (hg : rootSwap g = true) : muBeta D ω k β g = 0 := by
  classical
  unfold muBeta
  have hu : uniformMeasure (genSet ω) g = 0 := by simp [uniformMeasure, hS]
  have hT : ∀ m : ℕ, (if 1 ≤ m ∧ D ∣ m then
      normConst D β * (2 : ℝ) ^ (-((m : ℝ) * β)) *
        (upsilon D ω k m g + upsilonCheck D ω k m g) else 0) = 0 := fun m => by
    split_ifs with hm
    · have h1 := upsilon_eq_zero D ω hω k hk m hm.2 g hg
      have h2 := upsilon_eq_zero D ω hω k hk m hm.2 (g : BinaryTreeAut)⁻¹
        (by rw [rootSwap_inv]; exact hg)
      simp only [upsilonCheck, h1, h2, add_zero, mul_zero]
    · rfl
  rw [hu, tsum_congr hT, tsum_zero]
  ring

/-! ### Gray codes under `St(1)` -/

theorem grayList_mod_two (w : List Bool) : grayList w % 2 = w.count false % 2 := by
  cases w with
  | nil => rfl
  | cons b w => rw [grayList_cons]; omega

theorem grayCode_sub_ne_two (g : BinaryTreeAut) (hg : rootSwap g = false)
    (x : Ray) (hx : IsCofinal x) (hxg : IsCofinal (x <• g)) :
    (grayCode (x <• g) : ℤ) - grayCode x ≠ 2 ∧ (grayCode (x <• g) : ℤ) - grayCode x ≠ -2 := by
  obtain ⟨N1, h1⟩ := (isCofinal_iff x).mp hx
  obtain ⟨N2, h2⟩ := (isCofinal_iff _).mp hxg
  set N := max N1 N2 + 1
  have hx' : AllOnesFrom N x := h1.mono (by omega)
  have hxg' : AllOnesFrom N (x <• g) := h2.mono (by omega)
  rw [grayCode_eq hx', grayCode_eq hxg', rayPrefix_smul]
  obtain ⟨b, v, hbv⟩ : ∃ b v, rayPrefix x N = b :: v := by
    cases h : rayPrefix x N with
    | nil =>
      have := length_rayPrefix x N
      rw [h] at this
      simp at this
    | cons b v => exact ⟨b, v, rfl⟩
  rw [hbv, cons_smul, hg, Bool.xor_false]
  set v' := v <• sec g [b]
  have hG := grayList_mod_two v
  have hG' := grayList_mod_two v'
  rw [grayList_cons, grayList_cons]
  have e1 : (b :: v).count false = v.count false + (if b = false then 1 else 0) := by
    cases b <;> simp
  have e2 : (b :: v').count false = v'.count false + (if b = false then 1 else 0) := by
    cases b <;> simp
  rw [e1, e2]
  split_ifs <;> omega

/-! ### Assembly -/

theorem isCofinal_of_mem_orbitOne (ω : ℕ → Fin 3) (x : orbitOne ω) : IsCofinal (x : Ray) := by
  obtain ⟨k, hk, hx⟩ := x.2
  have := OrbitsDev.cof_smul_of_mem ω hk oneRay
  rw [← hx] at this
  exact this.mono fun n h => by rw [h]; rfl

theorem schreierDist_smul_gens_le (ω : ℕ → Fin 3) {s : BinaryTreeAut} (hs : s ∈ gens ω)
    (x : Ray) : schreierDist ω x (x <• s) ≤ 1 := by
  apply Nat.sInf_le
  refine ⟨[s].prod, ?_, by simp⟩
  exact mem_wordBall_of_list ω [s] (by simpa using hs)

end NewP718SmallZero

open NewP718SmallZero

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open NewP718SmallZero
theorem solution (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (β : ℝ) (x y : orbitOne ω)
    (hxy : orbitDist ω x y = 2) :
    orbitKernel (grigorchuk ω) (muBeta D ω k β) oneRay x y = 0 := by
  classical
  have hd : schreierDist ω x y = 2 := by
    unfold orbitDist at hxy
    exact_mod_cast hxy
  unfold orbitKernel
  have hterm : ∀ g : grigorchuk ω,
      (if (x : Ray) <• (g : BinaryTreeAut) = y then muBeta D ω k β g else 0) = 0 := by
    intro g
    split_ifs with h
    · by_cases hS : g ∈ genSet ω
      · exfalso
        have := schreierDist_smul_gens_le ω (s := (g : BinaryTreeAut)) hS (x : Ray)
        rw [h, hd] at this
        omega
      · cases hr : GrigBasic.rootSwap (g : BinaryTreeAut)
        · exfalso
          have hcx := isCofinal_of_mem_orbitOne ω x
          have hcy := isCofinal_of_mem_orbitOne ω y
          have hg := grayCode_sub_ne_two g hr x hcx (by rw [h]; exact hcy)
          have hdist := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x y hcx hcy
          rw [h] at hg
          rw [hd] at hdist
          rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 2)).mp hdist.symm with e | e <;> omega
        · exact muBeta_eq_zero D ω hω k hk β g hS hr
    · rfl
  rw [tsum_congr hterm, tsum_zero]
end
