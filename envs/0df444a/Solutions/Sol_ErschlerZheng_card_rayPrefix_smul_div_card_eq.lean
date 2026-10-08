-- Prove2me | solution 1 for ErschlerZheng.card_rayPrefix_smul_div_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T08:46:05.813236+00:00
-- url     : https://prove2.me/submissions/e4ba94da-ee7d-4442-bd3c-5a2a55f1f2f5

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms
import Theorems.Thm_ErschlerZheng_exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem
import Theorems.Thm_ErschlerZheng_setOf_not_mem_letterGerms_seqG_eq
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

theorem orbit_smul {G : Subgroup H} {o x : X} (hx : x ∈ rightOrbit G o) {g : H} (hg : g ∈ G) :
    x <• g ∈ rightOrbit G o := by
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k * g, G.mul_mem hk hg, (rsmul_mul o k g).symm⟩

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

theorem goodAt_inv (ω : ℕ → Fin 3) {g : BinaryTreeAut} {x : Ray} (hg : GoodAt ω g x) :
    GoodAt ω g⁻¹ (x <• g) := by
  obtain ⟨N, hN⟩ := hg
  have e : ∀ n, sec g⁻¹ (rayPrefix (x <• g) n) = (sec g (rayPrefix x n))⁻¹ := fun n => by
    rw [sec_inv, rayPrefix_smul, vertex_smul_smul_inv]
  refine ⟨N, ?_⟩
  rcases hN with hN | hN
  · exact Or.inl fun n hn => by rw [e, hN n hn, inv_one]
  · exact Or.inr fun n hn => by rw [e, hN n hn, gen_inv]

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
# Proposition 7.12, `υ_n` half: no mass at `x = 1^∞` (prover 3, item 3)

For every `p ∈ Λ_n`, `(θ_n(p), 1^∞) ∈ ℋ^b`, so `υ_n{g : (g, 1^∞) ∉ ℋ^b} = 0`. In
`θ = γ_n^{ε_n} ⋯ γ_1^{ε_1}` the factor `γ_j` acts at `1^∞·γ_n^{ε_n}⋯γ_{j+1}^{ε_{j+1}}`, which begins with
`1^{j+1}` because every `γ_i ∈ St(L_i)`; points beginning with `1^{j+1}` are not bad for `γ_j` (the
bad points have `j + 1 + Σ_{i ⩽ j+1} x_i` odd); and good germs compose (sections eventually `1` or
`b`). A reduction to the Construction milestones (7.1)/Lemma 5.6 (`seqG`), Lemma 7.9 (`gTilde`),
`B_j` and (7.16).
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErschlerZheng

namespace P3U0Dev

open GrigBasic RayBasic SchreierDev GermBase GrigGermsDev P3P712Dev

theorem fix_le {g : BinaryTreeAut} {K : Subgroup BinaryTreeAut} {i : ℕ} (hg : g ∈ levelStab K i)
    {m : ℕ} (hm : m ≤ i) (u : List Bool) (hu : u.length = m) : u <• g = u := by
  have hfix := (Subgroup.mem_inf.mp hg).2
  set w := u ++ List.replicate (i - m) true
  have hw : w <• g = w := hfix w (by simp [w, hu]; omega)
  have hp : u <• g <+: w <• g := (vertex_smul_prefix_iff g u w).2 (List.prefix_append _ _)
  rw [hw] at hp
  have hp2 : u <+: w := List.prefix_append _ _
  exact List.prefix_of_prefix_length_le hp hp2 (by rw [length_vertex_smul]) |>.eq_of_length
    (by rw [length_vertex_smul])

section

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
  (n : ℕ) (hn : D ∣ n)

include hω hk hn

/-- Every factor `γ_{i+1}` lies in `St(L_{i+1})`. -/
theorem levelStab_factor (p : LambdaN D ω k n) (i : Fin n) :
    (p.2 i : BinaryTreeAut) ∈ levelStab (grigorchuk ω) (i + 1) := by
  have h := (p.2 i).2
  unfold fSet at h
  split_ifs at h with hc
  · obtain ⟨v, hv, -, e⟩ := h
    rw [e]
    have hDk : D ∣ 2 * k n := Dvd.dvd.mul_left ((hk.2 n (by omega) hn).2) 2
    exact ((exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem D ω hω (i + 1) (by omega)
      (2 * k n) hDk v hv).2.2 (by rw [hc.1]; decide)).1
  · rw [Set.mem_singleton_iff.mp h]
    exact ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).1 (i + 1)
      (by omega)).1

end

end P3U0Dev

end ErschlerZheng
end

section
/-!
# G8 (pp. 55–56, corrected): uniform digits — counting tools (prover 3, in progress)

Each factor `F_i` keeps the first `i + 1` digits and flips digit `i + 1` exactly when its exponent
bit is set. Then the first digits of `x·F_s(e_s)⋯F_{s+L-1}(e_{s+L-1})` beyond position `s` are a
bijective function of the bits `e_s, …, e_{s+L-1}`: flipping the last bit toggles the last digit and
changes nothing before it (`card_forward`).
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ErschlerZheng

namespace P3G8Dev

open RayBasic

/-- Half of a set is cut out by a predicate that an involution toggles. -/
theorem two_mul_card {α : Type*} [Fintype α] (σ : α ≃ α) (A B : α → Prop) [DecidablePred A]
    [DecidablePred B] (hA : ∀ a, A (σ a) ↔ A a) (hB : ∀ a, B (σ a) ↔ ¬ B a) :
    2 * Fintype.card {a // A a ∧ B a} = Fintype.card {a // A a} := by
  have h1 : Fintype.card {a // A a ∧ B a} = Fintype.card {a // A a ∧ ¬ B a} :=
    Fintype.card_congr (σ.subtypeEquiv fun a => by
      constructor
      · rintro ⟨ha, hb⟩; exact ⟨(hA a).mpr ha, (hB a).not.mpr (not_not.mpr hb)⟩
      · rintro ⟨ha, hb⟩; exact ⟨(hA a).mp ha, by simpa using (hB a).not.mp hb⟩)
  have h2 : Fintype.card {a // A a} =
      Fintype.card {a // A a ∧ B a} + Fintype.card {a // A a ∧ ¬ B a} := by
    simp only [Fintype.card_subtype]
    rw [← Finset.filter_filter, ← Finset.filter_filter,
      Finset.card_filter_add_card_filter_not]
  omega

/-- Extending a finite bit vector by `false`. -/
def ext {n : ℕ} (e : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then e ⟨i, h⟩ else false

/-- `F_s(e_s) ⋯ F_{s+L-1}(e_{s+L-1})`. -/
def Q (F : ℕ → Bool → BinaryTreeAut) (s L : ℕ) (e : ℕ → Bool) : BinaryTreeAut :=
  ((List.range L).map fun t => F (s + t) (e (s + t))).prod

theorem Q_succ (F : ℕ → Bool → BinaryTreeAut) (s L : ℕ) (e : ℕ → Bool) :
    Q F s (L + 1) e = Q F s L e * F (s + L) (e (s + L)) := by
  simp [Q, List.range_succ, List.prod_append]

theorem Q_congr (F : ℕ → Bool → BinaryTreeAut) (s L : ℕ) {e e' : ℕ → Bool}
    (h : ∀ t < L, e (s + t) = e' (s + t)) : Q F s L e = Q F s L e' := by
  unfold Q
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [h t (List.mem_range.mp ht)]

theorem rayPrefix_succ' (z : Ray) (m : ℕ) : rayPrefix z (m + 1) = rayPrefix z m ++ [z m] := by
  unfold rayPrefix
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

/-- Forward products: the count of bit vectors giving a prescribed prefix. -/
theorem card_forward (n : ℕ) (F : ℕ → Bool → BinaryTreeAut) (s : ℕ)
    (hF : ∀ i, s ≤ i → i < n → ∀ b (z : Ray),
      rayPrefix (z <• F i b) (i + 1) = rayPrefix z (i + 1) ∧
        (z <• F i b) (i + 1) = xor (z (i + 1)) b) :
    ∀ L, s + L ≤ n → ∀ (x : Ray) (w : List Bool), w.length = s + 1 + L →
      Fintype.card {e : Fin n → Bool // rayPrefix (x <• Q F s L (ext e)) (s + 1 + L) = w} =
        if rayPrefix x (s + 1) = w.take (s + 1) then 2 ^ (n - L) else 0
  | 0, _, x, w, hw => by
    classical
    have hQ : Q F s 0 (fun _ => false) = 1 := by simp [Q]
    simp only [Q, List.range_zero, List.map_nil, List.prod_nil, add_zero]
    rw [MulOpposite.op_one, one_smul]
    have hwt : w.take (s + 1) = w := List.take_of_length_le (by omega)
    rw [hwt]
    split_ifs with h
    · simp [h]
    · simp [h]
  | L + 1, hL, x, w, hw => by
    classical
    have ih := card_forward n F s hF L (by omega) x (w.take (s + 1 + L)) (by simp [hw])
    set c := w[s + 1 + L]'(by omega)
    have hwsplit : w = w.take (s + 1 + L) ++ [c] := by
      have h1 : w.take (s + 1 + L + 1) = w := List.take_of_length_le (by omega)
      have h2 := List.take_add_one (l := w) (i := s + 1 + L)
      rw [h1, List.getElem?_eq_getElem (by omega), Option.toList_some] at h2
      exact h2
    -- the condition splits
    have key : ∀ e : Fin n → Bool, rayPrefix (x <• Q F s (L + 1) (ext e)) (s + 1 + (L + 1)) = w ↔
        (rayPrefix (x <• Q F s L (ext e)) (s + 1 + L) = w.take (s + 1 + L) ∧
          xor ((x <• Q F s L (ext e)) (s + 1 + L)) (ext e (s + L)) = c) := by
      intro e
      rw [Q_succ, MulOpposite.op_mul, mul_smul]
      set y := x <• Q F s L (ext e)
      have h := hF (s + L) (by omega) (by omega) (ext e (s + L)) y
      rw [show s + 1 + (L + 1) = (s + L + 1) + 1 by ring, rayPrefix_succ', h.1, h.2,
        show s + L + 1 = s + 1 + L by ring]
      conv_lhs => rw [hwsplit]
      constructor
      · intro h'
        have := List.append_inj h' (by rw [length_rayPrefix, List.length_take]; omega)
        exact ⟨this.1, by simpa using this.2⟩
      · rintro ⟨h1, h2⟩; rw [h1, h2]
    -- the flip of bit `s + L`
    have hlt : s + L < n := by omega
    let σ : (Fin n → Bool) ≃ (Fin n → Bool) :=
      { toFun := fun e => Function.update e ⟨s + L, hlt⟩ (!e ⟨s + L, hlt⟩)
        invFun := fun e => Function.update e ⟨s + L, hlt⟩ (!e ⟨s + L, hlt⟩)
        left_inv := fun e => by funext i; by_cases hi : i = ⟨s + L, hlt⟩ <;> simp [hi]
        right_inv := fun e => by funext i; by_cases hi : i = ⟨s + L, hlt⟩ <;> simp [hi] }
    have hext : ∀ e : Fin n → Bool, ∀ i, i ≠ s + L → ext (σ e) i = ext e i := by
      intro e i hi
      unfold ext
      split_ifs with h
      · simp only [σ, Equiv.coe_fn_mk]
        rw [Function.update_of_ne]
        exact fun h' => hi (by simpa using congrArg Fin.val h')
      · rfl
    have hextL : ∀ e : Fin n → Bool, ext (σ e) (s + L) = !ext e (s + L) := by
      intro e; simp [ext, hlt, σ]
    have hQσ : ∀ e : Fin n → Bool, Q F s L (ext (σ e)) = Q F s L (ext e) := fun e =>
      Q_congr F s L fun t ht => hext e (s + t) (by omega)
    have hcount := two_mul_card σ
      (fun e => rayPrefix (x <• Q F s L (ext e)) (s + 1 + L) = w.take (s + 1 + L))
      (fun e => xor ((x <• Q F s L (ext e)) (s + 1 + L)) (ext e (s + L)) = c)
      (fun e => by simp only [hQσ])
      (fun e => by simp only [hQσ, hextL]; cases ext e (s + L) <;> cases c <;> simp)
    rw [ih] at hcount
    have htake : (w.take (s + 1 + L)).take (s + 1) = w.take (s + 1) := by
      rw [List.take_take]; congr 1; omega
    rw [htake] at hcount
    have hcard : Fintype.card {e : Fin n → Bool //
        rayPrefix (x <• Q F s (L + 1) (ext e)) (s + 1 + (L + 1)) = w} =
        Fintype.card {e : Fin n → Bool //
          rayPrefix (x <• Q F s L (ext e)) (s + 1 + L) = w.take (s + 1 + L) ∧
          xor ((x <• Q F s L (ext e)) (s + 1 + L)) (ext e (s + L)) = c} :=
      Fintype.card_congr (Equiv.subtypeEquivRight key)
    rw [hcard]
    split_ifs at hcount ⊢ with h
    · have : 2 ^ (n - L) = 2 * 2 ^ (n - (L + 1)) := by
        rw [← pow_succ']; congr 1; omega
      omega
    · omega

/-! ### One factor flips one digit -/

open GrigBasic

theorem flip_of {g : BinaryTreeAut} {m : ℕ} (hfix : ∀ u : List Bool, u.length = m → u <• g = u)
    (hsw : ∀ u : List Bool, u.length = m → rootSwap (sec g u) = true) (z : Ray) :
    rayPrefix (z <• g) m = rayPrefix z m ∧ (z <• g) m = !(z m) := by
  have h1 : rayPrefix (z <• g) m = rayPrefix z m := by
    rw [rayPrefix_smul, hfix _ (length_rayPrefix z m)]
  refine ⟨h1, ?_⟩
  have h2 : rayPrefix (z <• g) (m + 1) = rayPrefix z m ++ [!(z m)] := by
    rw [rayPrefix_smul, rayPrefix_succ', append_vertex_smul, hfix _ (length_rayPrefix z m),
      singleton_smul, hsw _ (length_rayPrefix z m)]
    simp
  rw [rayPrefix_succ', h1] at h2
  have := List.append_inj h2 rfl
  simpa using this.2

theorem flip_of_inv {g : BinaryTreeAut} {m : ℕ} (hfix : ∀ u : List Bool, u.length = m → u <• g = u)
    (hsw : ∀ u : List Bool, u.length = m → rootSwap (sec g u) = true) :
    (∀ u : List Bool, u.length = m → u <• g⁻¹ = u) ∧
      ∀ u : List Bool, u.length = m → rootSwap (sec g⁻¹ u) = true := by
  have hf : ∀ u : List Bool, u.length = m → u <• g⁻¹ = u := fun u hu => by
    conv_lhs => rw [← hfix u hu]
    exact vertex_smul_smul_inv g u
  refine ⟨hf, fun u hu => ?_⟩
  rw [sec_inv, hf u hu, rootSwap_inv]
  exact hsw u hu

section Inst

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
  (n : ℕ) (hn : D ∣ n)

include hω hk hn

theorem rootSwap_cElt (j : ℕ) (v : List Bool) : rootSwap (cElt ω j v) = false := by
  simp [cElt, rootSwap_mul, rootSwap_inv, rootSwap_gen]

/-- The sections of `γ_{i+1}` at level `i + 1` swap the root. -/
theorem rootSwap_sec_factor (p : LambdaN D ω k n) (i : Fin n) (u : List Bool)
    (hu : u.length = i + 1) : rootSwap (sec (p.2 i : BinaryTreeAut) u) = true := by
  have h := (p.2 i).2
  unfold fSet at h
  split_ifs at h with hc
  · obtain ⟨v, hv, -, e⟩ := h
    rw [e]
    have hDk : D ∣ 2 * k n := Dvd.dvd.mul_left ((hk.2 n (by omega) hn).2) 2
    rcases ((exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem D ω hω (i + 1) (by omega)
      (2 * k n) hDk v hv).2.2 (by rw [hc.1]; decide)).2 u hu with h1 | h1
    · rw [h1, rootSwap_mul, rootSwap_grigA, rootSwap_cElt D ω hω k hk n hn]; rfl
    · rw [h1, rootSwap_mul, rootSwap_grigA, rootSwap_cElt D ω hω k hk n hn]; rfl
  · rw [Set.mem_singleton_iff.mp h]
    rcases ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).1 (i + 1)
      (by omega)).2 u hu with h1 | h1
    · rw [h1]
      split_ifs <;> simp [evalWord, rootSwap_mul, rootSwap_grigA, rootSwap_gen]
    · rw [h1]
      split_ifs <;> simp [evalWord, rootSwap_mul, rootSwap_grigA, rootSwap_gen]

theorem fix_factor (p : LambdaN D ω k n) (i : Fin n) (u : List Bool) (hu : u.length = i + 1) :
    u <• (p.2 i : BinaryTreeAut) = u :=
  (Subgroup.mem_inf.mp (P3U0Dev.levelStab_factor D ω hω k hk n hn p i)).2 u hu

/-- The factor `F_i(b) = (γ_{i+1}^b)⁻¹` (inverse) or `γ_{i+1}^b`. -/
noncomputable def Fac {n : ℕ} (γ : Fin n → BinaryTreeAut) (inv : Bool) (i : ℕ) (b : Bool) :
    BinaryTreeAut :=
  if h : i < n then (if inv then ((γ ⟨i, h⟩) ^ b.toNat)⁻¹ else (γ ⟨i, h⟩) ^ b.toNat) else 1

theorem hF_fac (p : LambdaN D ω k n) (inv : Bool) (i : ℕ) (hi : i < n) (b : Bool) (z : Ray) :
    rayPrefix (z <• Fac (fun i => (p.2 i : BinaryTreeAut)) inv i b) (i + 1) =
        rayPrefix z (i + 1) ∧
      (z <• Fac (fun i => (p.2 i : BinaryTreeAut)) inv i b) (i + 1) = xor (z (i + 1)) b := by
  have hfix := fix_factor D ω hω k hk n hn p ⟨i, hi⟩
  have hsw := rootSwap_sec_factor D ω hω k hk n hn p ⟨i, hi⟩
  simp only [Fac, dif_pos hi]
  cases b
  · cases inv <;> simp [MulOpposite.op_one, one_smul]
  · cases inv
    · simp only [Bool.toNat_true, pow_one, Bool.false_eq_true, if_false, Bool.xor_true]
      exact flip_of hfix hsw z
    · simp only [Bool.toNat_true, pow_one, if_true, Bool.xor_true]
      obtain ⟨hf', hs'⟩ := flip_of_inv hfix hsw
      exact flip_of hf' hs' z

end Inst

theorem filter_range (j n : ℕ) (h : j ≤ n) :
    (List.range n).filter (fun i => decide (j ≤ i)) = (List.range (n - j)).map (j + ·) := by
  conv_lhs => rw [show n = j + (n - j) by omega, List.range_add]
  rw [List.filter_append, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr]
  · rfl
  · intro a ha; simp at ha; obtain ⟨b, -, rfl⟩ := ha; simp
  · intro a ha; simp at ha; simp; omega

theorem prod_eq_Q {n : ℕ} (γ : Fin n → BinaryTreeAut) (inv : Bool) (ε : Fin n → Bool) (j : ℕ)
    (hj : j ≤ n) :
    (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map fun i =>
      Fac γ inv i.val (ε i)).prod = Q (Fac γ inv) j (n - j) (ext ε) := by
  unfold Q
  congr 1
  have h1 : (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map fun i =>
      Fac γ inv i.val (ε i)) =
      (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map Fin.val).map
        fun i => Fac γ inv i (ext ε i) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    simp [ext, i.2]
  have h2 : (List.map Fin.val (List.filter (fun i : Fin n => decide (j ≤ i.val))
      (List.finRange n))) = (List.range n).filter (fun i => decide (j ≤ i)) := by
    rw [← List.map_coe_finRange_eq_range, List.filter_map]; rfl
  rw [h1, h2, filter_range j n hj, List.map_map]
  rfl

/-! ### Clause 1, for fixed `x` and `γ` -/

section Clause1

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
  (n : ℕ) (hn : D ∣ n)

include hω hk hn

theorem card_eps1 (γ : fProd D ω k n) (j : ℕ) (hjn : j + 1 ≤ n) (x : Ray) (w : List Bool)
    (hw : w.length = n) :
    Fintype.card {ε : Fin n → Bool // rayPrefix (x <• (((List.finRange n).filter
      fun i : Fin n => j ≤ i.val).map fun i => ((γ i : BinaryTreeAut) ^ (ε i).toNat)⁻¹).prod) n
        = w} = if rayPrefix x (j + 1) = w.take (j + 1) then 2 ^ (j + 1) else 0 := by
  classical
  set G : Fin n → BinaryTreeAut := fun i => (γ i : BinaryTreeAut)
  have hF : ∀ i, j ≤ i → i < n → ∀ b (z : Ray),
      rayPrefix (z <• Fac G true i b) (i + 1) = rayPrefix z (i + 1) ∧
        (z <• Fac G true i b) (i + 1) = xor (z (i + 1)) b := fun i _ hi b z =>
    hF_fac D ω hω k hk n hn (fun _ => false, γ) true i hi b z
  have hprod : ∀ ε : Fin n → Bool, (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
      fun i => ((γ i : BinaryTreeAut) ^ (ε i).toNat)⁻¹).prod = Q (Fac G true) j (n - j) (ext ε) := by
    intro ε
    rw [← prod_eq_Q G true ε j (by omega)]
    congr 1
    apply List.map_congr_left
    intro i _
    simp [Fac, i.2, G]
  have hlast : ∀ ε : Fin n → Bool, rayPrefix (x <• Q (Fac G true) j (n - j) (ext ε)) n =
      rayPrefix (x <• Q (Fac G true) j (n - j - 1) (ext ε)) n := by
    intro ε
    rw [show n - j = (n - j - 1) + 1 by omega, Q_succ, MulOpposite.op_mul, mul_smul]
    have := (hF (j + (n - j - 1)) (by omega) (by omega) (ext ε (j + (n - j - 1)))
      (x <• Q (Fac G true) j (n - j - 1) (ext ε))).1
    rwa [show j + (n - j - 1) + 1 = n by omega] at this
  have hc := card_forward n (Fac G true) j hF (n - j - 1) (by omega) x w (by omega)
  rw [show j + 1 + (n - j - 1) = n by omega, show n - (n - j - 1) = j + 1 by omega] at hc
  rw [← hc]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro ε
  rw [hprod, hlast]

end Clause1

/-! ### Counting `B_j` -/

theorem card_odd (m c : ℕ) :
    2 * Fintype.card {f : Fin (m + 1) → Bool // Odd (c + (List.ofFn f).count true)} = 2 ^ (m + 1) := by
  classical
  let σ : (Fin (m + 1) → Bool) ≃ (Fin (m + 1) → Bool) :=
    { toFun := fun f => Function.update f 0 (!f 0)
      invFun := fun f => Function.update f 0 (!f 0)
      left_inv := fun f => by funext i; by_cases hi : i = 0 <;> simp [hi]
      right_inv := fun f => by funext i; by_cases hi : i = 0 <;> simp [hi] }
  have hcount : ∀ f : Fin (m + 1) → Bool, (List.ofFn (σ f)).count true =
      (List.ofFn fun i : Fin m => f i.succ).count true + (if f 0 then 0 else 1) ∧
      (List.ofFn f).count true =
      (List.ofFn fun i : Fin m => f i.succ).count true + (if f 0 then 1 else 0) := by
    intro f
    have hs : ∀ i : Fin m, σ f i.succ = f i.succ := fun i => by
      simp [σ, Function.update, Fin.succ_ne_zero]
    constructor
    · rw [List.ofFn_succ, List.count_cons]
      simp only [hs]
      cases h : f 0 <;> simp [σ, h]
    · rw [List.ofFn_succ, List.count_cons]
      cases h : f 0 <;> simp [h]
  have := two_mul_card σ (fun _ => True) (fun f => Odd (c + (List.ofFn f).count true))
    (fun _ => Iff.rfl) (fun f => by
      obtain ⟨h1, h2⟩ := hcount f
      rw [h1, h2]
      cases f 0 <;> simp [← add_assoc, Nat.odd_add_one])
  simp only [true_and] at this
  rw [this, Fintype.card_subtype_true, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem rayPrefix_prepend' (p : List Bool) : rayPrefix (prepend p oneRay) p.length = p :=
  rayPrefix_prepend p oneRay

section Bj

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j : ℕ) (hj1 : 1 ≤ j) (hj : ω (j - 1) = 2)

/-- `B_j`. -/
abbrev Bset : Set Ray := {x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b}

include hω hj1 hj

theorem mem_Bset_iff (x : Ray) : x ∈ Bset ω j ↔
    ∃ p : List Bool, p.length = j + 1 ∧ Odd (j + 1 + p.count true) ∧ x = prepend p oneRay := by
  rw [show Bset ω j = _ from setOf_not_mem_letterGerms_seqG_eq D ω hω j hj1 hj]
  rfl

/-- `B_j ≃ {f : {0,1}^{j+1} odd}`. -/
noncomputable def eB : Bset ω j ≃ {f : Fin (j + 1) → Bool // Odd (j + 1 + (List.ofFn f).count true)} where
  toFun x := ⟨fun i => x.1 i, by
    obtain ⟨p, hp, hodd, hx⟩ := (mem_Bset_iff D ω hω j hj1 hj x.1).mp x.2
    have : (List.ofFn fun i : Fin (j + 1) => x.1 i) = p := by
      rw [show (List.ofFn fun i : Fin (j + 1) => x.1 i) = rayPrefix x.1 (j + 1) from rfl, hx,
        ← hp, rayPrefix_prepend']
    rw [this]; exact hodd⟩
  invFun f := ⟨prepend (List.ofFn f.1) oneRay, (mem_Bset_iff D ω hω j hj1 hj _).mpr
    ⟨List.ofFn f.1, by simp, f.2, rfl⟩⟩
  left_inv x := by
    obtain ⟨p, hp, hodd, hx⟩ := (mem_Bset_iff D ω hω j hj1 hj x.1).mp x.2
    apply Subtype.ext
    simp only
    have : (List.ofFn fun i : Fin (j + 1) => x.1 i) = p := by
      rw [show (List.ofFn fun i : Fin (j + 1) => x.1 i) = rayPrefix x.1 (j + 1) from rfl, hx,
        ← hp, rayPrefix_prepend']
    rw [this, hx]
  right_inv f := by
    apply Subtype.ext
    funext i
    show prepend (List.ofFn f.1) oneRay i = f.1 i
    unfold prepend
    rw [dif_pos (by simp [i.2])]
    simp only [List.getElem_ofFn]

theorem card_Bset [Fintype (Bset ω j)] : Fintype.card (Bset ω j) = 2 ^ j := by
  classical
  have h := card_odd j (j + 1)
  rw [Fintype.card_congr (eB D ω hω j hj1 hj)]
  rw [pow_succ] at h
  omega

theorem card_Bset_prefix [Fintype (Bset ω j)] (p : List Bool) (hp : p.length = j + 1) :
    Fintype.card {x : Bset ω j // rayPrefix x.1 (j + 1) = p} =
      if Odd (j + 1 + p.count true) then 1 else 0 := by
  classical
  split_ifs with hodd
  · rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨prepend p oneRay, (mem_Bset_iff D ω hω j hj1 hj _).mpr ⟨p, hp, hodd, rfl⟩⟩,
      by show rayPrefix (prepend p oneRay) (j + 1) = p
         have := rayPrefix_prepend' p
         rwa [hp] at this⟩, fun y => ?_⟩
    obtain ⟨q, hq, -, hy⟩ := (mem_Bset_iff D ω hω j hj1 hj y.1.1).mp y.1.2
    have hpq : q = p := by rw [← y.2, hy, ← hq, rayPrefix_prepend']
    apply Subtype.ext; apply Subtype.ext
    simp only
    rw [hy, hpq]
  · rw [Fintype.card_eq_zero_iff]
    refine ⟨fun y => hodd ?_⟩
    obtain ⟨q, hq, hq', hy⟩ := (mem_Bset_iff D ω hω j hj1 hj y.1.1).mp y.1.2
    have hpq : q = p := by rw [← y.2, hy, ← hq, rayPrefix_prepend']
    rwa [← hpq]

end Bj

/-! ### `Λ_n` is finite and non-empty -/

theorem nonempty_fSet_gen (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
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
      refine le_trans ?_ (P3P712Dev.cpl_replicate_append _ _)
      have := hc.2.1
      omega
  · exact Set.singleton_nonempty _

/-! ### Clause 1 -/

/-- The sigma decomposition of the counted set. -/
def sigmaEquiv {B F : Type*} {n : ℕ} (P : B → (Fin n → Bool) → F → Prop) :
    {q : B × ((Fin n → Bool) × F) // P q.1 q.2.1 q.2.2} ≃ Σ (x : B), Σ (γ : F), {ε // P x ε γ} where
  toFun q := ⟨q.1.1, q.1.2.2, q.1.2.1, q.2⟩
  invFun s := ⟨(s.1, (s.2.2.1, s.2.1)), s.2.2.2⟩
  left_inv q := rfl
  right_inv s := rfl

theorem clause1 (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hjn : j + k n ≤ n) (hj : ω (j - 1) = 2) :
    ∀ w : List Bool, w.length = n →
      (Nat.card {q : ↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} × LambdaN D ω k n //
          rayPrefix ((q.1 : Ray) <• (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
            fun i => ((q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat)⁻¹).prod) n = w} : ℝ) /
          Nat.card (↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} × LambdaN D ω k n) =
        if Odd (j + 1 + (w.take (j + 1)).count true) then 2 / 2 ^ n else 0 := by
  classical
  intro w hw
  have hn1 : 1 ≤ n := by omega
  have hkn := (hk.2 n hn1 hn).1
  have hjn1 : j + 1 ≤ n := by omega
  haveI : ∀ i : Fin n, Finite (fSet D ω k (i + 1) n) := fun i =>
    (P3P712Dev.finite_fSet D ω k (i + 1) n).to_subtype
  letI : Fintype (fProd D ω k n) := Fintype.ofFinite _
  letI : Fintype (Bset ω j) := Fintype.ofEquiv _ (eB D ω hω j hj1 hj).symm
  have hne : Nonempty (fProd D ω k n) :=
    ⟨fun i => ⟨_, (nonempty_fSet_gen D ω k hk n hn hn1 i).some_mem⟩⟩
  have hcF : 0 < Fintype.card (fProd D ω k n) := Fintype.card_pos
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hnum : Fintype.card {q : Bset ω j × LambdaN D ω k n //
      rayPrefix ((q.1 : Ray) <• (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
        fun i => ((q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat)⁻¹).prod) n = w} =
      Fintype.card (fProd D ω k n) * 2 ^ (j + 1) *
        (if Odd (j + 1 + (w.take (j + 1)).count true) then 1 else 0) := by
    rw [Fintype.card_congr (sigmaEquiv (fun (x : Bset ω j) (ε : Fin n → Bool) (γ : fProd D ω k n) =>
      rayPrefix ((x : Ray) <• (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
        fun i => ((γ i : Garrido.BinaryTreeAut) ^ (ε i).toNat)⁻¹).prod) n = w)),
      Fintype.card_sigma]
    simp_rw [Fintype.card_sigma]
    simp_rw [card_eps1 D ω hω k hk n hn _ j hjn1 _ w hw]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← card_Bset_prefix D ω hω j hj1 hj (w.take (j + 1)) (by simp [hw]; omega),
      Fintype.card_subtype, Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  have hden : Fintype.card (Bset ω j × LambdaN D ω k n) =
      2 ^ j * (2 ^ n * Fintype.card (fProd D ω k n)) := by
    rw [Fintype.card_prod, Fintype.card_prod, card_Bset D ω hω j hj1 hj, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  rw [hnum, hden]
  have hc : (0 : ℝ) < Fintype.card (fProd D ω k n) := by exact_mod_cast hcF
  split_ifs
  · push_cast
    field_simp
    ring
  · simp

/-! ### Backward products -/

/-- `F_{L-1}(e_{L-1}) ⋯ F_0(e_0)`. -/
def R (F : ℕ → Bool → BinaryTreeAut) (L : ℕ) (e : ℕ → Bool) : BinaryTreeAut :=
  ((List.range L).reverse.map fun t => F t (e t)).prod

theorem R_succ (F : ℕ → Bool → BinaryTreeAut) (L : ℕ) (e : ℕ → Bool) :
    R F (L + 1) e = F L (e L) * R F L e := by
  simp [R, List.range_succ, List.reverse_append]

theorem R_congr (F : ℕ → Bool → BinaryTreeAut) (L : ℕ) {e e' : ℕ → Bool}
    (h : ∀ t < L, e t = e' t) : R F L e = R F L e' := by
  unfold R
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [h t (by simpa using ht)]

theorem digit_ne_of_smul (g : BinaryTreeAut) {z₁ z₂ : Ray} {m : ℕ}
    (hp : rayPrefix z₁ m = rayPrefix z₂ m) (hd : z₁ m ≠ z₂ m) : (z₁ <• g) m ≠ (z₂ <• g) m := by
  intro h
  apply hd
  have h1 : rayPrefix (z₁ <• g) (m + 1) = rayPrefix (z₂ <• g) (m + 1) := by
    rw [rayPrefix_succ', rayPrefix_succ', h, rayPrefix_smul, rayPrefix_smul, hp]
  rw [rayPrefix_smul, rayPrefix_smul] at h1
  have h2 := congrArg (fun v => v <• g⁻¹) h1
  simp only [vertex_smul_smul_inv] at h2
  rw [rayPrefix_succ', rayPrefix_succ'] at h2
  have := List.append_inj h2 (by simp [length_rayPrefix])
  simpa using this.2

theorem bool_toggle {a a' c : Bool} (h : a ≠ a') : a = c ↔ ¬ a' = c := by
  cases a <;> cases a' <;> cases c <;> simp at h ⊢

theorem card_backward (n : ℕ) (F : ℕ → Bool → BinaryTreeAut)
    (hF : ∀ i, i < n → ∀ b (z : Ray),
      rayPrefix (z <• F i b) (i + 1) = rayPrefix z (i + 1) ∧
        (z <• F i b) (i + 1) = xor (z (i + 1)) b) :
    ∀ L, L ≤ n → ∀ (x : Ray) (w : List Bool), w.length = L + 1 →
      Fintype.card {e : Fin n → Bool // rayPrefix (x <• R F L (ext e)) (L + 1) = w} =
        if rayPrefix x 1 = w.take 1 then 2 ^ (n - L) else 0
  | 0, _, x, w, hw => by
    classical
    simp only [R, List.range_zero, List.reverse_nil, List.map_nil, List.prod_nil, zero_add]
    rw [MulOpposite.op_one, one_smul]
    have hwt : w.take 1 = w := List.take_of_length_le (by omega)
    rw [hwt]
    split_ifs with h
    · simp [h]
    · simp [h]
  | L + 1, hL, x, w, hw => by
    classical
    have ih := card_backward n F hF L (by omega) x (w.take (L + 1)) (by simp [hw])
    set c := w[L + 1]'(by omega)
    have hwsplit : w = w.take (L + 1) ++ [c] := by
      have h1 : w.take (L + 1 + 1) = w := List.take_of_length_le (by omega)
      have h2 := List.take_add_one (l := w) (i := L + 1)
      rw [h1, List.getElem?_eq_getElem (by omega), Option.toList_some] at h2
      exact h2
    have hlt : L < n := by omega
    have key : ∀ e : Fin n → Bool, rayPrefix (x <• R F (L + 1) (ext e)) (L + 1 + 1) = w ↔
        (rayPrefix (x <• R F L (ext e)) (L + 1) = w.take (L + 1) ∧
          ((x <• F L (ext e L)) <• R F L (ext e)) (L + 1) = c) := by
      intro e
      rw [R_succ, MulOpposite.op_mul, mul_smul]
      have h := hF L hlt (ext e L) x
      have hp : rayPrefix ((x <• F L (ext e L)) <• R F L (ext e)) (L + 1) =
          rayPrefix (x <• R F L (ext e)) (L + 1) := by
        rw [rayPrefix_smul (R F L (ext e)) (x <• F L (ext e L)), h.1, ← rayPrefix_smul]
      rw [rayPrefix_succ', hp]
      conv_lhs => rw [hwsplit]
      constructor
      · intro h'
        have := List.append_inj h' (by rw [length_rayPrefix, List.length_take]; omega)
        exact ⟨this.1, by simpa using this.2⟩
      · rintro ⟨h1, h2⟩; rw [h1, h2]
    let σ : (Fin n → Bool) ≃ (Fin n → Bool) :=
      { toFun := fun e => Function.update e ⟨L, hlt⟩ (!e ⟨L, hlt⟩)
        invFun := fun e => Function.update e ⟨L, hlt⟩ (!e ⟨L, hlt⟩)
        left_inv := fun e => by funext i; by_cases hi : i = ⟨L, hlt⟩ <;> simp [hi]
        right_inv := fun e => by funext i; by_cases hi : i = ⟨L, hlt⟩ <;> simp [hi] }
    have hext : ∀ e : Fin n → Bool, ∀ i, i ≠ L → ext (σ e) i = ext e i := by
      intro e i hi
      unfold ext
      split_ifs with h
      · simp only [σ, Equiv.coe_fn_mk]
        rw [Function.update_of_ne]
        exact fun h' => hi (by simpa using congrArg Fin.val h')
      · rfl
    have hextL : ∀ e : Fin n → Bool, ext (σ e) L = !ext e L := by
      intro e; simp [ext, hlt, σ]
    have hRσ : ∀ e : Fin n → Bool, R F L (ext (σ e)) = R F L (ext e) := fun e =>
      R_congr F L fun t ht => hext e t (by omega)
    have hcount := two_mul_card σ
      (fun e => rayPrefix (x <• R F L (ext e)) (L + 1) = w.take (L + 1))
      (fun e => ((x <• F L (ext e L)) <• R F L (ext e)) (L + 1) = c)
      (fun e => by simp only [hRσ])
      (fun e => by
        simp only [hRσ, hextL]
        have h1 := hF L hlt (ext e L) x
        have h2 := hF L hlt (!ext e L) x
        have hd : (x <• F L (!ext e L)) (L + 1) ≠ (x <• F L (ext e L)) (L + 1) := by
          rw [h1.2, h2.2]
          generalize x (L + 1) = d
          generalize ext e L = b
          cases d <;> cases b <;> decide
        have hne := digit_ne_of_smul (R F L (ext e)) (z₁ := x <• F L (!ext e L))
          (z₂ := x <• F L (ext e L)) (m := L + 1) (by rw [h1.1, h2.1]) hd
        exact bool_toggle hne)
    rw [ih] at hcount
    have htake : (w.take (L + 1)).take 1 = w.take 1 := by
      rw [List.take_take]; congr 1
    rw [htake] at hcount
    have hcard : Fintype.card {e : Fin n → Bool //
        rayPrefix (x <• R F (L + 1) (ext e)) (L + 1 + 1) = w} =
        Fintype.card {e : Fin n → Bool //
          rayPrefix (x <• R F L (ext e)) (L + 1) = w.take (L + 1) ∧
          ((x <• F L (ext e L)) <• R F L (ext e)) (L + 1) = c} :=
      Fintype.card_congr (Equiv.subtypeEquivRight key)
    rw [hcard]
    split_ifs at hcount ⊢ with h
    · have : 2 ^ (n - L) = 2 * 2 ^ (n - (L + 1)) := by
        rw [← pow_succ']; congr 1; omega
      omega
    · omega

/-! ### `B'_j = B_j · g_j` -/

theorem card_first (m : ℕ) (c : Bool) :
    2 * Fintype.card {f : Fin (m + 1) → Bool // f 0 = c} = 2 ^ (m + 1) := by
  classical
  let σ : (Fin (m + 1) → Bool) ≃ (Fin (m + 1) → Bool) :=
    { toFun := fun f => Function.update f 0 (!f 0)
      invFun := fun f => Function.update f 0 (!f 0)
      left_inv := fun f => by funext i; by_cases hi : i = 0 <;> simp [hi]
      right_inv := fun f => by funext i; by_cases hi : i = 0 <;> simp [hi] }
  have := two_mul_card σ (fun _ => True) (fun f => f 0 = c) (fun _ => Iff.rfl) (fun f => by
    simp only [σ, Equiv.coe_fn_mk, Function.update_self]
    cases f 0 <;> cases c <;> simp)
  simp only [true_and] at this
  rw [this, Fintype.card_subtype_true, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem card_odd_first (m c : ℕ) (b : Bool) :
    2 * Fintype.card {f : Fin (m + 2) → Bool //
      f 0 = b ∧ Odd (c + (List.ofFn f).count true)} = 2 ^ (m + 1) := by
  classical
  let σ : (Fin (m + 2) → Bool) ≃ (Fin (m + 2) → Bool) :=
    { toFun := fun f => Function.update f (Fin.last _) (!f (Fin.last _))
      invFun := fun f => Function.update f (Fin.last _) (!f (Fin.last _))
      left_inv := fun f => by funext i; by_cases hi : i = Fin.last _ <;> simp [hi]
      right_inv := fun f => by funext i; by_cases hi : i = Fin.last _ <;> simp [hi] }
  have h0 : ∀ f, σ f 0 = f 0 := fun f => by
    simp only [σ, Equiv.coe_fn_mk]
    rw [Function.update_of_ne (by intro h; exact absurd (congrArg Fin.val h) (by simp))]
  have hcount : ∀ f : Fin (m + 2) → Bool,
      (List.ofFn (σ f)).count true + (if f (Fin.last _) then 1 else 0) =
      (List.ofFn f).count true + (if f (Fin.last _) then 0 else 1) := by
    intro f
    have e1 : (fun i : Fin (m + 1) => σ f i.castSucc) = fun i => f i.castSucc := by
      funext i
      simp only [σ, Equiv.coe_fn_mk]
      rw [Function.update_of_ne (Fin.castSucc_ne_last i)]
    have e2 : σ f (Fin.last _) = !f (Fin.last _) := by simp [σ]
    rw [List.ofFn_succ' (σ f), List.ofFn_succ' f, List.concat_eq_append, List.concat_eq_append,
      List.count_append, List.count_append, e1, e2]
    generalize List.count true (List.ofFn fun i : Fin (m + 1) => f i.castSucc) = X
    cases f (Fin.last _) <;> norm_num
  have := two_mul_card σ (fun f => f 0 = b) (fun f => Odd (c + (List.ofFn f).count true))
    (fun f => by rw [h0]) (fun f => by
      have := hcount f
      cases h : f (Fin.last _)
      · simp only [h, Bool.false_eq_true, if_false, add_zero] at this
        rw [show (List.ofFn (σ f)).count true = (List.ofFn f).count true + 1 by omega,
          ← add_assoc, Nat.odd_add_one]
      · simp only [h, if_true, add_zero] at this
        rw [show (List.ofFn f).count true = (List.ofFn (σ f)).count true + 1 by omega,
          ← add_assoc, Nat.odd_add_one, not_not])
  have h2 : 2 * Fintype.card {f : Fin (m + 2) → Bool // f 0 = b} = 2 ^ (m + 2) :=
    card_first (m + 1) b
  have h3 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
  beta_reduce at this ⊢
  simp only [Fintype.card_eq_nat_card] at this h2 ⊢
  omega

theorem ray_inv_smul (y : Ray) (h : BinaryTreeAut) : (y <• h⁻¹) <• h = y := by
  simpa using GermBase.rsmul_inv_smul y h⁻¹

section Bj'

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j : ℕ) (hj1 : 1 ≤ j) (hj : ω (j - 1) = 2)

/-- `B'_j`. -/
abbrev Bset' : Set Ray := {x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b}

include hω hj1 hj

theorem seqG_mem : seqG ω j ∈ grigorchuk ω :=
  (Subgroup.mem_inf.mp ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).1 j
    hj1).1).1

theorem seqG_fix1 (z : Ray) : rayPrefix (z <• (seqG ω j)⁻¹) 1 = rayPrefix z 1 := by
  have hst := ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).1 j hj1).1
  rw [rayPrefix_smul]
  exact P3U0Dev.fix_le (inv_mem hst) hj1 _ (length_rayPrefix z 1)

/-- `B'_j ≃ B_j`, `y ↦ y·g_j⁻¹`. -/
noncomputable def eB' : Bset' ω j ≃ Bset ω j where
  toFun y := ⟨y.1 <• (seqG ω j)⁻¹, by
    refine ⟨GermBase.orbit_smul y.2.1 (inv_mem (seqG_mem D ω hω j hj1 hj)), fun h => y.2.2 ?_⟩
    have hG := P3P712Dev.goodAt_of_mem ω (seqG_mem D ω hω j hj1 hj)
      (GermBase.orbit_smul y.2.1 (inv_mem (seqG_mem D ω hω j hj1 hj))) h
    have := P3P712Dev.goodAt_inv ω hG
    rw [ray_inv_smul] at this
    exact P3P712Dev.mem_of_goodAt ω (inv_mem (seqG_mem D ω hω j hj1 hj)) y.2.1 this⟩
  invFun x := ⟨x.1 <• seqG ω j, by
    refine ⟨GermBase.orbit_smul x.2.1 (seqG_mem D ω hω j hj1 hj), fun h => x.2.2 ?_⟩
    have hG := P3P712Dev.goodAt_of_mem ω (inv_mem (seqG_mem D ω hω j hj1 hj))
      (GermBase.orbit_smul x.2.1 (seqG_mem D ω hω j hj1 hj)) h
    have := P3P712Dev.goodAt_inv ω hG
    rw [inv_inv, GermBase.rsmul_inv_smul] at this
    exact P3P712Dev.mem_of_goodAt ω (seqG_mem D ω hω j hj1 hj) x.2.1 this⟩
  left_inv y := by apply Subtype.ext; exact ray_inv_smul _ _
  right_inv x := by apply Subtype.ext; exact GermBase.rsmul_inv_smul _ _

theorem card_Bset' [Fintype (Bset' ω j)] [Fintype (Bset ω j)] : Fintype.card (Bset' ω j) = 2 ^ j := by
  rw [Fintype.card_congr (eB' D ω hω j hj1 hj), card_Bset D ω hω j hj1 hj]

theorem card_Bset'_first [Fintype (Bset' ω j)] (p : List Bool) (hp : p.length = 1) :
    Fintype.card {y : Bset' ω j // rayPrefix y.1 1 = p} = 2 ^ (j - 1) := by
  classical
  obtain ⟨c, rfl⟩ : ∃ c, p = [c] := by
    match p, hp with
    | [c], _ => exact ⟨c, rfl⟩
  have e1 : {y : Bset' ω j // rayPrefix y.1 1 = [c]} ≃
      {f : {f : Fin (j + 1) → Bool // Odd (j + 1 + (List.ofFn f).count true)} // f.1 ⟨0, by omega⟩ = c} :=
    ((eB' D ω hω j hj1 hj).trans (eB D ω hω j hj1 hj)).subtypeEquiv fun y => by
      simp only [Equiv.trans_apply, eB, eB', Equiv.coe_fn_mk]
      have := seqG_fix1 D ω hω j hj1 hj y.1
      rw [← this]
      simp [rayPrefix]
  rw [Fintype.card_congr e1]
  have e2 : {f : {f : Fin (j + 1) → Bool // Odd (j + 1 + (List.ofFn f).count true)} //
      f.1 ⟨0, by omega⟩ = c} ≃
      {f : Fin (j + 1) → Bool // f ⟨0, by omega⟩ = c ∧ Odd (j + 1 + (List.ofFn f).count true)} :=
    { toFun := fun f => ⟨f.1.1, f.2, f.1.2⟩
      invFun := fun f => ⟨⟨f.1, f.2.2⟩, f.2.1⟩
      left_inv := fun f => rfl
      right_inv := fun f => rfl }
  rw [Fintype.card_congr e2]
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have h4 : 2 * Fintype.card {f : Fin (m + 1 + 1) → Bool //
      f 0 = c ∧ Odd (m + 1 + 1 + (List.ofFn f).count true)} = 2 ^ (m + 1) :=
    card_odd_first m (m + 1 + 1) c
  simp only [Nat.add_sub_cancel]
  have h3 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have hz : (⟨0, by omega⟩ : Fin (m + 1 + 1)) = 0 := rfl
  rw [hz]
  simp only [Fintype.card_eq_nat_card] at h4 ⊢
  omega

end Bj'

theorem filter_range_lt (j n : ℕ) (h : j - 1 ≤ n) :
    (List.range n).filter (fun i => decide (i + 2 ≤ j)) = List.range (j - 1) := by
  conv_lhs => rw [show n = (j - 1) + (n - (j - 1)) by omega, List.range_add]
  rw [List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr]
  · simp
  · intro a ha; simp at ha; obtain ⟨b, -, rfl⟩ := ha; simp; omega
  · intro a ha; simp at ha; simp; omega

theorem prod_lower {n : ℕ} (γ : Fin n → BinaryTreeAut) (ε : Fin n → Bool) (j : ℕ)
    (hj : j - 1 ≤ n) :
    ((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map (fun i => Fac γ false i.val (ε i)) =
      (List.range (j - 1)).map fun t => Fac γ false t (ext ε t) := by
  have h1 : (((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map fun i =>
      Fac γ false i.val (ε i)) =
      (((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map Fin.val).map
        fun i => Fac γ false i (ext ε i) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    simp [ext, i.2]
  have h2 : (List.map Fin.val (List.filter (fun i : Fin n => decide (i.val + 2 ≤ j))
      (List.finRange n))) = (List.range n).filter (fun i => decide (i + 2 ≤ j)) := by
    rw [← List.map_coe_finRange_eq_range, List.filter_map]; rfl
  rw [h1, h2, filter_range_lt j n hj]

/-! ### Clauses 2 and 3, for fixed `y` and `γ` -/

theorem Q_zero (F : ℕ → Bool → BinaryTreeAut) (L : ℕ) (e : ℕ → Bool) :
    Q F 0 L e = ((List.range L).map fun t => F t (e t)).prod := by
  simp [Q]


section Clause23

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
  (n : ℕ) (hn : D ∣ n)

include hω hk hn

theorem card_eps2 (γ : fProd D ω k n) (j : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n) (y : Ray)
    (w : List Bool) (hw : w.length = j - 1) :
    Fintype.card {ε : Fin n → Bool // rayPrefix (y <• (((List.finRange n).filter
      fun i : Fin n => i.val + 2 ≤ j).map fun i => (γ i : BinaryTreeAut) ^ (ε i).toNat).prod)
        (j - 1) = w} = if rayPrefix y 1 = w.take 1 then 2 ^ (n - (j - 2)) else 0 := by
  classical
  set G : Fin n → BinaryTreeAut := fun i => (γ i : BinaryTreeAut)
  have hF : ∀ i, 0 ≤ i → i < n → ∀ b (z : Ray),
      rayPrefix (z <• Fac G false i b) (i + 1) = rayPrefix z (i + 1) ∧
        (z <• Fac G false i b) (i + 1) = xor (z (i + 1)) b := fun i _ hi b z =>
    hF_fac D ω hω k hk n hn (fun _ => false, γ) false i hi b z
  have hprod : ∀ ε : Fin n → Bool, (((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map
      fun i => (γ i : BinaryTreeAut) ^ (ε i).toNat).prod = Q (Fac G false) 0 (j - 1) (ext ε) := by
    intro ε
    rw [Q_zero, ← prod_lower G ε j (by omega)]
    congr 1
    apply List.map_congr_left
    intro i _
    simp [Fac, i.2, G]
  have hlast : ∀ ε : Fin n → Bool, rayPrefix (y <• Q (Fac G false) 0 (j - 1) (ext ε)) (j - 1) =
      rayPrefix (y <• Q (Fac G false) 0 (j - 2) (ext ε)) (j - 1) := by
    intro ε
    rw [show j - 1 = (j - 2) + 1 by omega, Q_succ, MulOpposite.op_mul, mul_smul]
    have := (hF (0 + (j - 2)) (by omega) (by omega) (ext ε (0 + (j - 2)))
      (y <• Q (Fac G false) 0 (j - 2) (ext ε))).1
    simp only [zero_add] at this ⊢
    exact this
  have hc := card_forward n (Fac G false) 0 hF (j - 2) (by omega) y w (by omega)
  rw [show 0 + 1 + (j - 2) = j - 1 by omega, zero_add] at hc
  rw [← hc]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro ε
  rw [hprod, hlast]

theorem card_eps3 (γ : fProd D ω k n) (j : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n) (y : Ray)
    (w : List Bool) (hw : w.length = j - 1) :
    Fintype.card {ε : Fin n → Bool // rayPrefix (y <• ((((List.finRange n).filter
      fun i : Fin n => i.val + 2 ≤ j).map fun i => (γ i : BinaryTreeAut) ^ (ε i).toNat).reverse).prod)
        (j - 1) = w} = if rayPrefix y 1 = w.take 1 then 2 ^ (n - (j - 2)) else 0 := by
  classical
  set G : Fin n → BinaryTreeAut := fun i => (γ i : BinaryTreeAut)
  have hF : ∀ i, i < n → ∀ b (z : Ray),
      rayPrefix (z <• Fac G false i b) (i + 1) = rayPrefix z (i + 1) ∧
        (z <• Fac G false i b) (i + 1) = xor (z (i + 1)) b := fun i hi b z =>
    hF_fac D ω hω k hk n hn (fun _ => false, γ) false i hi b z
  have hprod : ∀ ε : Fin n → Bool, ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map
      fun i => (γ i : BinaryTreeAut) ^ (ε i).toNat).reverse).prod = R (Fac G false) (j - 1) (ext ε) := by
    intro ε
    unfold R
    rw [List.map_reverse, ← prod_lower G ε j (by omega)]
    congr 2
    apply List.map_congr_left
    intro i _
    simp [Fac, i.2, G]
  have hlast : ∀ ε : Fin n → Bool, rayPrefix (y <• R (Fac G false) (j - 1) (ext ε)) (j - 1) =
      rayPrefix (y <• R (Fac G false) (j - 2) (ext ε)) (j - 1) := by
    intro ε
    rw [show j - 1 = (j - 2) + 1 by omega, R_succ, MulOpposite.op_mul, mul_smul,
      rayPrefix_smul (R (Fac G false) (j - 2) (ext ε)),
      (hF (j - 2) (by omega) (ext ε (j - 2)) y).1, ← rayPrefix_smul]
  have hc := card_backward n (Fac G false) hF (j - 2) (by omega) y w (by omega)
  rw [show j - 2 + 1 = j - 1 by omega] at hc
  rw [← hc]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro ε
  rw [hprod, hlast]

end Clause23

/-! ### Assembly -/

theorem ratio23 (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hjn : j + k n ≤ n) (hj : ω (j - 1) = 2) (w : List Bool)
    (P : Bset' ω j → (Fin n → Bool) → fProd D ω k n → Prop) [∀ y ε γ, Decidable (P y ε γ)]
    [Fintype (Bset' ω j)] [Fintype (Bset ω j)] [Fintype (fProd D ω k n)]
    (hP : ∀ y γ, Fintype.card {ε // P y ε γ} =
      if j = 1 then 2 ^ n else if rayPrefix y.1 1 = w.take 1 then 2 ^ (n - (j - 2)) else 0)
    (hw1 : w.take 1 = w.take 1 ∧ (2 ≤ j → (w.take 1).length = 1)) :
    (Nat.card {q : Bset' ω j × LambdaN D ω k n // P q.1 q.2.1 q.2.2} : ℝ) /
      Nat.card (Bset' ω j × LambdaN D ω k n) = 1 / 2 ^ (j - 1) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hne : Nonempty (fProd D ω k n) :=
    ⟨fun i => ⟨_, (nonempty_fSet_gen D ω k hk n hn hn1 i).some_mem⟩⟩
  have hcF : 0 < Fintype.card (fProd D ω k n) := Fintype.card_pos
  have hcB := card_Bset' D ω hω j hj1 hj
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_congr (sigmaEquiv P), Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, hP]
  rw [Fintype.card_prod, Fintype.card_prod, hcB, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  have hc : (0 : ℝ) < Fintype.card (fProd D ω k n) := by exact_mod_cast hcF
  by_cases h1 : j = 1
  · subst h1
    simp only [if_true, Finset.sum_const, Finset.card_univ, smul_eq_mul, hcB]
    push_cast
    field_simp
  · simp only [h1, if_false, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have hsum : (∑ x : Bset' ω j, Fintype.card (fProd D ω k n) *
        if rayPrefix x.1 1 = w.take 1 then 2 ^ (n - (j - 2)) else 0) =
        Fintype.card (fProd D ω k n) * 2 ^ (n - (j - 2)) * 2 ^ (j - 1) := by
      rw [← card_Bset'_first D ω hω j hj1 hj (w.take 1) (hw1.2 (by omega)),
        Fintype.card_subtype, Finset.card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> ring
    rw [hsum]
    have e : 2 ^ (n - (j - 2)) * 2 ^ (j - 1) * 2 ^ (j - 1) = 2 ^ j * 2 ^ n := by
      rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
    have e' : (2 : ℝ) ^ (n - (j - 2)) * 2 ^ (j - 1) * 2 ^ (j - 1) = 2 ^ j * 2 ^ n := by
      exact_mod_cast e
    push_cast
    field_simp
    nlinarith [e']

end P3G8Dev

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open ErschlerZheng
open P3G8Dev in
theorem solution (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hjn : j + k n ≤ n) (hj : ω (j - 1) = 2) :
    (({x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} : Set Ray).Finite ∧
      ({x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} : Set Ray).Nonempty ∧
      ({x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} : Set Ray).Finite ∧
      ({x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} : Set Ray).Nonempty ∧
      Finite (LambdaN D ω k n) ∧ Nonempty (LambdaN D ω k n)) ∧
    (∀ w : List Bool, w.length = n →
      (Nat.card {q : ↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} × LambdaN D ω k n //
          rayPrefix ((q.1 : Ray) <• (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
            fun i => ((q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat)⁻¹).prod) n = w} : ℝ) /
          Nat.card (↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} × LambdaN D ω k n) =
        if Odd (j + 1 + (w.take (j + 1)).count true) then 2 / 2 ^ n else 0) ∧
    (∀ w : List Bool, w.length = j - 1 →
      (Nat.card
          {q : ↥{x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} × LambdaN D ω k n //
            rayPrefix ((q.1 : Ray) <• (((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map
              fun i => (q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat).prod) (j - 1) = w} :
          ℝ) /
          Nat.card
            (↥{x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} × LambdaN D ω k n) =
        1 / 2 ^ (j - 1)) ∧
    ∀ w : List Bool, w.length = j - 1 →
      (Nat.card
          {q : ↥{x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} × LambdaN D ω k n //
            rayPrefix ((q.1 : Ray) <• ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map
              fun i => (q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat).reverse).prod) (j - 1) = w} :
          ℝ) /
          Nat.card
            (↥{x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} × LambdaN D ω k n) =
        1 / 2 ^ (j - 1) := by
  classical
  have hn1 : 1 ≤ n := by omega
  haveI : ∀ i : Fin n, Finite (fSet D ω k (i + 1) n) := fun i =>
    (P3P712Dev.finite_fSet D ω k (i + 1) n).to_subtype
  letI : Fintype (fProd D ω k n) := Fintype.ofFinite _
  letI : Fintype (Bset ω j) := Fintype.ofEquiv _ (eB D ω hω j hj1 hj).symm
  letI : Fintype (Bset' ω j) := Fintype.ofEquiv _ (eB' D ω hω j hj1 hj).symm
  refine ⟨⟨Set.toFinite _, ?_, Set.toFinite _, ?_, inferInstance, ?_⟩,
    clause1 D ω hω k hk n hn j hj1 hjn hj, fun w hw => ?_, fun w hw => ?_⟩
  -- `B_j`, `B'_j` and `Λ_n` are finite and non-empty
  · exact Set.nonempty_coe_sort.mp
      (Fintype.card_pos_iff.mp (by rw [card_Bset D ω hω j hj1 hj]; positivity))
  · exact Set.nonempty_coe_sort.mp
      (Fintype.card_pos_iff.mp (by rw [card_Bset' D ω hω j hj1 hj]; positivity))
  · exact ⟨(fun _ => false, fun i => ⟨_, (nonempty_fSet_gen D ω k hk n hn hn1 i).some_mem⟩)⟩
  · exact ratio23 D ω hω k hk n hn j hj1 hjn hj w
      (fun y ε γ => rayPrefix ((y : Ray) <• (((List.finRange n).filter
        fun i : Fin n => i.val + 2 ≤ j).map fun i => (γ i : Garrido.BinaryTreeAut) ^
          (ε i).toNat).prod) (j - 1) = w)
      (fun y γ => by
        by_cases h1 : j = 1
        · subst h1
          rw [if_pos rfl]
          have : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
          subst this
          simp [rayPrefix]
        · rw [if_neg h1]
          exact card_eps2 D ω hω k hk n hn γ j (by omega) (by omega) y.1 w hw)
      ⟨rfl, fun h => by simp; omega⟩
  · exact ratio23 D ω hω k hk n hn j hj1 hjn hj w
      (fun y ε γ => rayPrefix ((y : Ray) <• ((((List.finRange n).filter
        fun i : Fin n => i.val + 2 ≤ j).map fun i => (γ i : Garrido.BinaryTreeAut) ^
          (ε i).toNat).reverse).prod) (j - 1) = w)
      (fun y γ => by
        by_cases h1 : j = 1
        · subst h1
          rw [if_pos rfl]
          have : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
          subst this
          simp [rayPrefix]
        · rw [if_neg h1]
          exact card_eps3 D ω hω k hk n hn γ j (by omega) (by omega) y.1 w hw)
      ⟨rfl, fun h => by simp; omega⟩
end
