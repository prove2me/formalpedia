-- Prove2me | solution 1 for ErschlerZheng.not_forall_germConfig_mem_isotropy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.792869+00:00
-- url     : https://prove2.me/submissions/79e9019f-6768-40a2-be1f-318b56156ced

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

theorem rayPrefix_prepend (u : List Bool) (x : Ray) :
    rayPrefix (prepend u x) u.length = u := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    simp [prepend, h2]

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

theorem germ_eq_one_of_isotropy {L : Subgroup H} {x : X} (hiso : isotropy L x = ⊥) {τ : H}
    (hτ : τ ∈ L) (hx : x <• τ = x) : germ x τ = 1 := by
  rw [germ_def hx]
  have hmem : (⟨τ, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top τ, hx⟩⟩ : pointStab (⊤ : Subgroup H) x)
      ∈ (pointStab L x).subgroupOf (pointStab ⊤ x) := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨hτ, hx⟩
  have := Subgroup.mem_map_of_mem (QuotientGroup.mk' (trivialNear (H := H) x)) hmem
  unfold isotropy at hiso
  rw [hiso, Subgroup.mem_bot] at this
  exact this

theorem conj_germEq {o x : X} {σ h h' : H} (hσ : o <• σ = x) (e : GermEq x h h') :
    GermEq o (σ * h * σ⁻¹) (σ * h' * σ⁻¹) := by
  have e1 : GermEq o (σ * h) (σ * h') := germEq_comp (germEq_refl o σ) (by rw [hσ]; exact e)
  exact germEq_comp e1 (germEq_refl _ _)

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

theorem mem_GL_of_G {ω : ℕ → Fin 3} {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) :
    g ∈ grigorchuk ω ⊔ finitary := (le_sup_left : grigorchuk ω ≤ _) hg

/-! ### Eventual sections -/

end GrigGermsDev

end ErschlerZheng
end

section
/-!
# B6F: Fact 3.5's printed `Φ_g(x) ∈ 𝒢_x` fails (p. 19)

Witness: `G = L_fin` (finitary automorphisms; every germ trivial, so `𝒢_x = {1}`) and
`L = b L_fin b⁻¹` with `b = b_ω` for the constant string `ω = 0^∞`. `L` has the cofinality classes
as orbits (`b` changes at most one digit) and trivial isotropy (a conjugate of a finitary element
fixing a point is trivial near it). For `g = a`, `x = 1^∞` and any `σ = b f b⁻¹ ∈ L` with
`1^∞·σ = 1^∞·a`: if `aσ⁻¹` had trivial germ at `1^∞`, then `a b f⁻¹ = aσ⁻¹ b` would have the germ
of `b` at `1^∞`, so their deep sections along `1^∞` would agree; but the sections of `a b f⁻¹` at
`1^n` are trivial for large `n`, while those of `b` are `b_{𝔰ⁿω} ≠ 1`.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace P3B6FDev

open GrigBasic RayBasic SchreierDev GermBase GrigGermsDev

/-- The constant string `0^∞`. -/
def ω₀ : ℕ → Fin 3 := fun _ => 0

/-- `b_{0^∞}`. -/
def bb : BinaryTreeAut := gen ω₀ .b

/-- `L = b L_fin b⁻¹`. -/
def LL : Subgroup BinaryTreeAut := Subgroup.map (MulAut.conj bb).toMonoidHom finitary

theorem mem_LL {k : BinaryTreeAut} : k ∈ LL ↔ ∃ f ∈ finitary, bb * f * bb⁻¹ = k := by
  simp [LL, Subgroup.mem_map, MulAut.conj_apply]

theorem bb_mem : bb ∈ grigorchuk ω₀ ⊔ finitary :=
  mem_GL_of_G (Subgroup.subset_closure (by simp [gens, bb]))

theorem bb_inv : bb⁻¹ = bb := gen_inv ω₀ .b

theorem cof_bb (x : Ray) : Cof x (x <• bb) := cof_smul_GL ω₀ bb_mem x

theorem orbit_fin (x : Ray) :
    rightOrbit finitary x = {y : Ray | ∀ᶠ n in Filter.atTop, y n = x n} :=
  (isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary.2.1 ω₀ x).2

theorem isotropy_fin (x : Ray) : isotropy finitary x = ⊥ :=
  (isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary.2.2 ω₀).2 x

theorem cof_fin {f : BinaryTreeAut} (hf : f ∈ finitary) (x : Ray) : Cof x (x <• f) := by
  have : x <• f ∈ rightOrbit finitary x := ⟨f, hf, rfl⟩
  rw [orbit_fin] at this
  exact this

theorem rightOrbit_LL (x : Ray) : rightOrbit LL x = rightOrbit finitary x := by
  rw [orbit_fin]
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨f, hf, rfl⟩ := mem_LL.mp hk
    rw [bb_inv]
    show Cof x _
    rw [rsmul_mul, rsmul_mul]
    exact cof_trans (cof_trans (cof_bb x) (cof_fin hf _)) (cof_bb _)
  · intro hy
    change Cof x y at hy
    have h1 : Cof (x <• bb) (y <• bb) :=
      cof_trans (cof_trans (cof_symm (cof_bb x)) hy) (cof_bb y)
    have h2 : y <• bb ∈ rightOrbit finitary (x <• bb) := by rw [orbit_fin]; exact h1
    obtain ⟨f, hf, e⟩ := h2
    refine ⟨bb * f * bb⁻¹, mem_LL.mpr ⟨f, hf, rfl⟩, ?_⟩
    rw [rsmul_mul, rsmul_mul, ← e, rsmul_inv_smul]

theorem isotropy_LL (x : Ray) : isotropy LL x = ⊥ := by
  unfold isotropy
  rw [Subgroup.map_eq_bot_iff]
  intro h hh
  rw [Subgroup.mem_subgroupOf] at hh
  obtain ⟨hL, hx⟩ := Subgroup.mem_inf.mp hh
  rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  show GermEq x (h : BinaryTreeAut) 1
  change x <• (h : BinaryTreeAut) = x at hx
  obtain ⟨f, hf, hfk⟩ := mem_LL.mp hL
  rw [← hfk] at hx ⊢
  have hfix : (x <• bb) <• f = x <• bb := by
    have := congrArg (fun z => z <• bb) hx
    simp only [rsmul_mul] at this
    rwa [← rsmul_mul _ bb⁻¹ bb, inv_mul_cancel, rsmul_one] at this
  have hg : germ (x <• bb) f = 1 := germ_eq_one_of_isotropy (isotropy_fin _) hf hfix
  rw [← germ_one (x <• bb), germ_eq_iff hfix (rsmul_one _)] at hg
  have := conj_germEq (H := BinaryTreeAut) (X := Ray) (o := x) (σ := bb)
    (rfl : x <• bb = x <• bb) hg
  simpa using this

theorem isAuxiliary_LL : IsAuxiliary (X := Ray) finitary LL :=
  ⟨rightOrbit_LL, isotropy_LL⟩

theorem grigA_mem_finitary : grigA ∈ finitary := by
  refine ⟨1, fun v hv => ?_⟩
  obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hv
  exact sec_grigA y

theorem gen_b_ne_one (ω : ℕ → Fin 3) (h0 : ω 0 = 0) : gen ω .b ≠ 1 := by
  intro e
  have : [false, false] <• gen ω .b = [false, false] <• (1 : BinaryTreeAut) := by rw [e]
  rw [vertex_smul_gen, MulOpposite.op_one, one_smul] at this
  have h2 : genFun ω .b [false, false] = [false, true] := by
    simp [genFun, letterValue, h0, BCD.killedBy]
    rfl
  rw [h2] at this
  simp at this

/-- The sections of `a b f⁻¹` along `1^∞` are trivial from level `M + 2` on, where `f⁻¹` has
trivial sections at level `M`. -/
theorem sec_a_b_f {f : BinaryTreeAut} {M : ℕ} (hM : ∀ v : List Bool, v.length = M → sec f v = 1)
    (n : ℕ) (hn : M + 2 ≤ n) : sec (grigA * bb * f) (List.replicate n true) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hlen : (List.replicate (k + 2) true <• (grigA * bb)).length = k + 2 := by
    rw [length_vertex_smul]; simp
  rw [sec_mul, sec_eq_one_of_le f (by omega : M ≤ k + 2) hM _ hlen, mul_one, sec_mul]
  rw [List.replicate_succ, sec_grigA_cons, one_mul, cons_smul, rootSwap_grigA, sec_grigA,
    MulOpposite.op_one, one_smul]
  simp only [Bool.xor_self]
  rw [sec_cons, bb, sec_gen_false]
  have hl : letterElt (ω₀ 0) .b = grigA := by
    simp [letterElt, letterValue, ω₀, BCD.killedBy]
  rw [hl, List.replicate_succ, sec_grigA_cons]

theorem germConfig_ne_one :
    germConfig LL grigA oneRay ≠ 1 := by
  intro hc
  have hex := exists_L_of_mem isAuxiliary_LL oneRay grigA_mem_finitary
  obtain ⟨hσL, hσ⟩ := transport_spec hex
  set σ := transport LL oneRay (oneRay <• grigA) with hσdef
  obtain ⟨f, hf, hfσ⟩ := mem_LL.mp hσL
  have hτ : oneRay <• (grigA * σ⁻¹) = oneRay := by
    rw [rsmul_mul, ← hσ, rsmul_inv_smul]
  unfold germConfig at hc
  rw [← hσdef, ← germ_one oneRay, germ_eq_iff hτ (rsmul_one _)] at hc
  have e1 : GermEq oneRay (grigA * σ⁻¹ * bb) (1 * bb) :=
    germEq_comp hc (by rw [hτ]; exact germEq_refl _ _)
  have hk : grigA * σ⁻¹ * bb = grigA * bb * f⁻¹ := by
    rw [← hfσ]
    group
  rw [hk, one_mul] at e1
  obtain ⟨N, hN⟩ := sec_eq_of_germEq e1
  obtain ⟨M, hM⟩ := finitary.inv_mem hf
  have h := (hN (N + M + 2) (by omega)).2
  rw [rayPrefix_oneRay, sec_a_b_f hM _ (by omega), bb, sec_gen_replicate_true] at h
  exact gen_b_ne_one _ rfl h.symm

end P3B6FDev

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
set_option linter.unusedSimpArgs false
open ErschlerZheng
open P3B6FDev in
theorem solution :
    ¬ ∀ G L : Subgroup Garrido.BinaryTreeAut, IsAuxiliary (X := Ray) G L →
      ∀ g ∈ G, ∀ x ∈ rightOrbit (X := Ray) G oneRay, germConfig L g x ∈ isotropy G x := by
  intro H
  have hmem := H finitary LL isAuxiliary_LL grigA grigA_mem_finitary oneRay
    ⟨1, finitary.one_mem, (one_smul _ _).symm⟩
  rw [isotropy_fin, Subgroup.mem_bot] at hmem
  exact germConfig_ne_one hmem
end
