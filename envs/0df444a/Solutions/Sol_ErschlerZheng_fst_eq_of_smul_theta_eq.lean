-- Prove2me | solution 1 for ErschlerZheng.fst_eq_of_smul_theta_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T06:04:11.200901+00:00
-- url     : https://prove2.me/submissions/5aca51ac-f9ca-492c-b97a-346483941fb3

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_vertex_smul_eq_smul_seqG_of_mem_fSet
import Theorems.Thm_ErschlerZheng_seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms

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
open scoped RightActions
open Garrido
open ErschlerZheng
open ErschlerZheng.ConstrLemma715
open GrigBasic
theorem solution (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (x : List Bool) (hx : x.length = n + D + 1)
    (p q : LambdaN D ω k n) (h : x <• theta D ω k n p = x <• theta D ω k n q) :
    p.1 = q.1 := by
  -- each `γ_i` acts as `g_i` on level `n + D + 1`
  have hact : ∀ (i : Fin n) (γ : fSet D ω k (i + 1) n) (w : List Bool), w.length = n + D + 1 →
      w <• (γ : BinaryTreeAut) = w <• seqG ω (i + 1) := by
    intro i γ w hw
    by_cases hc : ω (i + 1 - 1) = 2 ∧ n < i + 1 + k n ∧ i + 1 ≤ n
    · exact vertex_smul_eq_smul_seqG_of_mem_fSet D ω hω k hk n hn (i + 1) (by omega) hc.1 hc.2.1
        hc.2.2 γ γ.2 w hw
    · obtain ⟨g, hg⟩ := γ
      unfold fSet at hg
      rw [if_neg hc] at hg
      show w <• g = _
      rw [Set.mem_singleton_iff.mp hg]
  have hθ : ∀ r : LambdaN D ω k n, ∀ z : List Bool, z.length = n + D + 1 →
      z <• theta D ω k n r = z <• (facs (seqG ω) 0 (List.ofFn r.1)).reverse.prod := by
    intro r z hz
    unfold theta
    rw [← ofFn_eq_facs (seqG ω) n 0 r.1, ← ofFn_rev]
    apply prod_smul_eq (n + D + 1) _ _ (by simp) _ z hz
    intro i h1 h2 w hw
    simp only [List.getElem_ofFn]
    cases r.1 (Fin.rev ⟨i, by simpa using h1⟩)
    · simp
    · simp only [Bool.toNat_true, pow_one, Nat.zero_add]
      exact hact _ _ w hw
  rw [hθ p x hx, hθ q x hx] at h
  have := facs_inj (seqG ω) (flips_seqG D ω hω) (List.ofFn p.1) (List.ofFn q.1) 0 (by simp) x
    (by simp; omega) h
  exact List.ofFn_injective this
end
