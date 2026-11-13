-- Prove2me | solution 1 for DerandSq.corollary_4_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:43:06.716407+00:00
-- url     : https://prove2.me/submissions/09a1c463-1415-4687-9ae4-1297ed5c0125

import Mathlib
import Definitions.Def_DerandSq_closedWalks
import Definitions.Def_DerandSq_mGen
import Definitions.Def_DerandSq_dsTree
import Definitions.Def_DerandSq_prunedX
import Definitions.Def_DerandSq_IsVertexTransitive
import Definitions.Def_DerandSq_LambdaH
import Definitions.Def_DerandSq_QH
import Theorems.Thm_DerandSq_proposition_4_6
import Theorems.Thm_DerandSq_theorem_4_7

section
set_option autoImplicit false
namespace DerandSq.Dev.C48a
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem append_left_cancel {u v w : V} (P : G.Walk u v) (q q' : G.Walk v w)
    (h : P.append q = P.append q') : q = q' := by
  induction P with
  | nil => simpa using h
  | cons hh p ih =>
    simp only [Walk.cons_append, Walk.cons.injEq, heq_eq_eq, true_and] at h
    exact ih _ _ h

theorem append_right_cancel {u v w : V} (P : G.Walk v w) (q q' : G.Walk u v)
    (h : q.append P = q'.append P) : q = q' := by
  have := congrArg Walk.reverse h
  simp only [Walk.reverse_append] at this
  have := append_left_cancel _ _ _ this
  simpa using congrArg Walk.reverse this

theorem append_inj_len {u v w : V} (p p' : G.Walk u v) (q q' : G.Walk v w)
    (hl : p.length = p'.length) (h : p.append q = p'.append q') : p = p' ∧ q = q' := by
  induction p with
  | nil =>
    cases p' with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons _ _ => simp at hl
  | cons hh p ih =>
    cases p' with
    | nil => simp at hl
    | cons hh' p' =>
      simp only [Walk.cons_append, Walk.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have h3 := eq_of_heq h2
      have := ih p' q q' (by simpa using hl) h3
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨rfl, rfl⟩

/-- closed-walk counts -/
theorem cw_mul (hfin : ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n})
    (v : V) (a b : ℕ) :
    closedWalks G v a * closedWalks G v b ≤ closedWalks G v (a + b) := by
  unfold closedWalks
  rw [← Nat.card_prod]
  have := hfin v v (a + b)
  refine Nat.card_le_card_of_injective
    (fun x : {w : G.Walk v v // w.length = a} × {w : G.Walk v v // w.length = b} =>
      (⟨x.1.1.append x.2.1, by simp [x.1.2, x.2.2]⟩ : {w : G.Walk v v // w.length = a + b})) ?_
  rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ h
  have h1 : p.append q = p'.append q' := congrArg Subtype.val h
  obtain ⟨rfl, rfl⟩ := append_inj_len p p' q q' (by rw [hp, hp']) h1
  rfl

theorem cw_zero (v : V) : closedWalks G v 0 = 1 := by
  unfold closedWalks
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨Walk.nil, rfl⟩⟩⟩
  have ha := Walk.eq_nil_iff_nil.2 (Walk.length_eq_zero_iff.1 a.2)
  have hb := Walk.eq_nil_iff_nil.2 (Walk.length_eq_zero_iff.1 b.2)
  rw [ha, hb]

theorem cw_pow (hfin : ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n})
    (v : V) (n q : ℕ) : closedWalks G v n ^ q ≤ closedWalks G v (n * q) := by
  induction q with
  | zero => simp [cw_zero]
  | succ q ih =>
    calc closedWalks G v n ^ (q + 1) = closedWalks G v n ^ q * closedWalks G v n := pow_succ _ _
      _ ≤ closedWalks G v (n * q) * closedWalks G v n := Nat.mul_le_mul_right _ ih
      _ ≤ closedWalks G v (n * q + n) := cw_mul hfin v _ _
      _ = closedWalks G v (n * (q + 1)) := by rw [Nat.mul_succ]

theorem cw_conj (hfin : ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n})
    {u v : V} (P : G.Walk u v) (n : ℕ) :
    closedWalks G v n ≤ closedWalks G u (n + 2 * P.length) := by
  unfold closedWalks
  have := hfin u u (n + 2 * P.length)
  refine Nat.card_le_card_of_injective
    (fun x : {w : G.Walk v v // w.length = n} =>
      (⟨(P.append x.1).append P.reverse, by simp [x.2]; omega⟩ :
        {w : G.Walk u u // w.length = n + 2 * P.length})) ?_
  rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
  have h1 : (P.append w).append P.reverse = (P.append w').append P.reverse := congrArg Subtype.val h
  have h2 := append_right_cancel _ _ _ h1
  have := append_left_cancel _ _ _ h2
  subst this
  rfl

theorem fin_of_hom {V' : Type*} {G' : SimpleGraph V'} (f : G →g G') (hf : Function.Injective f)
    (hfin : ∀ (u y : V') (n : ℕ), Finite {w : G'.Walk u y // w.length = n}) :
    ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n} := by
  intro u y n
  have := hfin (f u) (f y) n
  exact Finite.of_injective
    (fun w : {w : G.Walk u y // w.length = n} =>
      (⟨w.1.map f, by simp [w.2]⟩ : {w : G'.Walk (f u) (f y) // w.length = n}))
    (by
      rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
      have := Walk.map_injective_of_injective hf u y (congrArg Subtype.val h)
      exact Subtype.ext this)

theorem cw_le_of_hom {V' : Type*} {G' : SimpleGraph V'} (f : G →g G')
    (hf : Function.Injective f)
    (hfin : ∀ (u y : V') (n : ℕ), Finite {w : G'.Walk u y // w.length = n})
    (u : V) (n : ℕ) : closedWalks G u n ≤ closedWalks G' (f u) n := by
  unfold closedWalks
  have := hfin (f u) (f u) n
  refine Nat.card_le_card_of_injective
    (fun w : {w : G.Walk u u // w.length = n} =>
      (⟨w.1.map f, by simp [w.2]⟩ : {w : G'.Walk (f u) (f u) // w.length = n})) ?_
  rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
  have := Walk.map_injective_of_injective hf u u (congrArg Subtype.val h)
  exact Subtype.ext this

end DerandSq.Dev.C48a
end

section
set_option autoImplicit false
namespace DerandSq.Dev.C48b
open DerandSq

/-- a homomorphism out of `Z₂` picking an involution -/
def invHom {G : Type*} [Group G] (s : G) (hs : s * s = 1) : Multiplicative (ZMod 2) →* G where
  toFun x := if x = 1 then 1 else s
  map_one' := by simp
  map_mul' x y := by
    have hx : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
    rcases hx x with rfl | rfl <;> rcases hx y with rfl | rfl
    · simp
    · simp
    · simp
    · have : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
      have h1 : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
      simp [this, h1, hs]

theorem invHom_gen {G : Type*} [Group G] (s : G) (hs : s * s = 1) :
    invHom s hs (Multiplicative.ofAdd 1) = s := by
  have h1 : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  simp [invHom, h1]

def ineg : ℤ ≃ᵢ ℤ := ⟨Equiv.neg ℤ, Isometry.of_dist_eq fun x y => by
  simp [Int.dist_eq]⟩

def ishift : ℤ ≃ᵢ ℤ := ⟨Equiv.subLeft (1 : ℤ), Isometry.of_dist_eq fun x y => by
  simp [Int.dist_eq]; rw [← abs_neg]; ring_nf⟩

theorem ineg_apply (x : ℤ) : ineg x = -x := rfl
theorem ishift_apply (x : ℤ) : ishift x = 1 - x := rfl

variable {d : ℕ}

def rho (a b : Fin d) (i : Fin d) : ℤ ≃ᵢ ℤ := if i = a then ineg else if i = b then ishift else 1

theorem rho_sq (a b : Fin d) (i : Fin d) : rho a b i * rho a b i = 1 := by
  unfold rho
  split_ifs
  · ext x; simp [ineg_apply]
  · ext x; simp [ishift_apply]
  · simp

noncomputable def Phi (a b : Fin d) : Gam d →* (ℤ ≃ᵢ ℤ) :=
  Monoid.CoprodI.lift (fun i => invHom (rho a b i) (rho_sq a b i))

theorem Phi_mGen (a b i : Fin d) : Phi a b (mGen i) = rho a b i := by
  unfold Phi mGen
  rw [Monoid.CoprodI.lift_of]
  exact invHom_gen _ _

noncomputable def F (a b : Fin d) (g : Gam d) : ℤ := Phi a b g 0

theorem rho_zero (a b i : Fin d) : rho a b i 0 = 0 ∨ rho a b i 0 = 1 := by
  unfold rho; split_ifs <;> simp [ineg_apply, ishift_apply]

theorem rho_small (a b i : Fin d) (x : ℤ) (hx : x = 0 ∨ x = 1) : |rho a b i x| ≤ 1 := by
  unfold rho; split_ifs <;> rcases hx with rfl | rfl <;> simp [ineg_apply, ishift_apply]

theorem rho_01 (a b i : Fin d) (hi : i ≠ a) (x : ℤ) (hx : x = 0 ∨ x = 1) :
    rho a b i x = 0 ∨ rho a b i x = 1 := by
  unfold rho; rw [if_neg hi]; split_ifs <;> rcases hx with rfl | rfl <;> simp [ishift_apply]

theorem F_step (a b i j : Fin d) (g : Gam d) :
    |F a b (g * mGen i * mGen j) - F a b g| ≤ 1 := by
  unfold F
  rw [mul_assoc, map_mul, map_mul, Phi_mGen, Phi_mGen]
  simp only [IsometryEquiv.coe_mul, Function.comp_apply]
  have h : |Phi a b g (rho a b i (rho a b j 0)) - Phi a b g 0| = |rho a b i (rho a b j 0)| := by
    have h := (Phi a b g).dist_eq (rho a b i (rho a b j 0)) 0
    rw [Int.dist_eq, Int.dist_eq] at h
    have h' : ((|Phi a b g (rho a b i (rho a b j 0)) - Phi a b g 0| : ℤ) : ℝ) =
        ((|rho a b i (rho a b j 0)| : ℤ) : ℝ) := by
      push_cast
      simpa using h
    exact_mod_cast h'
  rw [h]
  exact rho_small a b i _ (rho_zero a b j)

theorem F_del (a b i0 i : Fin d) (h : i0 ≠ a) :
    F a b (mGen i0 * mGen i) = 0 ∨ F a b (mGen i0 * mGen i) = 1 := by
  unfold F
  rw [map_mul, Phi_mGen, Phi_mGen]
  simp only [IsometryEquiv.coe_mul, Function.comp_apply]
  exact rho_01 a b i0 h _ (rho_zero a b i)

theorem F_pow (a b : Fin d) (hab : a ≠ b) (t : ℕ) :
    F a b ((mGen a * mGen b) ^ t) = -(t : ℤ) := by
  unfold F
  rw [map_pow, map_mul, Phi_mGen, Phi_mGen]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ']
    simp only [IsometryEquiv.coe_mul, Function.comp_apply] at ih ⊢
    rw [ih]
    simp [rho, hab.symm, ineg_apply, ishift_apply]
    ring

theorem F_neq (a b : Fin d) (hab : a ≠ b) (g : Gam d) : F a b (g * mGen a * mGen b) ≠ F a b g := by
  unfold F
  rw [mul_assoc, map_mul, map_mul, Phi_mGen, Phi_mGen]
  intro h
  have := (Phi a b g).injective h
  simp [rho, hab.symm, ineg_apply, ishift_apply] at this

end DerandSq.Dev.C48b
end

section
set_option autoImplicit false
namespace DerandSq.Dev.C48
open DerandSq DerandSq.Dev.C48a DerandSq.Dev.C48b SimpleGraph

section tree
variable {d : ℕ} (H : SimpleGraph (Fin d))

theorem T_fin : ∀ (u y : Gam d) (n : ℕ), Finite {w : (dsTree H).Walk u y // w.length = n} := by
  classical
  have hlf : (dsTree H).LocallyFinite := fun x => by
    have hs : ((dsTree H).neighborSet x).Finite := by
      refine (Set.finite_range (fun p : Fin d × Fin d => x * mGen p.1 * mGen p.2)).subset ?_
      rintro y ⟨_, i, j, _, rfl⟩
      exact ⟨(i, j), rfl⟩
    have : Finite ((dsTree H).neighborSet x) := hs.to_subtype
    exact Fintype.ofFinite _
  intro u y n
  infer_instance

theorem T_adj_F (a b : Fin d) {x y : Gam d} (h : (dsTree H).Adj x y) :
    |F a b y - F a b x| ≤ 1 := by
  obtain ⟨_, i, j, _, rfl⟩ := h
  exact F_step a b i j x

theorem supp_bound (a b : Fin d) {u v : Gam d} (w : (dsTree H).Walk u v) :
    ∀ x ∈ w.support, |F a b x - F a b u| ≤ w.length := by
  induction w with
  | nil => intro x hx; simp at hx; subst hx; simp
  | @cons u' v' w' h p ih =>
    intro x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    rw [Walk.length_cons]
    rcases hx with rfl | hx
    · simp; positivity
    · have h1 := ih x hx
      have h2 := T_adj_F H a b h
      have h3 : |F a b x - F a b u'| ≤ |F a b x - F a b v'| + |F a b v' - F a b u'| := by
        have := abs_add_le (F a b x - F a b v') (F a b v' - F a b u')
        simpa using this
      push_cast
      linarith

theorem del_F (a b i0 : Fin d) (hi : i0 ≠ a) {x y : Gam d}
    (h : s(x, y) ∈ {e : Sym2 (Gam d) | ∃ i j, H.Adj i j ∧ e = s(mGen i0 * mGen i, mGen i0 * mGen j)}) :
    (F a b x = 0 ∨ F a b x = 1) ∧ (F a b y = 0 ∨ F a b y = 1) := by
  obtain ⟨i, j, _, h⟩ := h
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨F_del a b i0 i hi, F_del a b i0 j hi⟩
  · exact ⟨F_del a b i0 j hi, F_del a b i0 i hi⟩

variable (i0 : Fin d)

theorem X_adj (a b : Fin d) (hi : i0 ≠ a) {x y : Gam d} (h : (dsTree H).Adj x y)
    (hx : F a b x < 0) : (prunedX H i0).Adj x y := by
  unfold prunedX
  rw [deleteEdges_adj]
  refine ⟨h, fun hd => ?_⟩
  have := (del_F H a b i0 hi hd).1
  omega

theorem X_le : prunedX H i0 ≤ dsTree H := deleteEdges_le _

theorem path_exists (a b : Fin d) (hab : H.Adj a b) (hi : i0 ≠ a) (s : ℕ) :
    ∃ P : (prunedX H i0).Walk 1 ((mGen a * mGen b) ^ s), P.length = s := by
  induction s with
  | zero => exact ⟨Walk.nil.copy rfl (pow_zero _).symm, by simp⟩
  | succ s ih =>
    obtain ⟨P, hP⟩ := ih
    have hv : (mGen a * mGen b) ^ (s + 1) = (mGen a * mGen b) ^ s * mGen a * mGen b := by
      rw [pow_succ, mul_assoc]
    have hadj : (dsTree H).Adj ((mGen a * mGen b) ^ s) ((mGen a * mGen b) ^ (s + 1)) := by
      rw [hv]
      exact ⟨fun h => F_neq a b hab.ne _ (by rw [← h]), a, b, hab, rfl⟩
    have hF : F a b ((mGen a * mGen b) ^ s) < 0 ∨ s = 0 := by
      rw [F_pow a b hab.ne]; omega
    have hXadj : (prunedX H i0).Adj ((mGen a * mGen b) ^ s) ((mGen a * mGen b) ^ (s + 1)) := by
      rcases hF with h | rfl
      · exact X_adj H i0 a b hi hadj h
      · -- first step: the far endpoint has negative F
        unfold prunedX
        rw [deleteEdges_adj]
        refine ⟨hadj, fun hd => ?_⟩
        have := (del_F H a b i0 hi hd).2
        rw [F_pow a b hab.ne] at this
        omega
    refine ⟨P.concat hXadj, ?_⟩
    simp [hP]

theorem walk_in_X (a b : Fin d) (hi : i0 ≠ a) (n : ℕ)
    (w : (dsTree H).Walk ((mGen a * mGen b) ^ (n + 1)) ((mGen a * mGen b) ^ (n + 1)))
    (hw : w.length = n) (hab : a ≠ b) :
    ∀ e ∈ w.edges, e ∈ (prunedX H i0).edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    have hT : (dsTree H).Adj x y := w.edges_subset_edgeSet he
    have hx := w.fst_mem_support_of_mem_edges he
    have h1 := supp_bound H a b w x hx
    rw [F_pow a b hab] at h1
    rw [hw] at h1
    have h2 : F a b x < 0 := by
      have := (abs_le.1 h1).2
      push_cast at this
      omega
    exact X_adj H i0 a b hi hT h2

theorem cw_T_le_X (a b : Fin d) (hab : a ≠ b) (hi : i0 ≠ a) (n : ℕ) :
    closedWalks (dsTree H) ((mGen a * mGen b) ^ (n + 1)) n ≤
      closedWalks (prunedX H i0) ((mGen a * mGen b) ^ (n + 1)) n := by
  unfold closedWalks
  have := fin_of_hom (Hom.ofLE (X_le H i0)) Function.injective_id (T_fin H)
  refine Nat.card_le_card_of_injective
    (fun w : {w : (dsTree H).Walk ((mGen a * mGen b) ^ (n + 1)) ((mGen a * mGen b) ^ (n + 1)) //
        w.length = n} =>
      (⟨w.1.transfer _ (walk_in_X H i0 a b hi n w.1 w.2 hab), by simp [w.2]⟩ :
        {w : (prunedX H i0).Walk ((mGen a * mGen b) ^ (n + 1)) ((mGen a * mGen b) ^ (n + 1)) //
          w.length = n})) ?_
  rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
  have := congrArg Subtype.val h
  apply Subtype.ext
  apply Walk.ext_support
  have h3 := congrArg Walk.support this
  simpa using h3

def lmul (v : Gam d) : dsTree H →g dsTree H where
  toFun x := v * x
  map_rel' := by
    rintro x y ⟨hne, i, j, hij, rfl⟩
    refine ⟨fun h => hne (mul_left_cancel h), i, j, hij, ?_⟩
    simp [mul_assoc]

theorem T_mul_le (v : Gam d) (n : ℕ) :
    closedWalks (dsTree H) 1 n ≤ closedWalks (dsTree H) v n := by
  have := cw_le_of_hom (lmul H v) (fun x y h => mul_left_cancel h) (T_fin H) 1 n
  simpa [lmul] using this

theorem key (a b : Fin d) (hab : H.Adj a b) (hi : i0 ≠ a) (n q : ℕ) :
    closedWalks (dsTree H) 1 n ^ q ≤ closedWalks (prunedX H i0) 1 (n * q + 2 * (n + 1)) := by
  have hXfin := fin_of_hom (Hom.ofLE (X_le H i0)) Function.injective_id (T_fin H)
  obtain ⟨P, hP⟩ := path_exists H i0 a b hab hi (n + 1)
  have h1 : closedWalks (dsTree H) 1 n ≤ closedWalks (prunedX H i0) ((mGen a * mGen b) ^ (n + 1)) n :=
    (T_mul_le H _ n).trans (cw_T_le_X H i0 a b hab.ne hi n)
  calc closedWalks (dsTree H) 1 n ^ q
      ≤ closedWalks (prunedX H i0) ((mGen a * mGen b) ^ (n + 1)) n ^ q := Nat.pow_le_pow_left h1 q
    _ ≤ closedWalks (prunedX H i0) ((mGen a * mGen b) ^ (n + 1)) (n * q) := cw_pow hXfin _ n q
    _ ≤ closedWalks (prunedX H i0) 1 (n * q + 2 * P.length) := cw_conj hXfin P _
    _ = _ := by rw [hP]

theorem upper (a b : Fin d) (hab : H.Adj a b) (hi : i0 ≠ a) (L : ℝ)
    (h47 : Filter.Tendsto
      (fun p : ℕ => (closedWalks (prunedX H i0) 1 (2 * p) : ℝ) ^ ((1 : ℝ) / (2 * p)))
      Filter.atTop (nhds L)) (p : ℕ) (hp : 1 ≤ p) :
    (closedWalks (dsTree H) 1 (2 * p) : ℝ) ^ ((1 : ℝ) / (2 * p)) ≤ L := by
  set A : ℝ := (closedWalks (dsTree H) 1 (2 * p) : ℝ) with hA
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rcases hA0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by positivity)]
    refine ge_of_tendsto' h47 (fun m => ?_)
    positivity
  set c : ℕ := 2 * p + 1 with hc
  let m : ℕ → ℕ := fun q => p * q + c
  have hm : Filter.Tendsto m Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun q => by show q ≤ p * q + c; nlinarith) Filter.tendsto_id
  have hg := h47.comp hm
  have hexp : Filter.Tendsto (fun q : ℕ => (q : ℝ) / (2 * (m q : ℝ))) Filter.atTop
      (nhds (1 / (2 * (p : ℝ)))) := by
    have h1 : Filter.Tendsto (fun q : ℕ => (c : ℝ) / q) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h2 : Filter.Tendsto (fun q : ℕ => 1 / (2 * ((p : ℝ) + (c : ℝ) / q))) Filter.atTop
        (nhds (1 / (2 * ((p : ℝ) + 0)))) :=
      Filter.Tendsto.div tendsto_const_nhds
        (tendsto_const_nhds.mul (tendsto_const_nhds.add h1)) (by positivity)
    rw [add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with q hq
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    simp only [m]
    push_cast
    field_simp
  have hh : Filter.Tendsto (fun q : ℕ => A ^ ((q : ℝ) / (2 * (m q : ℝ)))) Filter.atTop
      (nhds (A ^ (1 / (2 * (p : ℝ))))) :=
    ((Real.continuousAt_const_rpow hpos.ne').tendsto).comp hexp
  refine le_of_tendsto_of_tendsto' hh hg (fun q => ?_)
  simp only [Function.comp]
  have hk := key H i0 a b hab hi (2 * p) q
  have hidx : 2 * p * q + 2 * (2 * p + 1) = 2 * m q := by simp only [m, hc]; ring
  rw [hidx] at hk
  have hk' : A ^ q ≤ (closedWalks (prunedX H i0) 1 (2 * m q) : ℝ) := by
    rw [hA]; exact_mod_cast hk
  have hmq : (0 : ℝ) < m q := by
    have : 0 < m q := by simp only [m, hc]; omega
    exact_mod_cast this
  calc A ^ ((q : ℝ) / (2 * (m q : ℝ))) = (A ^ (q : ℝ)) ^ ((1 : ℝ) / (2 * (m q : ℝ))) := by
        rw [← Real.rpow_mul hA0]; congr 1; ring
    _ = (A ^ q) ^ ((1 : ℝ) / (2 * (m q : ℝ))) := by rw [Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hk' (by positivity)

theorem exists_edge {k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) [DecidableRel H.Adj]
    (hH : H.IsRegularOfDegree k) :
    ∃ a b, H.Adj a b ∧ i0 ≠ a := by
  have v0 : Fin d := ⟨0, by omega⟩
  have hdeg := hH v0
  have : 0 < H.degree v0 := by omega
  obtain ⟨b, hb⟩ := (H.degree_pos_iff_exists_adj v0).1 this
  by_cases h : i0 = v0
  · exact ⟨b, v0, hb.symm, fun h' => hb.ne (h.symm.trans h')⟩
  · exact ⟨v0, b, hb, h⟩

end tree

end DerandSq.Dev.C48

namespace DerandSq
open DerandSq.Dev.C48 DerandSq.Dev.C48a in
theorem chk_corollary_4_8 {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (H : SimpleGraph (Fin d))
    [DecidableRel H.Adj] (hH : H.IsRegularOfDegree k) (hvt : IsVertexTransitive H) :
    ‖QH H‖ = LambdaH d H := by
  have i0 : Fin d := ⟨0, by omega⟩
  obtain ⟨a, b, hab, hi⟩ := exists_edge H i0 hd hk hH
  have h47 := DerandSq.theorem_4_7 hd hk H hH hvt i0
  have hT := (DerandSq.proposition_4_6 hd hk H hH).2
  apply le_antisymm
  · refine le_of_tendsto hT ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with p hp
    exact upper H i0 a b hab hi _ h47 p hp
  · refine le_of_tendsto_of_tendsto' h47 hT (fun p => ?_)
    have hle : closedWalks (prunedX H i0) 1 (2 * p) ≤ closedWalks (dsTree H) 1 (2 * p) :=
      cw_le_of_hom (SimpleGraph.Hom.ofLE (X_le H i0)) Function.injective_id (T_fin H) 1 _
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle) (by positivity)
end DerandSq
end

theorem solution : type_of% @DerandSq.chk_corollary_4_8 := @DerandSq.chk_corollary_4_8
