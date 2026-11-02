-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityB.l_separation_theorem
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T04:11:00.339362+00:00
-- url     : https://prove2.me/submissions/cbfd944d-1d75-42d3-91ca-0a2f160e28f4

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateZR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConcaveConjugateZR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomERealConcave
import Theorems.Thm_DiscreteConvex_MConvexSets_discrete_separation_submodular
import Theorems.Thm_DiscreteConvex_LConvexSets_discrete_separation_lconvex

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LSepAux

open Classical
open scoped Pointwise
open DiscreteConvex.ConjugacyDualityB

section Basic
variable {V : Type*} [Fintype V] [DecidableEq V]

def idot (p x : V → ℤ) : ℤ := ∑ i, p i * x i

lemma dot_eq (p x : V → ℤ) : (∑ i, (p i : ℝ) * (x i : ℝ)) = ((idot p x : ℤ) : ℝ) := by
  simp [idot]

lemma idot_comm (p x : V → ℤ) : idot p x = idot x p := by
  simp only [idot, mul_comm]

lemma idot_add_left (p q x : V → ℤ) : idot (p + q) x = idot p x + idot q x := by
  simp only [idot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma idot_add_right (p x y : V → ℤ) : idot p (x + y) = idot p x + idot p y := by
  simp only [idot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma idot_sub_left (p q x : V → ℤ) : idot (p - q) x = idot p x - idot q x := by
  simp only [idot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma idot_sub_right (p x y : V → ℤ) : idot p (x - y) = idot p x - idot p y := by
  simp only [idot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma idot_neg_left (p x : V → ℤ) : idot (-p) x = - idot p x := by
  simp only [idot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

lemma idot_neg_right (p x : V → ℤ) : idot p (-x) = - idot p x := by
  simp only [idot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

lemma idot_smul_left (t : ℤ) (q x : V → ℤ) : idot (t • q) x = t * idot q x := by
  simp only [idot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma idot_one_right (p : V → ℤ) : idot p (1 : V → ℤ) = ∑ i, p i := by
  simp [idot]

lemma idot_sup_inf (z a b : V → ℤ) : idot z (a ⊔ b) + idot z (a ⊓ b) = idot z a + idot z b := by
  simp only [idot, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (a ⊔ b) i + (a ⊓ b) i = a i + b i := by
    show max (a i) (b i) + min (a i) (b i) = a i + b i
    omega
  linarith [congrArg (z i * ·) this]

noncomputable def iv (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) : ℤ :=
  if h : ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ) then h.choose else 0

lemma iv_spec {f : (V → ℤ) → WithTop ℝ} (hZ : IsIntegerValuedFn f) {x : V → ℤ} (hx : f x ≠ ⊤) :
    f x = (((iv f x : ℤ) : ℝ) : WithTop ℝ) := by
  have h : ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ) := (hZ x).resolve_left hx
  unfold iv
  rw [dif_pos h]
  exact h.choose_spec

def IsMaxZ (f : (V → ℤ) → WithTop ℝ) (p x : V → ℤ) : Prop :=
  f x ≠ ⊤ ∧ ∀ y, f y ≠ ⊤ → idot p y - iv f y ≤ idot p x - iv f x

lemma untopD_coe (r : ℝ) : ((r : WithTop ℝ)).untopD 0 = r := rfl

lemma coe_untopD {a : WithTop ℝ} (ha : a ≠ ⊤) : ((a.untopD 0 : ℝ) : WithTop ℝ) = a := by
  rcases WithTop.ne_top_iff_exists.mp ha with ⟨r, rfl⟩
  rfl

lemma add_untopD_le {a b c d : WithTop ℝ} (hc : c ≠ ⊤) (hd : d ≠ ⊤) (hle : a + b ≤ c + d) :
    a ≠ ⊤ ∧ b ≠ ⊤ ∧ a.untopD 0 + b.untopD 0 ≤ c.untopD 0 + d.untopD 0 := by
  have hcd : c + d ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hc, hd⟩
  have hab : a + b ≠ ⊤ := ne_top_of_le_ne_top hcd hle
  obtain ⟨ha, hb⟩ := WithTop.add_ne_top.mp hab
  refine ⟨ha, hb, ?_⟩
  rw [← coe_untopD ha, ← coe_untopD hb, ← coe_untopD hc, ← coe_untopD hd,
    ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hle
  exact hle

end Basic

section LocGlob

theorem loc_glob {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : (W → ℤ) → WithTop ℝ)
    (hsub : ∀ p q, G (p ⊔ q) + G (p ⊓ q) ≤ G p + G q)
    (htr : ∀ p, G (p + 1) = G p) (z : W → ℤ) (hz : G z ≠ ⊤)
    (hloc : ∀ X : Finset W, G z ≤ G (fun a => z a + if a ∈ X then 1 else 0)) :
    ∀ y, G z ≤ G y := by
  have htrk : ∀ (k : ℕ) (p : W → ℤ), G (fun a => p a + k) = G p := by
    intro k
    induction k with
    | zero => intro p; simp
    | succ k ih =>
      intro p
      rw [← ih p, ← htr (fun a => p a + k)]
      congr 1; funext a; simp; ring
  have key : ∀ M : ℕ, ∀ y : W → ℤ, (∀ a, z a ≤ y a) → (∀ a, y a - z a ≤ M) → G z ≤ G y := by
    intro M
    induction M with
    | zero =>
      intro y h1 h2
      have : y = z := funext fun a => by have := h1 a; have := h2 a; push_cast at *; omega
      rw [this]
    | succ M ih =>
      intro y h1 h2
      set U := Finset.univ.filter (fun a => z a < y a) with hU
      set y' : W → ℤ := (y - 1) ⊔ z with hy'
      have hs := hsub (y - 1) z
      have e1 : G (y - 1) = G y := by
        have := htr (y - 1); rw [sub_add_cancel] at this; exact this.symm
      have e2 : G ((y - 1) ⊓ z) = G (fun a => z a + if a ∈ U then 1 else 0) := by
        rw [← htr]; congr 1; funext a
        simp only [Pi.add_apply, Pi.inf_apply, Pi.sub_apply, Pi.one_apply, hU,
          Finset.mem_filter, Finset.mem_univ, true_and]
        have := h1 a
        split_ifs with h <;> omega
      have hy'1 : G z ≤ G y' := by
        apply ih y'
        · intro a; simp only [hy', Pi.sup_apply]; omega
        · intro a; simp only [hy', Pi.sup_apply, Pi.sub_apply, Pi.one_apply]
          have := h1 a; have := h2 a; push_cast at *; omega
      have hl := hloc U
      have hle : G y' + G z ≤ G y + G z := by
        calc G y' + G z ≤ G y' + G ((y - 1) ⊓ z) := by rw [e2]; exact add_le_add le_rfl hl
          _ ≤ G (y - 1) + G z := hs
          _ = G y + G z := by rw [e1]
      have := (WithTop.add_le_add_iff_right hz).mp hle
      exact le_trans hy'1 this
  intro y
  obtain ⟨a0, -, ha0⟩ := Finset.exists_min_image Finset.univ (fun a => y a - z a)
    Finset.univ_nonempty
  set y0 : W → ℤ := fun a => y a - (y a0 - z a0) with hy0
  obtain ⟨b0, -, hb0⟩ := Finset.exists_max_image Finset.univ (fun a => y0 a - z a)
    Finset.univ_nonempty
  have hge : ∀ a, z a ≤ y0 a := by
    intro a; have := ha0 a (Finset.mem_univ a); simp only [hy0]; omega
  have hyy : G y = G y0 := by
    rcases le_total 0 (y a0 - z a0) with h | h
    · have := htrk (y a0 - z a0).toNat y0
      rw [← this]; congr 1; funext a; simp only [hy0]; omega
    · have := htrk (z a0 - y a0).toNat y
      rw [← this]; congr 1; funext a; simp only [hy0]; omega
  rw [hyy]
  apply key (y0 b0 - z b0).toNat y0 hge
  intro a
  have := hb0 a (Finset.mem_univ a)
  have := hge b0
  omega

noncomputable def chi {W : Type*} (X : Finset W) : W → ℤ := fun a => if a ∈ X then 1 else 0

lemma idot_chi {W : Type*} [Fintype W] (z : W → ℤ) (X : Finset W) :
    idot z (chi X) = ∑ a ∈ X, z a := by
  simp [idot, chi, Finset.sum_ite_mem, Finset.univ_inter]

lemma lmax_of_local0 {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {g : (W → ℤ) → WithTop ℝ} (hs : SBF g) (hZ : IsIntegerValuedFn g)
    (htr : ∀ p, g (p + 1) = g p) {z p : W → ℤ}
    (hsz : ∑ i, z i = 0) (hp : g p ≠ ⊤)
    (hloc : ∀ X : Finset W, g (p + chi X) ≠ ⊤ →
      ∑ a ∈ X, z a ≤ iv g (p + chi X) - iv g p) : IsMaxZ g z p := by
  refine ⟨hp, fun q hq => ?_⟩
  let G : (W → ℤ) → WithTop ℝ := fun q => g q + ((((-(idot z q)) : ℤ) : ℝ) : WithTop ℝ)
  have hsub : ∀ a b, G (a ⊔ b) + G (a ⊓ b) ≤ G a + G b := by
    intro a b
    simp only [G]
    rw [add_add_add_comm, add_add_add_comm (g a), ← WithTop.coe_add, ← WithTop.coe_add]
    have e := idot_sup_inf z a b
    have e2 : ((-(idot z (a ⊔ b)) : ℤ) : ℝ) + ((-(idot z (a ⊓ b)) : ℤ) : ℝ) =
        ((-(idot z a) : ℤ) : ℝ) + ((-(idot z b) : ℤ) : ℝ) := by
      push_cast
      have e' : ((idot z (a ⊔ b) : ℤ) : ℝ) + ((idot z (a ⊓ b) : ℤ) : ℝ) =
          ((idot z a : ℤ) : ℝ) + ((idot z b : ℤ) : ℝ) := by exact_mod_cast e
      linarith
    rw [e2]
    exact add_le_add (hs a b) le_rfl
  have hGtr : ∀ a, G (a + 1) = G a := by
    intro a
    simp only [G]
    rw [htr, idot_add_right, idot_one_right, hsz, add_zero]
  have hGp : G p ≠ ⊤ := WithTop.add_ne_top.2 ⟨hp, WithTop.coe_ne_top⟩
  have hl : ∀ X : Finset W, G p ≤ G (fun a => p a + if a ∈ X then 1 else 0) := by
    intro X
    have e : (fun a => p a + if a ∈ X then (1 : ℤ) else 0) = p + chi X := by
      funext a; simp [chi]
    rw [e]
    by_cases hX : g (p + chi X) = ⊤
    · simp only [G, hX, top_add]; exact le_top
    · have h1 := hloc X hX
      simp only [G]
      rw [iv_spec hZ hX, iv_spec hZ hp, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe,
        idot_add_right, idot_chi]
      have h2 : iv g p - idot z p ≤ iv g (p + chi X) - (idot z p + ∑ a ∈ X, z a) := by omega
      have h3 : ((iv g p - idot z p : ℤ) : ℝ) ≤
          ((iv g (p + chi X) - (idot z p + ∑ a ∈ X, z a) : ℤ) : ℝ) := by exact_mod_cast h2
      push_cast at h3 ⊢; linarith
  have hglob := loc_glob G hsub hGtr p hGp hl q
  simp only [G] at hglob
  rw [iv_spec hZ hq, iv_spec hZ hp, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hglob
  have h4 : ((iv g p - idot z p : ℤ) : ℝ) ≤ ((iv g q - idot z q : ℤ) : ℝ) := by
    push_cast at hglob ⊢; linarith
  have h5 : iv g p - idot z p ≤ iv g q - idot z q := by exact_mod_cast h4
  omega

end LocGlob

section LiftSubgrad
variable {V : Type*} [Fintype V] [DecidableEq V]

def liftZ (p : V → ℤ) : Option V → ℤ := fun o => Option.elim o 0 p

lemma lift_eval (g : (V → ℤ) → WithTop ℝ) (p : V → ℤ) :
    LiftedFunctionL g (liftZ p) = g p := by
  simp [LiftedFunctionL, liftZ]

lemma lift_tr (g : (V → ℤ) → WithTop ℝ) (W : Option V → ℤ) :
    LiftedFunctionL g (W + 1) = LiftedFunctionL g W := by
  simp only [LiftedFunctionL, Pi.add_apply, Pi.one_apply]
  congr 1; funext v; ring

lemma lift_intval {g : (V → ℤ) → WithTop ℝ} (hg : IsIntegerValuedFn g) :
    IsIntegerValuedFn (LiftedFunctionL g) :=
  fun W => hg (fun v => W (some v) - W none)

lemma iv_congr {W1 W2 : Type*} {f : (W1 → ℤ) → WithTop ℝ} {g : (W2 → ℤ) → WithTop ℝ}
    {x : W1 → ℤ} {y : W2 → ℤ} (h : f x = g y) : iv f x = iv g y := by
  unfold iv; simp only [h]

lemma idot_lift {y : Option V → ℤ} (_hy : ∑ o : Option V, y o = 0) (p : V → ℤ) :
    idot y (liftZ p) = idot (fun v => y (some v)) p := by
  simp [idot, liftZ, Fintype.sum_option]

lemma chi_sup {W : Type*} [DecidableEq W] (Z : W → ℤ) (X Y : Finset W) :
    (Z + chi X) ⊔ (Z + chi Y) = Z + chi (X ∪ Y) := by
  funext a
  show max ((Z + chi X) a) ((Z + chi Y) a) = (Z + chi (X ∪ Y)) a
  by_cases hX : a ∈ X <;> by_cases hY : a ∈ Y <;> simp [chi, hX, hY]

lemma chi_inf {W : Type*} [DecidableEq W] (Z : W → ℤ) (X Y : Finset W) :
    (Z + chi X) ⊓ (Z + chi Y) = Z + chi (X ∩ Y) := by
  funext a
  show min ((Z + chi X) a) ((Z + chi Y) a) = (Z + chi (X ∩ Y)) a
  by_cases hX : a ∈ X <;> by_cases hY : a ∈ Y <;> simp [chi, hX, hY]

lemma sub_chi_sup {W : Type*} [DecidableEq W] (Z : W → ℤ) (X Y : Finset W) :
    (Z - chi X) ⊔ (Z - chi Y) = Z - chi (X ∩ Y) := by
  funext a
  show max ((Z - chi X) a) ((Z - chi Y) a) = (Z - chi (X ∩ Y)) a
  by_cases hX : a ∈ X <;> by_cases hY : a ∈ Y <;> simp [chi, hX, hY]

lemma sub_chi_inf {W : Type*} [DecidableEq W] (Z : W → ℤ) (X Y : Finset W) :
    (Z - chi X) ⊓ (Z - chi Y) = Z - chi (X ∪ Y) := by
  funext a
  show min ((Z - chi X) a) ((Z - chi Y) a) = (Z - chi (X ∪ Y)) a
  by_cases hX : a ∈ X <;> by_cases hY : a ∈ Y <;> simp [chi, hX, hY]

theorem subgrad_at_min {g1 g2 : (V → ℤ) → WithTop ℝ}
    (hg1 : LNaturalConvex g1) (hg2 : LNaturalConvex g2)
    (hg1z : IsIntegerValuedFn g1) (hg2z : IsIntegerValuedFn g2)
    {p0 p1s p2s : V → ℤ} (hp0 : p0 = p1s + p2s)
    (hp1 : g1 p1s ≠ ⊤) (hp2 : g2 p2s ≠ ⊤)
    (hmin : ∀ p1 p2 : V → ℤ, p0 = p1 + p2 → g1 p1 ≠ ⊤ → g2 p2 ≠ ⊤ →
      iv g1 p1s + iv g2 p2s ≤ iv g1 p1 + iv g2 p2) :
    ∃ x : V → ℤ, IsMaxZ g1 x p1s ∧ IsMaxZ g2 x p2s := by
  let G1 := LiftedFunctionL g1
  let G2 := LiftedFunctionL g2
  have hs1 : SBF G1 := hg1.1
  have hs2 : SBF G2 := hg2.1
  have hG1Z : IsIntegerValuedFn G1 := lift_intval hg1z
  have hG2Z : IsIntegerValuedFn G2 := lift_intval hg2z
  let Z1 := liftZ p1s
  let Z2 := liftZ p2s
  have hZ1 : G1 Z1 ≠ ⊤ := by change LiftedFunctionL g1 (liftZ p1s) ≠ ⊤; rw [lift_eval]; exact hp1
  have hZ2 : G2 Z2 ≠ ⊤ := by change LiftedFunctionL g2 (liftZ p2s) ≠ ⊤; rw [lift_eval]; exact hp2
  have hivZ1 : iv G1 Z1 = iv g1 p1s := iv_congr (lift_eval g1 p1s)
  have hivZ2 : iv G2 Z2 = iv g2 p2s := iv_congr (lift_eval g2 p2s)
  let ρ : Finset (Option V) → WithTop ℝ := fun Y =>
    if G1 (Z1 + chi Y) = ⊤ then ⊤ else (((iv G1 (Z1 + chi Y) - iv G1 Z1 : ℤ) : ℝ) : WithTop ℝ)
  let μ : Finset (Option V) → WithBot ℝ := fun Y =>
    if G2 (Z2 - chi Y) = ⊤ then ⊥ else (((iv G2 Z2 - iv G2 (Z2 - chi Y) : ℤ) : ℝ) : WithBot ℝ)
  have hchi0 : chi (∅ : Finset (Option V)) = 0 := by funext o; simp [chi]
  have hchiu : chi (Finset.univ : Finset (Option V)) = 1 := by funext o; simp [chi]
  have hZ1u : G1 (Z1 + 1) = G1 Z1 := lift_tr g1 Z1
  have hZ2u : G2 (Z2 - 1) = G2 Z2 := by
    have := lift_tr g2 (Z2 - 1)
    rw [sub_add_cancel] at this
    exact this.symm
  have hρ0 : ρ ∅ = 0 := by simp [ρ, hchi0, hZ1]
  have hρu : ρ Finset.univ = 0 := by
    have h1 : G1 (Z1 + chi Finset.univ) = G1 Z1 := by rw [hchiu, hZ1u]
    simp [ρ, h1, hZ1, iv_congr h1]
  have hμ0 : μ ∅ = 0 := by simp [μ, hchi0, hZ2]
  have hμu : μ Finset.univ = 0 := by
    have h1 : G2 (Z2 - chi Finset.univ) = G2 Z2 := by rw [hchiu, hZ2u]
    simp [μ, h1, hZ2, iv_congr h1]
  have hρ_sub : DiscreteConvex.MConvexSets.SubmodularSetFunction ρ := by
    refine ⟨hρ0, by rw [hρu]; exact WithTop.coe_ne_top, fun X Y => ?_⟩
    by_cases hX : G1 (Z1 + chi X) = ⊤
    · simp [ρ, hX]
    by_cases hY : G1 (Z1 + chi Y) = ⊤
    · simp [ρ, hY]
    have hs := hs1 (Z1 + chi X) (Z1 + chi Y)
    rw [chi_sup, chi_inf] at hs
    have hfin : G1 (Z1 + chi (X ∪ Y)) + G1 (Z1 + chi (X ∩ Y)) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hX, hY⟩) hs
    obtain ⟨hU, hI⟩ := WithTop.add_ne_top.1 hfin
    rw [iv_spec hG1Z hU, iv_spec hG1Z hI, iv_spec hG1Z hX, iv_spec hG1Z hY,
      ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at hs
    have hs' : iv G1 (Z1 + chi (X ∪ Y)) + iv G1 (Z1 + chi (X ∩ Y)) ≤
        iv G1 (Z1 + chi X) + iv G1 (Z1 + chi Y) := by exact_mod_cast hs
    simp only [ρ, if_neg hX, if_neg hY, if_neg hU, if_neg hI, ge_iff_le,
      ← WithTop.coe_add, WithTop.coe_le_coe]
    have : ((iv G1 (Z1 + chi (X ∪ Y)) - iv G1 Z1 + (iv G1 (Z1 + chi (X ∩ Y)) - iv G1 Z1) : ℤ) : ℝ) ≤
        ((iv G1 (Z1 + chi X) - iv G1 Z1 + (iv G1 (Z1 + chi Y) - iv G1 Z1) : ℤ) : ℝ) := by
      exact_mod_cast (by omega)
    push_cast at this ⊢; linarith
  have hμ_sup : DiscreteConvex.MConvexSets.SupermodularSetFunction μ := by
    refine ⟨hμ0, by rw [hμu]; exact WithBot.coe_ne_bot, fun X Y => ?_⟩
    by_cases hX : G2 (Z2 - chi X) = ⊤
    · simp [μ, hX]
    by_cases hY : G2 (Z2 - chi Y) = ⊤
    · simp [μ, hY]
    have hs := hs2 (Z2 - chi X) (Z2 - chi Y)
    rw [sub_chi_sup, sub_chi_inf] at hs
    have hfin : G2 (Z2 - chi (X ∩ Y)) + G2 (Z2 - chi (X ∪ Y)) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hX, hY⟩) hs
    obtain ⟨hI, hU⟩ := WithTop.add_ne_top.1 hfin
    rw [iv_spec hG2Z hI, iv_spec hG2Z hU, iv_spec hG2Z hX, iv_spec hG2Z hY,
      ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at hs
    have hs' : iv G2 (Z2 - chi (X ∩ Y)) + iv G2 (Z2 - chi (X ∪ Y)) ≤
        iv G2 (Z2 - chi X) + iv G2 (Z2 - chi Y) := by exact_mod_cast hs
    simp only [μ, if_neg hX, if_neg hY, if_neg hU, if_neg hI,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    have : ((iv G2 Z2 - iv G2 (Z2 - chi X) + (iv G2 Z2 - iv G2 (Z2 - chi Y)) : ℤ) : ℝ) ≤
        ((iv G2 Z2 - iv G2 (Z2 - chi (X ∪ Y)) + (iv G2 Z2 - iv G2 (Z2 - chi (X ∩ Y))) : ℤ) : ℝ) := by
      exact_mod_cast (by omega)
    push_cast at this ⊢; linarith
  have hsep : ∀ Y : Finset (Option V),
      DiscreteConvex.MConvexSets.ToERealOfBot (μ Y) ≤ DiscreteConvex.MConvexSets.ToEReal (ρ Y) := by
    intro Y
    by_cases h1 : G1 (Z1 + chi Y) = ⊤
    · simp only [ρ, if_pos h1, DiscreteConvex.MConvexSets.ToEReal]; exact le_top
    by_cases h2 : G2 (Z2 - chi Y) = ⊤
    · simp only [μ, if_pos h2, DiscreteConvex.MConvexSets.ToERealOfBot]; exact bot_le
    simp only [ρ, μ, if_neg h1, if_neg h2]
    change (((iv G2 Z2 - iv G2 (Z2 - chi Y) : ℤ) : ℝ) : EReal) ≤
      (((iv G1 (Z1 + chi Y) - iv G1 Z1 : ℤ) : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff]
    let q1 : V → ℤ := fun v => (Z1 + chi Y) (some v) - (Z1 + chi Y) none
    let q2 : V → ℤ := fun v => (Z2 - chi Y) (some v) - (Z2 - chi Y) none
    have hq0 : p0 = q1 + q2 := by
      funext v
      have := congrFun hp0 v
      simp only [q1, q2, Z1, Z2, liftZ, Pi.add_apply, Pi.sub_apply, Option.elim] at this ⊢
      omega
    have hq1 : g1 q1 = G1 (Z1 + chi Y) := rfl
    have hq2 : g2 q2 = G2 (Z2 - chi Y) := rfl
    have hm := hmin q1 q2 hq0 (by rwa [hq1]) (by rwa [hq2])
    have e1 : iv G1 (Z1 + chi Y) = iv g1 q1 := rfl
    have e2 : iv G2 (Z2 - chi Y) = iv g2 q2 := rfl
    rw [hivZ1, hivZ2, e1, e2]
    exact_mod_cast (by omega : iv g2 p2s - iv g2 q2 ≤ iv g1 q1 - iv g1 p1s)
  have hρZ : DiscreteConvex.MConvexSets.IsIntegerValued ρ := by
    intro Y
    by_cases h : G1 (Z1 + chi Y) = ⊤
    · exact Or.inl (by simp [ρ, h])
    · exact Or.inr ⟨iv G1 (Z1 + chi Y) - iv G1 Z1, by simp [ρ, h]⟩
  have hμZ : DiscreteConvex.MConvexSets.IsIntegerValuedBot μ := by
    intro Y
    by_cases h : G2 (Z2 - chi Y) = ⊤
    · exact Or.inl (by simp [μ, h])
    · exact Or.inr ⟨iv G2 Z2 - iv G2 (Z2 - chi Y), by simp [μ, h]⟩
  obtain ⟨y, hy⟩ :=
    (DiscreteConvex.MConvexSets.discrete_separation_submodular ρ μ hρ_sub hμ_sup hsep).2 hρZ hμZ
  have hy_ρ : ∀ Y : Finset (Option V), G1 (Z1 + chi Y) ≠ ⊤ →
      ∑ o ∈ Y, y o ≤ iv G1 (Z1 + chi Y) - iv G1 Z1 := by
    intro Y hY
    have h := (hy Y).2
    simp only [ρ, if_neg hY] at h
    change (((∑ o ∈ Y, (y o : ℝ) : ℝ)) : EReal) ≤
      (((iv G1 (Z1 + chi Y) - iv G1 Z1 : ℤ) : ℝ) : EReal) at h
    rw [EReal.coe_le_coe_iff] at h
    exact_mod_cast h
  have hy_μ : ∀ Y : Finset (Option V), G2 (Z2 - chi Y) ≠ ⊤ →
      iv G2 Z2 - iv G2 (Z2 - chi Y) ≤ ∑ o ∈ Y, y o := by
    intro Y hY
    have h := (hy Y).1
    simp only [μ, if_neg hY] at h
    change (((iv G2 Z2 - iv G2 (Z2 - chi Y) : ℤ) : ℝ) : EReal) ≤
      (((∑ o ∈ Y, (y o : ℝ) : ℝ)) : EReal) at h
    rw [EReal.coe_le_coe_iff] at h
    exact_mod_cast h
  have hsum_y : ∑ o : Option V, y o = 0 := by
    have h1 := hy_ρ Finset.univ (by rw [hchiu, hZ1u]; exact hZ1)
    have h2 := hy_μ Finset.univ (by rw [hchiu, hZ2u]; exact hZ2)
    have e1 : iv G1 (Z1 + chi Finset.univ) = iv G1 Z1 := iv_congr (by rw [hchiu, hZ1u])
    have e2 : iv G2 (Z2 - chi Finset.univ) = iv G2 Z2 := iv_congr (by rw [hchiu, hZ2u])
    rw [e1, sub_self] at h1
    rw [e2, sub_self] at h2
    omega
  have hmax1 : IsMaxZ G1 y Z1 :=
    lmax_of_local0 hs1 hG1Z (lift_tr g1) hsum_y hZ1 hy_ρ
  let U : (Option V → ℤ) → WithTop ℝ := fun W => G2 (-W)
  have hU_sbf : SBF U := by
    intro a b
    show G2 (-(a ⊔ b)) + G2 (-(a ⊓ b)) ≤ G2 (-a) + G2 (-b)
    rw [neg_sup, neg_inf, add_comm (G2 (-a ⊓ -b))]
    exact hs2 (-a) (-b)
  have hU_Z : IsIntegerValuedFn U := fun W => hG2Z (-W)
  have hU_tr : ∀ W, U (W + 1) = U W := by
    intro W
    show G2 (-(W + 1)) = G2 (-W)
    have e : -W = -(W + 1) + 1 := by funext o; simp
    rw [e]; exact (lift_tr g2 (-(W + 1))).symm
  have hUZ2 : U (-Z2) ≠ ⊤ := by show G2 (- -Z2) ≠ ⊤; rw [neg_neg]; exact hZ2
  have hivU : ∀ W, iv U W = iv G2 (-W) := fun _ => rfl
  have hmaxU : IsMaxZ U (-y) (-Z2) := by
    apply lmax_of_local0 hU_sbf hU_Z hU_tr (by simp [Finset.sum_neg_distrib, hsum_y]) hUZ2
    intro Y hY
    have hY' : G2 (Z2 - chi Y) ≠ ⊤ := by
      convert hY using 2; funext o; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]; ring
    have hm := hy_μ Y hY'
    have e : iv U (-Z2 + chi Y) = iv G2 (Z2 - chi Y) := by
      show iv G2 (-(-Z2 + chi Y)) = iv G2 (Z2 - chi Y)
      congr 1; funext o; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]; ring
    have e0 : iv U (-Z2) = iv G2 Z2 := by show iv G2 (- -Z2) = iv G2 Z2; rw [neg_neg]
    simp only [Pi.neg_apply, Finset.sum_neg_distrib, e, e0]
    omega
  refine ⟨fun v => y (some v), ⟨hp1, fun q hq => ?_⟩, ⟨hp2, fun q hq => ?_⟩⟩
  · have hq' : G1 (liftZ q) ≠ ⊤ := by change LiftedFunctionL g1 (liftZ q) ≠ ⊤; rw [lift_eval]; exact hq
    have h := hmax1.2 (liftZ q) hq'
    have eq1 : iv G1 (liftZ q) = iv g1 q := iv_congr (lift_eval g1 q)
    rw [idot_lift hsum_y q, idot_lift hsum_y p1s, eq1, hivZ1] at h
    exact h
  · have hq' : U (-(liftZ q)) ≠ ⊤ := by
      change LiftedFunctionL g2 (- -(liftZ q)) ≠ ⊤; rw [neg_neg, lift_eval]; exact hq
    have h := hmaxU.2 (-(liftZ q)) hq'
    have eq1 : iv U (-(liftZ q)) = iv g2 q := by
      show iv G2 (- -(liftZ q)) = iv g2 q
      rw [neg_neg]; exact iv_congr (lift_eval g2 q)
    have eq0 : iv U (-Z2) = iv g2 p2s := by
      show iv G2 (- -Z2) = iv g2 p2s
      rw [neg_neg, hivZ2]
    have id1 : idot (-y) (-(liftZ q)) = idot (fun v => y (some v)) q := by
      rw [← idot_lift hsum_y q]; simp [idot]
    have id2 : idot (-y) (-Z2) = idot (fun v => y (some v)) p2s := by
      rw [← idot_lift hsum_y p2s]; simp [idot, Z2]
    rw [id1, id2, eq1, eq0] at h
    exact h

theorem sep_disjoint {g1 g2 : (V → ℤ) → WithTop ℝ}
    (hg1 : LNaturalConvex g1) (hg2 : LNaturalConvex g2)
    {p1_0 p2_0 : V → ℤ} (hp1_0 : g1 p1_0 ≠ ⊤) (hp2_0 : g2 p2_0 ≠ ⊤)
    {p0 : V → ℤ} (hdisj : ∀ p1 p2 : V → ℤ, p0 = p1 + p2 → g1 p1 = ⊤ ∨ g2 p2 = ⊤) :
    ∃ d : V → ℤ, ∀ p1 p2 : V → ℤ, g1 p1 ≠ ⊤ → g2 p2 ≠ ⊤ →
      idot d (p1 + p2) ≤ idot d p0 - 1 := by
  let G1 := LiftedFunctionL g1
  let G2 := LiftedFunctionL g2
  have hs1 : SBF G1 := hg1.1
  have hs2 : SBF G2 := hg2.1
  have hG1_tr : ∀ W, G1 (W + 1) = G1 W := lift_tr g1
  have hG2_tr : ∀ W, G2 (W + 1) = G2 W := lift_tr g2
  let P0 := liftZ p0
  let D1 : Set (Option V → ℤ) := {W | G2 (P0 - W) ≠ ⊤}
  let D2 : Set (Option V → ℤ) := {W | G1 W ≠ ⊤}
  have hD1 : DiscreteConvex.LConvexSets.LConvexSet D1 := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · have ha' : G2 (P0 - a) ≠ ⊤ := ha
      have hb' : G2 (P0 - b) ≠ ⊤ := hb
      have hs := hs2 (P0 - a) (P0 - b)
      have e_sup : (P0 - a) ⊔ (P0 - b) = P0 - (a ⊓ b) := by
        funext o; show max (P0 o - a o) (P0 o - b o) = P0 o - min (a o) (b o); omega
      have e_inf : (P0 - a) ⊓ (P0 - b) = P0 - (a ⊔ b) := by
        funext o; show min (P0 o - a o) (P0 o - b o) = P0 o - max (a o) (b o); omega
      rw [e_sup, e_inf] at hs
      have hfin := ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨ha', hb'⟩) hs
      exact ⟨(WithTop.add_ne_top.1 hfin).2, (WithTop.add_ne_top.1 hfin).1⟩
    · have ha' : G2 (P0 - a) ≠ ⊤ := ha
      refine ⟨?_, ?_⟩
      · show G2 (P0 - (fun o => a o + 1)) ≠ ⊤
        have e : P0 - a = (P0 - fun o => a o + 1) + 1 := by funext o; simp; ring
        rw [e, hG2_tr] at ha'; exact ha'
      · show G2 (P0 - (fun o => a o - 1)) ≠ ⊤
        have e : P0 - (fun o => a o - 1) = (P0 - a) + 1 := by funext o; simp; ring
        rw [e, hG2_tr]; exact ha'
  have hD2 : DiscreteConvex.LConvexSets.LConvexSet D2 := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · have hs := hs1 a b
      have hfin := ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨ha, hb⟩) hs
      exact WithTop.add_ne_top.1 hfin
    · have ha' : G1 a ≠ ⊤ := ha
      refine ⟨?_, ?_⟩
      · show G1 (a + 1) ≠ ⊤; rw [hG1_tr]; exact ha'
      · show G1 (fun o => a o - 1) ≠ ⊤
        have e : a = (fun o => a o - 1) + 1 := by funext o; simp
        rw [e, hG1_tr] at ha'; exact ha'
  have hDdisj : D1 ∩ D2 = ∅ := by
    ext W
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h2, h1⟩
    let p1 : V → ℤ := fun v => W (some v) - W none
    let p2 : V → ℤ := fun v => (P0 - W) (some v) - (P0 - W) none
    have hp : p0 = p1 + p2 := by
      funext v; simp [p1, p2, P0, liftZ]
    rcases hdisj p1 p2 hp with ht1 | ht2
    · exact h1 ht1
    · exact h2 ht2
  obtain ⟨Y, -, hsep⟩ :=
    DiscreteConvex.LConvexSets.discrete_separation_lconvex D1 D2 hD1 hD2 hDdisj
  have hle : ∀ W1 ∈ D2, ∀ W2 ∈ D1, idot Y W1 + 1 ≤ idot Y W2 := by
    intro W1 hW1 W2 hW2
    have h1 : (((∑ o, (Y o : ℝ) * (W1 o : ℝ) : ℝ) : EReal)) ≤
        sSup ((fun p : Option V → ℤ => ((∑ v, (Y v : ℝ) * (p v : ℝ) : ℝ) : EReal)) '' D2) :=
      le_sSup ⟨W1, hW1, rfl⟩
    have h2 : sInf ((fun p : Option V → ℤ => ((∑ v, (Y v : ℝ) * (p v : ℝ) : ℝ) : EReal)) '' D1) ≤
        (((∑ o, (Y o : ℝ) * (W2 o : ℝ) : ℝ) : EReal)) :=
      sInf_le ⟨W2, hW2, rfl⟩
    have h3 : (((∑ o, (Y o : ℝ) * (W1 o : ℝ) : ℝ) : EReal)) + 1 ≤
        (((∑ o, (Y o : ℝ) * (W2 o : ℝ) : ℝ) : EReal)) :=
      (add_le_add_left h1 1).trans (hsep.trans h2)
    rw [dot_eq, dot_eq] at h3
    change (((idot Y W1 : ℤ) : ℝ) : EReal) + ((1 : ℝ) : EReal) ≤
      (((idot Y W2 : ℤ) : ℝ) : EReal) at h3
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    have h4 : ((idot Y W1 + 1 : ℤ) : ℝ) ≤ ((idot Y W2 : ℤ) : ℝ) := by push_cast; exact h3
    exact_mod_cast h4
  have hW1_0 : liftZ p1_0 ∈ D2 := by
    change LiftedFunctionL g1 (liftZ p1_0) ≠ ⊤; rw [lift_eval]; exact hp1_0
  have hW2_0 : P0 - liftZ p2_0 ∈ D1 := by
    change LiftedFunctionL g2 (P0 - (P0 - liftZ p2_0)) ≠ ⊤
    rw [sub_sub_cancel, lift_eval]; exact hp2_0
  have hsumY : ∑ o : Option V, Y o = 0 := by
    let C : ℤ := idot Y (P0 - liftZ p2_0) - idot Y (liftZ p1_0)
    by_contra hne
    have hshift : ∀ k : ℕ, (fun o => liftZ p1_0 o + (k : ℤ)) ∈ D2 ∧
        (fun o => liftZ p1_0 o - (k : ℤ)) ∈ D2 := by
      intro k
      induction k with
      | zero => simp [hW1_0]
      | succ k ih =>
        refine ⟨?_, ?_⟩
        · convert (hD2.2 _ ih.1).1 using 2; push_cast; ring
        · convert (hD2.2 _ ih.2).2 using 2; push_cast; ring
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · set k := C.natAbs + 1
      have hk := hle _ (hshift k).2 _ hW2_0
      have hid : idot Y (fun o => liftZ p1_0 o - (k : ℤ)) =
          idot Y (liftZ p1_0) - (k : ℤ) * ∑ o, Y o := by
        simp only [idot, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        refine congrArg (∑ x, Y x * liftZ p1_0 x - ·) (Finset.sum_congr rfl fun o _ => mul_comm _ _)
      rw [hid] at hk
      have : (k : ℤ) * (-(∑ o, Y o)) ≥ (k : ℤ) * 1 :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      have : C ≤ (C.natAbs : ℤ) := Int.le_natAbs
      dsimp [C, k] at hk this ⊢
      nlinarith
    · set k := C.natAbs + 1
      have hk := hle _ (hshift k).1 _ hW2_0
      have hid : idot Y (fun o => liftZ p1_0 o + (k : ℤ)) =
          idot Y (liftZ p1_0) + (k : ℤ) * ∑ o, Y o := by
        simp only [idot, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        refine congrArg (∑ x, Y x * liftZ p1_0 x + ·) (Finset.sum_congr rfl fun o _ => mul_comm _ _)
      rw [hid] at hk
      have : (k : ℤ) * (∑ o, Y o) ≥ (k : ℤ) * 1 :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      have : C ≤ (C.natAbs : ℤ) := Int.le_natAbs
      dsimp [C, k] at hk this ⊢
      nlinarith
  refine ⟨fun v => Y (some v), fun p1 p2 hp1 hp2 => ?_⟩
  have hm1 : liftZ p1 ∈ D2 := by
    change LiftedFunctionL g1 (liftZ p1) ≠ ⊤; rw [lift_eval]; exact hp1
  have hm2 : P0 - liftZ p2 ∈ D1 := by
    change LiftedFunctionL g2 (P0 - (P0 - liftZ p2)) ≠ ⊤
    rw [sub_sub_cancel, lift_eval]; exact hp2
  have h := hle _ hm1 _ hm2
  have e2 : idot Y (P0 - liftZ p2) = idot Y P0 - idot Y (liftZ p2) := by
    simp only [idot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [e2, idot_lift hsumY p1, idot_lift hsumY p0, idot_lift hsumY p2] at h
  rw [idot_add_right]
  omega

lemma lnat_trf (g : (V → ℤ) → WithTop ℝ) : TRF (LiftedFunctionL g) :=
  ⟨0, fun W => by simp [lift_tr]⟩

lemma lnat_neg {g : (V → ℤ) → WithTop ℝ} (hg : LNaturalConvex g) :
    LNaturalConvex (fun p => g (-p)) := by
  refine ⟨fun P Q => ?_, lnat_trf _⟩
  have hs := hg.1 (-P) (-Q)
  have e1 : LiftedFunctionL (fun p => g (-p)) (P ⊔ Q) = LiftedFunctionL g ((-P) ⊓ (-Q)) := by
    show g (-(fun v => (P ⊔ Q) (some v) - (P ⊔ Q) none)) =
      g (fun v => (-P ⊓ -Q) (some v) - (-P ⊓ -Q) none)
    congr 1; funext v
    show -(max (P (some v)) (Q (some v)) - max (P none) (Q none)) =
      min (-P (some v)) (-Q (some v)) - min (-P none) (-Q none)
    omega
  have e2 : LiftedFunctionL (fun p => g (-p)) (P ⊓ Q) = LiftedFunctionL g ((-P) ⊔ (-Q)) := by
    show g (-(fun v => (P ⊓ Q) (some v) - (P ⊓ Q) none)) =
      g (fun v => (-P ⊔ -Q) (some v) - (-P ⊔ -Q) none)
    congr 1; funext v
    show -(min (P (some v)) (Q (some v)) - min (P none) (Q none)) =
      max (-P (some v)) (-Q (some v)) - max (-P none) (-Q none)
    omega
  have e3 : LiftedFunctionL (fun p => g (-p)) P = LiftedFunctionL g (-P) := by
    show g (-(fun v => P (some v) - P none)) = g (fun v => (-P) (some v) - (-P) none)
    congr 1; funext v
    show -(P (some v) - P none) = -P (some v) - -P none
    omega
  have e4 : LiftedFunctionL (fun p => g (-p)) Q = LiftedFunctionL g (-Q) := by
    show g (-(fun v => Q (some v) - Q none)) = g (fun v => (-Q) (some v) - (-Q) none)
    congr 1; funext v
    show -(Q (some v) - Q none) = -Q (some v) - -Q none
    omega
  rw [ge_iff_le, e1, e2, e3, e4, add_comm (LiftedFunctionL g ((-P) ⊓ (-Q)))]
  exact hs

lemma lnat_shift {g : (V → ℤ) → WithTop ℝ} (hg : LNaturalConvex g) (p0 : V → ℤ) :
    LNaturalConvex (fun p => g (p0 + p)) := by
  refine ⟨fun P Q => ?_, lnat_trf _⟩
  let P0 := liftZ p0
  have hs := hg.1 (P0 + P) (P0 + Q)
  have e1 : LiftedFunctionL (fun p => g (p0 + p)) (P ⊔ Q) = LiftedFunctionL g ((P0 + P) ⊔ (P0 + Q)) := by
    show g (p0 + fun v => (P ⊔ Q) (some v) - (P ⊔ Q) none) =
      g (fun v => ((P0 + P) ⊔ (P0 + Q)) (some v) - ((P0 + P) ⊔ (P0 + Q)) none)
    congr 1; funext v
    show p0 v + (max (P (some v)) (Q (some v)) - max (P none) (Q none)) =
      max (p0 v + P (some v)) (p0 v + Q (some v)) - max (0 + P none) (0 + Q none)
    omega
  have e2 : LiftedFunctionL (fun p => g (p0 + p)) (P ⊓ Q) = LiftedFunctionL g ((P0 + P) ⊓ (P0 + Q)) := by
    show g (p0 + fun v => (P ⊓ Q) (some v) - (P ⊓ Q) none) =
      g (fun v => ((P0 + P) ⊓ (P0 + Q)) (some v) - ((P0 + P) ⊓ (P0 + Q)) none)
    congr 1; funext v
    show p0 v + (min (P (some v)) (Q (some v)) - min (P none) (Q none)) =
      min (p0 v + P (some v)) (p0 v + Q (some v)) - min (0 + P none) (0 + Q none)
    omega
  have e3 : LiftedFunctionL (fun p => g (p0 + p)) P = LiftedFunctionL g (P0 + P) := by
    show g (p0 + fun v => P (some v) - P none) = g (fun v => (P0 + P) (some v) - (P0 + P) none)
    congr 1; funext v
    show p0 v + (P (some v) - P none) = (p0 v + P (some v)) - (0 + P none)
    omega
  have e4 : LiftedFunctionL (fun p => g (p0 + p)) Q = LiftedFunctionL g (P0 + Q) := by
    show g (p0 + fun v => Q (some v) - Q none) = g (fun v => (P0 + Q) (some v) - (P0 + Q) none)
    congr 1; funext v
    show p0 v + (Q (some v) - Q none) = (p0 v + Q (some v)) - (0 + Q none)
    omega
  rw [ge_iff_le, e1, e2, e3, e4]
  exact hs

lemma subgrad_single {g : (V → ℤ) → WithTop ℝ} (hg : LNaturalConvex g) (hgZ : IsIntegerValuedFn g)
    {p1 : V → ℤ} (hp1 : g p1 ≠ ⊤) : ∃ x : V → ℤ, IsMaxZ g x p1 := by
  let δ0 : (V → ℤ) → WithTop ℝ := fun q => if q = 0 then (0 : WithTop ℝ) else ⊤
  have hδ0_lnat : LNaturalConvex δ0 := by
    refine ⟨fun P Q => ?_, lnat_trf _⟩
    change δ0 (fun v => (P ⊔ Q) (some v) - (P ⊔ Q) none) +
        δ0 (fun v => (P ⊓ Q) (some v) - (P ⊓ Q) none) ≤
      δ0 (fun v => P (some v) - P none) + δ0 (fun v => Q (some v) - Q none)
    by_cases hP : (fun v => P (some v) - P none) = 0
    · by_cases hQ : (fun v => Q (some v) - Q none) = 0
      · have hPQ_sup : (fun v => (P ⊔ Q) (some v) - (P ⊔ Q) none) = 0 := by
          funext v
          have hPv : P (some v) - P none = 0 := congrFun hP v
          have hQv : Q (some v) - Q none = 0 := congrFun hQ v
          show max (P (some v)) (Q (some v)) - max (P none) (Q none) = 0
          omega
        have hPQ_inf : (fun v => (P ⊓ Q) (some v) - (P ⊓ Q) none) = 0 := by
          funext v
          have hPv : P (some v) - P none = 0 := congrFun hP v
          have hQv : Q (some v) - Q none = 0 := congrFun hQ v
          show min (P (some v)) (Q (some v)) - min (P none) (Q none) = 0
          omega
        rw [hP, hQ, hPQ_sup, hPQ_inf]
      · have hQ_top : δ0 (fun v => Q (some v) - Q none) = ⊤ := if_neg hQ
        rw [hQ_top, add_top]
        exact le_top
    · have hP_top : δ0 (fun v => P (some v) - P none) = ⊤ := if_neg hP
      rw [hP_top, top_add]
      exact le_top
  have hδ0Z : IsIntegerValuedFn δ0 := by
    intro q
    dsimp [δ0]
    split_ifs
    · exact Or.inr ⟨0, by simp⟩
    · exact Or.inl rfl
  have h0_ne : δ0 0 ≠ ⊤ := by simp [δ0]
  obtain ⟨x, hx, -⟩ := subgrad_at_min hg hδ0_lnat hgZ hδ0Z (p0 := p1) (p1s := p1) (p2s := 0)
    (by simp) hp1 h0_ne (by
      intro q1 q2 hq hq1 hq2
      have hq2_zero : q2 = 0 := by
        by_contra hne
        exact hq2 (if_neg hne)
      subst hq2_zero
      have hq1_eq : q1 = p1 := by simpa using hq.symm
      subst hq1_eq
      exact le_rfl)
  exact ⟨x, hx⟩

end LiftSubgrad

section Dist1Bound
variable {V : Type*} [Fintype V] [DecidableEq V]

def dist1 (z w : V → ℤ) : ℕ := ∑ v : V, (z v - w v).natAbs

lemma dist1_self (z : V → ℤ) : dist1 z z = 0 := by
  simp [dist1]

lemma eq_of_dist1_eq_zero {z w : V → ℤ} (h : dist1 z w = 0) : z = w := by
  unfold dist1 at h
  rw [Finset.sum_eq_zero_iff] at h
  funext v
  have hv := h v (Finset.mem_univ v)
  omega

lemma exists_ne_of_dist1_pos {z w : V → ℤ} (h : 0 < dist1 z w) : ∃ v : V, z v ≠ w v := by
  by_contra hall
  push_neg at hall
  have hzw : z = w := funext hall
  rw [hzw, dist1_self] at h
  exact lt_irrefl 0 h

lemma sbf_cut_nonneg {g0 : (V → ℤ) → WithTop ℝ} (hg0 : LNaturalConvex g0)
    (z : V → ℤ) {c : ℤ} (hc : 0 ≤ c) :
    g0 (fun v => max (z v - c) 0) + g0 (fun v => min (z v) c) ≤ g0 z + g0 0 := by
  let P : Option V → ℤ := liftZ z
  let Q : Option V → ℤ := fun _ => c
  have hs := hg0.1 P Q
  have e1 : LiftedFunctionL g0 (P ⊔ Q) = g0 (fun v => max (z v - c) 0) := by
    unfold LiftedFunctionL
    congr 1; funext v
    show max (z v) c - max 0 c = max (z v - c) 0
    omega
  have e2 : LiftedFunctionL g0 (P ⊓ Q) = g0 (fun v => min (z v) c) := by
    unfold LiftedFunctionL
    congr 1; funext v
    show min (z v) c - min 0 c = min (z v) c
    omega
  have e3 : LiftedFunctionL g0 P = g0 z := lift_eval g0 z
  have e4 : LiftedFunctionL g0 Q = g0 0 := by
    unfold LiftedFunctionL
    congr 1; funext v; simp [Q]
  rw [ge_iff_le, e1, e2, e3, e4] at hs
  exact hs

lemma dist1_nonneg_bound {g0 k0 : (V → ℤ) → WithTop ℝ}
    (hg0 : LNaturalConvex g0) (hk0 : LNaturalConvex k0)
    (hg0_0 : g0 0 ≠ ⊤) (hk0_0 : k0 0 ≠ ⊤)
    (hge0 : ∀ p : V → ℤ, g0 p + k0 p ≥ 0) :
    ∃ M_pos : ℝ, 0 ≤ M_pos ∧
      ∀ (n : ℕ) (z w : V → ℤ), dist1 z w = n → (∀ v, 0 ≤ z v) → (∀ v, 0 ≤ w v) →
        g0 z ≠ ⊤ → k0 w ≠ ⊤ →
        0 ≤ (g0 z).untopD 0 + (k0 w).untopD 0 + M_pos * (n : ℝ) := by
  let Box01 : Finset (V → ℤ) := Fintype.piFinset (fun _ : V => Finset.Icc (0 : ℤ) 1)
  have hBox01 : ∀ y : V → ℤ, (∀ v, 0 ≤ y v ∧ y v ≤ 1) → y ∈ Box01 := by
    intro y hy
    rw [Fintype.mem_piFinset]
    intro v
    rw [Finset.mem_Icc]
    exact hy v
  let c0 : ℝ := |(g0 0).untopD 0| + |(k0 0).untopD 0|
  let B01 : ℝ := ∑ u ∈ Box01, (|(g0 u).untopD 0| + |(k0 u).untopD 0|)
  have hc0_nn : 0 ≤ c0 := by positivity
  have hB01_nn : 0 ≤ B01 := Finset.sum_nonneg fun u _ => by positivity
  have hBox_bound : ∀ y y' : V → ℤ, (∀ v, 0 ≤ y v ∧ y v ≤ 1) → (∀ v, 0 ≤ y' v ∧ y' v ≤ 1) →
      -((g0 y).untopD 0 + (k0 y').untopD 0) ≤ 2 * B01 := by
    intro y y' hy hy'
    have hy_le : |(g0 y).untopD 0| + |(k0 y).untopD 0| ≤ B01 :=
      Finset.single_le_sum (f := fun u => |(g0 u).untopD 0| + |(k0 u).untopD 0|)
        (fun u _ => by positivity) (hBox01 y hy)
    have hy'_le : |(g0 y').untopD 0| + |(k0 y').untopD 0| ≤ B01 :=
      Finset.single_le_sum (f := fun u => |(g0 u).untopD 0| + |(k0 u).untopD 0|)
        (fun u _ => by positivity) (hBox01 y' hy')
    have h1 := neg_abs_le ((g0 y).untopD 0)
    have h2 := neg_abs_le ((k0 y').untopD 0)
    have h3 := abs_nonneg ((k0 y).untopD 0)
    have h4 := abs_nonneg ((g0 y').untopD 0)
    linarith
  let M_pos : ℝ := 2 * c0 + 2 * B01
  have hM_pos_nn : 0 ≤ M_pos := by positivity
  refine ⟨M_pos, hM_pos_nn, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z w hdist hz_nn hw_nn hgz hkw
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · have hzw : z = w := eq_of_dist1_eq_zero hdist
      subst hzw
      have h0 := hge0 z
      rw [← coe_untopD hgz, ← coe_untopD hkw, ← WithTop.coe_add, ge_iff_le,
        ← WithTop.coe_zero, WithTop.coe_le_coe] at h0
      simp only [Nat.cast_zero, mul_zero, add_zero]
      exact h0
    · obtain ⟨v_ne, hv_ne⟩ := exists_ne_of_dist1_pos (hdist.symm ▸ hn_pos)
      let S_ne : Finset V := Finset.univ.filter (fun v : V => z v ≠ w v)
      have hS_ne : S_ne.Nonempty := ⟨v_ne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_ne⟩⟩
      let c : ℤ := S_ne.inf' hS_ne (fun v => min (z v) (w v))
      have hc_nn : 0 ≤ c := by
        rw [Finset.le_inf'_iff]
        intro v _
        exact le_min (hz_nn v) (hw_nn v)
      have hc_le : ∀ v : V, z v ≠ w v → c ≤ z v ∧ c ≤ w v := by
        intro v hv
        have hmem : v ∈ S_ne := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
        have hle : c ≤ min (z v) (w v) := Finset.inf'_le (fun u => min (z u) (w u)) hmem
        exact ⟨hle.trans (min_le_left _ _), hle.trans (min_le_right _ _)⟩
      obtain ⟨v0, hv0_mem, hv0_eq⟩ := Finset.exists_mem_eq_inf' hS_ne (fun v => min (z v) (w v))
      have hv0_ne : z v0 ≠ w v0 := (Finset.mem_filter.mp hv0_mem).2
      have hv0_min : min (z v0) (w v0) = c := hv0_eq.symm
      let z_c : V → ℤ := fun v => max (z v - c) 0
      let y_c : V → ℤ := fun v => min (z v) c
      let w_c : V → ℤ := fun v => max (w v - c) 0
      let y'_c : V → ℤ := fun v => min (w v) c
      obtain ⟨hgz_c, hgy_c, hle_zc⟩ := add_untopD_le hgz hg0_0 (sbf_cut_nonneg hg0 z hc_nn)
      obtain ⟨hkw_c, hky'_c, hle_wc⟩ := add_untopD_le hkw hk0_0 (sbf_cut_nonneg hk0 w hc_nn)
      have hy_eq : y_c = y'_c := by
        funext v
        dsimp [y_c, y'_c]
        by_cases hv : z v = w v
        · rw [hv]
        · obtain ⟨hcz, hcw⟩ := hc_le v hv
          omega
      have hy_sum_nn : 0 ≤ (g0 y_c).untopD 0 + (k0 y'_c).untopD 0 := by
        change g0 y_c ≠ ⊤ at hgy_c
        change k0 y'_c ≠ ⊤ at hky'_c
        rw [← hy_eq] at hky'_c ⊢
        have h0 := hge0 y_c
        rw [← coe_untopD hgy_c, ← coe_untopD hky'_c, ← WithTop.coe_add, ge_iff_le,
          ← WithTop.coe_zero, WithTop.coe_le_coe] at h0
        exact h0
      have hzc_wc_bound : (g0 z_c).untopD 0 + (k0 w_c).untopD 0 ≤
          (g0 z).untopD 0 + (k0 w).untopD 0 + c0 := by
        have h1 := le_abs_self ((g0 0).untopD 0)
        have h2 := le_abs_self ((k0 0).untopD 0)
        dsimp [c0]
        linarith
      have hdist_zc : dist1 z_c w_c = n := by
        rw [← hdist]
        unfold dist1
        refine Finset.sum_congr rfl fun v _ => ?_
        dsimp [z_c, w_c]
        by_cases hv : z v = w v
        · simp [hv]
        · obtain ⟨hcz, hcw⟩ := hc_le v hv
          congr 1
          omega
      let z_1 : V → ℤ := fun v => max (z_c v - 1) 0
      let y_1 : V → ℤ := fun v => min (z_c v) 1
      let w_1 : V → ℤ := fun v => max (w_c v - 1) 0
      let y'_1 : V → ℤ := fun v => min (w_c v) 1
      have h1_nn : (0 : ℤ) ≤ 1 := by omega
      obtain ⟨hgz_1, hgy_1, hle_z1⟩ := add_untopD_le hgz_c hg0_0 (sbf_cut_nonneg hg0 z_c h1_nn)
      obtain ⟨hkw_1, hky'_1, hle_w1⟩ := add_untopD_le hkw_c hk0_0 (sbf_cut_nonneg hk0 w_c h1_nn)
      have hy1_box : ∀ v, 0 ≤ y_1 v ∧ y_1 v ≤ 1 := by
        intro v; dsimp [y_1, z_c]; omega
      have hy'1_box : ∀ v, 0 ≤ y'_1 v ∧ y'_1 v ≤ 1 := by
        intro v; dsimp [y'_1, w_c]; omega
      have hy1_bound := hBox_bound y_1 y'_1 hy1_box hy'1_box
      have hz1_w1_bound : (g0 z_1).untopD 0 + (k0 w_1).untopD 0 ≤
          (g0 z).untopD 0 + (k0 w).untopD 0 + M_pos := by
        have h1 := le_abs_self ((g0 0).untopD 0)
        have h2 := le_abs_self ((k0 0).untopD 0)
        dsimp [M_pos, c0] at hzc_wc_bound ⊢
        linarith
      have hdist_split : dist1 z_c w_c = dist1 z_1 w_1 + dist1 y_1 y'_1 := by
        unfold dist1
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        dsimp [z_1, w_1, y_1, y'_1, z_c, w_c]
        omega
      have hy1_pos : 1 ≤ dist1 y_1 y'_1 := by
        have hv0_term : 1 ≤ (y_1 v0 - y'_1 v0).natAbs := by
          dsimp [y_1, y'_1, z_c, w_c]
          obtain ⟨hcz0, hcw0⟩ := hc_le v0 hv0_ne
          omega
        exact hv0_term.trans (Finset.single_le_sum (f := fun v => (y_1 v - y'_1 v).natAbs)
          (fun v _ => Nat.zero_le _) (Finset.mem_univ v0))
      have hdist_z1_lt : dist1 z_1 w_1 < n := by
        omega
      have hz1_nn : ∀ v, 0 ≤ z_1 v := fun v => le_max_right _ _
      have hw1_nn : ∀ v, 0 ≤ w_1 v := fun v => le_max_right _ _
      have h_ih := ih (dist1 z_1 w_1) hdist_z1_lt z_1 w_1 rfl hz1_nn hw1_nn hgz_1 hkw_1
      have hdist_le : (dist1 z_1 w_1 : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast (by omega : dist1 z_1 w_1 + 1 ≤ n)
      have hmul_le : M_pos * (dist1 z_1 w_1 : ℝ) + M_pos ≤ M_pos * (n : ℝ) := by
        nlinarith
      linarith

lemma dist1_gen_bound {g0 k0 : (V → ℤ) → WithTop ℝ}
    (hg0 : LNaturalConvex g0) (hk0 : LNaturalConvex k0)
    (hg0_0 : g0 0 ≠ ⊤) (hk0_0 : k0 0 ≠ ⊤)
    (hge0 : ∀ p : V → ℤ, g0 p + k0 p ≥ 0) :
    ∃ M_tot : ℝ, 0 ≤ M_tot ∧
      ∀ z w : V → ℤ, g0 z ≠ ⊤ → k0 w ≠ ⊤ →
        0 ≤ (g0 z).untopD 0 + (k0 w).untopD 0 + M_tot * (dist1 z w : ℝ) := by
  obtain ⟨M_pos, hM_pos_nn, hM_pos⟩ := dist1_nonneg_bound hg0 hk0 hg0_0 hk0_0 hge0
  let g0_neg : (V → ℤ) → WithTop ℝ := fun p => g0 (-p)
  let k0_neg : (V → ℤ) → WithTop ℝ := fun p => k0 (-p)
  have hg0_neg : LNaturalConvex g0_neg := lnat_neg hg0
  have hk0_neg : LNaturalConvex k0_neg := lnat_neg hk0
  have hg0_neg_0 : g0_neg 0 ≠ ⊤ := by show g0 (-0) ≠ ⊤; simpa using hg0_0
  have hk0_neg_0 : k0_neg 0 ≠ ⊤ := by show k0 (-0) ≠ ⊤; simpa using hk0_0
  have hge0_neg : ∀ p : V → ℤ, g0_neg p + k0_neg p ≥ 0 := fun p => hge0 (-p)
  obtain ⟨M_neg, hM_neg_nn, hM_neg⟩ := dist1_nonneg_bound hg0_neg hk0_neg hg0_neg_0 hk0_neg_0 hge0_neg
  let c0 : ℝ := |(g0 0).untopD 0| + |(k0 0).untopD 0|
  let M_tot : ℝ := max M_pos M_neg + c0
  have hM_tot_nn : 0 ≤ M_tot := by
    have : 0 ≤ c0 := by positivity
    linarith [le_max_left M_pos M_neg]
  refine ⟨M_tot, hM_tot_nn, fun z w hgz hkw => ?_⟩
  by_cases hzw : z = w
  · subst hzw
    have h0 := hge0 z
    rw [← coe_untopD hgz, ← coe_untopD hkw, ← WithTop.coe_add, ge_iff_le,
      ← WithTop.coe_zero, WithTop.coe_le_coe] at h0
    rw [dist1_self]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    exact h0
  · have hdist_ge_1 : 1 ≤ dist1 z w := by
      by_contra hlt
      have h0 : dist1 z w = 0 := by omega
      exact hzw (eq_of_dist1_eq_zero h0)
    have h0_nn : (0 : ℤ) ≤ 0 := le_rfl
    have hcut_g := sbf_cut_nonneg hg0 z h0_nn
    have hcut_k := sbf_cut_nonneg hk0 w h0_nn
    simp only [sub_zero] at hcut_g hcut_k
    let z_p : V → ℤ := fun v => max (z v) 0
    let z_m : V → ℤ := fun v => max (-z v) 0
    let w_p : V → ℤ := fun v => max (w v) 0
    let w_m : V → ℤ := fun v => max (-w v) 0
    obtain ⟨hgz_p, hgz_inf, hle_z⟩ := add_untopD_le hgz hg0_0 hcut_g
    obtain ⟨hkw_p, hkw_inf, hle_w⟩ := add_untopD_le hkw hk0_0 hcut_k
    have hzm_eq : (fun v => min (z v) 0) = -z_m := by
      funext v; dsimp [z_m]; omega
    have hwm_eq : (fun v => min (w v) 0) = -w_m := by
      funext v; dsimp [w_m]; omega
    have hgz_m : g0_neg z_m ≠ ⊤ := by
      change g0 (-z_m) ≠ ⊤; rwa [← hzm_eq]
    have hkw_m : k0_neg w_m ≠ ⊤ := by
      change k0 (-w_m) ≠ ⊤; rwa [← hwm_eq]
    have h_pos := hM_pos (dist1 z_p w_p) z_p w_p rfl (fun v => le_max_right _ _)
      (fun v => le_max_right _ _) hgz_p hkw_p
    have h_neg := hM_neg (dist1 z_m w_m) z_m w_m rfl (fun v => le_max_right _ _)
      (fun v => le_max_right _ _) hgz_m hkw_m
    have hgz_m_val : (g0_neg z_m).untopD 0 = (g0 (fun v => min (z v) 0)).untopD 0 := by
      change (g0 (-z_m)).untopD 0 = _; rw [hzm_eq]
    have hkw_m_val : (k0_neg w_m).untopD 0 = (k0 (fun v => min (w v) 0)).untopD 0 := by
      change (k0 (-w_m)).untopD 0 = _; rw [hwm_eq]
    rw [hgz_m_val] at h_neg
    rw [hkw_m_val] at h_neg
    have hdist_split : dist1 z w = dist1 z_p w_p + dist1 z_m w_m := by
      unfold dist1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      dsimp [z_p, w_p, z_m, w_m]
      omega
    have hdist_split_R : (dist1 z w : ℝ) = (dist1 z_p w_p : ℝ) + (dist1 z_m w_m : ℝ) := by
      exact_mod_cast hdist_split
    have h1 := le_abs_self ((g0 0).untopD 0)
    have h2 := le_abs_self ((k0 0).untopD 0)
    have hMp_le : M_pos ≤ max M_pos M_neg := le_max_left _ _
    have hMn_le : M_neg ≤ max M_pos M_neg := le_max_right _ _
    have hdp_nn : (0 : ℝ) ≤ (dist1 z_p w_p : ℝ) := Nat.cast_nonneg _
    have hdn_nn : (0 : ℝ) ≤ (dist1 z_m w_m : ℝ) := Nat.cast_nonneg _
    have hd_ge_1 : (1 : ℝ) ≤ (dist1 z w : ℝ) := by exact_mod_cast hdist_ge_1
    have hc0_nn : 0 ≤ c0 := by positivity
    have hmul_p : M_pos * (dist1 z_p w_p : ℝ) ≤ max M_pos M_neg * (dist1 z_p w_p : ℝ) :=
      mul_le_mul_of_nonneg_right hMp_le hdp_nn
    have hmul_n : M_neg * (dist1 z_m w_m : ℝ) ≤ max M_pos M_neg * (dist1 z_m w_m : ℝ) :=
      mul_le_mul_of_nonneg_right hMn_le hdn_nn
    have hc0_mul : c0 ≤ c0 * (dist1 z w : ℝ) := by nlinarith
    change (g0 z_p).untopD 0 + (g0 (fun v => min (z v) 0)).untopD 0 ≤
      (g0 z).untopD 0 + (g0 0).untopD 0 at hle_z
    change (k0 w_p).untopD 0 + (k0 (fun v => min (w v) 0)).untopD 0 ≤
      (k0 w).untopD 0 + (k0 0).untopD 0 at hle_w
    have h_expand : M_tot * (dist1 z w : ℝ) =
        max M_pos M_neg * (dist1 z_p w_p : ℝ) + max M_pos M_neg * (dist1 z_m w_m : ℝ) +
          c0 * (dist1 z w : ℝ) := by
      dsimp [M_tot]
      rw [hdist_split_R]
      ring
    have hc0_def : c0 = |(g0 0).untopD 0| + |(k0 0).untopD 0| := rfl
    linarith

lemma dist1_bound_from_p0 {g k2 : (V → ℤ) → WithTop ℝ}
    (hg : LNaturalConvex g) (hk2 : LNaturalConvex k2)
    {p0 : V → ℤ} (hp0_g : g p0 ≠ ⊤) (hp0_k : k2 p0 ≠ ⊤)
    (hge : ∀ p : V → ℤ, g p + k2 p ≥ 0) :
    ∃ M_0 : ℝ, 0 ≤ M_0 ∧
      ∀ z w : V → ℤ, g z ≠ ⊤ → k2 w ≠ ⊤ →
        0 ≤ (g z).untopD 0 + (k2 w).untopD 0 + M_0 * (dist1 z w : ℝ) := by
  let g0 : (V → ℤ) → WithTop ℝ := fun p => g (p0 + p)
  let k0 : (V → ℤ) → WithTop ℝ := fun p => k2 (p0 + p)
  have hg0 : LNaturalConvex g0 := lnat_shift hg p0
  have hk0 : LNaturalConvex k0 := lnat_shift hk2 p0
  have hg0_0 : g0 0 ≠ ⊤ := by show g (p0 + 0) ≠ ⊤; simpa using hp0_g
  have hk0_0 : k0 0 ≠ ⊤ := by show k2 (p0 + 0) ≠ ⊤; simpa using hp0_k
  have hge0 : ∀ p : V → ℤ, g0 p + k0 p ≥ 0 := fun p => hge (p0 + p)
  obtain ⟨M_tot, hM_nn, hM⟩ := dist1_gen_bound hg0 hk0 hg0_0 hk0_0 hge0
  refine ⟨M_tot, hM_nn, fun z w hgz hkw => ?_⟩
  have hz_eq : p0 + (z - p0) = z := add_sub_cancel p0 z
  have hw_eq : p0 + (w - p0) = w := add_sub_cancel p0 w
  have h := hM (z - p0) (w - p0) (by show g (p0 + (z - p0)) ≠ ⊤; rwa [hz_eq])
    (by show k2 (p0 + (w - p0)) ≠ ⊤; rwa [hw_eq])
  have hdist_eq : dist1 (z - p0) (w - p0) = dist1 z w := by
    unfold dist1
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1; simp only [Pi.sub_apply]; ring
  change 0 ≤ (g (p0 + (z - p0))).untopD 0 + (k2 (p0 + (w - p0))).untopD 0 +
    M_tot * (dist1 (z - p0) (w - p0) : ℝ) at h
  rwa [hz_eq, hw_eq, hdist_eq] at h

end Dist1Bound

section GreedyRound
variable {V : Type*} [Fintype V] [DecidableEq V]

def IntEmbedL {W : Type*} (S : Set (W → ℤ)) : Set (W → ℝ) :=
  (fun (x : W → ℤ) (v : W) => (x v : ℝ)) '' S

def LConvexSetL {W : Type*} (D : Set (W → ℤ)) : Prop :=
  D.Nonempty ∧
  (∀ p ∈ D, ∀ q ∈ D, (p ⊔ q) ∈ D ∧ (p ⊓ q) ∈ D) ∧
  (∀ p ∈ D, (fun v => p v + 1) ∈ D ∧ (fun v => p v - 1) ∈ D)

def LiftedSetLL (D : Set (V → ℤ)) : Set (Option V → ℤ) :=
  {p | (fun v => p (some v) - p none) ∈ D}

def LNatConvexSetL (D : Set (V → ℤ)) : Prop :=
  LConvexSetL (LiftedSetLL D)

theorem ceil_int_add (n : ℤ) (y : ℝ) (h1 : -1 < y) (h2 : y ≤ 1) :
    ⌈(n : ℝ) + y⌉ = n + if 0 < y then 1 else 0 := by
  rw [Int.ceil_eq_iff]
  split_ifs with h
  · push_cast; constructor <;> linarith
  · push_cast; constructor <;> linarith [not_lt.mp h]

theorem round_hull {ι : Type*} [Fintype ι] :
    ∀ (n : ℕ) (q : ι → ℝ), (Finset.univ.filter (fun i => Int.fract (q i) ≠ 0)).card ≤ n →
      q ∈ convexHull ℝ {x : ι → ℝ | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
        x = fun i => ((⌈q i - θ⌉ : ℤ) : ℝ)} := by
  intro n
  induction n with
  | zero =>
    intro q hq
    apply subset_convexHull
    refine ⟨0, le_refl _, one_pos, ?_⟩
    funext i
    have hf : Int.fract (q i) = 0 := by
      by_contra h
      have hmem : i ∈ Finset.univ.filter (fun i => Int.fract (q i) ≠ 0) := by simp [h]
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hq)] at hmem
      simp at hmem
    have h2 : q i = (⌊q i⌋ : ℝ) := by have := Int.floor_add_fract (q i); linarith
    rw [sub_zero, h2, Int.ceil_intCast]
  | succ n ih =>
    intro q hq
    by_cases hle : (Finset.univ.filter (fun i => Int.fract (q i) ≠ 0)).card ≤ n
    · exact ih q hle
    have hpos : 0 < (Finset.univ.filter (fun i => Int.fract (q i) ≠ 0)).card := by omega
    obtain ⟨i1, hi1⟩ := Finset.card_pos.mp hpos
    have hne : (Finset.univ : Finset ι).Nonempty := ⟨i1, Finset.mem_univ _⟩
    set μ := Finset.univ.sup' hne (fun i => Int.fract (q i)) with hμdef
    have hle_mu : ∀ i, Int.fract (q i) ≤ μ := fun i => Finset.le_sup' (fun i => Int.fract (q i)) (Finset.mem_univ i)
    obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' hne (fun i => Int.fract (q i))
    have hi0' : Int.fract (q i0) = μ := hi0.symm
    have hf1 : Int.fract (q i1) ≠ 0 := (Finset.mem_filter.mp hi1).2
    have hμpos : 0 < μ := lt_of_lt_of_le (lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hf1)) (hle_mu i1)
    have hμlt : μ < 1 := hi0' ▸ Int.fract_lt_one _
    have hμne : μ ≠ 0 := ne_of_gt hμpos
    set A : ι → ℝ := fun i => (⌊q i⌋ : ℝ) + Int.fract (q i) / μ with hA
    have claim1 : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → ∀ i, ⌈A i - θ⌉ = ⌈q i - μ * θ⌉ := by
      intro θ h0 h1 i
      have hf0 := Int.fract_nonneg (q i)
      have hfl := hle_mu i
      have hμθ : μ * θ < μ := by nlinarith
      have e1 : A i - θ = (⌊q i⌋ : ℝ) + (Int.fract (q i) - μ * θ) / μ := by
        simp only [hA]; field_simp; ring
      have e2 : q i - μ * θ = (⌊q i⌋ : ℝ) + (Int.fract (q i) - μ * θ) := by
        have := Int.floor_add_fract (q i); linarith
      rw [e1, e2]
      have hy1 : -1 < (Int.fract (q i) - μ * θ) / μ := by
        rw [lt_div_iff₀ hμpos]; linarith
      have hy2 : (Int.fract (q i) - μ * θ) / μ ≤ 1 := by
        rw [div_le_iff₀ hμpos]; nlinarith
      rw [ceil_int_add _ _ hy1 hy2, ceil_int_add _ _ (by nlinarith) (by nlinarith)]
      have : (0 < (Int.fract (q i) - μ * θ) / μ) ↔ (0 < Int.fract (q i) - μ * θ) :=
        div_pos_iff_of_pos_right hμpos
      simp only [this]
    have claim2 : ∀ i, ⌈q i - μ⌉ = ⌊q i⌋ := by
      intro i
      have hf0 := Int.fract_nonneg (q i)
      have hfl := hle_mu i
      have e2 : q i - μ = (⌊q i⌋ : ℝ) + (Int.fract (q i) - μ) := by
        have := Int.floor_add_fract (q i); linarith
      rw [e2, ceil_int_add _ _ (by linarith) (by linarith)]
      simp [not_lt.mpr (sub_nonpos.mpr hfl)]
    have claim3 : (Finset.univ.filter (fun i => Int.fract (A i) ≠ 0)).card ≤ n := by
      have hsub : Finset.univ.filter (fun i => Int.fract (A i) ≠ 0) ⊂
          Finset.univ.filter (fun i => Int.fract (q i) ≠ 0) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i0, ?_, ?_⟩
          · simp [hi0', hμne]
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
            have : A i0 = ((⌊q i0⌋ + 1 : ℤ) : ℝ) := by
              simp only [hA, hi0', div_self hμne]; push_cast; ring
            rw [this, Int.fract_intCast]
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          intro hq0
          apply hi
          have : A i = ((⌊q i⌋ : ℤ) : ℝ) := by simp [hA, hq0]
          rw [this, Int.fract_intCast]
      have := Finset.card_lt_card hsub
      omega
    have hAmem := ih A claim3
    have hsubset : {x : ι → ℝ | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ x = fun i => ((⌈A i - θ⌉ : ℤ) : ℝ)} ⊆
        {x : ι → ℝ | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ x = fun i => ((⌈q i - θ⌉ : ℤ) : ℝ)} := by
      rintro x ⟨θ, h0, h1, rfl⟩
      refine ⟨μ * θ, by positivity, by nlinarith, ?_⟩
      funext i
      rw [claim1 θ h0 h1 i]
    have hA' := convexHull_mono hsubset hAmem
    have hF : (fun i => ((⌊q i⌋ : ℤ) : ℝ)) ∈ convexHull ℝ
        {x : ι → ℝ | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ x = fun i => ((⌈q i - θ⌉ : ℤ) : ℝ)} := by
      apply subset_convexHull
      refine ⟨μ, hμpos.le, hμlt, ?_⟩
      funext i
      rw [claim2 i]
    have hcomb := convex_convexHull ℝ _ hA' hF hμpos.le (by linarith : (0:ℝ) ≤ 1 - μ)
      (by ring : μ + (1 - μ) = 1)
    convert hcomb using 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hA]
    have := Int.floor_add_fract (q i)
    field_simp
    linarith

theorem lconv_mem {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W] (E : Set (W → ℤ))
    (hE : LConvexSetL E) (p : W → ℝ) (hp : p ∈ convexHull ℝ (IntEmbedL E)) (y : W → ℤ)
    (hy : ∀ a b, ((y b : ℝ) - y a) < p b - p a + 1) : y ∈ E := by
  obtain ⟨hne, hmm, htr⟩ := hE
  have step1 : ∀ a b, ∃ d ∈ E, y b - y a ≤ d b - d a := by
    intro a b
    by_contra hcon
    push_neg at hcon
    have hsub : IntEmbedL E ⊆ {x : W → ℝ | x b - x a ≤ ((y b - y a - 1 : ℤ) : ℝ)} := by
      rintro x ⟨d, hd, rfl⟩
      have := hcon d hd
      simp only [Set.mem_setOf_eq]
      have h' : d b - d a ≤ y b - y a - 1 := by omega
      exact_mod_cast h'
    have hconv : Convex ℝ {x : W → ℝ | x b - x a ≤ ((y b - y a - 1 : ℤ) : ℝ)} := by
      intro x hx z hz α β hα hβ hαβ
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hz ⊢
      have : α * x b + β * z b - (α * x a + β * z a) = α * (x b - x a) + β * (z b - z a) := by ring
      rw [this]
      calc α * (x b - x a) + β * (z b - z a) ≤ α * ((y b - y a - 1 : ℤ) : ℝ) + β * ((y b - y a - 1 : ℤ) : ℝ) := by
            gcongr
        _ = _ := by rw [← add_mul, hαβ, one_mul]
    have := convexHull_min hsub hconv hp
    simp only [Set.mem_setOf_eq] at this
    have h2 := hy a b
    push_cast at this
    linarith
  have step2 : ∀ d ∈ E, ∀ k : ℤ, (fun v => d v + k) ∈ E := by
    intro d hd k
    induction k using Int.induction_on with
    | zero => simpa using hd
    | succ k ih =>
      have := (htr _ ih).1
      convert this using 2 with v
      push_cast; ring
    | pred k ih =>
      have := (htr _ ih).2
      convert this using 2 with v
      push_cast; ring
  have step3 : ∀ a b, ∃ d ∈ E, d a = y a ∧ y b ≤ d b := by
    intro a b
    obtain ⟨d, hd, hdb⟩ := step1 a b
    refine ⟨fun v => d v + (y a - d a), step2 d hd _, by ring, by simp only; omega⟩
  have step4 : ∀ a, ∀ s : Finset W, ∃ e ∈ E, e a = y a ∧ ∀ b ∈ s, y b ≤ e b := by
    intro a s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨d, hd, hda, -⟩ := step3 a a
      exact ⟨d, hd, hda, by simp⟩
    | insert b s hb ih =>
      obtain ⟨e, he, hea, heb⟩ := ih
      obtain ⟨d, hd, hda, hdb⟩ := step3 a b
      refine ⟨fun v => max (e v) (d v), (hmm e he d hd).1, by simp [hea, hda], ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact le_trans hdb (le_max_right _ _)
      · exact le_trans (heb c hc) (le_max_left _ _)
  have step5 : ∀ s : Finset W, ∃ f ∈ E, (∀ v, y v ≤ f v) ∧ ∀ a ∈ s, f a = y a := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨e, he, -, heb⟩ := step4 (Classical.arbitrary W) Finset.univ
      exact ⟨e, he, fun v => heb v (Finset.mem_univ v), by simp⟩
    | insert a s ha ih =>
      obtain ⟨f, hf, hfy, hfa⟩ := ih
      obtain ⟨e, he, hea, heb⟩ := step4 a Finset.univ
      refine ⟨fun v => min (f v) (e v), (hmm f hf e he).2, ?_, ?_⟩
      · intro v; exact le_min (hfy v) (heb v (Finset.mem_univ v))
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · simp only; rw [hea]; exact min_eq_right (hfy c)
        · simp only; rw [hfa c hc]; exact min_eq_left (heb c (Finset.mem_univ c))
  obtain ⟨f, hf, -, hfa⟩ := step5 Finset.univ
  have : f = y := funext fun v => hfa v (Finset.mem_univ v)
  rw [← this]; exact hf

noncomputable def liftLin (V : Type*) : (V → ℝ) →ₗ[ℝ] (Option V → ℝ) where
  toFun x o := Option.elim o 0 x
  map_add' x y := by funext o; cases o <;> simp
  map_smul' c x := by funext o; cases o <;> simp

theorem lnat_mem (D : Set (V → ℤ))
    (hD : LNatConvexSetL D) (x : V → ℝ) (hx : x ∈ convexHull ℝ (IntEmbedL D)) (y : V → ℤ)
    (hb1 : ∀ v, (y v : ℝ) < x v + 1) (hb2 : ∀ v, x v - 1 < (y v : ℝ))
    (hy : ∀ a b, ((y b : ℝ) - y a) < x b - x a + 1) : y ∈ D := by
  have hlift : liftLin V x ∈ convexHull ℝ (IntEmbedL (LiftedSetLL D)) := by
    have h1 : liftLin V x ∈ liftLin V '' convexHull ℝ (IntEmbedL D) := ⟨x, hx, rfl⟩
    rw [LinearMap.image_convexHull] at h1
    refine convexHull_mono ?_ h1
    rintro z ⟨w, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨fun o => Option.elim o 0 d, ?_, ?_⟩
    · show (fun v => d v - 0) ∈ D
      simpa using hd
    · funext o; cases o <;> simp [liftLin]
  have hmem := lconv_mem (LiftedSetLL D) hD (liftLin V x) hlift (fun o => Option.elim o 0 y) (by
    intro a b
    rcases a with _ | a <;> rcases b with _ | b <;> simp [liftLin]
    · linarith [hb1 b]
    · linarith [hb2 a]
    · linarith [hy a b])
  have : (fun v => (fun o => Option.elim o 0 y) (some v) - (fun o => Option.elim o 0 y) none) = y := by
    funext v; simp
  have h' : (fun v => (fun o => Option.elim o 0 y) (some v) - (fun o => Option.elim o 0 y) none) ∈ D :=
    hmem
  rwa [this] at h'

theorem greedy {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) (W : Finset α), W.card ≤ n → ∀ (D : Set (Finset α)) (ρ : Finset α → ℝ)
      (C : Set (Finset α)), (∀ X ∈ D, X ⊆ W) → ∅ ∈ D → W ∈ D →
      (∀ X ∈ D, ∀ Y ∈ D, X ∪ Y ∈ D ∧ X ∩ Y ∈ D) →
      (∀ X ∈ D, ∀ Y ∈ D, ρ (X ∪ Y) + ρ (X ∩ Y) ≤ ρ X + ρ Y) → ρ ∅ = 0 →
      C ⊆ D → IsChain (· ⊆ ·) C →
      ∃ μ : α → ℝ, (∀ X ∈ D, ∑ a ∈ X, μ a ≤ ρ X) ∧ (∀ X ∈ C, ∑ a ∈ X, μ a = ρ X) ∧
        ∑ a ∈ W, μ a = ρ W := by
  intro n
  induction n with
  | zero =>
    intro W hW D ρ C hDW _ _ _ _ hρ0 hCD _
    have hW0 : W = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hW)
    subst hW0
    refine ⟨0, ?_, ?_, ?_⟩
    · intro X hX; rw [Finset.subset_empty.mp (hDW X hX)]; simp [hρ0]
    · intro X hX; rw [Finset.subset_empty.mp (hDW X (hCD hX))]; simp [hρ0]
    · simp [hρ0]
  | succ n ih =>
    intro W hW D ρ C hDW hD0 hDW' hDcl hsub hρ0 hCD hC
    by_cases hWe : W = ∅
    · subst hWe
      refine ⟨0, ?_, ?_, ?_⟩
      · intro X hX; rw [Finset.subset_empty.mp (hDW X hX)]; simp [hρ0]
      · intro X hX; rw [Finset.subset_empty.mp (hDW X (hCD hX))]; simp [hρ0]
      · simp [hρ0]
    have hWne : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hWe
    set K : Set (Finset α) := {X | (X ∈ C ∧ X.Nonempty) ∨ X = W} with hK
    have hKfin : K.Finite := by
      apply (W.powerset.finite_toSet).subset
      intro X hX
      rcases hX with ⟨hXC, -⟩ | rfl
      · exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr (hDW X (hCD hXC)))
      · exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr le_rfl)
    obtain ⟨B, hBK, hBmin⟩ := Set.exists_min_image K Finset.card hKfin ⟨W, Or.inr rfl⟩
    have hBD : B ∈ D := by
      rcases hBK with ⟨hBC, -⟩ | rfl
      · exact hCD hBC
      · exact hDW'
    have hBne : B.Nonempty := by
      rcases hBK with ⟨-, h⟩ | rfl
      · exact h
      · exact hWne
    have hBsub : ∀ X ∈ C, X.Nonempty → B ⊆ X := by
      intro X hXC hXne
      have hXK : X ∈ K := Or.inl ⟨hXC, hXne⟩
      have hcard := hBmin X hXK
      rcases hBK with ⟨hBC, -⟩ | rfl
      · by_cases hXB : X = B
        · rw [hXB]
        · rcases hC hXC hBC hXB with h | h
          · exact (Finset.eq_of_subset_of_card_le h hcard) ▸ le_rfl
          · exact h
      · have hXW : X ⊆ B := hDW X (hCD hXC)
        exact (Finset.eq_of_subset_of_card_le hXW hcard) ▸ le_rfl
    set Aset : Set (Finset α) := {X | X ∈ D ∧ X.Nonempty ∧ X ⊆ B} with hAset
    have hAfin : Aset.Finite := by
      apply (B.powerset.finite_toSet).subset
      intro X hX
      exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr hX.2.2)
    obtain ⟨A, ⟨hAD, hAne, hAB⟩, hAmin⟩ :=
      Set.exists_min_image Aset Finset.card hAfin ⟨B, hBD, hBne, le_rfl⟩
    have hAW : A ⊆ W := hDW A hAD
    have hAdich : ∀ X ∈ D, X ∩ A = ∅ ∨ A ⊆ X := by
      intro X hX
      by_cases h : (X ∩ A).Nonempty
      · right
        have hmem : X ∩ A ∈ Aset :=
          ⟨(hDcl X hX A hAD).2, h, (Finset.inter_subset_right).trans hAB⟩
        have hc := hAmin _ hmem
        have heq := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁ := X)) hc
        rw [← heq]; exact Finset.inter_subset_left
      · left; exact Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨a0, ha0⟩ := hAne
    set W' := W \ A with hW'
    have hW'card : W'.card ≤ n := by
      have h1 : W'.card < W.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro h
        have := h (hAW ha0)
        simp [hW'] at this
        exact this.2 ha0
      omega
    set D' : Set (Finset α) := {Y | Y ⊆ W' ∧ Y ∪ A ∈ D} with hD'
    set ρ' : Finset α → ℝ := fun Y => ρ (Y ∪ A) - ρ A with hρ'
    set C' : Set (Finset α) := {Y | Y ⊆ W' ∧ Y ∪ A ∈ C} with hC'
    have eU : ∀ Y1 Y2 : Finset α, (Y1 ∪ Y2) ∪ A = (Y1 ∪ A) ∪ (Y2 ∪ A) := by
      intro Y1 Y2; ext a; simp only [Finset.mem_union]; tauto
    have eI : ∀ Y1 Y2 : Finset α, (Y1 ∩ Y2) ∪ A = (Y1 ∪ A) ∩ (Y2 ∪ A) := by
      intro Y1 Y2; ext a; simp only [Finset.mem_union, Finset.mem_inter]; tauto
    have hdisj : ∀ Y ⊆ W', Disjoint Y A := by
      intro Y hY
      rw [Finset.disjoint_left]
      intro a ha haA
      have := hY ha
      simp [hW'] at this
      exact this.2 haA
    have hrec : ∀ Y ⊆ W', (Y ∪ A) \ A = Y := by
      intro Y hY
      rw [Finset.union_sdiff_right]
      exact Finset.sdiff_eq_self_of_disjoint (hdisj Y hY)
    obtain ⟨μ', hμ'D, hμ'C, hμ'W⟩ := ih W' hW'card D' ρ' C'
      (fun X hX => hX.1)
      ⟨Finset.empty_subset _, by simpa using hAD⟩
      ⟨le_rfl, by rw [hW', Finset.sdiff_union_of_subset hAW]; exact hDW'⟩
      (by
        intro X hX Y hY
        refine ⟨⟨Finset.union_subset hX.1 hY.1, ?_⟩, ⟨(Finset.inter_subset_left).trans hX.1, ?_⟩⟩
        · rw [eU]; exact (hDcl _ hX.2 _ hY.2).1
        · rw [eI]; exact (hDcl _ hX.2 _ hY.2).2)
      (by
        intro X hX Y hY
        simp only [hρ']
        rw [eU, eI]
        have := hsub _ hX.2 _ hY.2
        linarith)
      (by simp [hρ'])
      (fun X hX => ⟨hX.1, hCD hX.2⟩)
      (by
        intro X hX Y hY hXY
        have hne : X ∪ A ≠ Y ∪ A := by
          intro h
          apply hXY
          rw [← hrec X hX.1, ← hrec Y hY.1, h]
        rcases hC hX.2 hY.2 hne with h | h
        · left
          intro a ha
          have := h (Finset.mem_union_left A ha)
          rcases Finset.mem_union.mp this with h1 | h1
          · exact h1
          · exact absurd h1 (Finset.disjoint_left.mp (hdisj X hX.1) ha)
        · right
          intro a ha
          have := h (Finset.mem_union_left A ha)
          rcases Finset.mem_union.mp this with h1 | h1
          · exact h1
          · exact absurd h1 (Finset.disjoint_left.mp (hdisj Y hY.1) ha))
    set μ : α → ℝ := fun a => if a ∈ A then (if a = a0 then ρ A else 0) else μ' a with hμ
    have hsplit : ∀ X : Finset α, ∑ a ∈ X, μ a = ∑ a ∈ X ∩ A, μ a + ∑ a ∈ X \ A, μ' a := by
      intro X
      rw [← Finset.sum_inter_add_sum_sdiff X A μ]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      have : a ∉ A := (Finset.mem_sdiff.mp ha).2
      simp [hμ, this]
    have hAsum : ∑ a ∈ A, μ a = ρ A := by
      rw [Finset.sum_congr rfl (g := fun a => if a = a0 then ρ A else 0)]
      · rw [Finset.sum_ite_eq' A a0]; simp [ha0]
      · intro a ha; simp [hμ, ha]
    refine ⟨μ, ?_, ?_, ?_⟩
    · intro X hX
      have hXW := hDW X hX
      have hXA' : X \ A ∈ D' := by
        refine ⟨Finset.sdiff_subset_sdiff hXW le_rfl, ?_⟩
        rw [Finset.sdiff_union_self_eq_union]
        exact (hDcl X hX A hAD).1
      have h1 := hμ'D _ hXA'
      simp only [hρ', Finset.sdiff_union_self_eq_union] at h1
      rw [hsplit]
      rcases hAdich X hX with h | h
      · rw [h, Finset.sum_empty, zero_add]
        have := hsub X hX A hAD
        rw [h, hρ0] at this
        linarith
      · rw [Finset.inter_eq_right.mpr h, hAsum]
        rw [Finset.union_eq_left.mpr h] at h1
        linarith
    · intro X hX
      by_cases hXe : X.Nonempty
      · have hAX : A ⊆ X := hAB.trans (hBsub X hX hXe)
        have hXW := hDW X (hCD hX)
        have hmem : X \ A ∈ C' := by
          refine ⟨Finset.sdiff_subset_sdiff hXW le_rfl, ?_⟩
          rw [Finset.sdiff_union_of_subset hAX]; exact hX
        have h1 := hμ'C _ hmem
        simp only [hρ', Finset.sdiff_union_of_subset hAX] at h1
        rw [hsplit, Finset.inter_eq_right.mpr hAX, hAsum, h1]
        ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hXe]; simp [hρ0]
    · simp only [hρ', hW', Finset.sdiff_union_of_subset hAW] at hμ'W
      rw [hsplit, Finset.inter_eq_right.mpr hAW, hAsum, hμ'W]
      ring

theorem ceil_sub_eq (r θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ⌈r - θ⌉ = ⌊r⌋ + if θ < Int.fract r then 1 else 0 := by
  have e : r - θ = (⌊r⌋ : ℝ) + (Int.fract r - θ) := by
    have := Int.floor_add_fract r; linarith
  rw [e, ceil_int_add _ _ (by linarith [Int.fract_nonneg r]) (by linarith [Int.fract_lt_one r])]
  simp [sub_pos]

theorem dom_lnat (f : (V → ℤ) → WithTop ℝ)
    (hf : LNaturalConvex f) (hne : (DomZ f).Nonempty) : LNatConvexSetL (DomZ f) := by
  obtain ⟨hsbf, -⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hne
    refine ⟨liftZ y, ?_⟩
    show LiftedFunctionL f (liftZ y) ≠ ⊤
    rw [lift_eval]; exact hy
  · intro p hp q hq
    have hp' : LiftedFunctionL f p ≠ ⊤ := hp
    have hq' : LiftedFunctionL f q ≠ ⊤ := hq
    have h : LiftedFunctionL f (p ⊔ q) + LiftedFunctionL f (p ⊓ q) ≤
        LiftedFunctionL f p + LiftedFunctionL f q := hsbf p q
    have hsum : LiftedFunctionL f (p ⊔ q) + LiftedFunctionL f (p ⊓ q) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hp', hq'⟩) h
    rw [WithTop.add_ne_top] at hsum
    exact ⟨hsum.1, hsum.2⟩
  · intro p hp
    have hp' : LiftedFunctionL f p ≠ ⊤ := hp
    constructor
    · show LiftedFunctionL f (fun v => p v + 1) ≠ ⊤
      have : (fun v => p v + 1) = p + 1 := rfl
      rw [this, lift_tr]; exact hp'
    · show LiftedFunctionL f (fun v => p v - 1) ≠ ⊤
      have : p = (fun v => p v - 1) + 1 := by funext v; simp
      rw [this, lift_tr] at hp'; exact hp'

theorem subgrad (f : (V → ℤ) → WithTop ℝ)
    (hf : LNaturalConvex f) (x : V → ℝ) (hx : x ∈ convexHull ℝ (IntEmbedL (DomZ f))) :
    ∃ (ℓ : V → ℝ) (c : ℝ),
      (∀ y : V → ℤ, (((∑ v, ℓ v * (y v : ℝ)) + c : ℝ) : WithTop ℝ) ≤ f y) ∧
      ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
        (fun v => ⌈x v - θ⌉) ∈ DomZ f ∧
        f (fun v => ⌈x v - θ⌉) =
          (((∑ v, ℓ v * ((⌈x v - θ⌉ : ℤ) : ℝ)) + c : ℝ) : WithTop ℝ) := by
  have hne : (DomZ f).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hx
    simp [IntEmbedL] at hx
  have hD := dom_lnat f hf hne
  have hch : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → (fun v => ⌈x v - θ⌉) ∈ DomZ f := by
    intro θ h0 h1
    apply lnat_mem (DomZ f) hD x hx
    · intro v; have := Int.ceil_lt_add_one (x v - θ); linarith
    · intro v; have := Int.le_ceil (x v - θ); linarith
    · intro a b; have := Int.ceil_lt_add_one (x b - θ); have := Int.le_ceil (x a - θ); linarith
  set b : V → ℤ := fun v => ⌊x v⌋ with hb
  have hbD : b ∈ DomZ f := by
    apply lnat_mem (DomZ f) hD x hx
    · intro v; have := Int.floor_le (x v); simp only [hb]; linarith
    · intro v; have := Int.lt_floor_add_one (x v); simp only [hb]; linarith
    · intro a b'; have := Int.floor_le (x a); have := Int.lt_floor_add_one (x b')
      have := Int.floor_le (x b'); have := Int.lt_floor_add_one (x a)
      simp only [hb]; linarith
  obtain ⟨hsbf, -⟩ := hf
  set F := LiftedFunctionL f with hF
  have hsbf' : ∀ p q, F (p ⊔ q) + F (p ⊓ q) ≤ F p + F q := fun p q => hsbf p q
  set zt : Option V → ℤ := fun o => Option.elim o 0 b with hzt
  set zX : Finset (Option V) → Option V → ℤ := fun X o => zt o + if o ∈ X then 1 else 0 with hzX
  have hzX_sup : ∀ X Y, zX X ⊔ zX Y = zX (X ∪ Y) := by
    intro X Y; funext o
    simp only [hzX, Pi.sup_apply]
    by_cases hx : o ∈ X <;> by_cases hy : o ∈ Y <;> simp [hx, hy]
  have hzX_inf : ∀ X Y, zX X ⊓ zX Y = zX (X ∩ Y) := by
    intro X Y; funext o
    simp only [hzX, Pi.inf_apply]
    by_cases hx : o ∈ X <;> by_cases hy : o ∈ Y <;> simp [hx, hy]
  have hzX0 : zX ∅ = zt := by funext o; simp [hzX]
  have hzXu : zX Finset.univ = zt + 1 := by funext o; simp [hzX]
  have hFz : F zt = f b := lift_eval f b
  have hFzt : F zt ≠ ⊤ := by rw [hFz]; exact hbD
  have hFu : F (zt + 1) = F zt := by rw [hF]; exact lift_tr f zt
  set D : Set (Finset (Option V)) := {X | F (zX X) ≠ ⊤} with hDdef
  set r0 : ℝ := (F zt).untopD 0 with hr0
  set ρ : Finset (Option V) → ℝ := fun X => (F (zX X)).untopD 0 - r0 with hρ
  set Xθ : ℝ → Finset (Option V) := fun θ =>
    Finset.univ.filter (fun o => Option.elim o False (fun v => θ < Int.fract (x v))) with hXθ
  have hzXθ : ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
      zX (Xθ θ) = fun o => Option.elim o 0 (fun v => ⌈x v - θ⌉) := by
    intro θ h0 h1; funext o
    cases o with
    | none => simp [hzX, hzt, hXθ]
    | some v =>
      rw [Option.elim_some, ceil_sub_eq (x v) θ h0 h1]
      simp [hzX, hzt, hXθ, hb]
  have hFlift : ∀ y : V → ℤ, F (fun o => Option.elim o 0 y) = f y := lift_eval f
  have hFXθ : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → F (zX (Xθ θ)) = f (fun v => ⌈x v - θ⌉) := by
    intro θ h0 h1
    rw [hzXθ θ h0 h1, hFlift]
  set C : Set (Finset (Option V)) := {X | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ X = Xθ θ} with hCdef
  have hCD : C ⊆ D := by
    rintro X ⟨θ, h0, h1, rfl⟩
    show F _ ≠ ⊤
    rw [hFXθ θ h0 h1]; exact hch θ h0 h1
  have hCchain : IsChain (· ⊆ ·) C := by
    rintro X ⟨θ1, -, -, rfl⟩ Y ⟨θ2, -, -, rfl⟩ -
    rcases le_total θ1 θ2 with h | h
    · right
      intro o ho
      simp only [hXθ, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
      cases o with
      | none => simp at ho
      | some v => simp only [Option.elim_some] at ho ⊢; linarith
    · left
      intro o ho
      simp only [hXθ, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
      cases o with
      | none => simp at ho
      | some v => simp only [Option.elim_some] at ho ⊢; linarith
  have hDcl : ∀ X ∈ D, ∀ Y ∈ D, X ∪ Y ∈ D ∧ X ∩ Y ∈ D := by
    intro X hX Y hY
    have h := hsbf' (zX X) (zX Y)
    rw [hzX_sup, hzX_inf] at h
    have hsum : F (zX (X ∪ Y)) + F (zX (X ∩ Y)) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hX, hY⟩) h
    rw [WithTop.add_ne_top] at hsum
    exact ⟨hsum.1, hsum.2⟩
  obtain ⟨μ, hμD, hμC, hμW⟩ := greedy (Fintype.card (Option V)) Finset.univ le_rfl D ρ C
    (fun X _ => Finset.subset_univ X)
    (by show F _ ≠ ⊤; rw [hzX0]; exact hFzt)
    (by show F _ ≠ ⊤; rw [hzXu, hFu]; exact hFzt)
    hDcl
    (by
      intro X hX Y hY
      have h := hsbf' (zX X) (zX Y)
      rw [hzX_sup, hzX_inf] at h
      have ⟨_, _, hle⟩ := add_untopD_le hX hY h
      simp only [hρ]
      linarith)
    (by simp [hρ, hzX0, hr0])
    hCD hCchain
  have hρu : ρ Finset.univ = 0 := by simp only [hρ, hzXu, hFu, hr0, sub_self]
  set L : (Option V → ℤ) → ℝ := fun w => ∑ o, μ o * (w o : ℝ) with hL
  set G : (Option V → ℤ) → WithTop ℝ := fun w => F w + ((-(L w) : ℝ) : WithTop ℝ) with hG
  have hLmod : ∀ p q : Option V → ℤ, L (p ⊔ q) + L (p ⊓ q) = L p + L q := by
    intro p q
    simp only [hL, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro o _
    have h : ((p ⊔ q) o : ℝ) + ((p ⊓ q) o : ℝ) = (p o : ℝ) + (q o : ℝ) := by
      have : (p ⊔ q) o + (p ⊓ q) o = p o + q o := by
        show max (p o) (q o) + min (p o) (q o) = p o + q o
        omega
      exact_mod_cast this
    linear_combination μ o * h
  have hGsub : ∀ p q, G (p ⊔ q) + G (p ⊓ q) ≤ G p + G q := by
    intro p q
    simp only [hG]
    rw [add_add_add_comm, add_add_add_comm (F p), ← WithTop.coe_add, ← WithTop.coe_add]
    have : -L (p ⊔ q) + -L (p ⊓ q) = -L p + -L q := by linarith [hLmod p q]
    rw [this]
    exact add_le_add (hsbf' p q) le_rfl
  have hLtr : ∀ p : Option V → ℤ, L (p + 1) = L p := by
    intro p
    simp only [hL, Pi.add_apply, Pi.one_apply, Int.cast_add, Int.cast_one, mul_add,
      Finset.sum_add_distrib, mul_one]
    have : ∑ o, μ o = 0 := by rw [hμW, hρu]
    rw [this, add_zero]
  have hGtr : ∀ p, G (p + 1) = G p := by
    intro p; simp only [hG, hLtr, hF, lift_tr]
  have hLX : ∀ X : Finset (Option V), L (zX X) = L zt + ∑ o ∈ X, μ o := by
    intro X
    simp only [hL, hzX, Int.cast_add, mul_add, Finset.sum_add_distrib]
    congr 1
    simp [Finset.sum_ite_mem]
  have hGz : G zt ≠ ⊤ := by
    simp only [hG]; exact WithTop.add_ne_top.mpr ⟨hFzt, WithTop.coe_ne_top⟩
  have hloc : ∀ X : Finset (Option V), G zt ≤ G (fun a => zt a + if a ∈ X then 1 else 0) := by
    intro X
    show G zt ≤ G (zX X)
    by_cases hX : X ∈ D
    · have h1 := hμD X hX
      have e1 : F (zX X) = (((F (zX X)).untopD 0 : ℝ) : WithTop ℝ) := (coe_untopD hX).symm
      simp only [hG]
      rw [e1, ← coe_untopD hFzt, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe, hLX X]
      simp only [hρ, hr0] at h1
      linarith
    · have : F (zX X) = ⊤ := by simpa [hDdef] using hX
      simp only [hG, this, WithTop.top_add]; exact le_top
  have hglob := loc_glob G hGsub hGtr zt hGz hloc
  have hLlift : ∀ y : V → ℤ, L (fun o => Option.elim o 0 y) = ∑ v, μ (some v) * (y v : ℝ) := by
    intro y; simp [hL, Fintype.sum_option]
  have hLz : L zt = ∑ v, μ (some v) * (b v : ℝ) := hLlift b
  have hfb : f b = ((r0 : ℝ) : WithTop ℝ) := by rw [← hFz]; exact (coe_untopD hFzt).symm
  refine ⟨fun v => μ (some v), r0 - ∑ v, μ (some v) * (b v : ℝ), ?_, ?_⟩
  · intro y
    have h := hglob (fun o => Option.elim o 0 y)
    simp only [hG] at h
    rw [hFlift y, hLlift y, hFlift b, hLlift b, hfb] at h
    by_cases hy : f y = ⊤
    · rw [hy]; exact le_top
    · rw [← coe_untopD hy] at h ⊢
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
      rw [WithTop.coe_le_coe]
      linarith
  · intro θ h0 h1
    refine ⟨hch θ h0 h1, ?_⟩
    have hmem : Xθ θ ∈ C := ⟨θ, h0, h1, rfl⟩
    have e1 := hμC _ hmem
    have e2 := hLX (Xθ θ)
    rw [hzXθ θ h0 h1, hLlift (fun v => ⌈x v - θ⌉), hLz] at e2
    rw [← hFXθ θ h0 h1, ← coe_untopD (hCD hmem)]
    congr 1
    have e3 : (F (zX (Xθ θ))).untopD 0 = ρ (Xθ θ) + r0 := by simp only [hρ]; ring
    rw [e3, ← e1, e2]
    ring

lemma sum_swap {α β : Type*} [Fintype β] (s : Finset α) (w : α → ℝ) (ℓ : β → ℝ)
    (c : α → β → ℝ) :
    ∑ b : β, ℓ b * ∑ a ∈ s, w a * c a b = ∑ a ∈ s, w a * ∑ b : β, ℓ b * c a b := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end GreedyRound

section RealSep
variable {V : Type*} [Fintype V] [DecidableEq V]

def castZ (z : V → ℤ) : V → ℝ := fun v => (z v : ℝ)

lemma sum_abs_le_card_mul_norm (u : V → ℝ) :
    ∑ v : V, |u v| ≤ (Fintype.card V : ℝ) * ‖u‖ := by
  calc ∑ v : V, |u v|
      ≤ ∑ _v : V, ‖u‖ := Finset.sum_le_sum fun v _ => norm_le_pi_norm u v
    _ = (Fintype.card V : ℝ) * ‖u‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma hull_A1_bound {g k2 : (V → ℤ) → WithTop ℝ}
    (hg : LNaturalConvex g) (hk2 : LNaturalConvex k2)
    {M_0 : ℝ} (hM_0_nn : 0 ≤ M_0)
    (hbound : ∀ z w : V → ℤ, g z ≠ ⊤ → k2 w ≠ ⊤ →
      0 ≤ (g z).untopD 0 + (k2 w).untopD 0 + M_0 * (dist1 z w : ℝ)) :
    let A1 : Set ((V → ℝ) × ℝ) :=
      { q | ∃ z w : V → ℤ, g z ≠ ⊤ ∧ k2 w ≠ ⊤ ∧ q = (castZ z - castZ w, (g z).untopD 0 + (k2 w).untopD 0) }
    ∀ q1 ∈ convexHull ℝ A1, 0 ≤ q1.2 + (M_0 * (Fintype.card V : ℝ)) * ‖q1.1‖ := by
  intro A1 q1 hq1
  rw [mem_convexHull_iff_exists_fintype] at hq1
  obtain ⟨κ, instκ, lam, Y, hlam0, hlam1, hYA1, hYsum⟩ := hq1
  letI : Fintype κ := instκ
  have hY_zw : ∀ k : κ, ∃ z w : V → ℤ, g z ≠ ⊤ ∧ k2 w ≠ ⊤ ∧
      Y k = (castZ z - castZ w, (g z).untopD 0 + (k2 w).untopD 0) := fun k => hYA1 k
  choose zk wk hgzk hkwk hYk using hY_zw
  set x1 : V → ℝ := fun v => ∑ k : κ, lam k * (zk k v : ℝ) with hx1
  set x2 : V → ℝ := fun v => ∑ k : κ, lam k * (wk k v : ℝ) with hx2
  have hq1_fst : q1.1 = x1 - x2 := by
    rw [← hYsum]
    funext v
    have h_fst : (∑ k : κ, lam k • Y k).1 v = ∑ k : κ, lam k * (Y k).1 v := by
      rw [Prod.fst_sum]
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [h_fst]
    simp only [Pi.sub_apply, hx1, hx2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hYk k]
    simp [castZ, mul_sub]
  have hq1_snd : q1.2 = ∑ k : κ, lam k * ((g (zk k)).untopD 0 + (k2 (wk k)).untopD 0) := by
    rw [← hYsum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hYk k]
    rfl
  have hx1c : x1 ∈ convexHull ℝ (IntEmbedL (DomZ g)) := by
    have := (convex_convexHull ℝ (IntEmbedL (DomZ g))).sum_mem (fun k _ => hlam0 k) hlam1
      (z := fun k : κ => fun v => (zk k v : ℝ))
      (fun k _ => subset_convexHull ℝ _ ⟨zk k, hgzk k, rfl⟩)
    convert this using 1
    funext v; simp [hx1, Finset.sum_apply]
  have hx2c : x2 ∈ convexHull ℝ (IntEmbedL (DomZ k2)) := by
    have := (convex_convexHull ℝ (IntEmbedL (DomZ k2))).sum_mem (fun k _ => hlam0 k) hlam1
      (z := fun k : κ => fun v => (wk k v : ℝ))
      (fun k _ => subset_convexHull ℝ _ ⟨wk k, hkwk k, rfl⟩)
    convert this using 1
    funext v; simp [hx2, Finset.sum_apply]
  obtain ⟨ℓ1, c1, hle1, heq1⟩ := subgrad g hg x1 hx1c
  obtain ⟨ℓ2, c2, hle2, heq2⟩ := subgrad k2 hk2 x2 hx2c
  set q : V ⊕ V → ℝ := Sum.elim x1 x2 with hq
  have hqh := round_hull _ q le_rfl
  rw [convexHull_eq] at hqh
  obtain ⟨ι, t, w, z, hw0, hw1, hz, hcm⟩ := hqh
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcm
  have hθ : ∀ i, ∃ θ : ℝ, i ∈ t → (0 ≤ θ ∧ θ < 1 ∧ z i = fun j => ((⌈q j - θ⌉ : ℤ) : ℝ)) := by
    intro i
    by_cases hi : i ∈ t
    · obtain ⟨θ, h0, h1, he⟩ := hz i hi
      exact ⟨θ, fun _ => ⟨h0, h1, he⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose θ hθ using hθ
  have hcoord : ∀ j, ∑ i ∈ t, w i * ((⌈q j - θ i⌉ : ℤ) : ℝ) = q j := by
    intro j
    have := congrFun hcm j
    rw [Finset.sum_apply] at this
    calc ∑ i ∈ t, w i * ((⌈q j - θ i⌉ : ℤ) : ℝ) = ∑ c ∈ t, (w c • z c) j := by
          apply Finset.sum_congr rfl; intro i hi; rw [(hθ i hi).2.2]; simp [smul_eq_mul]
      _ = q j := this
  set c1p : ι → V → ℤ := fun i v => ⌈x1 v - θ i⌉ with hc1p
  set c2p : ι → V → ℤ := fun i v => ⌈x2 v - θ i⌉ with hc2p
  have hs1 : ∀ v, ∑ i ∈ t, w i * (c1p i v : ℝ) = x1 v := fun v => by
    simpa [hq] using hcoord (Sum.inl v)
  have hs2 : ∀ v, ∑ i ∈ t, w i * (c2p i v : ℝ) = x2 v := fun v => by
    simpa [hq] using hcoord (Sum.inr v)
  have hlow_q1 : (∑ v, ℓ1 v * x1 v + c1) + (∑ v, ℓ2 v * x2 v + c2) ≤ q1.2 := by
    rw [hq1_snd]
    have h_k : ∀ k : κ, (∑ v, ℓ1 v * (zk k v : ℝ) + c1) + (∑ v, ℓ2 v * (wk k v : ℝ) + c2) ≤
        (g (zk k)).untopD 0 + (k2 (wk k)).untopD 0 := by
      intro k
      have i1 := hle1 (zk k)
      have i2 := hle2 (wk k)
      rw [← coe_untopD (hgzk k), WithTop.coe_le_coe] at i1
      rw [← coe_untopD (hkwk k), WithTop.coe_le_coe] at i2
      linarith
    have eq1 := sum_swap Finset.univ lam ℓ1 (fun k v => (zk k v : ℝ))
    have eq2 := sum_swap Finset.univ lam ℓ2 (fun k v => (wk k v : ℝ))
    calc (∑ v, ℓ1 v * x1 v + c1) + (∑ v, ℓ2 v * x2 v + c2)
        = ∑ k : κ, lam k * ((∑ v, ℓ1 v * (zk k v : ℝ) + c1) + (∑ v, ℓ2 v * (wk k v : ℝ) + c2)) := by
          simp only [hx1, hx2] at eq1 eq2 ⊢
          rw [eq1, eq2]
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hlam1, one_mul]
      _ ≤ ∑ k : κ, lam k * ((g (zk k)).untopD 0 + (k2 (wk k)).untopD 0) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h_k k) (hlam0 k)
  have hround_eq : ∑ i ∈ t, w i * ((g (c1p i)).untopD 0 + (k2 (c2p i)).untopD 0) =
      (∑ v, ℓ1 v * x1 v + c1) + (∑ v, ℓ2 v * x2 v + c2) := by
    have h_i : ∀ i ∈ t, (g (c1p i)).untopD 0 + (k2 (c2p i)).untopD 0 =
        (∑ v, ℓ1 v * (c1p i v : ℝ) + c1) + (∑ v, ℓ2 v * (c2p i v : ℝ) + c2) := by
      intro i hi
      obtain ⟨h0, h1', -⟩ := hθ i hi
      have ⟨_, e1⟩ := heq1 (θ i) h0 h1'
      have ⟨_, e2⟩ := heq2 (θ i) h0 h1'
      have e1' : (g (c1p i)).untopD 0 = ∑ v, ℓ1 v * (c1p i v : ℝ) + c1 := by
        show (g (fun v => ⌈x1 v - θ i⌉)).untopD 0 = _
        rw [e1, untopD_coe]
      have e2' : (k2 (c2p i)).untopD 0 = ∑ v, ℓ2 v * (c2p i v : ℝ) + c2 := by
        show (k2 (fun v => ⌈x2 v - θ i⌉)).untopD 0 = _
        rw [e2, untopD_coe]
      rw [e1', e2']
    calc ∑ i ∈ t, w i * ((g (c1p i)).untopD 0 + (k2 (c2p i)).untopD 0)
        = ∑ i ∈ t, w i * ((∑ v, ℓ1 v * (c1p i v : ℝ) + c1) + (∑ v, ℓ2 v * (c2p i v : ℝ) + c2)) :=
          Finset.sum_congr rfl fun i hi => by rw [h_i i hi]
      _ = (∑ v, ℓ1 v * x1 v + c1) + (∑ v, ℓ2 v * x2 v + c2) := by
          have e1 := sum_swap t w ℓ1 (fun i v => (c1p i v : ℝ))
          have e2 := sum_swap t w ℓ2 (fun i v => (c2p i v : ℝ))
          simp only [hs1, hs2] at e1 e2
          rw [e1, e2]
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
  have hdist_sum : ∑ i ∈ t, w i * (dist1 (c1p i) (c2p i) : ℝ) = ∑ v : V, |x1 v - x2 v| := by
    have h_v : ∀ v : V, ∑ i ∈ t, w i * (((c1p i v - c2p i v).natAbs : ℤ) : ℝ) = |x1 v - x2 v| := by
      intro v
      rcases le_total (x2 v) (x1 v) with hle_v | hle_v
      · have h_pos : ∀ i ∈ t, (((c1p i v - c2p i v).natAbs : ℤ) : ℝ) = (c1p i v : ℝ) - (c2p i v : ℝ) := by
          intro i _
          have hm : c2p i v ≤ c1p i v := Int.ceil_mono (by linarith)
          have hm' : ((c1p i v - c2p i v).natAbs : ℤ) = c1p i v - c2p i v :=
            Int.natAbs_of_nonneg (by omega)
          exact_mod_cast hm'
        rw [Finset.sum_congr rfl fun i hi => by rw [h_pos i hi]]
        simp only [mul_sub, Finset.sum_sub_distrib, hs1 v, hs2 v]
        rw [abs_of_nonneg (by linarith)]
      · have h_neg : ∀ i ∈ t, (((c1p i v - c2p i v).natAbs : ℤ) : ℝ) = (c2p i v : ℝ) - (c1p i v : ℝ) := by
          intro i _
          have hm : c1p i v ≤ c2p i v := Int.ceil_mono (by linarith)
          have hm' : ((c1p i v - c2p i v).natAbs : ℤ) = c2p i v - c1p i v := by omega
          exact_mod_cast hm'
        rw [Finset.sum_congr rfl fun i hi => by rw [h_neg i hi]]
        simp only [mul_sub, Finset.sum_sub_distrib, hs1 v, hs2 v]
        rw [abs_of_nonpos (by linarith)]
        ring
    calc ∑ i ∈ t, w i * (dist1 (c1p i) (c2p i) : ℝ)
        = ∑ i ∈ t, w i * ∑ v : V, (((c1p i v - c2p i v).natAbs : ℤ) : ℝ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold dist1; simp only [Nat.cast_sum, Int.cast_natCast]
      _ = ∑ v : V, ∑ i ∈ t, w i * (((c1p i v - c2p i v).natAbs : ℤ) : ℝ) := by
          simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      _ = ∑ v : V, |x1 v - x2 v| := Finset.sum_congr rfl fun v _ => h_v v
  have h_nonneg_i : ∀ i ∈ t, 0 ≤ w i * ((g (c1p i)).untopD 0 + (k2 (c2p i)).untopD 0 + M_0 * (dist1 (c1p i) (c2p i) : ℝ)) := by
    intro i hi
    obtain ⟨h0, h1', -⟩ := hθ i hi
    have hg_i := (heq1 (θ i) h0 h1').1
    have hk_i := (heq2 (θ i) h0 h1').1
    exact mul_nonneg (hw0 i hi) (hbound (c1p i) (c2p i) hg_i hk_i)
  have h_sum_nn : 0 ≤ ∑ i ∈ t, w i * ((g (c1p i)).untopD 0 + (k2 (c2p i)).untopD 0 + M_0 * (dist1 (c1p i) (c2p i) : ℝ)) :=
    Finset.sum_nonneg h_nonneg_i
  have h_sum_split : ∑ i ∈ t, w i * ((g (c1p i)).untopD 0 + (k2 (c2p i)).untopD 0 + M_0 * (dist1 (c1p i) (c2p i) : ℝ)) =
      ∑ i ∈ t, w i * ((g (c1p i)).untopD 0 + (k2 (c2p i)).untopD 0) + M_0 * ∑ i ∈ t, w i * (dist1 (c1p i) (c2p i) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h_sum_split, hround_eq, hdist_sum] at h_sum_nn
  have h_abs_norm : ∑ v : V, |x1 v - x2 v| ≤ (Fintype.card V : ℝ) * ‖q1.1‖ := by
    rw [hq1_fst]
    exact sum_abs_le_card_mul_norm (x1 - x2)
  have h_M0_le : M_0 * ∑ v : V, |x1 v - x2 v| ≤ (M_0 * (Fintype.card V : ℝ)) * ‖q1.1‖ := by
    calc M_0 * ∑ v : V, |x1 v - x2 v|
        ≤ M_0 * ((Fintype.card V : ℝ) * ‖q1.1‖) := mul_le_mul_of_nonneg_left h_abs_norm hM_0_nn
      _ = (M_0 * (Fintype.card V : ℝ)) * ‖q1.1‖ := by ring
  linarith

theorem real_sep_of_hull_bound {g k2 : (V → ℤ) → WithTop ℝ}
    {p0 : V → ℤ} (hp0_g : g p0 ≠ ⊤) (hp0_k : k2 p0 ≠ ⊤)
    {M_1 : ℝ} (hM_1_nn : 0 ≤ M_1)
    (hA1_bound : ∀ q1 ∈ convexHull ℝ
      { q : (V → ℝ) × ℝ | ∃ z w : V → ℤ, g z ≠ ⊤ ∧ k2 w ≠ ⊤ ∧
        q = (castZ z - castZ w, (g z).untopD 0 + (k2 w).untopD 0) },
      0 ≤ q1.2 + M_1 * ‖q1.1‖) :
    ∃ beta : ℝ, ∃ x : V → ℝ,
      (∀ p : V → ℤ, g p ≥ ((beta + ∑ v, x v * (p v : ℝ) : ℝ) : WithTop ℝ)) ∧
      (∀ p : V → ℤ, ((beta + ∑ v, x v * (p v : ℝ) : ℝ) : WithTop ℝ) + k2 p ≥ 0) := by
  let A1 : Set ((V → ℝ) × ℝ) :=
    { q | ∃ z w : V → ℤ, g z ≠ ⊤ ∧ k2 w ≠ ⊤ ∧ q = (castZ z - castZ w, (g z).untopD 0 + (k2 w).untopD 0) }
  let K : Set ((V → ℝ) × ℝ) :=
    { q | ∃ q1 ∈ convexHull ℝ A1, ∃ (v : V → ℝ) (s : ℝ), 0 ≤ s ∧ q = (q1.1 + v, q1.2 + M_1 * ‖v‖ + s) }
  have hK_conv : Convex ℝ K := by
    rintro p ⟨p1, hp1, v1, s1, hs1, rfl⟩ q ⟨q1, hq1, v2, s2, hs2, rfl⟩ a b ha hb hab
    refine ⟨a • p1 + b • q1, convex_convexHull ℝ A1 hp1 hq1 ha hb hab, a • v1 + b • v2,
      a * s1 + b * s2 + (a * (M_1 * ‖v1‖) + b * (M_1 * ‖v2‖) - M_1 * ‖a • v1 + b • v2‖), ?_, ?_⟩
    · have hnorm : ‖a • v1 + b • v2‖ ≤ a * ‖v1‖ + b * ‖v2‖ := by
        calc ‖a • v1 + b • v2‖ ≤ ‖a • v1‖ + ‖b • v2‖ := norm_add_le _ _
          _ = a * ‖v1‖ + b * ‖v2‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      have hMnorm : M_1 * ‖a • v1 + b • v2‖ ≤ a * (M_1 * ‖v1‖) + b * (M_1 * ‖v2‖) := by
        calc M_1 * ‖a • v1 + b • v2‖ ≤ M_1 * (a * ‖v1‖ + b * ‖v2‖) :=
              mul_le_mul_of_nonneg_left hnorm hM_1_nn
          _ = a * (M_1 * ‖v1‖) + b * (M_1 * ‖v2‖) := by ring
      have : 0 ≤ a * s1 + b * s2 := by positivity
      linarith
    · ext : 1
      · show a • (p1.1 + v1) + b • (q1.1 + v2) = (a • p1.1 + b • q1.1) + (a • v1 + b • v2)
        module
      · show a * (p1.2 + M_1 * ‖v1‖ + s1) + b * (q1.2 + M_1 * ‖v2‖ + s2) =
          (a * p1.2 + b * q1.2) + M_1 * ‖a • v1 + b • v2‖ +
          (a * s1 + b * s2 + (a * (M_1 * ‖v1‖) + b * (M_1 * ‖v2‖) - M_1 * ‖a • v1 + b • v2‖))
        ring
  have hK_zero_nn : ∀ t : ℝ, ((0 : V → ℝ), t) ∈ K → 0 ≤ t := by
    rintro t ⟨q1, hq1, v, s, hs, h_eq⟩
    have h1 : (0 : V → ℝ) = q1.1 + v := congrArg Prod.fst h_eq
    have h2 : t = q1.2 + M_1 * ‖v‖ + s := congrArg Prod.snd h_eq
    have hv : v = -q1.1 := eq_neg_of_add_eq_zero_right h1.symm
    rw [hv, norm_neg] at h2
    have h3 := hA1_bound q1 hq1
    linarith
  have h_shift_int : ∀ q1 ∈ A1, ∀ δ : ℝ, 0 < δ → (q1.1, q1.2 + δ) ∈ interior K := by
    intro q1 hq1 δ hδ
    rw [mem_interior]
    let r : ℝ := δ / (2 * (M_1 + 1))
    have hr_pos : 0 < r := by
      dsimp [r]; positivity
    refine ⟨Metric.ball q1.1 r ×ˢ Set.Ioi (q1.2 + δ / 2), ?_,
      IsOpen.prod Metric.isOpen_ball isOpen_Ioi, ?_⟩
    · rintro ⟨u', t'⟩ ⟨hu', ht'⟩
      rw [Metric.mem_ball, dist_eq_norm] at hu'
      rw [Set.mem_Ioi] at ht'
      refine ⟨q1, subset_convexHull ℝ A1 hq1, u' - q1.1, t' - q1.2 - M_1 * ‖u' - q1.1‖, ?_, ?_⟩
      · have hM_lt : M_1 * ‖u' - q1.1‖ < δ / 2 := by
          calc M_1 * ‖u' - q1.1‖ ≤ (M_1 + 1) * ‖u' - q1.1‖ := by
                have := norm_nonneg (u' - q1.1); nlinarith
            _ < (M_1 + 1) * (δ / (2 * (M_1 + 1))) :=
                mul_lt_mul_of_pos_left hu' (by positivity)
            _ = δ / 2 := by
                have hne : M_1 + 1 ≠ 0 := by positivity
                field_simp
        linarith
      · ext : 1
        · simp
        · dsimp; ring
    · refine ⟨Metric.mem_ball_self hr_pos, ?_⟩
      rw [Set.mem_Ioi]; linarith
  have h0_not_int : (0 : (V → ℝ) × ℝ) ∉ interior K := by
    intro h0_int
    rw [mem_interior] at h0_int
    obtain ⟨U, hUK, hU_open, h0U⟩ := h0_int
    rw [Metric.isOpen_iff] at hU_open
    obtain ⟨ε, hε, hball⟩ := hU_open 0 h0U
    let p_neg : (V → ℝ) × ℝ := (0, -ε / 2)
    have hp_ball : p_neg ∈ Metric.ball (0 : (V → ℝ) × ℝ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _),
        Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    have hp_K : p_neg ∈ K := hUK (hball hp_ball)
    have h_nn := hK_zero_nn (-ε / 2) hp_K
    linarith
  obtain ⟨f_lin0, hf_lin0⟩ := geometric_hahn_banach_open_point hK_conv.interior isOpen_interior h0_not_int
  rw [map_zero] at hf_lin0
  let f_lin : (V → ℝ) × ℝ →L[ℝ] ℝ := -f_lin0
  have hf_lin : ∀ a ∈ interior K, 0 < f_lin a := by
    intro a ha
    have := hf_lin0 a ha
    change 0 < -f_lin0 a
    linarith
  let c0 : ℝ := (g p0).untopD 0 + (k2 p0).untopD 0
  have hq0_A1 : ((0 : V → ℝ), c0) ∈ A1 := by
    refine ⟨p0, p0, hp0_g, hp0_k, ?_⟩
    simp [c0]
  have hf_01_pos : 0 < f_lin ((0 : V → ℝ), (1 : ℝ)) := by
    let δ0 : ℝ := |c0| + 1
    have hδ0_pos : 0 < δ0 := by positivity
    have h_int := h_shift_int ((0 : V → ℝ), c0) hq0_A1 δ0 hδ0_pos
    have h_pos := hf_lin ((0 : V → ℝ), c0 + δ0) h_int
    have h_eq : ((0 : V → ℝ), c0 + δ0) = (c0 + δ0) • ((0 : V → ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [h_eq, f_lin.map_smul, smul_eq_mul] at h_pos
    have hc0_pos : 0 < c0 + δ0 := by
      have := neg_abs_le c0
      dsimp [δ0]; linarith
    nlinarith
  have hf_A1_nn : ∀ q1 ∈ A1, 0 ≤ f_lin q1 := by
    intro q1 hq1
    by_contra hneg
    push_neg at hneg
    let δ : ℝ := (-f_lin q1) / (2 * f_lin ((0 : V → ℝ), (1 : ℝ)))
    have hδ_pos : 0 < δ := div_pos (by linarith) (by linarith)
    have h_int := h_shift_int q1 hq1 δ hδ_pos
    have h_pos := hf_lin (q1.1, q1.2 + δ) h_int
    have h_eq : (q1.1, q1.2 + δ) = q1 + δ • ((0 : V → ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [h_eq, map_add, f_lin.map_smul, smul_eq_mul] at h_pos
    have h_cancel : δ * f_lin ((0 : V → ℝ), (1 : ℝ)) = (-f_lin q1) / 2 := by
      dsimp [δ]
      have hne : f_lin ((0 : V → ℝ), (1 : ℝ)) ≠ 0 := ne_of_gt hf_01_pos
      field_simp
    linarith
  let γ : ℝ := f_lin ((0 : V → ℝ), (1 : ℝ))
  have hγ_ne : γ ≠ 0 := ne_of_gt hf_01_pos
  let x : V → ℝ := fun v => - (f_lin (Pi.single v (1 : ℝ), (0 : ℝ))) / γ
  have hf_eval : ∀ (u : V → ℝ) (t : ℝ), f_lin (u, t) = γ * (t - ∑ v : V, x v * u v) := by
    intro u t
    have hu_eq : (u, t) = (∑ v : V, u v • (Pi.single v (1 : ℝ), (0 : ℝ))) + t • ((0 : V → ℝ), (1 : ℝ)) := by
      ext : 1
      · funext v
        rw [Prod.fst_add, Prod.fst_sum]
        simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
      · rw [Prod.snd_add, Prod.snd_sum]
        simp
    rw [hu_eq, map_add, map_sum, f_lin.map_smul, smul_eq_mul]
    have h_sum : ∑ v : V, f_lin (u v • (Pi.single v (1 : ℝ), (0 : ℝ))) =
        - (γ * ∑ v : V, x v * u v) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [f_lin.map_smul, smul_eq_mul]
      dsimp [x, γ]
      field_simp
    rw [h_sum]
    dsimp [γ]
    ring
  have h_sep_zw : ∀ z w : V → ℤ, g z ≠ ⊤ → k2 w ≠ ⊤ →
      -(k2 w).untopD 0 - ∑ v : V, x v * (w v : ℝ) ≤
        (g z).untopD 0 - ∑ v : V, x v * (z v : ℝ) := by
    intro z w hgz hkw
    have hmem : (castZ z - castZ w, (g z).untopD 0 + (k2 w).untopD 0) ∈ A1 :=
      ⟨z, w, hgz, hkw, rfl⟩
    have h_nn := hf_A1_nn _ hmem
    rw [hf_eval] at h_nn
    have h_pos' : 0 ≤ ((g z).untopD 0 + (k2 w).untopD 0) - ∑ v : V, x v * (castZ z - castZ w) v := by
      nlinarith
    have h_sub_sum : ∑ v : V, x v * (castZ z - castZ w) v =
        (∑ v : V, x v * (z v : ℝ)) - (∑ v : V, x v * (w v : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [castZ, mul_sub]
    linarith
  let S_low : Set ℝ := { r | ∃ w : V → ℤ, k2 w ≠ ⊤ ∧ r = -(k2 w).untopD 0 - ∑ v : V, x v * (w v : ℝ) }
  have hS_ne : S_low.Nonempty := ⟨_, p0, hp0_k, rfl⟩
  have hS_bdd : BddAbove S_low := by
    refine ⟨(g p0).untopD 0 - ∑ v : V, x v * (p0 v : ℝ), ?_⟩
    rintro r ⟨w, hkw, rfl⟩
    exact h_sep_zw p0 w hp0_g hkw
  let beta : ℝ := sSup S_low
  refine ⟨beta, x, fun p => ?_, fun p => ?_⟩
  · by_cases hgp : g p = ⊤
    · rw [hgp]; exact le_top
    · rw [← coe_untopD hgp, ge_iff_le, WithTop.coe_le_coe]
      have hle : beta ≤ (g p).untopD 0 - ∑ v : V, x v * (p v : ℝ) := by
        apply csSup_le hS_ne
        rintro r ⟨w, hkw, rfl⟩
        exact h_sep_zw p w hgp hkw
      linarith
  · by_cases hkp : k2 p = ⊤
    · rw [hkp, add_top]; exact le_top
    · rw [← coe_untopD hkp, ← WithTop.coe_add, ge_iff_le, ← WithTop.coe_zero, WithTop.coe_le_coe]
      have hge_beta : -(k2 p).untopD 0 - ∑ v : V, x v * (p v : ℝ) ≤ beta :=
        le_csSup hS_bdd ⟨p, hkp, rfl⟩
      linarith

theorem real_sep_case1 {g k2 : (V → ℤ) → WithTop ℝ}
    (hg : LNaturalConvex g) (hk2 : LNaturalConvex k2)
    {p0 : V → ℤ} (hp0_g : g p0 ≠ ⊤) (hp0_k : k2 p0 ≠ ⊤)
    (hge : ∀ p : V → ℤ, g p + k2 p ≥ 0) :
    ∃ beta : ℝ, ∃ x : V → ℝ,
      (∀ p : V → ℤ, g p ≥ ((beta + ∑ v, x v * (p v : ℝ) : ℝ) : WithTop ℝ)) ∧
      (∀ p : V → ℤ, ((beta + ∑ v, x v * (p v : ℝ) : ℝ) : WithTop ℝ) + k2 p ≥ 0) := by
  obtain ⟨M_0, hM_0_nn, hbound⟩ := dist1_bound_from_p0 hg hk2 hp0_g hp0_k hge
  have hM_1_nn : 0 ≤ M_0 * (Fintype.card V : ℝ) := by positivity
  exact real_sep_of_hull_bound hp0_g hp0_k hM_1_nn (hull_A1_bound hg hk2 hM_0_nn hbound)

end RealSep

section Case2Helpers
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma conj_bound_of_ne_top {g : (V → ℤ) → WithTop ℝ} {x_R : V → ℝ}
    (hx_g : ConvexConjugateZR g x_R ≠ ⊤) {p1 : V → ℤ} (hp1 : g p1 ≠ ⊤) :
    ∃ C1 : ℝ, ∀ p : V → ℤ, g p ≠ ⊤ →
      -C1 + ∑ v : V, x_R v * (p v : ℝ) ≤ (g p).untopD 0 := by
  have h_ne_bot : ConvexConjugateZR g x_R ≠ ⊥ := by
    apply ne_bot_of_le_ne_bot (b := ((∑ v : V, x_R v * (p1 v : ℝ) - (g p1).untopD 0 : ℝ) : EReal))
      (EReal.coe_ne_bot _)
    unfold ConvexConjugateZR
    apply le_sSup
    refine ⟨p1, ?_⟩
    rw [← coe_untopD hp1]
    change (((∑ v : V, x_R v * (p1 v : ℝ) - (g p1).untopD 0 : ℝ)) : EReal) =
      ((∑ i : V, x_R i * (p1 i : ℝ) : ℝ) : EReal) - (((g p1).untopD 0 : ℝ) : EReal)
    rw [← EReal.coe_sub]
  lift ConvexConjugateZR g x_R to ℝ using ⟨hx_g, h_ne_bot⟩ with C1 hC1
  refine ⟨C1, fun p hgp => ?_⟩
  have hle : ((∑ i : V, x_R i * (p i : ℝ) : ℝ) : EReal) - ToEReal (g p) ≤ (C1 : EReal) := by
    rw [hC1]
    exact le_sSup ⟨p, rfl⟩
  rw [← coe_untopD hgp] at hle
  change ((∑ i : V, x_R i * (p i : ℝ) : ℝ) : EReal) - (((g p).untopD 0 : ℝ) : EReal) ≤ (C1 : EReal) at hle
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hle
  linarith

lemma concave_conj_bound_of_ne_bot {k2 : (V → ℤ) → WithTop ℝ} {x_R : V → ℝ}
    (hx_k : ConcaveConjugateZR k2 x_R ≠ ⊥) {p2 : V → ℤ} (hp2 : k2 p2 ≠ ⊤) :
    ∃ C2 : ℝ, ∀ q : V → ℤ, k2 q ≠ ⊤ →
      C2 - ∑ v : V, x_R v * (q v : ℝ) ≤ (k2 q).untopD 0 := by
  have h_ne_top : ConcaveConjugateZR k2 x_R ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (EReal.coe_ne_top (∑ v : V, x_R v * (p2 v : ℝ) + (k2 p2).untopD 0))
    unfold ConcaveConjugateZR
    apply sInf_le
    refine ⟨p2, ?_⟩
    rw [← coe_untopD hp2]
    change ((∑ i : V, x_R i * (p2 i : ℝ) : ℝ) : EReal) + (((k2 p2).untopD 0 : ℝ) : EReal) =
      (((∑ v : V, x_R v * (p2 v : ℝ) + (k2 p2).untopD 0 : ℝ)) : EReal)
    rw [← EReal.coe_add]
  lift ConcaveConjugateZR k2 x_R to ℝ using ⟨h_ne_top, hx_k⟩ with C2 hC2
  refine ⟨C2, fun q hkq => ?_⟩
  have hge : (C2 : EReal) ≤ ((∑ i : V, x_R i * (q i : ℝ) : ℝ) : EReal) + ToEReal (k2 q) := by
    rw [hC2]
    exact sInf_le ⟨q, rfl⟩
  rw [← coe_untopD hkq] at hge
  change (C2 : EReal) ≤ ((∑ i : V, x_R i * (q i : ℝ) : ℝ) : EReal) + (((k2 q).untopD 0 : ℝ) : EReal) at hge
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hge
  linarith

end Case2Helpers
end LSepAux

open Classical
open scoped Pointwise
open DiscreteConvex.ConjugacyDualityB
open LSepAux

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (g k2 : (V → ℤ) → WithTop ℝ) (hg : LNaturalConvex g)
    (hk2 : LNaturalConvex k2)
    (hdom : (DomZ g ∩ DomZ k2).Nonempty ∨
      (DomEReal (ConvexConjugateZR g) ∩ DomERealConcave (ConcaveConjugateZR k2)).Nonempty)
    (hge : ∀ p : V → ℤ, g p + k2 p ≥ 0) :
    (∃ beta : ℝ, ∃ x : V → ℝ,
      (∀ p : V → ℤ, g p ≥ ((beta + ∑ v, x v * (p v : ℝ) : ℝ) : WithTop ℝ)) ∧
      (∀ p : V → ℤ, ((beta + ∑ v, x v * (p v : ℝ) : ℝ) : WithTop ℝ) + k2 p ≥ 0)) ∧
    (IsIntegerValuedFn g → IsIntegerValuedFn k2 →
      ∃ beta : ℤ, ∃ x : V → ℤ,
        (∀ p : V → ℤ, g p ≥ ((beta + ∑ v, (x v : ℝ) * (p v : ℝ) : ℝ) : WithTop ℝ)) ∧
        (∀ p : V → ℤ, ((beta + ∑ v, (x v : ℝ) * (p v : ℝ) : ℝ) : WithTop ℝ) + k2 p ≥ 0)) := by
  by_cases h_inter : (DomZ g ∩ DomZ k2).Nonempty
  · obtain ⟨p0, hp0_g, hp0_k⟩ := h_inter
    refine ⟨real_sep_case1 hg hk2 hp0_g hp0_k hge, fun hgZ hk2Z => ?_⟩
    let g2 : (V → ℤ) → WithTop ℝ := fun p => k2 (-p)
    have hg2 : LNaturalConvex g2 := lnat_neg hk2
    have hg2Z : IsIntegerValuedFn g2 := fun p => hk2Z (-p)
    let P : ℤ → Prop := fun k => ∃ p1 p2 : V → ℤ, (0 : V → ℤ) = p1 + p2 ∧
      g p1 ≠ ⊤ ∧ g2 p2 ≠ ⊤ ∧ k = iv g p1 + iv g2 p2
    have hP_bdd : ∃ b : ℤ, ∀ k : ℤ, P k → b ≤ k := by
      refine ⟨0, ?_⟩
      rintro k ⟨p1, p2, hp12, hgp1, hg2p2, rfl⟩
      have hp2_eq : p2 = -p1 := eq_neg_of_add_eq_zero_right hp12.symm
      subst hp2_eq
      have hkp1 : k2 p1 ≠ ⊤ := by
        change k2 (- -p1) ≠ ⊤ at hg2p2
        rwa [neg_neg] at hg2p2
      have h0 := hge p1
      rw [iv_spec hgZ hgp1, iv_spec hk2Z hkp1, ← WithTop.coe_add, ge_iff_le,
        ← WithTop.coe_zero, WithTop.coe_le_coe] at h0
      have hiv_eq : iv g2 (-p1) = iv k2 p1 := by
        change iv (fun p => k2 (-p)) (-p1) = iv k2 p1
        exact iv_congr (by rw [neg_neg])
      rw [hiv_eq]
      have h0' : (0 : ℝ) ≤ ((iv g p1 + iv k2 p1 : ℤ) : ℝ) := by push_cast; exact h0
      exact_mod_cast h0'
    have hP_ne : ∃ k : ℤ, P k := by
      refine ⟨iv g p0 + iv g2 (-p0), p0, -p0, (add_neg_cancel p0).symm, hp0_g, ?_, rfl⟩
      show k2 (- -p0) ≠ ⊤; rw [neg_neg]; exact hp0_k
    obtain ⟨k_min, ⟨p1s, p2s, hp12s, hgp1s, hg2p2s, rfl⟩, hk_min⟩ :=
      Int.exists_least_of_bdd hP_bdd hP_ne
    obtain ⟨x, hx1, hx2⟩ := subgrad_at_min hg hg2 hgZ hg2Z hp12s hgp1s hg2p2s
      (fun p1 p2 hp12 h1 h2 => hk_min _ ⟨p1, p2, hp12, h1, h2, rfl⟩)
    let beta : ℤ := iv g p1s - idot x p1s
    refine ⟨beta, x, fun p => ?_, fun p => ?_⟩
    · by_cases hgp : g p = ⊤
      · rw [hgp]; exact le_top
      · rw [iv_spec hgZ hgp, dot_eq, ge_iff_le, WithTop.coe_le_coe]
        have h1 := hx1.2 p hgp
        have h2 : beta + idot x p ≤ iv g p := by dsimp [beta]; omega
        exact_mod_cast h2
    · by_cases hkp : k2 p = ⊤
      · rw [hkp, add_top]; exact le_top
      · rw [iv_spec hk2Z hkp, dot_eq, ← WithTop.coe_add, ge_iff_le, ← WithTop.coe_zero, WithTop.coe_le_coe]
        have hg2_negp : g2 (-p) ≠ ⊤ := by show k2 (- -p) ≠ ⊤; rw [neg_neg]; exact hkp
        have h1 := hx2.2 (-p) hg2_negp
        have hiv_negp : iv g2 (-p) = iv k2 p := iv_congr (by show k2 (- -p) = k2 p; rw [neg_neg])
        have hp2s_eq : p2s = -p1s := eq_neg_of_add_eq_zero_right hp12s.symm
        have hkp1s : k2 p1s ≠ ⊤ := by
          rw [hp2s_eq] at hg2p2s
          change k2 (- -p1s) ≠ ⊤ at hg2p2s
          rwa [neg_neg] at hg2p2s
        have hiv_p2s : iv g2 p2s = iv k2 p1s := by
          rw [hp2s_eq]; exact iv_congr (by show k2 (- -p1s) = k2 p1s; rw [neg_neg])
        have h0 := hge p1s
        rw [iv_spec hgZ hgp1s, iv_spec hk2Z hkp1s, ← WithTop.coe_add, ge_iff_le,
          ← WithTop.coe_zero, WithTop.coe_le_coe] at h0
        have h0_Z : 0 ≤ iv g p1s + iv k2 p1s := by
          have : (0 : ℝ) ≤ ((iv g p1s + iv k2 p1s : ℤ) : ℝ) := by push_cast; exact h0
          exact_mod_cast this
        rw [idot_neg_right, hiv_negp, hiv_p2s, hp2s_eq, idot_neg_right] at h1
        have h2 : 0 ≤ beta + idot x p + iv k2 p := by dsimp [beta]; omega
        exact_mod_cast h2
  · rcases hdom with h_in | ⟨x_R, hx_g, hx_k⟩
    · exact absurd h_in h_inter
    by_cases hdom_g : (DomZ g).Nonempty
    · obtain ⟨p1, hp1⟩ := hdom_g
      obtain ⟨C1, hC1⟩ := conj_bound_of_ne_top hx_g hp1
      by_cases hdom_k : (DomZ k2).Nonempty
      · obtain ⟨p2, hp2⟩ := hdom_k
        obtain ⟨C2, hC2⟩ := concave_conj_bound_of_ne_bot hx_k hp2
        let g2 : (V → ℤ) → WithTop ℝ := fun p => k2 (-p)
        have hg2 : LNaturalConvex g2 := lnat_neg hk2
        have hp2_neg : g2 (-p2) ≠ ⊤ := by show k2 (- -p2) ≠ ⊤; rw [neg_neg]; exact hp2
        have hdisj0 : ∀ q1 q2 : V → ℤ, (0 : V → ℤ) = q1 + q2 → g q1 = ⊤ ∨ g2 q2 = ⊤ := by
          intro q1 q2 hq12
          have hq2 : q2 = -q1 := eq_neg_of_add_eq_zero_right hq12.symm
          subst hq2
          by_contra hboth
          push_neg at hboth
          have h1 : q1 ∈ DomZ g := hboth.1
          have h2 : q1 ∈ DomZ k2 := by
            have := hboth.2; change k2 (- -q1) ≠ ⊤ at this; rwa [neg_neg] at this
          exact h_inter ⟨q1, h1, h2⟩
        obtain ⟨d0, hd0⟩ := sep_disjoint hg hg2 hp1 hp2_neg hdisj0
        let d' : V → ℤ := -d0
        have hd'_sep : ∀ p q : V → ℤ, g p ≠ ⊤ → k2 q ≠ ⊤ → idot d' q + 1 ≤ idot d' p := by
          intro p q hgp hkq
          have h := hd0 p (-q) hgp (by show k2 (- -q) ≠ ⊤; rw [neg_neg]; exact hkq)
          simp only [d', idot_neg_left, idot_add_right, idot_neg_right] at h ⊢
          have h0 : idot d0 0 = 0 := by simp [idot]
          omega
        let P_sep : ℤ → Prop := fun k => ∃ p : V → ℤ, g p ≠ ⊤ ∧ k = idot d' p
        have hP_sep_bdd : ∃ b : ℤ, ∀ k : ℤ, P_sep k → b ≤ k := by
          refine ⟨idot d' p2 + 1, ?_⟩
          rintro k ⟨p, hgp, rfl⟩
          exact hd'_sep p p2 hgp hp2
        obtain ⟨γ1, ⟨p_star, hgp_star, rfl⟩, hγ1_min⟩ :=
          Int.exists_least_of_bdd hP_sep_bdd ⟨idot d' p1, p1, hp1, rfl⟩
        let γ : ℤ := idot d' p_star - 1
        have hγ_g : ∀ p : V → ℤ, g p ≠ ⊤ → γ + 1 ≤ idot d' p := by
          intro p hgp
          have := hγ1_min (idot d' p) ⟨p, hgp, rfl⟩
          dsimp [γ]; omega
        have hγ_k : ∀ q : V → ℤ, k2 q ≠ ⊤ → idot d' q ≤ γ := by
          intro q hkq
          have := hd'_sep p_star q hgp_star hkq
          dsimp [γ]; omega
        refine ⟨?_, fun hgZ hk2Z => ?_⟩
        · let t : ℝ := max 0 (C1 - C2)
          have ht_nn : 0 ≤ t := le_max_left _ _
          let x : V → ℝ := fun v => x_R v - t * (d' v : ℝ)
          let beta : ℝ := -C1 + t * ((γ + 1 : ℤ) : ℝ)
          refine ⟨beta, x, fun p => ?_, fun q => ?_⟩
          · by_cases hgp : g p = ⊤
            · rw [hgp]; exact le_top
            · rw [← coe_untopD hgp, ge_iff_le, WithTop.coe_le_coe]
              have h1 := hC1 p hgp
              have h2 : ((γ + 1 : ℤ) : ℝ) ≤ ∑ v : V, (d' v : ℝ) * (p v : ℝ) := by
                rw [dot_eq]
                exact_mod_cast hγ_g p hgp
              have h_sum : ∑ v : V, x v * (p v : ℝ) =
                  (∑ v : V, x_R v * (p v : ℝ)) - t * ∑ v : V, (d' v : ℝ) * (p v : ℝ) := by
                dsimp [x]
                simp_rw [sub_mul, mul_assoc]
                rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
              rw [h_sum]
              have h3 : t * ((γ + 1 : ℤ) : ℝ) ≤ t * ∑ v : V, (d' v : ℝ) * (p v : ℝ) :=
                mul_le_mul_of_nonneg_left h2 ht_nn
              dsimp [beta]
              linarith
          · by_cases hkq : k2 q = ⊤
            · rw [hkq, add_top]; exact le_top
            · rw [← coe_untopD hkq, ← WithTop.coe_add, ge_iff_le, ← WithTop.coe_zero, WithTop.coe_le_coe]
              have h1 := hC2 q hkq
              have h2 : ∑ v : V, (d' v : ℝ) * (q v : ℝ) ≤ (γ : ℝ) := by
                rw [dot_eq]
                exact_mod_cast hγ_k q hkq
              have h_sum : ∑ v : V, x v * (q v : ℝ) =
                  (∑ v : V, x_R v * (q v : ℝ)) - t * ∑ v : V, (d' v : ℝ) * (q v : ℝ) := by
                dsimp [x]
                simp_rw [sub_mul, mul_assoc]
                rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
              rw [h_sum]
              have h3 : t * ∑ v : V, (d' v : ℝ) * (q v : ℝ) ≤ t * (γ : ℝ) :=
                mul_le_mul_of_nonneg_left h2 ht_nn
              have ht_diff : C1 - C2 ≤ t := le_max_right _ _
              dsimp [beta]
              push_cast
              linarith
        · have hg2Z : IsIntegerValuedFn g2 := fun p => hk2Z (-p)
          let p0_sum : V → ℤ := p1 - p2
          let P_conv : ℤ → Prop := fun k => ∃ q1 q2 : V → ℤ, p0_sum = q1 + q2 ∧
            g q1 ≠ ⊤ ∧ g2 q2 ≠ ⊤ ∧ k = iv g q1 + iv g2 q2
          have hP_conv_bdd : ∃ b : ℤ, ∀ k : ℤ, P_conv k → b ≤ k := by
            let B_low : ℝ := -C1 + C2 + ∑ v : V, x_R v * (p0_sum v : ℝ)
            refine ⟨⌊B_low⌋, ?_⟩
            rintro k ⟨q1, q2, hq12, hgq1, hg2q2, rfl⟩
            have hkq2 : k2 (-q2) ≠ ⊤ := hg2q2
            have h1 := hC1 q1 hgq1
            have h2 := hC2 (-q2) hkq2
            have hiv1 : (g q1).untopD 0 = (iv g q1 : ℝ) := by
              rw [iv_spec hgZ hgq1, untopD_coe]
            have hiv2 : (k2 (-q2)).untopD 0 = (iv g2 q2 : ℝ) := by
              have : g2 q2 = k2 (-q2) := rfl
              rw [← this, iv_spec hg2Z hg2q2, untopD_coe]
            rw [hiv1] at h1
            rw [hiv2] at h2
            have h_sum_xR : (∑ v : V, x_R v * (q1 v : ℝ)) - (∑ v : V, x_R v * ((-q2) v : ℝ)) =
                ∑ v : V, x_R v * (p0_sum v : ℝ) := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun v _ => ?_
              have hv : p0_sum v = q1 v + q2 v := congrFun hq12 v
              simp only [hv, Pi.neg_apply, Int.cast_add, Int.cast_neg]
              ring
            have h_le_R : B_low ≤ ((iv g q1 + iv g2 q2 : ℤ) : ℝ) := by
              dsimp [B_low]
              push_cast
              linarith
            exact Int.floor_le_iff.mpr (by linarith)
          have hP_conv_ne : ∃ k : ℤ, P_conv k :=
            ⟨iv g p1 + iv g2 (-p2), p1, -p2, rfl, hp1, hp2_neg, rfl⟩
          obtain ⟨k_min, ⟨q1s, q2s, hq12s, hgq1s, hg2q2s, rfl⟩, hk_min⟩ :=
            Int.exists_least_of_bdd hP_conv_bdd hP_conv_ne
          obtain ⟨x0, hx0_1, hx0_2⟩ := subgrad_at_min hg hg2 hgZ hg2Z hq12s hgq1s hg2q2s
            (fun q1 q2 hq12 h1 h2 => hk_min _ ⟨q1, q2, hq12, h1, h2, rfl⟩)
          let A1_int : ℤ := iv g q1s - idot x0 q1s
          let A2_int : ℤ := -iv g2 q2s - idot x0 (-q2s)
          let t_Z : ℤ := max 0 (A2_int - A1_int)
          let x : V → ℤ := x0 - t_Z • d'
          let beta : ℤ := A1_int + t_Z * (γ + 1)
          refine ⟨beta, x, fun p => ?_, fun q => ?_⟩
          · by_cases hgp : g p = ⊤
            · rw [hgp]; exact le_top
            · rw [iv_spec hgZ hgp, dot_eq, ge_iff_le, WithTop.coe_le_coe]
              have h1 := hx0_1.2 p hgp
              have h2 := hγ_g p hgp
              have ht_nn : 0 ≤ t_Z := le_max_left _ _
              have h3 : t_Z * (γ + 1) ≤ t_Z * idot d' p := mul_le_mul_of_nonneg_left h2 ht_nn
              have h_idot : idot x p = idot x0 p - t_Z * idot d' p := by
                dsimp [x]; rw [idot_sub_left, idot_smul_left]
              have h4 : beta + idot x p ≤ iv g p := by
                rw [h_idot]; dsimp [beta, A1_int]; omega
              exact_mod_cast h4
          · by_cases hkq : k2 q = ⊤
            · rw [hkq, add_top]; exact le_top
            · rw [iv_spec hk2Z hkq, dot_eq, ← WithTop.coe_add, ge_iff_le, ← WithTop.coe_zero, WithTop.coe_le_coe]
              have hg2_negq : g2 (-q) ≠ ⊤ := by show k2 (- -q) ≠ ⊤; rw [neg_neg]; exact hkq
              have h1 := hx0_2.2 (-q) hg2_negq
              have hiv_negq : iv g2 (-q) = iv k2 q := iv_congr (by show k2 (- -q) = k2 q; rw [neg_neg])
              rw [idot_neg_right, hiv_negq] at h1
              have h2 := hγ_k q hkq
              have ht_nn : 0 ≤ t_Z := le_max_left _ _
              have h3 : t_Z * idot d' q ≤ t_Z * γ := mul_le_mul_of_nonneg_left h2 ht_nn
              have ht_diff : A2_int - A1_int ≤ t_Z := le_max_right _ _
              have h_idot : idot x q = idot x0 q - t_Z * idot d' q := by
                dsimp [x]; rw [idot_sub_left, idot_smul_left]
              have h4 : 0 ≤ beta + idot x q + iv k2 q := by
                have h_mul : t_Z * (γ + 1) = t_Z * γ + t_Z := by ring
                have hA1 : A1_int = iv g q1s - idot x0 q1s := rfl
                have hA2 : A2_int = -iv g2 q2s + idot x0 q2s := by
                  dsimp [A2_int]; rw [idot_neg_right]; ring
                have h_beta : beta = A1_int + (t_Z * γ + t_Z) := by
                  dsimp [beta]; rw [h_mul]
                omega
              exact_mod_cast h4
      · have hk_all_top : ∀ q : V → ℤ, k2 q = ⊤ := by
          intro q
          by_contra hne
          exact hdom_k ⟨q, hne⟩
        refine ⟨⟨-C1, x_R, fun p => ?_, fun q => ?_⟩, fun hgZ _ => ?_⟩
        · by_cases hgp : g p = ⊤
          · rw [hgp]; exact le_top
          · rw [← coe_untopD hgp, ge_iff_le, WithTop.coe_le_coe]
            exact hC1 p hgp
        · rw [hk_all_top q, add_top]; exact le_top
        · obtain ⟨x, hx⟩ := subgrad_single hg hgZ hp1
          refine ⟨iv g p1 - idot x p1, x, fun p => ?_, fun q => ?_⟩
          · by_cases hgp : g p = ⊤
            · rw [hgp]; exact le_top
            · rw [iv_spec hgZ hgp, dot_eq, ge_iff_le, WithTop.coe_le_coe]
              have h1 := hx.2 p hgp
              exact_mod_cast (by omega : iv g p1 - idot x p1 + idot x p ≤ iv g p)
          · rw [hk_all_top q, add_top]; exact le_top
    · have hg_all_top : ∀ p : V → ℤ, g p = ⊤ := by
        intro p
        by_contra hne
        exact hdom_g ⟨p, hne⟩
      by_cases hdom_k : (DomZ k2).Nonempty
      · obtain ⟨p2, hp2⟩ := hdom_k
        obtain ⟨C2, hC2⟩ := concave_conj_bound_of_ne_bot hx_k hp2
        refine ⟨⟨-C2, x_R, fun p => ?_, fun q => ?_⟩, fun _ hk2Z => ?_⟩
        · rw [hg_all_top p]; exact le_top
        · by_cases hkq : k2 q = ⊤
          · rw [hkq, add_top]; exact le_top
          · rw [← coe_untopD hkq, ← WithTop.coe_add, ge_iff_le, ← WithTop.coe_zero, WithTop.coe_le_coe]
            have h1 := hC2 q hkq
            linarith
        · let g2 : (V → ℤ) → WithTop ℝ := fun p => k2 (-p)
          have hg2 : LNaturalConvex g2 := lnat_neg hk2
          have hg2Z : IsIntegerValuedFn g2 := fun p => hk2Z (-p)
          have hp2_neg : g2 (-p2) ≠ ⊤ := by show k2 (- -p2) ≠ ⊤; rw [neg_neg]; exact hp2
          obtain ⟨x, hx⟩ := subgrad_single hg2 hg2Z hp2_neg
          refine ⟨-iv g2 (-p2) - idot x p2, x, fun p => ?_, fun q => ?_⟩
          · rw [hg_all_top p]; exact le_top
          · by_cases hkq : k2 q = ⊤
            · rw [hkq, add_top]; exact le_top
            · rw [iv_spec hk2Z hkq, dot_eq, ← WithTop.coe_add, ge_iff_le, ← WithTop.coe_zero, WithTop.coe_le_coe]
              have hg2_negq : g2 (-q) ≠ ⊤ := by show k2 (- -q) ≠ ⊤; rw [neg_neg]; exact hkq
              have h1 := hx.2 (-q) hg2_negq
              have hiv_negq : iv g2 (-q) = iv k2 q := iv_congr (by show k2 (- -q) = k2 q; rw [neg_neg])
              rw [idot_neg_right, idot_neg_right, hiv_negq] at h1
              exact_mod_cast (by omega : 0 ≤ -iv g2 (-p2) - idot x p2 + idot x q + iv k2 q)
      · have hk_all_top : ∀ q : V → ℤ, k2 q = ⊤ := by
          intro q
          by_contra hne
          exact hdom_k ⟨q, hne⟩
        refine ⟨⟨0, 0, fun p => by rw [hg_all_top p]; exact le_top,
          fun q => by rw [hk_all_top q, add_top]; exact le_top⟩,
          fun _ _ => ⟨0, 0, fun p => by rw [hg_all_top p]; exact le_top,
          fun q => by rw [hk_all_top q, add_top]; exact le_top⟩⟩

