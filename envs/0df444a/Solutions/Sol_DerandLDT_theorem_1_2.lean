-- Prove2me | solution 1 for DerandLDT.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T08:20:13.771074+00:00
-- url     : https://prove2.me/submissions/2e9833fc-9dcf-4212-aa9e-ec140a7c4058

import Mathlib
import Definitions.Def_DerandLDT_localAgr
import Definitions.Def_LineVsPoint_agr
import Theorems.Thm_DerandLDT_lemma_3_18
import Theorems.Thm_DerandLDT_lemma_3_2_ii

set_option autoImplicit false

universe u

section Part0
open Polynomial

namespace DLT

section Coord
variable {F : Type*} [Field F]

/-- The determinant of two vectors of `F²`. -/
def det2 (a b : Fin 2 → F) : F := a 0 * b 1 - a 1 * b 0

/-- First coordinate of `x` in the basis `(w, v)`. -/
noncomputable def lam (w v x : Fin 2 → F) : F := det2 x v / det2 w v

/-- Second coordinate of `x` in the basis `(w, v)`. -/
noncomputable def mu (w v x : Fin 2 → F) : F := det2 w x / det2 w v

lemma det2_self (a : Fin 2 → F) : det2 a a = 0 := by unfold det2; ring

lemma det2_comm (a b : Fin 2 → F) : det2 a b = - det2 b a := by unfold det2; ring

lemma det2_add_left (a a' b : Fin 2 → F) : det2 (a + a') b = det2 a b + det2 a' b := by
  unfold det2; simp only [Pi.add_apply]; ring

lemma det2_add_right (a b b' : Fin 2 → F) : det2 a (b + b') = det2 a b + det2 a b' := by
  unfold det2; simp only [Pi.add_apply]; ring

lemma det2_smul_left (c : F) (a b : Fin 2 → F) : det2 (c • a) b = c * det2 a b := by
  unfold det2; simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma det2_smul_right (c : F) (a b : Fin 2 → F) : det2 a (c • b) = c * det2 a b := by
  unfold det2; simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma decomp {w v : Fin 2 → F} (h : det2 w v ≠ 0) (x : Fin 2 → F) :
    x = lam w v x • w + mu w v x • v := by
  funext i
  simp only [lam, mu, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
  fin_cases i <;> simp [det2] <;> ring

lemma lam_comb {w v : Fin 2 → F} (h : det2 w v ≠ 0) (a t : F) :
    lam w v (a • w + t • v) = a := by
  unfold lam
  rw [det2_add_left, det2_smul_left, det2_smul_left, det2_self]
  field_simp
  ring

lemma mu_comb {w v : Fin 2 → F} (h : det2 w v ≠ 0) (a t : F) :
    mu w v (a • w + t • v) = t := by
  unfold mu
  rw [det2_add_right, det2_smul_right, det2_smul_right, det2_self]
  field_simp
  ring

lemma lam_add {w v : Fin 2 → F} (x y : Fin 2 → F) :
    lam w v (x + y) = lam w v x + lam w v y := by
  unfold lam; rw [det2_add_left, add_div]

lemma mu_add {w v : Fin 2 → F} (x y : Fin 2 → F) :
    mu w v (x + y) = mu w v x + mu w v y := by
  unfold mu; rw [det2_add_right, add_div]

lemma lam_smul {w v : Fin 2 → F} (c : F) (x : Fin 2 → F) :
    lam w v (c • x) = c * lam w v x := by
  unfold lam; rw [det2_smul_left, mul_div_assoc]

lemma mu_smul {w v : Fin 2 → F} (c : F) (x : Fin 2 → F) :
    mu w v (c • x) = c * mu w v x := by
  unfold mu; rw [det2_smul_right, mul_div_assoc]

lemma lam_v {w v : Fin 2 → F} : lam w v v = 0 := by
  unfold lam; rw [det2_self, zero_div]

lemma mu_v {w v : Fin 2 → F} (h : det2 w v ≠ 0) : mu w v v = 1 := by
  unfold mu; exact div_self h

/-- `det2 a b = 0` with `a ≠ 0` forces `b` to be a multiple of `a`. -/
lemma eq_smul_of_det2_eq_zero {a b : Fin 2 → F} (ha : a ≠ 0) (h : det2 a b = 0) :
    ∃ c : F, b = c • a := by
  unfold det2 at h
  by_cases h0 : a 0 = 0
  · have h1 : a 1 ≠ 0 := by
      intro h1; apply ha; funext i; fin_cases i <;> simp [h0, h1]
    refine ⟨b 1 / a 1, ?_⟩
    funext i
    fin_cases i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta]
      rw [h0, zero_mul] at h
      have : b 0 = 0 := by
        rcases mul_eq_zero.mp (show a 1 * b 0 = 0 by linear_combination -h) with h' | h'
        · exact absurd h' h1
        · exact h'
      rw [this, h0, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.mk_one]
      field_simp
  · refine ⟨b 0 / a 0, ?_⟩
    funext i
    fin_cases i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta]
      field_simp
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.mk_one]
      field_simp
      linear_combination h

end Coord

end DLT

end Part0

section Part1

open Polynomial

namespace DLT

section Bridge
variable {F : Type*} [Field F]

/-- A nonzero generator of a one-dimensional subspace. -/
lemma exists_gen (u : Submodule F (Fin 2 → F)) (hu : Module.finrank F u = 1) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ u = Submodule.span F {v} := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hu
  refine ⟨v, fun h => hv0 (Subtype.ext h), ?_⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc⟩ := hv ⟨x, hx⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact v.2

open Classical in
/-- A complement vector. -/
noncomputable def compl (v : Fin 2 → F) : Fin 2 → F := if v 0 = 0 then ![1, 0] else ![0, 1]

lemma det2_compl {v : Fin 2 → F} (hv : v ≠ 0) : det2 (compl v) v ≠ 0 := by
  unfold compl det2
  split_ifs with h
  · simp only [Matrix.cons_val_zero, one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      zero_mul, sub_zero]
    intro h1; apply hv; funext i; fin_cases i <;> simp [h, h1]
  · simp [h]

/-- The line `{a • w + t • v}`. -/
def lineOf (w v : Fin 2 → F) (hv : v ≠ 0) (a : F) : LineVsPoint.Line F 2 where
  carrier := Set.range (fun t : F => a • w + t • v)
  isFlat := by
    refine ⟨a • w, ![v], ?_, ?_⟩
    · exact linearIndependent_unique_iff.mpr (by simpa using hv)
    · ext x
      simp only [Set.mem_range, Fin.sum_univ_one, Matrix.cons_val_fin_one]
      constructor
      · rintro ⟨t, rfl⟩; exact ⟨fun _ => t, rfl⟩
      · rintro ⟨t, rfl⟩; exact ⟨t 0, rfl⟩

lemma vectorSpan_range_line (p u : Fin 2 → F) :
    vectorSpan F (Set.range fun t : F => p + t • u) = Submodule.span F {u} := by
  rw [vectorSpan_eq_span_vsub_set_right F (show p ∈ Set.range fun t : F => p + t • u from
    ⟨0, by simp⟩)]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    simp only [vsub_eq_sub, add_sub_cancel_left, SetLike.mem_coe]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    apply Submodule.subset_span
    exact ⟨p + (1 : F) • u, ⟨1, rfl⟩, by simp⟩

/-- Every line is `{p + t • u}` with `u ≠ 0`. -/
lemma line_param (L : LineVsPoint.Line F 2) :
    ∃ p u : Fin 2 → F, u ≠ 0 ∧ L.carrier = Set.range fun t : F => p + t • u := by
  obtain ⟨a, vv, hli, hc⟩ := L.isFlat
  refine ⟨a, vv 0, hli.ne_zero 0, ?_⟩
  rw [hc]
  ext x
  simp only [Set.mem_range, Fin.sum_univ_one]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t 0, rfl⟩
  · rintro ⟨t, rfl⟩; exact ⟨fun _ => t, rfl⟩

lemma lineOf_carrier (w v : Fin 2 → F) (hv : v ≠ 0) (a : F) :
    (lineOf w v hv a).carrier = Set.range (fun t : F => a • w + t • v) := rfl

lemma vectorSpan_lineOf (w v : Fin 2 → F) (hv : v ≠ 0) (a : F) :
    vectorSpan F (lineOf w v hv a).carrier = Submodule.span F {v} :=
  vectorSpan_range_line _ _

lemma mem_lineOf {w v : Fin 2 → F} (hv : v ≠ 0) (h : det2 w v ≠ 0) (a : F) (x : Fin 2 → F) :
    x ∈ (lineOf w v hv a).carrier ↔ lam w v x = a := by
  rw [lineOf_carrier]
  constructor
  · rintro ⟨t, rfl⟩; exact lam_comb h a t
  · intro hx; exact ⟨mu w v x, by rw [← hx]; exact (decomp h x).symm⟩

/-- A line along `span {v}` through `x` is `lineOf w v (lam x)`. -/
lemma eq_lineOf {w v : Fin 2 → F} (hv : v ≠ 0) (h : det2 w v ≠ 0) (L : LineVsPoint.Line F 2)
    (hL : vectorSpan F L.carrier = Submodule.span F {v}) (x : Fin 2 → F) (hx : x ∈ L.carrier) :
    L = lineOf w v hv (lam w v x) := by
  obtain ⟨p, u, hu, hc⟩ := line_param L
  have hsp : Submodule.span F {u} = Submodule.span F {v} := by
    rw [← hL, hc, vectorSpan_range_line]
  have hu' : u ∈ Submodule.span F {v} := hsp ▸ Submodule.mem_span_singleton_self u
  obtain ⟨c, hcu⟩ := Submodule.mem_span_singleton.mp hu'
  have hc0 : c ≠ 0 := by rintro rfl; apply hu; rw [← hcu, zero_smul]
  rw [hc] at hx
  obtain ⟨s₀, hs₀⟩ := hx
  simp only at hs₀
  have hd := decomp h x
  apply LineVsPoint.AffFlat.ext
  rw [hc, lineOf_carrier]
  ext y
  simp only [Set.mem_range]
  subst hcu
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨mu w v x + (s - s₀) * c, ?_⟩
    rw [← hs₀] at hd ⊢
    linear_combination (norm := module) -hd
  · rintro ⟨t, rfl⟩
    refine ⟨s₀ + (t - mu w v x) / c, ?_⟩
    have e : ((t - mu w v x) / c) • c • v = (t - mu w v x) • v := by
      rw [smul_smul, div_mul_cancel₀ _ hc0]
    rw [add_smul, ← add_assoc, e]
    rw [← hs₀] at hd ⊢
    linear_combination (norm := module) hd

/-- Data attached to a line of the table along `span {v}` in the basis `(w, v)`. -/
lemma table_line_data {k : ℕ} (P : LineVsPoint.LineTable F 2 k) {w v : Fin 2 → F} (hv : v ≠ 0)
    (h : det2 w v ≠ 0) (a : F) :
    P.a (lineOf w v hv a) = a • w + mu w v (P.a (lineOf w v hv a)) • v ∧
    P.u (lineOf w v hv a) = mu w v (P.u (lineOf w v hv a)) • v ∧
    mu w v (P.u (lineOf w v hv a)) ≠ 0 := by
  set L := lineOf w v hv a
  have hr := P.range_eq L
  have ha : P.a L ∈ L.carrier := by rw [hr]; exact ⟨0, by simp⟩
  have ha1 : P.a L + P.u L ∈ L.carrier := by rw [hr]; exact ⟨1, by simp⟩
  rw [mem_lineOf hv h] at ha ha1
  rw [lam_add, ha] at ha1
  have hlu : lam w v (P.u L) = 0 := by linear_combination ha1
  have hdu := decomp h (P.u L)
  rw [hlu, zero_smul, zero_add] at hdu
  refine ⟨?_, hdu, ?_⟩
  · have := decomp h (P.a L); rwa [ha] at this
  · intro h0; apply P.u_ne L; rw [hdu, h0, zero_smul]

/-- The line polynomial in the `mu`-parameter. -/
noncomputable def tablePoly {k : ℕ} (P : LineVsPoint.LineTable F 2 k) (w v : Fin 2 → F)
    (hv : v ≠ 0) (a : F) : Polynomial F :=
  (P.p (lineOf w v hv a)).comp (C (mu w v (P.u (lineOf w v hv a)))⁻¹ *
    (X - C (mu w v (P.a (lineOf w v hv a)))))

lemma tablePoly_natDegree {k : ℕ} (P : LineVsPoint.LineTable F 2 k) (w v : Fin 2 → F)
    (hv : v ≠ 0) (a : F) : (tablePoly P w v hv a).natDegree ≤ k := by
  unfold tablePoly
  refine (natDegree_comp_le).trans ?_
  have h1 : (C (mu w v (P.u (lineOf w v hv a)))⁻¹ * (X - C (mu w v (P.a (lineOf w v hv a))))
      : Polynomial F).natDegree ≤ 1 := by
    refine (natDegree_C_mul_le _ _).trans ?_
    exact (natDegree_sub_le _ _).trans (by simp)
  calc _ ≤ (P.p (lineOf w v hv a)).natDegree * 1 := Nat.mul_le_mul_left _ h1
    _ ≤ k := by rw [mul_one]; exact P.natDegree_le _

lemma accepted_iff {k : ℕ} (P : LineVsPoint.LineTable F 2 k) (f : (Fin 2 → F) → F)
    {w v : Fin 2 → F} (hv : v ≠ 0) (h : det2 w v ≠ 0) (x : Fin 2 → F) :
    LineVsPoint.Accepted f P x (lineOf w v hv (lam w v x)) ↔
      (tablePoly P w v hv (lam w v x)).eval (mu w v x) = f x := by
  obtain ⟨hA, hU, hk⟩ := table_line_data P hv h (lam w v x)
  set L := lineOf w v hv (lam w v x)
  set τ := mu w v (P.a L)
  set κ := mu w v (P.u L)
  have hxL : x ∈ L.carrier := (mem_lineOf hv h _ x).mpr rfl
  unfold LineVsPoint.Accepted tablePoly
  simp only [eval_comp, eval_mul, eval_C, eval_sub, eval_X]
  constructor
  · rintro ⟨-, t, ht, hp⟩
    have hmu := congrArg (mu w v) ht
    rw [hA, hU, smul_smul, show lam w v x • w + τ • v + (t * κ) • v =
      lam w v x • w + (τ + t * κ) • v by module, mu_comb h] at hmu
    have : κ⁻¹ * (mu w v x - τ) = t := by
      rw [← hmu]; field_simp; ring
    rw [this]; exact hp
  · intro hp
    refine ⟨hxL, κ⁻¹ * (mu w v x - τ), ?_, hp⟩
    rw [hA, hU, smul_smul]
    have hd := decomp h x
    conv_rhs => rw [hd]
    have e : κ⁻¹ * (mu w v x - τ) * κ = mu w v x - τ := by field_simp
    rw [e]
    module

lemma span_eq_of_det2_eq_zero {a b : Fin 2 → F} (ha : a ≠ 0) (hb : b ≠ 0) (h : det2 a b = 0) :
    Submodule.span F {b} = Submodule.span F {a} := by
  obtain ⟨c, rfl⟩ := eq_smul_of_det2_eq_zero ha h
  have hc : c ≠ 0 := by rintro rfl; exact hb (zero_smul _ _)
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc) a

end Bridge

section Count
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem bridge (k r : ℕ) (U : Finset (Submodule F (Fin 2 → F)))
    (hU : ∀ u ∈ U, Module.finrank F u = 1) (hr : U.card = r)
    (P : LineVsPoint.LineTable F 2 k) (f : (Fin 2 → F) → F) :
    ∃ (w v : Fin r → Fin 2 → F) (G : Fin r → F → Polynomial F),
      (∀ i, det2 (w i) (v i) ≠ 0) ∧ (∀ i j, i ≠ j → det2 (v i) (v j) ≠ 0) ∧
      (∀ i a, (G i a).natDegree ≤ k) ∧
      DerandLDT.localAgr f P U * ((r : ℝ) * (Fintype.card F : ℝ) ^ 2) =
        ∑ i, ((Finset.univ.filter fun x =>
          (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card : ℝ) := by
  classical
  let e : Fin r ≃ U := (U.equivFinOfCardEq hr).symm
  have hgen : ∀ i, ∃ v : Fin 2 → F, v ≠ 0 ∧ (e i : Submodule F (Fin 2 → F)) =
      Submodule.span F {v} := fun i => exists_gen _ (hU _ (e i).2)
  choose v hv hspan using hgen
  let w : Fin r → Fin 2 → F := fun i => compl (v i)
  have hw : ∀ i, det2 (w i) (v i) ≠ 0 := fun i => det2_compl (hv i)
  refine ⟨w, v, fun i a => tablePoly P (w i) (v i) (hv i) a, hw, ?_, ?_, ?_⟩
  · intro i j hij h0
    apply hij
    have h1 := span_eq_of_det2_eq_zero (hv i) (hv j) h0
    apply e.injective
    apply Subtype.ext
    rw [hspan i, hspan j, h1]
  · intro i a; exact tablePoly_natDegree P _ _ _ a
  -- the counting
  let lineAt : Fin r → (Fin 2 → F) → LineVsPoint.Line F 2 :=
    fun i x => lineOf (w i) (v i) (hv i) (lam (w i) (v i) x)
  have hmem : ∀ i x, x ∈ (lineAt i x).carrier := fun i x =>
    (mem_lineOf (hv i) (hw i) _ x).mpr rfl
  have halong : ∀ i x, lineAt i x ∈ DerandLDT.linesAlong U := by
    intro i x
    simp only [DerandLDT.linesAlong, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [vectorSpan_lineOf, ← hspan i]; exact (e i).2
  have hsurj : ∀ L ∈ DerandLDT.linesAlong U, ∀ x ∈ L.carrier, ∃ i, L = lineAt i x := by
    intro L hL x hx
    simp only [DerandLDT.linesAlong, Finset.mem_filter, Finset.mem_univ, true_and] at hL
    obtain ⟨i, hi⟩ := e.surjective ⟨_, hL⟩
    refine ⟨i, eq_lineOf (hv i) (hw i) L ?_ x hx⟩
    rw [← hspan i, hi]
  have hinj : ∀ x i j, lineAt i x = lineAt j x → i = j := by
    intro x i j hij
    have := congrArg (fun L : LineVsPoint.Line F 2 => vectorSpan F L.carrier) hij
    simp only [lineAt, vectorSpan_lineOf] at this
    apply e.injective; apply Subtype.ext; rw [hspan i, hspan j, this]
  let φ : (Fin 2 → F) × Fin r → (Fin 2 → F) × LineVsPoint.Line F 2 :=
    fun xi => (xi.1, lineAt xi.2 xi.1)
  have hφ : Function.Injective φ := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    rw [hinj x i j h2]
  have hInc : (Finset.univ.filter fun xL : (Fin 2 → F) × LineVsPoint.Line F 2 =>
      xL.2 ∈ DerandLDT.linesAlong U ∧ xL.1 ∈ xL.2.carrier) = Finset.univ.image φ := by
    ext ⟨x, L⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, φ, Prod.mk.injEq,
      Prod.exists]
    constructor
    · rintro ⟨hL, hx⟩
      obtain ⟨i, rfl⟩ := hsurj L hL x hx
      exact ⟨x, i, rfl, rfl⟩
    · rintro ⟨y, i, rfl, rfl⟩
      exact ⟨halong i y, hmem i y⟩
  have hAcc : (Finset.univ.filter fun xL : (Fin 2 → F) × LineVsPoint.Line F 2 =>
      xL.2 ∈ DerandLDT.linesAlong U ∧ LineVsPoint.Accepted f P xL.1 xL.2) =
      (Finset.univ.filter fun xi : (Fin 2 → F) × Fin r =>
        (tablePoly P (w xi.2) (v xi.2) (hv xi.2) (lam (w xi.2) (v xi.2) xi.1)).eval
          (mu (w xi.2) (v xi.2) xi.1) = f xi.1).image φ := by
    ext ⟨x, L⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, φ, Prod.mk.injEq,
      Prod.exists]
    constructor
    · rintro ⟨hL, hacc⟩
      obtain ⟨i, rfl⟩ := hsurj L hL x hacc.1
      exact ⟨x, i, (accepted_iff P f (hv i) (hw i) x).mp hacc, rfl, rfl⟩
    · rintro ⟨y, i, hy, rfl, rfl⟩
      exact ⟨halong i y, (accepted_iff P f (hv i) (hw i) y).mpr hy⟩
  have hcardInc : ((Finset.univ.filter fun xL : (Fin 2 → F) × LineVsPoint.Line F 2 =>
      xL.2 ∈ DerandLDT.linesAlong U ∧ xL.1 ∈ xL.2.carrier).card : ℝ) =
      (r : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
    rw [hInc, Finset.card_image_of_injective _ hφ, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fun, Fintype.card_fin]
    push_cast; ring
  have hcardAcc : ((Finset.univ.filter fun xL : (Fin 2 → F) × LineVsPoint.Line F 2 =>
      xL.2 ∈ DerandLDT.linesAlong U ∧ LineVsPoint.Accepted f P xL.1 xL.2).card : ℝ) =
      ∑ i, ((Finset.univ.filter fun x =>
          (tablePoly P (w i) (v i) (hv i) (lam (w i) (v i) x)).eval (mu (w i) (v i) x) =
            f x).card : ℝ) := by
    rw [hAcc, Finset.card_image_of_injective _ hφ]
    rw [← Nat.cast_sum]
    congr 1
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.card_filter]
  unfold DerandLDT.localAgr
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    simp
  have hpos : (0 : ℝ) < (r : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
    have : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    positivity
  have e1 : ((Finset.univ.filter fun xL : (Fin 2 → F) × LineVsPoint.Line F 2 =>
      xL.2 ∈ DerandLDT.linesAlong U ∧ xL.1 ∈ xL.2.carrier).card : ℝ) =
      (r : ℝ) * (Fintype.card F : ℝ) ^ 2 := hcardInc
  rw [← hcardAcc]
  convert div_mul_cancel₀ _ hpos.ne' using 3

end Count
end DLT
end Part1

section Part2
open Polynomial

namespace DLT
namespace A1

theorem comp_CX_coeff {R : Type*} [CommRing R] (p : R[X]) (c : R) (m : ℕ) :
    (p.comp (C c * X)).coeff m = c ^ m * p.coeff m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc,
      ← C_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

theorem comp_CX_injective {R : Type*} [CommRing R] [IsDomain R] (c : R) (hc : c ≠ 0) (p q : R[X])
    (hp : p.comp (C c * X) = q.comp (C c * X)) : p = q := by
  ext m
  have := congrArg (fun r => r.coeff m) hp
  simp only [comp_CX_coeff] at this
  exact mul_left_cancel₀ (pow_ne_zero m hc) this

theorem natDegree_comp_CX_le {R : Type*} [CommRing R] (p : R[X]) (c : R) :
    (p.comp (C c * X)).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [comp_CX_coeff, coeff_eq_zero_of_natDegree_lt hm, mul_zero]

theorem eval_coeff_zero {B : Type*} [CommRing B] (p : B[X][X]) (x : B[X]) (hx : x.coeff 0 = 0) :
    (p.eval x).coeff 0 = (p.coeff 0).coeff 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    cases n with
    | zero => simp
    | succ n => simp [coeff_monomial, mul_coeff_zero, pow_succ, hx]

theorem step {B : Type*} [CommRing B] (T : B[X][X]) (hT1 : (T.coeff 1).coeff 0 = 1)
    (x e : B[X]) (hx : x.coeff 0 = 0) (j : ℕ) (hj : 1 ≤ j) (he : X ^ j ∣ e) (i : ℕ) (hi : i ≤ j) :
    (T.eval (x + e)).coeff i = (T.eval x).coeff i + if i = j then e.coeff j else 0 := by
  obtain ⟨k, hk⟩ := binomExpansion T x e
  obtain ⟨e', rfl⟩ := he
  have hd : ((derivative T).eval x).coeff 0 = 1 := by
    rw [eval_coeff_zero _ _ hx, coeff_derivative]; simp [hT1]
  rw [hk, coeff_add, coeff_add]
  have h1 : (eval x (derivative T) * (X ^ j * e')).coeff i
      = if i = j then (X ^ j * e').coeff j else 0 := by
    rw [mul_left_comm]
    by_cases hij : i = j
    · subst hij; simp [coeff_X_pow_mul', mul_coeff_zero, hd]
    · rw [if_neg hij, coeff_X_pow_mul', if_neg (by omega)]
  have h2 : (k * (X ^ j * e') ^ 2).coeff i = 0 := by
    rw [show k * (X ^ j * e') ^ 2 = X ^ (2 * j) * (k * e' ^ 2) by ring, coeff_X_pow_mul',
      if_neg (by omega)]
  rw [h1, h2, add_zero]

theorem unique {B : Type*} [CommRing B] (T : B[X][X]) (hT1 : (T.coeff 1).coeff 0 = 1)
    (x y : B[X]) (hx0 : x.coeff 0 = 0) (hy0 : y.coeff 0 = 0) (J : ℕ) (hxd : x.natDegree ≤ J)
    (hyd : y.natDegree ≤ J) (hx : ∀ i ≤ J, (T.eval x).coeff i = 0)
    (hy : ∀ i ≤ J, (T.eval y).coeff i = 0) : x = y := by
  by_contra hne
  set e := y - x with he_def
  have he0 : e ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  set j := e.natTrailingDegree with hj
  have hcoeff : e.coeff j ≠ 0 := mt trailingCoeff_eq_zero.mp he0
  have hdvd : X ^ j ∣ e := X_pow_dvd_iff.mpr fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd
  have hj1 : 1 ≤ j := by
    by_contra h0
    have h00 : j = 0 := by omega
    apply hcoeff; rw [h00]; simp [e, hx0, hy0]
  have hjJ : j ≤ J := le_trans (natTrailingDegree_le_natDegree _)
    (le_trans (natDegree_sub_le _ _) (max_le hyd hxd))
  have := step T hT1 x e hx0 j hj1 hdvd j le_rfl
  rw [show x + e = y by simp [e], hx j hjJ, hy j hjJ, if_pos rfl, zero_add] at this
  exact hcoeff this.symm

noncomputable def newton {B : Type*} [CommRing B] (T : B[X][X]) : ℕ → B[X]
  | 0 => 0
  | j + 1 => newton T j - C ((T.eval (newton T j)).coeff (j + 1)) * X ^ (j + 1)

theorem newton_spec {B : Type*} [CommRing B] (T : B[X][X]) (hT0 : (T.coeff 0).coeff 0 = 0)
    (hT1 : (T.coeff 1).coeff 0 = 1) (j : ℕ) :
    (newton T j).coeff 0 = 0 ∧ (newton T j).natDegree ≤ j ∧
      ∀ i ≤ j, (T.eval (newton T j)).coeff i = 0 := by
  induction j with
  | zero =>
    refine ⟨by simp [newton], by simp [newton], fun i hi => ?_⟩
    have : i = 0 := by omega
    subst this
    simp [newton, ← coeff_zero_eq_eval_zero, hT0]
  | succ j ih =>
    obtain ⟨h0, hd, hc⟩ := ih
    set c := (T.eval (newton T j)).coeff (j + 1) with hcdef
    have hnew : newton T (j + 1) = newton T j + (-(C c * X ^ (j + 1))) := by
      simp [newton, sub_eq_add_neg, c]
    refine ⟨?_, ?_, ?_⟩
    · rw [hnew]; simp [h0]
    · rw [hnew]
      refine (natDegree_add_le _ _).trans (max_le (by omega) ?_)
      rw [natDegree_neg]; exact natDegree_C_mul_X_pow_le _ _
    · intro i hi
      rw [hnew, step T hT1 _ _ h0 (j + 1) (by omega) (dvd_neg.mpr (dvd_mul_left _ _)) i hi]
      by_cases hij : i = j + 1
      · subst hij; simp [c]
      · rw [if_neg hij, hc i (by omega), add_zero]


/-! ## Integer-offset degree bookkeeping -/

def Q {F : Type*} [Field F] (p : F[X]) (b : ℤ) : Prop := p = 0 ∨ (p.natDegree : ℤ) ≤ b

theorem Q_mono {F : Type*} [Field F] {p : F[X]} {b b' : ℤ} (h : Q p b) (hb : b ≤ b') : Q p b' := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hb)

theorem Q_zero {F : Type*} [Field F] (b : ℤ) : Q (0 : F[X]) b := Or.inl rfl

theorem Q_add {F : Type*} [Field F] {p q : F[X]} {b : ℤ} (hp : Q p b) (hq : Q q b) :
    Q (p + q) b := by
  rcases hp with rfl | hp
  · simpa using hq
  rcases hq with rfl | hq
  · rw [add_zero]; exact Or.inr hp
  right
  have := natDegree_add_le p q
  omega

theorem Q_neg {F : Type*} [Field F] {p : F[X]} {b : ℤ} (hp : Q p b) : Q (-p) b := by
  rcases hp with rfl | hp
  · simp [Q]
  · right; rwa [natDegree_neg]

theorem Q_sum {F : Type*} [Field F] {ι : Type*} (s : Finset ι) (f : ι → F[X]) (b : ℤ)
    (h : ∀ i ∈ s, Q (f i) b) : Q (∑ i ∈ s, f i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Q]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Q_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Q_mul {F : Type*} [Field F] {p q : F[X]} {b1 b2 : ℤ} (hp : Q p b1) (hq : Q q b2) :
    Q (p * q) (b1 + b2) := by
  rcases hp with rfl | hp
  · simp [Q]
  rcases hq with rfl | hq
  · simp [Q]
  right
  have := natDegree_mul_le (p := p) (q := q)
  omega

def Bnd {F : Type*} [Field F] (D : ℕ) (G : F[X][X]) (c : ℤ) : Prop :=
  ∀ m : ℕ, Q (G.coeff m) (6 * D * m - c)

theorem Bnd_mono {F : Type*} [Field F] {D : ℕ} {G : F[X][X]} {c c' : ℤ} (h : Bnd D G c)
    (hc : c' ≤ c) : Bnd D G c' := fun m => Q_mono (h m) (by linarith)

theorem Bnd_add {F : Type*} [Field F] {D : ℕ} {G H : F[X][X]} {c : ℤ} (hG : Bnd D G c)
    (hH : Bnd D H c) : Bnd D (G + H) c := fun m => by rw [coeff_add]; exact Q_add (hG m) (hH m)

theorem Bnd_neg {F : Type*} [Field F] {D : ℕ} {G : F[X][X]} {c : ℤ} (hG : Bnd D G c) :
    Bnd D (-G) c := fun m => by rw [coeff_neg]; exact Q_neg (hG m)

theorem Bnd_sub {F : Type*} [Field F] {D : ℕ} {G H : F[X][X]} {c : ℤ} (hG : Bnd D G c)
    (hH : Bnd D H c) : Bnd D (G - H) c := by
  rw [sub_eq_add_neg]; exact Bnd_add hG (Bnd_neg hH)

theorem Bnd_sum {F : Type*} [Field F] {D : ℕ} {ι : Type*} (s : Finset ι) (f : ι → F[X][X]) (c : ℤ)
    (h : ∀ i ∈ s, Bnd D (f i) c) : Bnd D (∑ i ∈ s, f i) c := fun m => by
  rw [finsetSum_coeff]; exact Q_sum s _ _ fun i hi => h i hi m

theorem Bnd_mul {F : Type*} [Field F] {D : ℕ} {G H : F[X][X]} {c1 c2 : ℤ} (hG : Bnd D G c1)
    (hH : Bnd D H c2) : Bnd D (G * H) (c1 + c2) := by
  intro m
  rw [coeff_mul]
  apply Q_sum
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  refine Q_mono (Q_mul (hG x.1) (hH x.2)) ?_
  have h1 : ((x.1 : ℤ) + x.2) = m := by exact_mod_cast hx
  have h2 : (6 * D * m : ℤ) = 6 * D * x.1 + 6 * D * x.2 := by rw [← h1]; ring
  linarith

theorem Bnd_one {F : Type*} [Field F] (D : ℕ) : Bnd D (1 : F[X][X]) 0 := by
  intro m
  rw [coeff_one]
  split_ifs with h
  · subst h; right; simp
  · exact Q_zero _

theorem Bnd_pow {F : Type*} [Field F] {D : ℕ} {G : F[X][X]} {c : ℤ} (hG : Bnd D G c) (n : ℕ) :
    Bnd D (G ^ n) (n * c) := by
  induction n with
  | zero => simpa using Bnd_one (F := F) D
  | succ n ih =>
    rw [pow_succ]
    refine Bnd_mono (Bnd_mul ih hG) (by push_cast; linarith)

/-! ## Natural-number weighted bounds for trivariate polynomials -/

def WB {F : Type*} [Field F] (D : ℕ) (T : F[X][X][X]) (c : ℕ) : Prop :=
  ∀ l m, ((T.coeff l).coeff m).natDegree ≤ c + 2 * D * m + D * l

theorem WB_mono {F : Type*} [Field F] {D : ℕ} {T : F[X][X][X]} {c c' : ℕ} (h : WB D T c)
    (hc : c ≤ c') : WB D T c' := fun l m => (h l m).trans (by omega)

theorem WB_zero {F : Type*} [Field F] (D c : ℕ) : WB D (0 : F[X][X][X]) c := fun l m => by simp

theorem WB_add {F : Type*} [Field F] {D : ℕ} {T U : F[X][X][X]} {c : ℕ} (hT : WB D T c)
    (hU : WB D U c) : WB D (T + U) c := fun l m => by
  rw [coeff_add, coeff_add]
  exact (natDegree_add_le _ _).trans (max_le (hT l m) (hU l m))

theorem WB_sum {F : Type*} [Field F] {D : ℕ} {ι : Type*} (s : Finset ι) (f : ι → F[X][X][X])
    (c : ℕ) (h : ∀ i ∈ s, WB D (f i) c) : WB D (∑ i ∈ s, f i) c := fun l m => by
  rw [finsetSum_coeff, finsetSum_coeff]
  exact natDegree_sum_le_of_forall_le _ _ fun i hi => h i hi l m

theorem WB_mul {F : Type*} [Field F] {D : ℕ} {T U : F[X][X][X]} {c1 c2 : ℕ} (hT : WB D T c1)
    (hU : WB D U c2) : WB D (T * U) (c1 + c2) := by
  intro l m
  rw [coeff_mul, finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro x hx
  rw [coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro y hy
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  refine natDegree_mul_le.trans ?_
  have h1 := hT x.1 y.1
  have h2 := hU x.2 y.2
  have e1 : D * x.1 + D * x.2 = D * l := by rw [← Nat.mul_add, hx]
  have e2 : 2 * D * y.1 + 2 * D * y.2 = 2 * D * m := by rw [← Nat.mul_add, hy]
  omega

theorem WB_one {F : Type*} [Field F] (D : ℕ) : WB D (1 : F[X][X][X]) 0 := by
  intro l m
  rw [coeff_one]
  split_ifs
  · rw [coeff_one]; split_ifs <;> simp
  · simp

theorem WB_pow {F : Type*} [Field F] {D : ℕ} {T : F[X][X][X]} {c : ℕ} (hT : WB D T c) (n : ℕ) :
    WB D (T ^ n) (n * c) := by
  induction n with
  | zero => simpa using WB_one (F := F) D
  | succ n ih =>
    rw [pow_succ]
    exact WB_mono (WB_mul ih hT) (by rw [Nat.succ_mul])

def WW {F : Type*} [Field F] (T : F[X][X][X]) (e : ℕ) : Prop := ∀ l, (T.coeff l).natDegree ≤ e

theorem WW_mono {F : Type*} [Field F] {T : F[X][X][X]} {e e' : ℕ} (h : WW T e) (he : e ≤ e') :
    WW T e' := fun l => (h l).trans he

theorem WW_sum {F : Type*} [Field F] {ι : Type*} (s : Finset ι) (f : ι → F[X][X][X]) (e : ℕ)
    (h : ∀ i ∈ s, WW (f i) e) : WW (∑ i ∈ s, f i) e := fun l => by
  rw [finsetSum_coeff]
  exact natDegree_sum_le_of_forall_le _ _ fun i hi => h i hi l

theorem WW_mul {F : Type*} [Field F] {T U : F[X][X][X]} {e1 e2 : ℕ} (hT : WW T e1)
    (hU : WW U e2) : WW (T * U) (e1 + e2) := by
  intro l
  rw [coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro x _
  exact natDegree_mul_le.trans (Nat.add_le_add (hT _) (hU _))

theorem WW_one {F : Type*} [Field F] : WW (1 : F[X][X][X]) 0 := by
  intro l; rw [coeff_one]; split_ifs <;> simp

theorem WW_pow {F : Type*} [Field F] {T : F[X][X][X]} {e : ℕ} (hT : WW T e) (n : ℕ) :
    WW (T ^ n) (n * e) := by
  induction n with
  | zero => simpa using WW_one (F := F)
  | succ n ih =>
    rw [pow_succ]
    exact WW_mono (WW_mul ih hT) (by rw [Nat.succ_mul])


/-! ## The normalized polynomial -/

noncomputable def sig {F : Type*} [Field F] (A : F[X]) : F[X][X] →+* F[X][X] :=
  compRingHom (C (A ^ 2) * X)

theorem sig_apply {F : Type*} [Field F] (A : F[X]) (p : F[X][X]) :
    sig A p = p.comp (C (A ^ 2) * X) := rfl

theorem sig_C {F : Type*} [Field F] (A r : F[X]) : sig A (C r) = C r := by
  rw [sig_apply, C_comp]

theorem sig_coeff {F : Type*} [Field F] (A : F[X]) (p : F[X][X]) (m : ℕ) :
    (sig A p).coeff m = (A ^ 2) ^ m * p.coeff m := by
  rw [sig_apply, comp_CX_coeff]

noncomputable def Sp {F : Type*} [Field F] (P : F[X][X][X]) (h A : F[X]) : F[X][X][X] :=
  (P.map (sig A)).comp (C (C A) * X + C (C h))

theorem Sp_coeff {F : Type*} [Field F] (P : F[X][X][X]) (h A : F[X]) (l : ℕ) :
    (Sp P h A).coeff l = C A ^ l * (taylor (C h) (P.map (sig A))).coeff l := by
  rw [Sp, show C (C A) * X + C (C h) = (X + C (C h)).comp (C (C A) * X) by
    simp [add_comp], ← comp_assoc, ← taylor_apply, comp_CX_coeff]

theorem taylor_coeff_zero' {F : Type*} [Field F] (P : F[X][X][X]) (h A : F[X]) (m : ℕ) :
    ((taylor (C h) (P.map (sig A))).coeff 0).coeff m = (A ^ 2) ^ m * (P.eval (C h)).coeff m := by
  have := eval_map_apply (p := P) (sig A) (C h)
  rw [sig_C] at this
  rw [taylor_coeff_zero, this, sig_coeff]

theorem taylor_coeff_one' {F : Type*} [Field F] (P : F[X][X][X]) (h A : F[X]) (m : ℕ) :
    ((taylor (C h) (P.map (sig A))).coeff 1).coeff m
      = (A ^ 2) ^ m * ((derivative P).eval (C h)).coeff m := by
  have := eval_map_apply (p := derivative P) (sig A) (C h)
  rw [sig_C] at this
  rw [taylor_coeff_one, derivative_map, this, sig_coeff]

theorem coeff0_eval_C {F : Type*} [Field F] (p : F[X][X][X]) (h : F[X]) :
    (p.eval (C h)).coeff 0 = (p.map (evalRingHom 0)).eval h := by
  rw [coeff_zero_eq_eval_zero, ← coe_evalRingHom, ← eval_map_apply, coe_evalRingHom, eval_C]

theorem normalize {F : Type*} [Field F] (P : F[X][X][X]) (h A : F[X]) (hA : A ≠ 0)
    (hP0 : (P.eval (C h)).coeff 0 = 0) (hP1 : ((derivative P).eval (C h)).coeff 0 = A) :
    ∃ T : F[X][X][X], Sp P h A = C (C (A ^ 2)) * T ∧ (T.coeff 0).coeff 0 = 0 ∧
      (T.coeff 1).coeff 0 = 1 := by
  have hcoef : ∀ l m, ((Sp P h A).coeff l).coeff m
      = A ^ l * ((taylor (C h) (P.map (sig A))).coeff l).coeff m := by
    intro l m
    rw [Sp_coeff, ← C_pow, coeff_C_mul]
  have hdvd : C (C (A ^ 2)) ∣ Sp P h A := by
    rw [C_dvd_iff_dvd_coeff]; intro l; rw [C_dvd_iff_dvd_coeff]; intro m
    rw [hcoef]
    rcases (show l = 0 ∨ l = 1 ∨ 2 ≤ l by omega) with rfl | rfl | hl
    · rw [taylor_coeff_zero']
      rcases m with _ | m
      · simp [hP0]
      · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _) _
    · rw [taylor_coeff_one']
      rcases m with _ | m
      · simp [hP1, sq]
      · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _) _
    · exact dvd_mul_of_dvd_left (pow_dvd_pow A hl) _
  obtain ⟨T, hT⟩ := hdvd
  refine ⟨T, hT, ?_, ?_⟩
  · have := hcoef 0 0
    rw [taylor_coeff_zero', hT, coeff_C_mul, coeff_C_mul] at this
    simpa [hP0, hA] using this
  · have := hcoef 1 0
    rw [taylor_coeff_one', hT, coeff_C_mul, coeff_C_mul, hP1] at this
    have h2 : A ^ 2 * (T.coeff 1).coeff 0 = A ^ 2 * 1 := by rw [this]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hA) h2

/-! ## Degree bounds -/

theorem natDegree_A_le {F : Type*} [Field F] (K D : ℕ) (P : F[X][X][X])
    (hdeg : ∀ n m, ((P.coeff n).coeff m) ≠ 0 → ((P.coeff n).coeff m).natDegree + m + K * n ≤ D)
    (h : F[X]) (hh : h.natDegree ≤ K) :
    (((derivative P).map (evalRingHom 0)).eval h).natDegree ≤ D := by
  rw [eval_eq_sum_range]
  apply natDegree_sum_le_of_forall_le
  intro n _
  rw [coeff_map, coeff_derivative]
  simp only [map_mul, map_add, map_natCast, map_one, coe_evalRingHom, ← coeff_zero_eq_eval_zero]
  by_cases hz : (P.coeff (n + 1)).coeff 0 = 0
  · simp [hz]
  · have := hdeg (n + 1) 0 hz
    have h1 := natDegree_pow_le (p := h) (n := n)
    have h2 : n * h.natDegree ≤ n * K := Nat.mul_le_mul_left _ hh
    have h3 : ((P.coeff (n + 1)).coeff 0 * ((n : F[X]) + 1)).natDegree
        ≤ ((P.coeff (n + 1)).coeff 0).natDegree := by
      refine natDegree_mul_le.trans ?_
      have : ((n : F[X]) + 1).natDegree = 0 := by
        rw [show ((n : F[X]) + 1) = ((n + 1 : ℕ) : F[X]) by push_cast; ring]
        exact natDegree_natCast _
      omega
    refine natDegree_mul_le.trans ?_
    have : K * (n + 1) = n * K + K := by ring
    omega

theorem natDegree_coeff_le {F : Type*} [Field F] (K D : ℕ) (P : F[X][X][X])
    (hdeg : ∀ n m, ((P.coeff n).coeff m) ≠ 0 → ((P.coeff n).coeff m).natDegree + m + K * n ≤ D)
    (n : ℕ) : (P.coeff n).natDegree ≤ D := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  by_contra hne
  have := hdeg n m hne
  omega

theorem WB_Sp {F : Type*} [Field F] (K D : ℕ) (P : F[X][X][X])
    (hdeg : ∀ n m, ((P.coeff n).coeff m) ≠ 0 → ((P.coeff n).coeff m).natDegree + m + K * n ≤ D)
    (h A : F[X]) (hh : h.natDegree ≤ K) (hAd : A.natDegree ≤ D) : WB D (Sp P h A) D := by
  have hq : WB D (C (C A) * X + C (C h)) K := by
    intro l m
    rw [coeff_add, coeff_C_mul_X, coeff_C]
    rcases (show l = 0 ∨ l = 1 ∨ 2 ≤ l by omega) with rfl | rfl | hl
    · rw [if_neg (show (0 : ℕ) ≠ 1 by omega), if_pos rfl, zero_add, coeff_C]
      split_ifs <;> (try simp) <;> omega
    · rw [if_pos rfl, if_neg (show (1 : ℕ) ≠ 0 by omega), add_zero, coeff_C]
      split_ifs <;> (try simp) <;> omega
    · rw [if_neg (by omega), if_neg (by omega)]; simp
  unfold Sp
  rw [comp, eval₂_eq_sum_range]
  apply WB_sum; intro n _
  rw [coeff_map]
  by_cases hKn : K * n ≤ D
  · have h1 : WB D (C (sig A (P.coeff n))) (D - K * n) := by
      intro l m
      rw [coeff_C]
      split_ifs with hl
      · rw [sig_coeff, ← pow_mul]
        refine natDegree_mul_le.trans ?_
        have e1 := natDegree_pow_le (p := A) (n := 2 * m)
        have e2 : 2 * m * A.natDegree ≤ 2 * D * m := by
          rw [show 2 * D * m = 2 * m * D by ring]; exact Nat.mul_le_mul_left _ hAd
        have e3 : ((P.coeff n).coeff m).natDegree ≤ D - K * n := by
          by_cases hz : (P.coeff n).coeff m = 0
          · simp [hz]
          · have := hdeg n m hz; omega
        omega
      · simp
    have := WB_mul h1 (WB_pow hq n)
    exact WB_mono this (by rw [Nat.mul_comm n K]; omega)
  · have : P.coeff n = 0 := by
      refine Polynomial.ext fun m => ?_
      rw [coeff_zero]
      by_contra hne
      exact hKn (by have := hdeg n m hne; omega)
    rw [this, map_zero, C_0, zero_mul]
    exact WB_zero _ _

theorem WW_Sp {F : Type*} [Field F] (K D : ℕ) (P : F[X][X][X])
    (hdeg : ∀ n m, ((P.coeff n).coeff m) ≠ 0 → ((P.coeff n).coeff m).natDegree + m + K * n ≤ D)
    (h A : F[X]) : WW (Sp P h A) D := by
  have hq : WW (C (C A) * X + C (C h)) 0 := by
    intro l
    rw [coeff_add, coeff_C_mul_X, coeff_C]
    split_ifs <;> simp
  unfold Sp
  rw [comp, eval₂_eq_sum_range]
  apply WW_sum; intro n _
  rw [coeff_map]
  have h1 : WW (C (sig A (P.coeff n))) D := by
    intro l
    rw [coeff_C]
    split_ifs
    · exact (natDegree_comp_CX_le _ _).trans (natDegree_coeff_le K D P hdeg n)
    · simp
  exact WW_mono (WW_mul h1 (WW_pow hq n)) (by simp)

theorem natDegree_Sp_le {F : Type*} [Field F] (P : F[X][X][X]) (h A : F[X]) :
    (Sp P h A).natDegree ≤ P.natDegree := by
  unfold Sp
  refine (natDegree_comp_le).trans ?_
  have h1 : (C (C A) * X + C (C h)).natDegree ≤ 1 := natDegree_linear_le
  have h2 : (P.map (sig A)).natDegree ≤ P.natDegree := natDegree_map_le
  calc _ ≤ P.natDegree * 1 := Nat.mul_le_mul h2 h1
    _ = _ := by ring


/-! ## Transfer to `T` and Newton bookkeeping -/

theorem WB_of_mul {F : Type*} [Field F] (D c : ℕ) (A : F[X]) (hA : A ≠ 0) (T : F[X][X][X])
    (h : WB D (C (C (A ^ 2)) * T) c) : WB D T c := by
  intro l m
  have := h l m
  rw [coeff_C_mul, coeff_C_mul] at this
  by_cases hz : (T.coeff l).coeff m = 0
  · rw [hz]; simp
  · rw [natDegree_mul (pow_ne_zero 2 hA) hz] at this
    omega

theorem WW_of_mul {F : Type*} [Field F] (e : ℕ) (A : F[X]) (hA : A ≠ 0) (T : F[X][X][X])
    (h : WW (C (C (A ^ 2)) * T) e) : WW T e := by
  intro l
  have := h l
  rwa [coeff_C_mul, natDegree_C_mul (pow_ne_zero 2 hA)] at this

theorem natDegree_of_mul {F : Type*} [Field F] (A : F[X]) (hA : A ≠ 0) (T : F[X][X][X]) :
    (C (C (A ^ 2)) * T).natDegree = T.natDegree := by
  rw [natDegree_C_mul]
  simpa using pow_ne_zero 2 hA

theorem Bnd_eval {F : Type*} [Field F] (D : ℕ) (T : F[X][X][X]) (hWB : WB D T D)
    (hT0 : (T.coeff 0).coeff 0 = 0) (hT1 : (T.coeff 1).coeff 0 = 1) (Φ : F[X][X])
    (hΦ : Bnd D Φ (3 * D)) : Bnd D (T.eval Φ) (3 * D) := by
  have : T.eval Φ = Φ + (T - X).eval Φ := by simp
  rw [this]
  apply Bnd_add hΦ
  rw [eval_eq_sum_range]
  apply Bnd_sum; intro l _
  rw [coeff_sub, coeff_X]
  rcases (show l = 0 ∨ l = 1 ∨ 2 ≤ l by omega) with rfl | rfl | hl2
  · rw [if_neg (by omega), sub_zero, pow_zero, mul_one]
    intro m
    rcases m with _ | m
    · left; exact hT0
    · right
      have := hWB 0 (m + 1)
      have h1 : (((T.coeff 0).coeff (m + 1)).natDegree : ℤ) ≤ D + 2 * D * (m + 1) + D * 0 := by
        exact_mod_cast this
      push_cast
      nlinarith
  · rw [if_pos rfl, pow_one]
    have hB : Bnd D (T.coeff 1 - 1) 0 := by
      intro m
      rw [coeff_sub, coeff_one]
      rcases m with _ | m
      · left; simp [hT1]
      · right
        rw [if_neg (by omega), sub_zero]
        have := hWB 1 (m + 1)
        have h1 : (((T.coeff 1).coeff (m + 1)).natDegree : ℤ) ≤ D + 2 * D * (m + 1) + D * 1 := by
          exact_mod_cast this
        push_cast
        nlinarith
    simpa using Bnd_mul hB hΦ
  · rw [if_neg (by omega), sub_zero]
    have hB : Bnd D (T.coeff l) (-(D + D * l)) := by
      intro m
      right
      have := hWB l m
      have h1 : (((T.coeff l).coeff m).natDegree : ℤ) ≤ D + 2 * D * m + D * l := by
        exact_mod_cast this
      have : (0 : ℤ) ≤ D * m := by positivity
      linarith
    refine Bnd_mono (Bnd_mul hB (Bnd_pow hΦ l)) ?_
    have : (2 : ℤ) ≤ l := by exact_mod_cast hl2
    have : (0 : ℤ) ≤ D := by positivity
    nlinarith

theorem newton_Bnd {F : Type*} [Field F] (D : ℕ) (T : F[X][X][X]) (hWB : WB D T D)
    (hT0 : (T.coeff 0).coeff 0 = 0) (hT1 : (T.coeff 1).coeff 0 = 1) (j : ℕ) :
    Bnd D (newton T j) (3 * D) := by
  induction j with
  | zero => intro m; simp [newton, Q]
  | succ j ih =>
    have hE := Bnd_eval D T hWB hT0 hT1 _ ih (j + 1)
    show Bnd D (newton T j - C ((T.eval (newton T j)).coeff (j + 1)) * X ^ (j + 1)) (3 * D)
    apply Bnd_sub ih
    intro m
    rw [coeff_C_mul_X_pow]
    split_ifs with hm
    · subst hm; exact hE
    · exact Q_zero _

theorem natDegree_eval_le {F : Type*} [Field F] (D d K J : ℕ) (T : F[X][X][X]) (hWW : WW T D)
    (hTd : T.natDegree ≤ d) (hKd : K * d ≤ D) (hJK : J ≤ K) (Φ : F[X][X])
    (hΦd : Φ.natDegree ≤ J) : (T.eval Φ).natDegree ≤ 2 * D := by
  rw [eval_eq_sum_range]
  apply natDegree_sum_le_of_forall_le
  intro l hl
  rw [Finset.mem_range] at hl
  refine natDegree_mul_le.trans ?_
  have h1 := hWW l
  have h2 := natDegree_pow_le (p := Φ) (n := l)
  have h3 : l * Φ.natDegree ≤ d * K := Nat.mul_le_mul (by omega) (hΦd.trans hJK)
  have h4 : d * K = K * d := Nat.mul_comm _ _
  omega

theorem exact_zero {F : Type*} [Field F] (D : ℕ) (G : F[X][X]) (hG : Bnd D G (3 * D))
    (hd : G.natDegree ≤ 2 * D) (s : Finset F) (hs : 12 * D ^ 2 < s.card)
    (hev : ∀ a ∈ s, ∀ m, (G.coeff m).eval a = 0) : G = 0 := by
  refine Polynomial.ext fun m => ?_
  rw [coeff_zero]
  by_cases hm : m ≤ 2 * D
  · rcases hG m with h0 | h1
    · exact h0
    · apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ s (fun a ha => hev a ha m)
      have hm' : (m : ℤ) ≤ 2 * D := by exact_mod_cast hm
      have : (6 * D * m : ℤ) ≤ 12 * D ^ 2 := by
        have : (0 : ℤ) ≤ D := by positivity
        nlinarith
      have hs' : (12 * D ^ 2 : ℤ) < s.card := by exact_mod_cast hs
      have : (0 : ℤ) ≤ D := by positivity
      have : ((G.coeff m).natDegree : ℤ) < s.card := by linarith
      exact_mod_cast this
  · exact coeff_eq_zero_of_natDegree_lt (by omega)


/-! ## Specialization and output -/

theorem spec {F : Type*} [Field F] (P : F[X][X][X]) (h A : F[X]) (T : F[X][X][X])
    (hT : Sp P h A = C (C (A ^ 2)) * T) (hT1 : (T.coeff 1).coeff 0 = 1)
    (J : ℕ) (Φ : F[X][X]) (hΦ0 : Φ.coeff 0 = 0) (hΦd : Φ.natDegree ≤ J)
    (hΦc : ∀ i ≤ J, (T.eval Φ).coeff i = 0)
    (a : F) (ha : A.eval a ≠ 0) (g : F[X]) (hgd : g.natDegree ≤ J) (hg0 : g.eval 0 = h.eval a)
    (hgr : (P.map (mapRingHom (evalRingHom a))).eval g = 0) :
    C (h.eval a) + C (A.eval a) * Φ.map (evalRingHom a) = g.comp (C (A.eval a ^ 2) * X) ∧
      (T.eval Φ).map (evalRingHom a) = 0 := by
  set α := A.eval a with hα
  set f : F[X][X] →+* F[X] := mapRingHom (evalRingHom a) with hf
  set σa : F[X] →+* F[X] := compRingHom (C (α ^ 2) * X) with hσa
  have hcomm : f.comp (sig A) = σa.comp f := by
    refine RingHom.ext fun p => ?_
    simp only [RingHom.comp_apply, f, σa, sig_apply, coe_mapRingHom, coe_compRingHom_apply,
      Polynomial.map_comp]
    simp [α]
  set ψ : F[X] := C α⁻¹ * (g.comp (C (α ^ 2) * X) - C (h.eval a)) with hψ
  have hlin : C (h.eval a) + C α * ψ = g.comp (C (α ^ 2) * X) := by
    rw [hψ, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]; ring
  have hψ0 : ψ.coeff 0 = 0 := by
    rw [hψ, coeff_C_mul, coeff_sub, comp_CX_coeff, coeff_C_zero, pow_zero, one_mul,
      coeff_zero_eq_eval_zero, hg0, sub_self, mul_zero]
  have hψd : ψ.natDegree ≤ J := by
    refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le ?_ ?_))
    · exact (natDegree_comp_CX_le _ _).trans hgd
    · simp
  set Ta := T.map f with hTa
  have hTa1 : (Ta.coeff 1).coeff 0 = 1 := by simp [Ta, f, hT1]
  have hψr : Ta.eval ψ = 0 := by
    have key : (Sp P h A).map f = C (C (α ^ 2)) * Ta := by
      rw [hT, Polynomial.map_mul, map_C]; congr 1; simp [f, α]
    have hS : ((Sp P h A).map f).eval ψ = 0 := by
      unfold Sp
      rw [Polynomial.map_comp, eval_comp, Polynomial.map_map, hcomm, ← Polynomial.map_map]
      have : ((C (C A) * X + C (C h)).map f).eval ψ = σa g := by
        rw [hσa, coe_compRingHom_apply, ← hlin]; simp [f, α]; ring
      rw [this, eval_map_apply, hgr, map_zero]
    rw [key, eval_mul, eval_C, mul_eq_zero] at hS
    rcases hS with hS | hS
    · exfalso; rw [C_eq_zero] at hS; exact ha (pow_eq_zero_iff (by norm_num) |>.mp hS)
    · exact hS
  have hφ : Φ.map (evalRingHom a) = ψ := by
    apply unique Ta hTa1 _ _ (by simp [hΦ0]) hψ0 J (natDegree_map_le.trans hΦd) hψd
    · intro i hi
      rw [show Φ.map (evalRingHom a) = f Φ from rfl, hTa, eval_map_apply, hf, coe_mapRingHom,
        coeff_map, hΦc i hi, map_zero]
    · intro i _; rw [hψr, coeff_zero]
  refine ⟨by rw [hφ, hlin], ?_⟩
  rw [show (T.eval Φ).map (evalRingHom a) = f (T.eval Φ) from rfl, ← eval_map_apply, ← hTa]
  rw [show f Φ = Φ.map (evalRingHom a) from rfl, hφ, hψr]

noncomputable def mkNt {F : Type*} [Field F] (A h : F[X]) (Φ : F[X][X]) (J : ℕ) : F[X][X] :=
  C (A ^ (2 * J) * h) + ∑ j ∈ Finset.range (J + 1), C (A ^ (2 * J + 1 - 2 * j) * Φ.coeff j) * X ^ j

theorem mkNt_natDegree {F : Type*} [Field F] (A h : F[X]) (Φ : F[X][X]) (J : ℕ) :
    (mkNt A h Φ J).natDegree ≤ J := by
  unfold mkNt
  refine (natDegree_add_le _ _).trans (max_le (by rw [natDegree_C]; exact Nat.zero_le _) ?_)
  apply natDegree_sum_le_of_forall_le
  intro j hj
  rw [Finset.mem_range] at hj
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem mkNt_sig {F : Type*} [Field F] (A h : F[X]) (Φ : F[X][X]) (J : ℕ)
    (hΦ0 : Φ.coeff 0 = 0) (hΦd : Φ.natDegree ≤ J) :
    sig A (mkNt A h Φ J) = C (A ^ (2 * J)) * (C h + C A * Φ) := by
  refine Polynomial.ext fun m => ?_
  rw [sig_coeff, mkNt, coeff_add, coeff_C, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, coeff_C_mul, coeff_add, coeff_C, coeff_C_mul]
  rcases m with _ | m
  · simp [hΦ0]
  · simp only [show m + 1 ≠ 0 by omega, ↓reduceIte, zero_add]
    by_cases hm : m + 1 ≤ J
    · rw [if_pos (by rw [Finset.mem_range]; omega)]
      have e : (A ^ 2) ^ (m + 1) * A ^ (2 * J + 1 - 2 * (m + 1)) = A ^ (2 * J) * A := by
        rw [← pow_mul, ← pow_add, ← pow_succ]; congr 1; omega
      linear_combination (Φ.coeff (m + 1)) * e
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp

end A1

open A1 in
theorem lifting {F : Type*} [Field F] [DecidableEq F] (K J D : ℕ) (hJK : J ≤ K)
    (P : Polynomial (Polynomial (Polynomial F)))
    (hdeg : ∀ n m, ((P.coeff n).coeff m) ≠ 0 → ((P.coeff n).coeff m).natDegree + m + K * n ≤ D)
    (h : Polynomial F) (hh : h.natDegree ≤ K)
    (hanchor : (P.map (Polynomial.evalRingHom 0)).eval h = 0)
    (hA : ((derivative P).map (Polynomial.evalRingHom 0)).eval h ≠ 0)
    (S : Finset F) (g : F → Polynomial F)
    (hg : ∀ a ∈ S, (g a).natDegree ≤ J ∧ (g a).eval 0 = h.eval a ∧
        (P.map (Polynomial.mapRingHom (Polynomial.evalRingHom a))).eval (g a) = 0)
    (hS : 12 * D ^ 2 < (S.filter fun a =>
        (((derivative P).map (Polynomial.evalRingHom 0)).eval h).eval a ≠ 0).card) :
    ∃ Nt : Polynomial (Polynomial F), Nt.natDegree ≤ J ∧
      (∀ a ∈ S, (((derivative P).map (Polynomial.evalRingHom 0)).eval h).eval a ≠ 0 →
        Nt.map (Polynomial.evalRingHom a) =
          C ((((derivative P).map (Polynomial.evalRingHom 0)).eval h).eval a ^ (2 * J)) * g a) ∧
      ∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * Nt ^ n *
          (C (((derivative P).map (Polynomial.evalRingHom 0)).eval h)) ^ (2 * J * (P.natDegree - n)) = 0 := by
  classical
  set A := ((derivative P).map (Polynomial.evalRingHom 0)).eval h with hAdef
  have hP0 : (P.eval (C h)).coeff 0 = 0 := by rw [coeff0_eval_C]; exact hanchor
  have hP1 : ((derivative P).eval (C h)).coeff 0 = A := by rw [coeff0_eval_C]
  have hAdeg : A.natDegree ≤ D := natDegree_A_le K D P hdeg h hh
  obtain ⟨T, hT, hT0, hT1⟩ := normalize P h A hA hP0 hP1
  have hWB : WB D T D := WB_of_mul D D A hA T (hT ▸ WB_Sp K D P hdeg h A hh hAdeg)
  have hWW : WW T D := WW_of_mul D A hA T (hT ▸ WW_Sp K D P hdeg h A)
  have hTd : T.natDegree ≤ P.natDegree := by
    rw [← natDegree_of_mul A hA T, ← hT]; exact natDegree_Sp_le P h A
  have hPne : P ≠ 0 := by rintro rfl; apply hA; simp [A]
  have hKd : K * P.natDegree ≤ D := by
    have hlc : P.coeff P.natDegree ≠ 0 := by
      rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hPne
    obtain ⟨m, hm⟩ : ∃ m, (P.coeff P.natDegree).coeff m ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hlc (Polynomial.ext (by simpa using hcon))
    have := hdeg _ _ hm
    omega
  set Φ := newton T J with hΦdef
  obtain ⟨hΦ0, hΦd, hΦc⟩ := newton_spec T hT0 hT1 J
  have hB := Bnd_eval D T hWB hT0 hT1 Φ (newton_Bnd D T hWB hT0 hT1 J)
  have hspec : ∀ a ∈ S, A.eval a ≠ 0 →
      (C (h.eval a) + C (A.eval a) * Φ.map (evalRingHom a) = (g a).comp (C (A.eval a ^ 2) * X)) ∧
        (T.eval Φ).map (evalRingHom a) = 0 := by
    intro a haS ha
    obtain ⟨hgd, hg0, hgr⟩ := hg a haS
    exact spec P h A T hT hT1 J Φ hΦ0 hΦd hΦc a ha (g a) hgd hg0 hgr
  have hzero : T.eval Φ = 0 := by
    apply exact_zero D _ hB (natDegree_eval_le D P.natDegree K J T hWW hTd hKd hJK Φ hΦd) _ hS
    intro a ha m
    rw [Finset.mem_filter] at ha
    have := congrArg (fun p => p.coeff m) (hspec a ha.1 ha.2).2
    simpa [coeff_map] using this
  refine ⟨mkNt A h Φ J, mkNt_natDegree A h Φ J, ?_, ?_⟩
  · intro a haS ha
    obtain ⟨h1, _⟩ := hspec a haS ha
    apply comp_CX_injective (A.eval a ^ 2) (pow_ne_zero 2 ha)
    have : ((mkNt A h Φ J).map (evalRingHom a)).comp (C (A.eval a ^ 2) * X)
        = (sig A (mkNt A h Φ J)).map (evalRingHom a) := by
      rw [sig_apply, Polynomial.map_comp]; simp
    rw [this, mkNt_sig A h Φ J hΦ0 hΦd, mul_comp, C_comp, ← h1]
    simp [Polynomial.map_mul]
  · apply comp_CX_injective (A ^ 2) (pow_ne_zero 2 hA)
    rw [zero_comp, ← sig_apply, map_sum]
    have hy : (P.map (sig A)).eval (C h + C A * Φ) = 0 := by
      have := congrArg (fun p => p.eval Φ) hT
      simp only [Sp, eval_comp, eval_mul, eval_C, hzero, mul_zero, eval_add, eval_X] at this
      rw [← this]; ring_nf
    rw [← mul_zero (C (A ^ (2 * J * P.natDegree))), ← hy,
      eval_eq_sum_range' (n := P.natDegree + 1) (Nat.lt_succ_of_le natDegree_map_le),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    rw [map_mul, map_mul, map_pow, map_pow, mkNt_sig A h Φ J hΦ0 hΦd, sig_C, coeff_map]
    have e : (C (A ^ (2 * J))) ^ n * C A ^ (2 * J * (P.natDegree - n))
        = C (A ^ (2 * J * P.natDegree)) := by
      rw [← C_pow, ← C_pow, ← C_mul, ← pow_mul, ← pow_add, ← Nat.mul_add,
        Nat.add_sub_cancel' (by omega)]
    rw [mul_pow, ← e]
    ring

end DLT

end Part2

section Part3
open Polynomial

namespace DLT.A2

variable {F : Type*} [Field F]

lemma coeff_swap {R : Type*} [CommSemiring R] (P : R[X][X]) (i j : ℕ) :
    ((Bivariate.swap P).coeff i).coeff j = (P.coeff j).coeff i := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add p q hp hq => simp [map_add, hp, hq]
    | monomial m r =>
      rw [Bivariate.swap_monomial_monomial]
      simp only [coeff_monomial]
      split_ifs <;> simp_all [coeff_monomial]

lemma sdeg_iff (P : F[X][X]) (k : ℕ) :
    (∀ n, (P.coeff n).natDegree ≤ k) ↔ (Bivariate.swap P).natDegree ≤ k := by
  simp only [natDegree_le_iff_coeff_eq_zero]
  constructor
  · intro h N hN
    ext j
    rw [coeff_swap, h j N hN, coeff_zero]
  · intro h n N hN
    rw [← coeff_swap, h N hN, coeff_zero]

lemma swap_map_eval (P : F[X][X]) (t : F) :
    (Bivariate.swap P).map (evalRingHom t) = P.eval (C t) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add p q hp hq => simp_all [map_add, Polynomial.map_add]
    | monomial m r =>
      rw [Bivariate.swap_monomial_monomial]
      simp [← C_mul_X_pow_eq_monomial]
      ring

lemma natDegree_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) F[X]) (b : Fin n → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ b j) : M.det.natDegree ≤ ∑ j, b j := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> rw [h1]
  · rw [one_smul]
    refine (natDegree_prod_le _ _).trans ?_
    exact Finset.sum_le_sum fun i _ => h _ _
  · rw [Units.neg_smul, one_smul, natDegree_neg]
    refine (natDegree_prod_le _ _).trans ?_
    exact Finset.sum_le_sum fun i _ => h _ _

lemma natDegree_resultant_le (f g : F[X][X]) (m n Df Dg : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df) (hg : ∀ i, (g.coeff i).natDegree ≤ Dg) :
    (resultant f g m n).natDegree ≤ m * Dg + n * Df := by
  unfold resultant
  refine (natDegree_det_le _ (Fin.addCases (fun _ => Dg) (fun _ => Df)) ?_).trans ?_
  · intro i j
    induction j using Fin.addCases with
    | left j => simp only [sylvester, Matrix.of_apply, Fin.addCases_left]; split_ifs <;> simp [hg]
    | right j => simp only [sylvester, Matrix.of_apply, Fin.addCases_right]; split_ifs <;> simp [hf]
  · simp [Fin.sum_univ_add]

lemma C_X_sub_dvd_of_map_eq_zero (P : F[X][X]) (s0 : F) (h : P.map (evalRingHom s0) = 0) :
    C (X - C s0) ∣ P := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  have := congrArg (fun p => p.coeff i) h
  simp only [coeff_map, coeff_zero, coe_evalRingHom] at this
  exact dvd_iff_isRoot.mpr this

lemma pow_dvd_resultant (f g : F[X][X]) (s0 : F) (n : ℕ) (hn : g.natDegree ≤ n)
    (hlc : f.leadingCoeff.eval s0 ≠ 0)
    (hdvd : f.map (evalRingHom s0) ∣ g.map (evalRingHom s0)) :
    (X - C s0) ^ f.natDegree ∣ resultant f g f.natDegree n := by
  obtain ⟨c, hc⟩ := hdvd
  have hfm : (f.map (evalRingHom s0)).natDegree = f.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ (by simpa using hlc)
  have hf0 : f.map (evalRingHom s0) ≠ 0 := by
    intro h0
    apply hlc
    have := coeff_map (p := f) (evalRingHom s0) f.natDegree
    rw [h0, coeff_zero] at this
    rw [leadingCoeff]; exact this.symm
  have key : resultant f g f.natDegree n = resultant f (g - f * c.map C) f.natDegree n := by
    by_cases hc0 : c = 0
    · subst hc0; rw [Polynomial.map_zero, mul_zero, sub_zero]
    · have : (-(c.map C)).natDegree + f.natDegree ≤ n := by
        rw [natDegree_neg, natDegree_map_eq_of_injective C_injective]
        have h1 := congrArg natDegree hc
        rw [natDegree_mul hf0 hc0, hfm] at h1
        have h2 := natDegree_map_le (f := evalRingHom s0) (p := g)
        omega
      rw [show g - f * c.map C = g + f * (-(c.map C)) by ring, resultant_add_mul_right _ _ _ _ _ this le_rfl]
  have hz : (g - f * c.map C).map (evalRingHom s0) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, hc]
    have : (evalRingHom s0).comp C = RingHom.id F := by ext; simp
    rw [this, Polynomial.map_id, sub_self]
  obtain ⟨M, hM⟩ := C_X_sub_dvd_of_map_eq_zero _ s0 hz
  rw [key, hM, resultant_C_mul_right]
  exact dvd_mul_right _ _

lemma mul_card_le_natDegree (R : F[X]) (hR : R ≠ 0) (S : Finset F) (a : ℕ)
    (h : ∀ s ∈ S, (X - C s) ^ a ∣ R) : a * S.card ≤ R.natDegree := by
  have hprod : ∏ s ∈ S, (X - C s) ^ a ∣ R := by
    apply Finset.prod_dvd_of_coprime
    · intro x _ y _ hxy
      exact IsCoprime.pow (by simpa using pairwise_coprime_X_sub_C (s := id) Function.injective_id hxy)
    · exact h
  have := natDegree_le_of_dvd hprod hR
  rw [natDegree_prod _ _ (fun s _ => pow_ne_zero _ (X_sub_C_ne_zero s))] at this
  simpa [natDegree_pow, natDegree_X_sub_C, mul_comm] using this

lemma resultant_ne_zero_of_isRelPrime (f g : F[X][X]) (hf : f ≠ 0) (h : IsRelPrime f g) :
    resultant f g ≠ 0 := by
  classical
  intro hR
  have hinj : Function.Injective (algebraMap F[X] (FractionRing F[X])) :=
    IsFractionRing.injective F[X] (FractionRing F[X])
  set φ := algebraMap F[X] (FractionRing F[X]) with hφ
  have hf' : f.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hf
  have hdeg : ∀ p : F[X][X], (p.map φ).natDegree = p.natDegree :=
    fun p => natDegree_map_eq_of_injective hinj p
  have h0 : resultant (f.map φ) (g.map φ) = 0 := by
    rw [hdeg f, hdeg g, resultant_map_map, hR, map_zero]
  rw [resultant_eq_zero_iff] at h0
  obtain ⟨-, hnc⟩ := h0
  obtain ⟨d, hd⟩ : ∃ d, d = EuclideanDomain.gcd (f.map φ) (g.map φ) := ⟨_, rfl⟩
  have hdu : ¬ IsUnit d := fun hu => hnc (EuclideanDomain.gcd_isUnit_iff.mp (hd ▸ hu))
  obtain ⟨q', hq'⟩ : d ∣ f.map φ := hd ▸ EuclideanDomain.gcd_dvd_left (f.map φ) (g.map φ)
  obtain ⟨p', hp'⟩ : d ∣ g.map φ := hd ▸ EuclideanDomain.gcd_dvd_right (f.map φ) (g.map φ)
  have hd0 : d ≠ 0 := by rintro h0; rw [h0, zero_mul] at hq'; exact hf' hq'
  have hq0 : q' ≠ 0 := by rintro h0; rw [h0, mul_zero] at hq'; exact hf' hq'
  have hdpos : 0 < d.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_ne_zero_of_nonunit hd0 hdu)
  have hqlt : q'.natDegree < f.natDegree := by
    have := congrArg natDegree hq'
    rw [natDegree_mul hd0 hq0, hdeg] at this
    omega
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors F[X]) q'
  obtain ⟨c, hc⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors F[X]) p'
  set Q := IsLocalization.integerNormalization (nonZeroDivisors F[X]) q'
  set P := IsLocalization.integerNormalization (nonZeroDivisors F[X]) p'
  have hsmul : ∀ (x : F[X]) (r : (FractionRing F[X])[X]), x • r = C (φ x) * r := by
    intro x r
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  rw [hsmul, ← hφ] at hb hc
  have hb0 : φ (b : F[X]) ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; exact nonZeroDivisors.coe_ne_zero b
  have hc0 : φ (c : F[X]) ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; exact nonZeroDivisors.coe_ne_zero c
  have heq : f * (C (b : F[X]) * P) = g * (C (c : F[X]) * Q) := by
    apply Polynomial.map_injective φ hinj
    simp only [Polynomial.map_mul, Polynomial.map_C, hb, hc, hq', hp']
    ring
  have hdvd : f ∣ C (c : F[X]) * Q := h.dvd_of_dvd_mul_left ⟨_, heq.symm⟩
  have hmapQ : (C (c : F[X]) * Q).map φ = C (φ c) * (C (φ b) * q') := by
    simp only [Polynomial.map_mul, Polynomial.map_C, hb]
  have hQ0 : C (c : F[X]) * Q ≠ 0 := by
    intro h0
    rw [h0, Polynomial.map_zero] at hmapQ
    exact (mul_ne_zero (C_ne_zero.mpr hc0) (mul_ne_zero (C_ne_zero.mpr hb0) hq0)) hmapQ.symm
  have := natDegree_le_of_dvd hdvd hQ0
  rw [← hdeg (C (c : F[X]) * Q), hmapQ, natDegree_C_mul hc0, natDegree_C_mul hb0] at this
  omega

lemma card_le_of_eval_eq_zero (p : F[X]) (hp : p ≠ 0) (S : Finset F)
    (h : ∀ s ∈ S, p.eval s = 0) : S.card ≤ p.natDegree := by
  have := mul_card_le_natDegree p hp S 1 (fun s hs => by
    rw [pow_one]; exact dvd_iff_isRoot.mpr (h s hs))
  simpa using this

lemma one_sided (D : ℕ) (G E₁ N₁ : F[X][X]) (hG : G ≠ 0) (hE₁ : E₁ ≠ 0)
    (hcop : IsRelPrime E₁ N₁) (hnu : ¬ IsUnit E₁)
    (hab : ∀ n, (E₁.coeff n).natDegree ≤ E₁.natDegree)
    (hN₁t : N₁.natDegree ≤ D)
    (hE₁s : ∀ n, (E₁.coeff n).natDegree ≤ D) (hN₁s : ∀ n, (N₁.coeff n).natDegree ≤ D)
    (hGs : ∀ n, (G.coeff n).natDegree ≤ D) (Ss : Finset F)
    (hS : ∀ s ∈ Ss, (G * E₁).map (evalRingHom s) ∣ (G * N₁).map (evalRingHom s))
    (hSc : 4 * D < Ss.card) : False := by
  classical
  set a := E₁.natDegree with ha_def
  have ha1 : 1 ≤ a := by
    by_contra h0
    have ha0 : E₁.natDegree = 0 := by omega
    have h1 : (E₁.coeff 0).natDegree = 0 := by have := hab 0; omega
    apply hnu
    rw [eq_C_of_natDegree_eq_zero ha0, eq_C_of_natDegree_eq_zero h1]
    apply isUnit_C.mpr
    apply isUnit_C.mpr
    apply Ne.isUnit
    intro hc
    apply hE₁
    rw [eq_C_of_natDegree_eq_zero ha0, eq_C_of_natDegree_eq_zero h1, hc, C_0, C_0]
  have hGlc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hG
  have hElc : E₁.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hE₁
  set Good := Ss.filter (fun s => G.leadingCoeff.eval s ≠ 0 ∧ E₁.leadingCoeff.eval s ≠ 0)
  set Bad1 := Ss.filter (fun s => G.leadingCoeff.eval s = 0)
  set Bad2 := Ss.filter (fun s => E₁.leadingCoeff.eval s = 0)
  have hB1 : Bad1.card ≤ D :=
    (card_le_of_eval_eq_zero _ hGlc Bad1 (fun s hs => (Finset.mem_filter.mp hs).2)).trans (hGs _)
  have hB2 : Bad2.card ≤ D :=
    (card_le_of_eval_eq_zero _ hElc Bad2 (fun s hs => (Finset.mem_filter.mp hs).2)).trans (hE₁s _)
  have hcover : Ss.card ≤ Good.card + Bad1.card + Bad2.card := by
    have : Ss ⊆ Good ∪ Bad1 ∪ Bad2 := by
      intro s hs
      simp only [Finset.mem_union, Finset.mem_filter, Good, Bad1, Bad2]
      tauto
    refine (Finset.card_le_card this).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    have := Finset.card_union_le Good Bad1
    omega
  set R := resultant E₁ N₁ a N₁.natDegree
  have hR : R ≠ 0 := resultant_ne_zero_of_isRelPrime E₁ N₁ hE₁ hcop
  have hdiv : ∀ s ∈ Good, (X - C s) ^ a ∣ R := by
    intro s hs
    obtain ⟨hsS, hGs0, hEs0⟩ := Finset.mem_filter.mp hs
    apply pow_dvd_resultant E₁ N₁ s _ le_rfl hEs0
    have h := hS s hsS
    rw [Polynomial.map_mul, Polynomial.map_mul] at h
    have hGm : G.map (evalRingHom s) ≠ 0 := by
      intro h0
      apply hGs0
      have := coeff_map (p := G) (evalRingHom s) G.natDegree
      rw [h0, coeff_zero] at this
      rw [leadingCoeff]; exact this.symm
    exact (mul_dvd_mul_iff_left hGm).mp h
  have h1 := mul_card_le_natDegree R hR Good a hdiv
  have h2 := natDegree_resultant_le E₁ N₁ a N₁.natDegree a D hab hN₁s
  have h3 : a * Good.card ≤ a * (2 * D) := by
    have : N₁.natDegree * a ≤ D * a := Nat.mul_le_mul_right _ hN₁t
    nlinarith
  have h4 : Good.card ≤ 2 * D := Nat.le_of_mul_le_mul_left h3 (by omega)
  omega

end DLT.A2

namespace DLT

open DLT.A2

/-- Polishchuk–Spielman divisibility. `F[s][t]`: inner variable `s`, outer variable `t`. -/
theorem ps_dvd {F : Type*} [Field F] (D : ℕ) (E N : Polynomial (Polynomial F)) (hE : E ≠ 0)
    (hEt : E.natDegree ≤ D) (hNt : N.natDegree ≤ D)
    (hEs : ∀ n, (E.coeff n).natDegree ≤ D) (hNs : ∀ n, (N.coeff n).natDegree ≤ D)
    (Ss Ts : Finset F)
    (hS : ∀ s ∈ Ss, E.map (Polynomial.evalRingHom s) ∣ N.map (Polynomial.evalRingHom s))
    (hT : ∀ t ∈ Ts, E.eval (C t) ∣ N.eval (C t))
    (hSc : 8 * D < Ss.card) (hTc : 8 * D < Ts.card) : E ∣ N := by
  by_cases hN : N = 0
  · rw [hN]; exact dvd_zero _
  obtain ⟨E₁, N₁, G, hcop, hGE, hGN⟩ := UniqueFactorizationMonoid.exists_reduced_factors E hE N
  have hG : G ≠ 0 := by rintro rfl; rw [zero_mul] at hGE; exact hE hGE.symm
  have hE₁ : E₁ ≠ 0 := by rintro rfl; rw [mul_zero] at hGE; exact hE hGE.symm
  have hN₁ : N₁ ≠ 0 := by rintro rfl; rw [mul_zero] at hGN; exact hN hGN.symm
  by_cases hu : IsUnit E₁
  · rw [← hGE, ← hGN]; exact mul_dvd_mul_left G hu.dvd
  exfalso
  have hsw0 : ∀ P : F[X][X], P ≠ 0 → Bivariate.swap P ≠ 0 := fun P hP h0 =>
    hP ((map_eq_zero_iff _ (Bivariate.swap (R := F)).injective).mp h0)
  -- t-degrees
  have hdE := natDegree_mul hG hE₁
  have hdN := natDegree_mul hG hN₁
  rw [hGE] at hdE
  rw [hGN] at hdN
  -- s-degrees
  have hsE := (sdeg_iff E D).mp hEs
  have hsN := (sdeg_iff N D).mp hNs
  rw [← hGE, map_mul, natDegree_mul (hsw0 G hG) (hsw0 E₁ hE₁)] at hsE
  rw [← hGN, map_mul, natDegree_mul (hsw0 G hG) (hsw0 N₁ hN₁)] at hsN
  have hGs : ∀ n, (G.coeff n).natDegree ≤ D := (sdeg_iff G D).mpr (by omega)
  have hE₁s : ∀ n, (E₁.coeff n).natDegree ≤ D := (sdeg_iff E₁ D).mpr (by omega)
  have hN₁s : ∀ n, (N₁.coeff n).natDegree ≤ D := (sdeg_iff N₁ D).mpr (by omega)
  by_cases hab : ∀ n, (E₁.coeff n).natDegree ≤ E₁.natDegree
  · refine one_sided D G E₁ N₁ hG hE₁ hcop hu hab (by omega) hE₁s hN₁s hGs Ss ?_ (by omega)
    intro s hs
    rw [hGE, hGN]; exact hS s hs
  · have hlt : E₁.natDegree < (Bivariate.swap E₁).natDegree := by
      rw [sdeg_iff] at hab; omega
    have sw := fun P : F[X][X] => Bivariate.swap_swap_apply P
    refine one_sided D (Bivariate.swap G) (Bivariate.swap E₁) (Bivariate.swap N₁)
      (hsw0 G hG) (hsw0 E₁ hE₁) ?_ ?_ ?_ ?_ ?_ ?_ ?_ Ts ?_ (by omega)
    · intro d hd1 hd2
      have h1 : Bivariate.swap d ∣ E₁ := by
        have := map_dvd (Bivariate.swap (R := F)) hd1; rwa [sw] at this
      have h2 : Bivariate.swap d ∣ N₁ := by
        have := map_dvd (Bivariate.swap (R := F)) hd2; rwa [sw] at this
      have := (hcop h1 h2).map (Bivariate.swap (R := F))
      rwa [sw] at this
    · intro hu'
      apply hu
      have := hu'.map (Bivariate.swap (R := F))
      rwa [sw] at this
    · first | omega | (rw [sdeg_iff, sw]; omega)
    · omega
    · first | omega | (rw [sdeg_iff, sw]; omega)
    · first | omega | (rw [sdeg_iff, sw]; omega)
    · first | omega | (rw [sdeg_iff, sw]; omega)
    · intro t ht
      rw [← map_mul, ← map_mul, hGE, hGN, swap_map_eval, swap_map_eval]
      exact hT t ht

end DLT

end Part3

section Part4

namespace DLT

namespace A3

open Finset

/-- Bernoulli-type bound: `(1 - x)^m ≤ 1 - m x / 2` when `0 ≤ x` and `m x ≤ 1`. -/
lemma pow_one_sub_le (x : ℝ) (m : ℕ) (hx0 : 0 ≤ x) (hmx : (m : ℝ) * x ≤ 1) :
    (1 - x) ^ m ≤ 1 - (m : ℝ) * x / 2 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  have hx1 : x ≤ 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have h1 : (1 - x) ^ m * (1 + x) ^ m ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀ <;> nlinarith
  have h2 : 1 + (m : ℝ) * x ≤ (1 + x) ^ m := one_add_mul_le_pow (by linarith) m
  have hP : 0 ≤ (1 - x) ^ m := pow_nonneg (by linarith) m
  have h3 : (1 - x) ^ m * (1 + (m : ℝ) * x) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left h2 hP) h1
  have hy0 : 0 ≤ (m : ℝ) * x := by positivity
  nlinarith [mul_nonneg hy0 (sub_nonneg.2 hmx)]

/-- Counting sequences avoiding a set. -/
lemma count_avoid {α : Type*} [DecidableEq α] (Lg T : Finset α) (m : ℕ) :
    ((Fintype.piFinset fun _ : Fin m => Lg).filter fun ω => ¬ ∃ t, ω t ∈ T).card
      = (Lg \ T).card ^ m := by
  have : ((Fintype.piFinset fun _ : Fin m => Lg).filter fun ω => ¬ ∃ t, ω t ∈ T)
      = Fintype.piFinset fun _ : Fin m => Lg \ T := by
    ext ω
    simp only [mem_filter, Fintype.mem_piFinset, mem_sdiff, not_exists]
    constructor
    · rintro ⟨h1, h2⟩ t; exact ⟨h1 t, h2 t⟩
    · intro h; exact ⟨fun t => (h t).1, fun t => (h t).2⟩
  rw [this, Fintype.card_piFinset]
  simp

/-- Second moment bound. -/
lemma second_moment {γ β : Type*} [DecidableEq β] (Ω : Finset γ) (S : Finset β) (Z : β → γ → ℝ) (p : β → ℝ)
    (hp : ∀ b ∈ S, ∑ ω ∈ Ω, Z b ω = Ω.card * p b)
    (hsq : ∀ b ∈ S, ∀ ω, Z b ω * Z b ω = Z b ω)
    (hcov : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → ∑ ω ∈ Ω, Z b ω * Z b' ω ≤ Ω.card * (p b * p b')) :
    ∑ ω ∈ Ω, (∑ b ∈ S, Z b ω - ∑ b ∈ S, p b) ^ 2 ≤ Ω.card * ∑ b ∈ S, p b * (1 - p b) := by
  have hexp : ∀ ω, (∑ b ∈ S, Z b ω - ∑ b ∈ S, p b) ^ 2
      = ∑ b ∈ S, ∑ b' ∈ S, (Z b ω - p b) * (Z b' ω - p b') := by
    intro ω
    rw [← Finset.sum_sub_distrib, sq, Finset.sum_mul_sum]
  have hinner : ∀ b ∈ S, ∀ b' ∈ S, ∑ ω ∈ Ω, (Z b ω - p b) * (Z b' ω - p b')
      = ∑ ω ∈ Ω, Z b ω * Z b' ω - Ω.card * (p b * p b') := by
    intro b hb b' hb'
    have e : ∀ ω, (Z b ω - p b) * (Z b' ω - p b')
        = Z b ω * Z b' ω - p b' * Z b ω - p b * Z b' ω + p b * p b' := by intro ω; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hp b hb, hp b' hb']
    ring
  calc ∑ ω ∈ Ω, (∑ b ∈ S, Z b ω - ∑ b ∈ S, p b) ^ 2
      = ∑ b ∈ S, ∑ b' ∈ S, ∑ ω ∈ Ω, (Z b ω - p b) * (Z b' ω - p b') := by
        simp only [hexp]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ b ∈ S, ∑ b' ∈ S, (∑ ω ∈ Ω, Z b ω * Z b' ω - Ω.card * (p b * p b')) := by
        refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun b' hb' => ?_
        exact hinner b hb b' hb'
    _ ≤ ∑ b ∈ S, (Ω.card : ℝ) * (p b * (1 - p b)) := by
        refine Finset.sum_le_sum fun b hb => ?_
        rw [← Finset.add_sum_erase S _ hb]
        have h1 : ∑ b' ∈ S.erase b, (∑ ω ∈ Ω, Z b ω * Z b' ω - Ω.card * (p b * p b')) ≤ 0 := by
          refine Finset.sum_nonpos fun b' hb' => ?_
          have := hcov b hb b' (Finset.mem_of_mem_erase hb') (Finset.ne_of_mem_erase hb').symm
          linarith
        have h2 : ∑ ω ∈ Ω, Z b ω * Z b ω = Ω.card * p b := by
          rw [← hp b hb]; exact Finset.sum_congr rfl fun ω _ => hsq b hb ω
        rw [h2]
        nlinarith
    _ = Ω.card * ∑ b ∈ S, p b * (1 - p b) := by rw [Finset.mul_sum]

lemma sum_ite_avoid {α : Type*} [DecidableEq α] (Lg T : Finset α) (m : ℕ) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin m => Lg),
      (if ∃ t, ω t ∈ T then (0 : ℝ) else 1) = ((Lg \ T).card : ℝ) ^ m := by
  have h : ∀ ω : Fin m → α, (if ∃ t, ω t ∈ T then (0 : ℝ) else 1)
      = if ¬ ∃ t, ω t ∈ T then 1 else 0 := fun ω => by split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun ω _ => h ω), Finset.sum_boole, count_avoid]
  push_cast; ring

lemma key_nat {α : Type*} [DecidableEq α] (Lg P Q : Finset α) (hPQ : Disjoint P Q) :
    Lg.card * (Lg \ (P ∪ Q)).card ≤ (Lg \ P).card * (Lg \ Q).card := by
  have hU : (Lg \ P) ∪ (Lg \ Q) = Lg := by
    ext x
    simp only [mem_union, mem_sdiff]
    have : x ∈ P → x ∉ Q := fun h => Finset.disjoint_left.1 hPQ h
    tauto
  have hI : (Lg \ P) ∩ (Lg \ Q) = Lg \ (P ∪ Q) := by
    ext x; simp only [mem_inter, mem_sdiff, mem_union]; tauto
  have h1 := Finset.card_union_add_card_inter (Lg \ P) (Lg \ Q)
  rw [hU, hI] at h1
  have h2 : (Lg \ (P ∪ Q)).card ≤ (Lg \ P).card := by
    rw [← hI]; exact card_le_card inter_subset_left
  have h3 : (Lg \ (P ∪ Q)).card ≤ (Lg \ Q).card := by
    rw [← hI]; exact card_le_card inter_subset_right
  obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le h2
  obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le h3
  rw [hx, hy] at h1 ⊢
  have : Lg.card = (Lg \ (P ∪ Q)).card + x + y := by omega
  rw [this]
  nlinarith

lemma per_line {α β : Type*} [DecidableEq α] [DecidableEq β] (Lg : Finset α) (m : ℕ)
    (S : Finset β) (Mb : β → Finset α) (hM : ∀ b ∈ S, Mb b ⊆ Lg)
    (hdisj : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → Disjoint (Mb b) (Mb b'))
    (n₀ d₀ D : ℕ) (hN : 0 < Lg.card) (hS : n₀ ≤ S.card) (hMc : ∀ b ∈ S, d₀ ≤ (Mb b).card)
    (hmd : m * d₀ ≤ Lg.card) (hmu : 4 * (D + 1) * Lg.card ≤ n₀ * m * d₀) :
    (((Fintype.piFinset fun _ : Fin m => Lg).filter fun ω =>
        (S.filter fun b => ∃ t, ω t ∈ Mb b).card ≤ D).card : ℝ) * ((n₀ * m * d₀ : ℕ) : ℝ)
      ≤ 8 * (Lg.card : ℝ) * (Lg.card : ℝ) ^ m := by
  set Ω := Fintype.piFinset fun _ : Fin m => Lg with hΩ
  set N := Lg.card with hNdef
  have hK : (Ω.card : ℝ) = (N : ℝ) ^ m := by
    rw [hΩ, Fintype.card_piFinset]; simp [hNdef]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set Z : β → (Fin m → α) → ℝ := fun b ω => if ∃ t, ω t ∈ Mb b then 0 else 1 with hZ
  set p : β → ℝ := fun b => (((Lg \ Mb b).card : ℝ) / N) ^ m with hpdef
  have hp : ∀ b ∈ S, ∑ ω ∈ Ω, Z b ω = Ω.card * p b := by
    intro b _
    rw [hZ, hΩ, sum_ite_avoid, hK, hpdef]
    simp only
    rw [div_pow]; field_simp
  have hsq : ∀ b ∈ S, ∀ ω, Z b ω * Z b ω = Z b ω := by
    intro b _ ω; rw [hZ]; simp only; split_ifs <;> norm_num
  have hcov : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → ∑ ω ∈ Ω, Z b ω * Z b' ω ≤ Ω.card * (p b * p b') := by
    intro b hb b' hb' hne
    have e : ∀ ω : Fin m → α, Z b ω * Z b' ω = if ∃ t, ω t ∈ Mb b ∪ Mb b' then 0 else 1 := by
      intro ω; rw [hZ]; simp only
      split_ifs <;> simp_all
    rw [Finset.sum_congr rfl (fun ω _ => e ω), hΩ, sum_ite_avoid, hK, hpdef]
    simp only
    have hk := key_nat Lg (Mb b) (Mb b') (hdisj b hb b' hb' hne)
    have hk' : (N : ℝ) * ((Lg \ (Mb b ∪ Mb b')).card : ℝ)
        ≤ ((Lg \ Mb b).card : ℝ) * ((Lg \ Mb b').card : ℝ) := by exact_mod_cast hk
    have hr : ((Lg \ (Mb b ∪ Mb b')).card : ℝ)
        ≤ ((Lg \ Mb b).card : ℝ) * ((Lg \ Mb b').card : ℝ) / N := by
      rw [le_div_iff₀ hNpos]; linarith
    calc ((Lg \ (Mb b ∪ Mb b')).card : ℝ) ^ m
        ≤ (((Lg \ Mb b).card : ℝ) * ((Lg \ Mb b').card : ℝ) / N) ^ m :=
          pow_le_pow_left₀ (by positivity) hr m
      _ = (N : ℝ) ^ m * ((((Lg \ Mb b).card : ℝ) / N) ^ m * (((Lg \ Mb b').card : ℝ) / N) ^ m) := by
          rw [← mul_pow, ← mul_pow]; congr 1; field_simp
  have hSM := second_moment Ω S Z p hp hsq hcov
  have hpb : ∀ b ∈ S, 0 ≤ p b ∧ p b ≤ 1 - (m : ℝ) * ((d₀ : ℝ) / N) / 2 := by
    intro b hb
    have hc := card_sdiff_add_card_eq_card (hM b hb)
    have hd := hMc b hb
    have hc' : ((Lg \ Mb b).card : ℝ) + d₀ ≤ N := by
      exact_mod_cast (by omega : (Lg \ Mb b).card + d₀ ≤ N)
    have hx : ((Lg \ Mb b).card : ℝ) / N ≤ 1 - (d₀ : ℝ) / N := by
      rw [div_le_iff₀ hNpos, sub_mul, div_mul_cancel₀ _ hNpos.ne']; linarith
    refine ⟨by positivity, ?_⟩
    calc p b ≤ (1 - (d₀ : ℝ) / N) ^ m := pow_le_pow_left₀ (by positivity) hx m
      _ ≤ _ := pow_one_sub_le _ m (by positivity) (by
          rw [mul_div_assoc', div_le_one hNpos]; exact_mod_cast hmd)
  have hp1 : ∀ b ∈ S, p b ≤ 1 := by
    intro b hb
    have := (hpb b hb).2
    have : 0 ≤ (m : ℝ) * ((d₀ : ℝ) / N) / 2 := by positivity
    linarith
  set μ : ℝ := ∑ b ∈ S, (1 - p b) with hμdef
  have hQ : ((n₀ * m * d₀ : ℕ) : ℝ) ≤ 2 * N * μ := by
    have h1 : ∑ b ∈ S, (m : ℝ) * ((d₀ : ℝ) / N) / 2 ≤ μ :=
      sum_le_sum fun b hb => by linarith [(hpb b hb).2]
    rw [sum_const, nsmul_eq_mul] at h1
    have h2 : (S.card : ℝ) * ((m : ℝ) * ((d₀ : ℝ) / N) / 2) * (2 * N) = S.card * m * d₀ := by
      field_simp
    have h3 : ((n₀ * m * d₀ : ℕ) : ℝ) ≤ S.card * m * d₀ := by
      push_cast
      have : (n₀ : ℝ) ≤ S.card := by exact_mod_cast hS
      have : (0 : ℝ) ≤ m * d₀ := by positivity
      nlinarith
    nlinarith
  have hμD : 2 * ((D : ℝ) + 1) ≤ μ := by
    have h1 : ((4 * (D + 1) * N : ℕ) : ℝ) ≤ ((n₀ * m * d₀ : ℕ) : ℝ) := by exact_mod_cast hmu
    push_cast at h1
    have : 2 * N * (2 * ((D : ℝ) + 1)) ≤ 2 * N * μ := by push_cast at hQ; nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hU : ∀ ω : Fin m → α, ((S.filter fun b => ∃ t, ω t ∈ Mb b).card : ℝ) + ∑ b ∈ S, Z b ω
      = S.card := by
    intro ω
    have e : ∀ b, Z b ω = if ¬ ∃ t, ω t ∈ Mb b then 1 else 0 := by
      intro b; rw [hZ]; simp only; split_ifs <;> simp_all
    rw [Finset.sum_congr rfl (fun b _ => e b), Finset.sum_boole]
    exact_mod_cast card_filter_add_card_filter_not _
  have hν : ∑ b ∈ S, p b = S.card - μ := by
    rw [hμdef, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]; ring
  set bad := Ω.filter fun ω => (S.filter fun b => ∃ t, ω t ∈ Mb b).card ≤ D with hbad
  have hμpos : 0 < μ := by have : (0 : ℝ) ≤ D := by positivity
                           linarith
  have hgap : ∀ ω ∈ bad, (μ / 2) ^ 2 ≤ (∑ b ∈ S, Z b ω - ∑ b ∈ S, p b) ^ 2 := by
    intro ω hω
    rw [hbad, mem_filter] at hω
    have hX : ((S.filter fun b => ∃ t, ω t ∈ Mb b).card : ℝ) ≤ D := by exact_mod_cast hω.2
    have := hU ω
    apply pow_le_pow_left₀ (by positivity)
    rw [hν]; linarith
  have hchain : (bad.card : ℝ) * (μ / 2) ^ 2 ≤ Ω.card * μ := by
    calc (bad.card : ℝ) * (μ / 2) ^ 2
        ≤ ∑ ω ∈ bad, (∑ b ∈ S, Z b ω - ∑ b ∈ S, p b) ^ 2 := by
          have := card_nsmul_le_sum bad _ _ hgap
          rwa [nsmul_eq_mul] at this
      _ ≤ ∑ ω ∈ Ω, (∑ b ∈ S, Z b ω - ∑ b ∈ S, p b) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ ≤ Ω.card * ∑ b ∈ S, p b * (1 - p b) := hSM
      _ ≤ Ω.card * μ := by
          gcongr
          refine sum_le_sum fun b hb => ?_
          nlinarith [(hpb b hb).1, hp1 b hb]
  have hbad4 : (bad.card : ℝ) * μ ≤ 4 * Ω.card := by
    have : (bad.card : ℝ) * μ * μ ≤ 4 * Ω.card * μ := by nlinarith
    exact le_of_mul_le_mul_right this hμpos
  rw [← hK]
  have hb0 : (0 : ℝ) ≤ bad.card := by positivity
  calc (bad.card : ℝ) * ((n₀ * m * d₀ : ℕ) : ℝ) ≤ bad.card * (2 * N * μ) :=
        mul_le_mul_of_nonneg_left hQ hb0
    _ = 2 * N * (bad.card * μ) := by ring
    _ ≤ 2 * N * (4 * Ω.card) := mul_le_mul_of_nonneg_left hbad4 (by linarith)
    _ = 8 * N * Ω.card := by ring

end A3

end DLT

namespace DLT

theorem sampling {α β : Type*} [DecidableEq α] [DecidableEq β] (Lg : Finset α) (hne : Lg.Nonempty)
    (B : α → Finset β) (M : α → β → Finset α) (hM : ∀ L ∈ Lg, ∀ b ∈ B L, M L b ⊆ Lg)
    (hdisj : ∀ L ∈ Lg, ∀ b ∈ B L, ∀ b' ∈ B L, b ≠ b' → Disjoint (M L b) (M L b'))
    (n₀ d₀ m D : ℕ) (hB : ∀ L ∈ Lg, n₀ ≤ (B L).card)
    (hMc : ∀ L ∈ Lg, ∀ b ∈ B L, d₀ ≤ (M L b).card)
    (hmd : m * d₀ ≤ Lg.card) (hmu : 4 * (D + 1) * Lg.card ≤ n₀ * m * d₀) :
    ∃ ω : Fin m → α, (∀ t, ω t ∈ Lg) ∧
      ((Lg.filter fun L => ((B L).filter fun b => ∃ t, ω t ∈ M L b).card ≤ D).card : ℝ) *
          ((n₀ * m * d₀ : ℕ) : ℝ) ≤ 8 * (Lg.card : ℝ) ^ 2 := by
  have hN : 0 < Lg.card := hne.card_pos
  set Ω := Fintype.piFinset fun _ : Fin m => Lg with hΩ
  have hΩne : Ω.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨fun _ => x, by simp [hΩ, hx]⟩
  have hK : (Ω.card : ℝ) = (Lg.card : ℝ) ^ m := by
    rw [hΩ, Fintype.card_piFinset]; simp
  have hbound : ∀ L ∈ Lg,
      ((Ω.filter fun ω => ((B L).filter fun b => ∃ t, ω t ∈ M L b).card ≤ D).card : ℝ) *
        ((n₀ * m * d₀ : ℕ) : ℝ) ≤ 8 * (Lg.card : ℝ) * (Lg.card : ℝ) ^ m := fun L hL =>
    A3.per_line Lg m (B L) (M L) (hM L hL) (hdisj L hL) n₀ d₀ D hN (hB L hL) (hMc L hL) hmd hmu
  have hsum : ∑ ω ∈ Ω,
      ((Lg.filter fun L => ((B L).filter fun b => ∃ t, ω t ∈ M L b).card ≤ D).card : ℝ) *
          ((n₀ * m * d₀ : ℕ) : ℝ)
      = ∑ L ∈ Lg,
      ((Ω.filter fun ω => ((B L).filter fun b => ∃ t, ω t ∈ M L b).card ≤ D).card : ℝ) *
        ((n₀ * m * d₀ : ℕ) : ℝ) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    congr 1
    simp only [Finset.card_filter]
    push_cast
    exact Finset.sum_comm
  have hle : ∑ ω ∈ Ω,
      ((Lg.filter fun L => ((B L).filter fun b => ∃ t, ω t ∈ M L b).card ≤ D).card : ℝ) *
          ((n₀ * m * d₀ : ℕ) : ℝ) ≤ ∑ _ω ∈ Ω, 8 * (Lg.card : ℝ) ^ 2 := by
    rw [hsum]
    calc _ ≤ ∑ _L ∈ Lg, 8 * (Lg.card : ℝ) * (Lg.card : ℝ) ^ m := Finset.sum_le_sum hbound
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, hK]
        ring
  obtain ⟨ω, hω, h⟩ := Finset.exists_le_of_sum_le hΩne hle
  refine ⟨ω, ?_, h⟩
  rw [hΩ, Fintype.mem_piFinset] at hω
  exact hω

end DLT

end Part4

section Part5
open Polynomial

namespace DLT.A5

theorem C_dvd_iff_map_mk {F : Type*} [Field F] (g : Polynomial F) (Q : Polynomial (Polynomial F)) :
    C g ∣ Q ↔ Q.map (Ideal.Quotient.mk (Ideal.span {g})) = 0 := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h; ext n; simp [coeff_map, (Ideal.Quotient.eq_zero_iff_dvd g _).2 (h n)]
  · intro h n
    have := congrArg (fun Q => Q.coeff n) h
    simpa [coeff_map, Ideal.Quotient.eq_zero_iff_dvd] using this

theorem expand_contract_of_coeff {R : Type*} [CommSemiring R] (q : ℕ) (hq : 0 < q) (f : R[X])
    (hf : ∀ n, ¬ q ∣ n → f.coeff n = 0) : expand R q (contract q f) = f := by
  ext n
  rw [coeff_expand hq]
  split_ifs with h
  · rw [coeff_contract hq.ne', Nat.div_mul_cancel h]
  · exact (hf n h).symm

theorem natDegree_contract_le {R : Type*} [CommSemiring R] (q k : ℕ) (hq : 0 < q) (f : R[X])
    (hf : f.natDegree ≤ q * k) : (contract q f).natDegree ≤ k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_contract hq.ne']
  apply coeff_eq_zero_of_natDegree_lt
  have hN' : k < N := by exact_mod_cast hN
  have : q * k < N * q := by rw [mul_comm N]; exact Nat.mul_lt_mul_of_pos_left hN' hq
  omega

theorem coeff_eval_C {R : Type*} [CommSemiring R] (U : R[X][X]) (t : R) (j : ℕ) :
    (U.eval (C t)).coeff j = ∑ n ∈ Finset.range (U.natDegree + 1), (U.coeff n).coeff j * t ^ n := by
  rw [eval_eq_sum_range, finsetSum_coeff]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← C_pow, coeff_mul_C]

theorem eval2_map {R : Type*} [CommSemiring R] (f : R →+* R) (W : R[X][X]) (s t : R) :
    ((W.map (mapRingHom f)).eval (C (f t))).eval (f s) = f ((W.eval (C t)).eval s) := by
  have : C (f t) = mapRingHom f (C t) := by simp
  rw [this, eval_map, eval₂_at_apply, coe_mapRingHom, eval_map, eval₂_at_apply]

end DLT.A5

namespace DLT

/-- A function that is a polynomial of degree `≤ d` along every row and every column is a
bivariate polynomial. -/
theorem rows_cols_poly {F : Type*} [Field F] [Fintype F] [DecidableEq F] (d : ℕ)
    (hd : d < Fintype.card F) (Ψ : F → F → F)
    (hrow : ∀ s, ∃ p : Polynomial F, p.natDegree ≤ d ∧ ∀ t, Ψ s t = p.eval t)
    (hcol : ∀ t, ∃ p : Polynomial F, p.natDegree ≤ d ∧ ∀ s, Ψ s t = p.eval s) :
    ∃ N : Polynomial (Polynomial F), N.natDegree ≤ d ∧ (∀ n, (N.coeff n).natDegree ≤ d) ∧
      ∀ s t, (N.eval (C t)).eval s = Ψ s t := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := d + 1)
    (by rw [Finset.card_univ]; omega)
  choose p hpdeg hp using hrow
  have hinj : Set.InjOn (id : F → F) ↑S := Function.injective_id.injOn
  refine ⟨∑ i ∈ S, C (Lagrange.basis S id i) * (p i).map C, ?_, ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    exact (natDegree_map_le).trans (hpdeg i)
  · intro n
    rw [finsetSum_coeff]
    refine natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)
    rw [coeff_C_mul, coeff_map]
    refine (natDegree_mul_le).trans ?_
    rw [Lagrange.natDegree_basis hinj hi, natDegree_C]; omega
  · intro s t
    obtain ⟨q, hqdeg, hq⟩ := hcol t
    have hq' : q = Lagrange.interpolate S id (fun i => Ψ i t) := by
      apply Lagrange.eq_interpolate_of_eval_eq _ hinj
      · calc q.degree ≤ q.natDegree := degree_le_natDegree
          _ < S.card := by rw [hS]; exact_mod_cast Nat.lt_succ_of_le hqdeg
      · intro i _; exact (hq i).symm
    rw [hq s, hq', Lagrange.interpolate_apply, eval_finsetSum, eval_finsetSum, eval_finsetSum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [eval_mul, eval_C, eval_map, eval₂_at_apply, eval_mul, eval_C, eval_mul, eval_C, ← hp i t,
      mul_comm]

/-- Dividing by a polynomial in the inner variable. -/
theorem dvd_of_dvd_mul_mapC {F : Type*} [Field F] (g h : Polynomial F) (hh : h ≠ 0)
    (P : Polynomial (Polynomial F)) (hdiv : C g ∣ P * h.map C) : C g ∣ P := by
  set h0 := h * C (h.leadingCoeff)⁻¹ with hh0
  have hm : h0.Monic := monic_mul_leadingCoeff_inv hh
  have hdiv' : C g ∣ P * h0.map C := by
    rw [hh0, Polynomial.map_mul, Polynomial.map_C, ← mul_assoc]
    exact dvd_mul_of_dvd_left hdiv _
  rw [A5.C_dvd_iff_map_mk] at hdiv' ⊢
  rw [Polynomial.map_mul, Polynomial.map_map] at hdiv'
  exact (hm.map _).mul_left_eq_zero_iff.1 hdiv'

/-- Extracting a `p^e`-th root. -/
theorem frobenius_root {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (e k : ℕ)
    (U : Polynomial (Polynomial F)) (hUt : U.natDegree ≤ p ^ e * k)
    (hUs : ∀ n, (U.coeff n).natDegree ≤ p ^ e * k)
    (Ss Ts : Finset F) (hSc : p ^ e * k < Ss.card) (hTc : p ^ e * k < Ts.card)
    (hS : ∀ s ∈ Ss, ∃ g : Polynomial F, U.map (Polynomial.evalRingHom s) = g ^ (p ^ e))
    (hT : ∀ t ∈ Ts, ∃ g : Polynomial F, U.eval (C t) = g ^ (p ^ e)) :
    ∃ V : Polynomial (Polynomial F), V.natDegree ≤ k ∧ (∀ n, (V.coeff n).natDegree ≤ k) ∧
      ∀ s t, ((V.eval (C t)).eval s) ^ (p ^ e) = (U.eval (C t)).eval s := by
  have : ExpChar F p := ExpChar.prime (Fact.out)
  have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  -- coefficients of a `p^e`-th power
  have hpow : ∀ (g : F[X]) (n : ℕ), ¬ p ^ e ∣ n → (g ^ (p ^ e)).coeff n = 0 := by
    intro g n hn
    rw [← map_iterateFrobenius_expand, coeff_map, coeff_expand hq, if_neg hn, map_zero]
  have hA : ∀ n j, ¬ p ^ e ∣ n → (U.coeff n).coeff j = 0 := by
    intro n j hn
    have : U.coeff n = 0 := by
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Ss
      · intro s hs
        obtain ⟨g, hg⟩ := hS s hs
        have h1 := congrArg (fun P => P.coeff n) hg
        simp only [coeff_map, coe_evalRingHom] at h1
        rw [h1, hpow g n hn]
      · exact lt_of_le_of_lt (hUs n) hSc
    rw [this, coeff_zero]
  have hB : ∀ n j, ¬ p ^ e ∣ j → (U.coeff n).coeff j = 0 := by
    intro n j hj
    set W : F[X] := ∑ m ∈ Finset.range (U.natDegree + 1), monomial m ((U.coeff m).coeff j) with hWdef
    have hW : W = 0 := by
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Ts
      · intro t ht
        obtain ⟨g, hg⟩ := hT t ht
        have : W.eval t = (U.eval (C t)).coeff j := by
          rw [A5.coeff_eval_C, hWdef, eval_finsetSum]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [eval_monomial]
        rw [this, hg, hpow g j hj]
      · refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hUt hTc)
        refine natDegree_sum_le_of_forall_le _ _ (fun m hm => ?_)
        refine (natDegree_monomial_le _).trans ?_
        have := Finset.mem_range.1 hm
        omega
    by_cases hn : n ≤ U.natDegree
    · have := congrArg (fun P => P.coeff n) hW
      simpa [hWdef, finsetSum_coeff, coeff_monomial, Nat.lt_succ_of_le hn] using this
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn), coeff_zero]
  -- the contracted polynomial
  set U' : F[X][X] := ∑ n ∈ Finset.range (U.natDegree + 1), monomial n (contract (p ^ e) (U.coeff n))
    with hU'def
  have hU'coeff : ∀ n, U'.coeff n = contract (p ^ e) (U.coeff n) := by
    intro n
    rw [hU'def, finsetSum_coeff]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · have : U.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by
        have := Finset.mem_range.not.1 h; omega)
      rw [this]
      ext m; rw [coeff_contract hq.ne']; simp
  have hU'map : U'.map (expand F (p ^ e) : F[X] →+* F[X]) = U := by
    ext1 n
    rw [coeff_map, hU'coeff]
    exact A5.expand_contract_of_coeff _ hq _ (hB n)
  have hU'exp : expand _ (p ^ e) (contract (p ^ e) U') = U' := by
    apply A5.expand_contract_of_coeff _ hq
    intro n hn
    rw [hU'coeff]
    have : U.coeff n = 0 := by ext j; rw [hA n j hn, coeff_zero]
    rw [this]
    ext m; rw [coeff_contract hq.ne']; simp
  set V' := contract (p ^ e) U' with hV'def
  set φ : F ≃+* F := iterateFrobeniusEquiv F p e with hφ
  refine ⟨V'.map (mapRingHom (φ.symm : F →+* F)), ?_, ?_, ?_⟩
  · refine (natDegree_map_le).trans ?_
    apply A5.natDegree_contract_le _ _ hq
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hU'coeff, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hUt (by exact_mod_cast hN))]
    ext m; rw [coeff_contract hq.ne']; simp
  · intro n
    rw [coeff_map, coe_mapRingHom]
    refine (natDegree_map_le).trans ?_
    rw [hV'def, coeff_contract hq.ne', hU'coeff]
    exact A5.natDegree_contract_le _ _ hq _ (hUs _)
  · intro s t
    have hφx : ∀ x : F, φ x = x ^ (p ^ e) := by
      intro x; rw [hφ, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
    have hid : (mapRingHom (φ : F →+* F)).comp (mapRingHom (φ.symm : F →+* F)) = RingHom.id _ := by
      ext a n
      · simp
      · simp
    rw [← hφx, ← RingEquiv.coe_toRingHom, ← A5.eval2_map, Polynomial.map_map, hid,
      Polynomial.map_id]
    rw [← hU'map, ← hU'exp, map_expand, expand_eval, ← C_pow]
    have hC : C (t ^ p ^ e) = (expand F (p ^ e) : F[X] →+* F[X]) (C (t ^ p ^ e)) := by simp
    rw [hC, eval_map, eval₂_at_apply]
    simp [expand_eval, hφx]

end DLT

end Part5

section Part6
open Polynomial

namespace DLT

/-- Restriction of `Q(X,Y,Z)` (as `F[X,Y][Z]`) to the line `t ↦ b + t v` with `Z = g(t)`. -/
noncomputable def restrictLine {F : Type*} [Field F] (b v : Fin 2 → F) (g : Polynomial F)
    (Q : Polynomial (MvPolynomial (Fin 2) F)) : Polynomial F :=
  (Q.map (MvPolynomial.aeval (fun i => C (b i) + C (v i) * X)).toRingHom).eval g

/-- `(1,1,K)`-weighted degree at most `D`. -/
def WDeg {F : Type*} [Field F] (K D : ℕ) (Q : Polynomial (MvPolynomial (Fin 2) F)) : Prop :=
  ∀ n, Q.coeff n ≠ 0 → (Q.coeff n).totalDegree + K * n ≤ D

namespace A6

theorem natDegree_aeval_le {F : Type*} [Field F] (b v : Fin 2 → F)
    (p : MvPolynomial (Fin 2) F) :
    (MvPolynomial.aeval (fun i => C (b i) + C (v i) * X) p).natDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun s hs => ?_)
  rw [MvPolynomial.aeval_monomial]
  refine (natDegree_mul_le).trans ?_
  rw [Polynomial.algebraMap_eq, natDegree_C, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine (natDegree_pow_le).trans ?_
  have : (C (b i) + C (v i) * X : Polynomial F).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans ?_
    simp only [natDegree_C, zero_le, max_le_iff, true_and]
    exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  calc s i * _ ≤ s i * 1 := Nat.mul_le_mul_left _ this
    _ = s i := mul_one _

end A6

theorem restrictLine_natDegree_le {F : Type*} [Field F] (K D : ℕ) (b v : Fin 2 → F)
    (g : Polynomial F) (Q : Polynomial (MvPolynomial (Fin 2) F)) (hQ : WDeg K D Q)
    (hg : g.natDegree ≤ K) : (restrictLine b v g Q).natDegree ≤ D := by
  unfold restrictLine
  rw [eval_map, eval₂_eq_sum, Polynomial.sum_def]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun n hn => ?_)
  have h := hQ n (mem_support_iff.mp hn)
  refine (natDegree_mul_le).trans ?_
  refine le_trans ?_ h
  refine add_le_add (A6.natDegree_aeval_le b v _) ?_
  refine (natDegree_pow_le).trans ?_
  rw [mul_comm]
  exact Nat.mul_le_mul_right _ hg

namespace A6

/-- exponent vector of `X 0 ^ m.1 * X 1 ^ m.2.1`. -/
noncomputable def ev (m : ℕ × ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 m.1 + Finsupp.single 1 m.2.1

theorem ev_inj {m m' : ℕ × ℕ × ℕ} (h : ev m = ev m') (h2 : m.2.2 = m'.2.2) : m = m' := by
  have h0 := congrArg (fun f => f 0) h
  have h1 := congrArg (fun f => f 1) h
  simp [ev] at h0 h1
  obtain ⟨a, b, c⟩ := m
  obtain ⟨a', b', c'⟩ := m'
  simp_all

theorem ev_degree (m : ℕ × ℕ × ℕ) : ((ev m).sum fun _ e => e) = m.1 + m.2.1 := by
  simp [ev, Finsupp.sum_fintype, Fin.sum_univ_two]

noncomputable def Phi {F : Type*} [Field F] (Mon : Finset (ℕ × ℕ × ℕ)) :
    (Mon → F) →ₗ[F] Polynomial (MvPolynomial (Fin 2) F) where
  toFun c := ∑ m : Mon, Polynomial.monomial m.1.2.2 (MvPolynomial.monomial (ev m.1) (c m))
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' a c := by
    simp [Finset.smul_sum, Polynomial.smul_monomial, MvPolynomial.smul_monomial]

theorem Phi_apply {F : Type*} [Field F] (Mon : Finset (ℕ × ℕ × ℕ)) (c : Mon → F) :
    Phi Mon c = ∑ m : Mon, Polynomial.monomial m.1.2.2 (MvPolynomial.monomial (ev m.1) (c m)) :=
  rfl

theorem Phi_coeff {F : Type*} [Field F] (Mon : Finset (ℕ × ℕ × ℕ)) (c : Mon → F) (n : ℕ)
    (s : Fin 2 →₀ ℕ) :
    ((Phi Mon c).coeff n).coeff s = ∑ m : Mon, if m.1.2.2 = n ∧ ev m.1 = s then c m else 0 := by
  rw [Phi_apply, Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases h1 : m.1.2.2 = n
  · by_cases h2 : ev m.1 = s
    · simp [h1, h2]
    · simp [h1, h2, MvPolynomial.coeff_monomial]
  · simp [h1, Polynomial.coeff_monomial]

theorem Phi_coeff_self {F : Type*} [Field F] (Mon : Finset (ℕ × ℕ × ℕ)) (c : Mon → F) (m : Mon) :
    ((Phi Mon c).coeff m.1.2.2).coeff (ev m.1) = c m := by
  rw [Phi_coeff, Finset.sum_eq_single m]
  · simp
  · intro m' _ hm'
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hm' (Subtype.ext (ev_inj h2 h1))
  · simp

theorem restrictLine_add {F : Type*} [Field F] (b v : Fin 2 → F) (g : Polynomial F)
    (P Q : Polynomial (MvPolynomial (Fin 2) F)) :
    restrictLine b v g (P + Q) = restrictLine b v g P + restrictLine b v g Q := by
  simp [restrictLine, Polynomial.map_add]

theorem restrictLine_smul {F : Type*} [Field F] (b v : Fin 2 → F) (g : Polynomial F) (a : F)
    (Q : Polynomial (MvPolynomial (Fin 2) F)) :
    restrictLine b v g (a • Q) = a • restrictLine b v g Q := by
  unfold restrictLine
  rw [← algebraMap_smul (MvPolynomial (Fin 2) F) a Q, Polynomial.smul_eq_C_mul,
    Polynomial.map_mul, map_C, eval_mul, eval_C, Polynomial.smul_eq_C_mul]
  congr 1
  simp

noncomputable def Psi {F : Type*} [Field F] (D : ℕ) {ι : Type*} (S : Finset ι)
    (b v : ι → Fin 2 → F) (g : ι → Polynomial F) :
    Polynomial (MvPolynomial (Fin 2) F) →ₗ[F] (S × Fin (D + 1) → F) where
  toFun Q := fun p => (restrictLine (b p.1) (v p.1) (g p.1) Q).coeff p.2
  map_add' P Q := by
    funext p
    simp [restrictLine_add]
  map_smul' a Q := by
    funext p
    simp [restrictLine_smul]

end A6

theorem interpolate {F : Type*} [Field F] (K D : ℕ) {ι : Type*} (S : Finset ι)
    (b v : ι → Fin 2 → F) (g : ι → Polynomial F) (hg : ∀ i ∈ S, (g i).natDegree ≤ K)
    (hcount : (D + 1) * S.card < ((Finset.range (D + 1) ×ˢ Finset.range (D + 1) ×ˢ
        Finset.range (D + 1)).filter fun m : ℕ × ℕ × ℕ => m.1 + m.2.1 + K * m.2.2 ≤ D).card) :
    ∃ Q : Polynomial (MvPolynomial (Fin 2) F), Q ≠ 0 ∧ WDeg K D Q ∧
      ∀ i ∈ S, restrictLine (b i) (v i) (g i) Q = 0 := by
  set Mon := ((Finset.range (D + 1) ×ˢ Finset.range (D + 1) ×ˢ
        Finset.range (D + 1)).filter fun m : ℕ × ℕ × ℕ => m.1 + m.2.1 + K * m.2.2 ≤ D) with hMon
  have hMonD : ∀ m ∈ Mon, m.1 + m.2.1 + K * m.2.2 ≤ D := by
    intro m hm
    rw [hMon, Finset.mem_filter] at hm
    exact hm.2
  let f := A6.Psi D S b v g ∘ₗ A6.Phi (F := F) Mon
  have hker : LinearMap.ker f ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin, mul_comm]
    exact hcount
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hW : WDeg K D (A6.Phi Mon c) := by
    intro n hn
    have key : ∀ s ∈ ((A6.Phi Mon c).coeff n).support, (s.sum fun _ e => e) + K * n ≤ D := by
      intro s hs
      rw [MvPolynomial.mem_support_iff, A6.Phi_coeff] at hs
      obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
      rw [ne_eq, ite_eq_right_iff, not_forall] at hm
      obtain ⟨⟨h1, h2⟩, -⟩ := hm
      subst h1 h2
      rw [A6.ev_degree]
      exact hMonD m.1 m.2
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hn
    have hs' := key s (MvPolynomial.mem_support_iff.mpr hs)
    have : ((A6.Phi Mon c).coeff n).totalDegree ≤ D - K * n := by
      unfold MvPolynomial.totalDegree
      refine Finset.sup_le (fun s hs => ?_)
      have := key s hs
      omega
    omega
  refine ⟨A6.Phi Mon c, ?_, hW, ?_⟩
  · intro h
    apply hc0
    funext m
    have := A6.Phi_coeff_self Mon c m
    rw [h] at this
    simpa using this.symm
  · intro i hi
    have hz : f c = 0 := hc
    have hdeg := restrictLine_natDegree_le K D (b i) (v i) (g i) (A6.Phi Mon c) hW (hg i hi)
    ext j
    rw [coeff_zero]
    by_cases hj : j ≤ D
    · have := congrFun hz (⟨i, hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩)
      simpa [f, A6.Psi] using this
    · exact coeff_eq_zero_of_natDegree_lt (by omega)

end DLT

end Part6

section Part7
open Polynomial

namespace DLT

section Infra
variable {F : Type*} [Field F]

/-- Point evaluation `Q(x, z)` of `Q ∈ F[X,Y][Z]`. -/
noncomputable def ptEval (Q : Polynomial (MvPolynomial (Fin 2) F)) (x : Fin 2 → F) (z : F) : F :=
  (Q.map (MvPolynomial.eval x)).eval z

lemma infra_evalRingHom_comp_aeval (b v : Fin 2 → F) (t : F) :
    (evalRingHom t).comp (MvPolynomial.aeval (R := F) (fun i => C (b i) + C (v i) * X)).toRingHom =
      MvPolynomial.eval (b + t • v) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
      MvPolynomial.eval_C, coe_evalRingHom, Polynomial.algebraMap_eq, eval_C]
  · intro i
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X,
      MvPolynomial.eval_X, coe_evalRingHom, eval_add, eval_C, eval_mul, eval_X, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

lemma restrictLine_eval (b v : Fin 2 → F) (g : Polynomial F)
    (Q : Polynomial (MvPolynomial (Fin 2) F)) (t : F) :
    (restrictLine b v g Q).eval t = ptEval Q (b + t • v) (g.eval t) := by
  unfold restrictLine ptEval
  rw [eval_map, eval_map]
  have := Polynomial.hom_eval₂ Q (MvPolynomial.aeval (R := F) (fun i => C (b i) + C (v i) * X)).toRingHom
    (evalRingHom t) g
  simp only [coe_evalRingHom] at this
  rw [this, infra_evalRingHom_comp_aeval]

lemma infra_comp_aeval (b v : Fin 2 → F) (c : F) :
    (compRingHom (X + C c)).comp (MvPolynomial.aeval (R := F) (fun i => C (b i) + C (v i) * X)).toRingHom =
      (MvPolynomial.aeval (R := F) (fun i => C ((b + c • v) i) + C (v i) * X)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
      Polynomial.algebraMap_eq, coe_compRingHom_apply, C_comp]
  · intro i
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X,
      coe_compRingHom_apply, add_comp, C_comp, mul_comp, X_comp, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, C_add, C_mul]
    ring

lemma restrictLine_shift (b v : Fin 2 → F) (c : F) (g : Polynomial F)
    (Q : Polynomial (MvPolynomial (Fin 2) F)) :
    restrictLine (b + c • v) v (g.comp (X + C c)) Q = (restrictLine b v g Q).comp (X + C c) := by
  unfold restrictLine
  rw [eval_map, eval_map]
  have := Polynomial.hom_eval₂ Q (MvPolynomial.aeval (R := F) (fun i => C (b i) + C (v i) * X)).toRingHom
    (compRingHom (X + C c)) g
  simp only [coe_compRingHom_apply] at this
  rw [this, infra_comp_aeval]

lemma restrictLine_expand (p : ℕ) (b v : Fin 2 → F) (g : Polynomial F)
    (Q : Polynomial (MvPolynomial (Fin 2) F)) :
    restrictLine b v g (expand (MvPolynomial (Fin 2) F) p Q) = restrictLine b v (g ^ p) Q := by
  unfold restrictLine
  rw [Polynomial.map_expand, expand_eval]

lemma ptEval_expand (p : ℕ) (Q : Polynomial (MvPolynomial (Fin 2) F)) (x : Fin 2 → F) (z : F) :
    ptEval (expand (MvPolynomial (Fin 2) F) p Q) x z = ptEval Q x (z ^ p) := by
  unfold ptEval
  rw [Polynomial.map_expand, expand_eval]

lemma restrictLine_C (b v : Fin 2 → F) (g : Polynomial F) (q : MvPolynomial (Fin 2) F) :
    restrictLine b v g (C q) = MvPolynomial.aeval (fun i => C (b i) + C (v i) * X) q := by
  unfold restrictLine
  rw [Polynomial.map_C, eval_C]
  rfl

lemma WDeg_derivative {K D : ℕ} {Q : Polynomial (MvPolynomial (Fin 2) F)} (h : WDeg K D Q) :
    WDeg K D (derivative Q) := by
  intro n hn
  rw [coeff_derivative] at hn ⊢
  have hq : Q.coeff (n + 1) ≠ 0 := by
    intro h0; apply hn; rw [h0, zero_mul]
  have h1 := h (n + 1) hq
  have h2 : (Q.coeff (n + 1) * ((n : MvPolynomial (Fin 2) F) + 1)).totalDegree ≤
      (Q.coeff (n + 1)).totalDegree := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have : ((n : MvPolynomial (Fin 2) F) + 1).totalDegree = 0 := by
      rw [show ((n : MvPolynomial (Fin 2) F) + 1) = MvPolynomial.C ((n : F) + 1) by simp]
      exact MvPolynomial.totalDegree_C _
    omega
  have h3 : K * n ≤ K * (n + 1) := Nat.mul_le_mul_left _ (Nat.le_succ n)
  omega

lemma infra_WDeg_of_expand_pos {K D p : ℕ} (hp : 0 < p) {Q : Polynomial (MvPolynomial (Fin 2) F)}
    (h : WDeg K D (expand (MvPolynomial (Fin 2) F) p Q)) : WDeg (p * K) D Q := by
  intro n hn
  have := h (n * p) (by rwa [coeff_expand_mul hp])
  rw [coeff_expand_mul hp] at this
  calc (Q.coeff n).totalDegree + p * K * n = (Q.coeff n).totalDegree + K * (n * p) := by ring
    _ ≤ D := this

lemma WDeg_of_expand {K D p : ℕ} (hp : 0 < p) {Q : Polynomial (MvPolynomial (Fin 2) F)}
    (h : WDeg K D (expand (MvPolynomial (Fin 2) F) p Q)) : WDeg (p * K) D Q :=
  infra_WDeg_of_expand_pos hp h

lemma natDegree_le_of_WDeg {K D : ℕ} {Q : Polynomial (MvPolynomial (Fin 2) F)} (h : WDeg K D Q) :
    K * Q.natDegree ≤ D := by
  by_cases hQ : Q = 0
  · subst hQ; simp
  · have := h Q.natDegree (by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hQ)
    omega

lemma totalDegree_coeff_le_of_WDeg {K D : ℕ} {Q : Polynomial (MvPolynomial (Fin 2) F)}
    (h : WDeg K D Q) (n : ℕ) : (Q.coeff n).totalDegree ≤ D := by
  by_cases hn : Q.coeff n = 0
  · rw [hn]; simp
  · have := h n hn; omega

/-- Substitution of the affine parametrization `(V, W) ↦ p₀ + V α + W β` into a bivariate
polynomial; the result lies in `F[V][W]` (inner variable `V`, outer `W`). -/
noncomputable def subst (p₀ α β : Fin 2 → F) :
    MvPolynomial (Fin 2) F →ₐ[F] Polynomial (Polynomial F) :=
  MvPolynomial.aeval (fun i => C (C (p₀ i)) + C (C (α i)) * C X + C (C (β i)) * X)

lemma infra_evalRingHom_comp_subst (p₀ α β : Fin 2 → F) :
    (evalRingHom (0 : Polynomial F)).comp (subst p₀ α β).toRingHom =
      (MvPolynomial.aeval (R := F) (fun i => C (p₀ i) + C (α i) * X)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [subst]
  · intro i
    simp [subst]

lemma subst_eval_zero (p₀ α β : Fin 2 → F) (q : MvPolynomial (Fin 2) F) :
    (subst p₀ α β q).eval 0 = MvPolynomial.aeval (fun i => C (p₀ i) + C (α i) * X) q := by
  have := congrArg (fun f => f q) (infra_evalRingHom_comp_subst p₀ α β)
  simpa using this

lemma infra_mapRingHom_comp_subst (p₀ α β : Fin 2 → F) (a : F) :
    (mapRingHom (evalRingHom a)).comp (subst p₀ α β).toRingHom =
      (MvPolynomial.aeval (R := F) (fun i => C ((p₀ + a • α) i) + C (β i) * X)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [subst]
  · intro i
    simp [subst]
    ring

lemma subst_map_eval (p₀ α β : Fin 2 → F) (a : F) (q : MvPolynomial (Fin 2) F) :
    (subst p₀ α β q).map (evalRingHom a) =
      MvPolynomial.aeval (fun i => C ((p₀ + a • α) i) + C (β i) * X) q := by
  have := congrArg (fun f => f q) (infra_mapRingHom_comp_subst p₀ α β a)
  simpa using this

lemma map_subst_anchor (p₀ α β : Fin 2 → F) (Q : Polynomial (MvPolynomial (Fin 2) F))
    (h : Polynomial F) :
    ((Q.map (subst p₀ α β).toRingHom).map (evalRingHom 0)).eval h = restrictLine p₀ α h Q := by
  unfold restrictLine
  rw [Polynomial.map_map, infra_evalRingHom_comp_subst]

lemma map_subst_line (p₀ α β : Fin 2 → F) (Q : Polynomial (MvPolynomial (Fin 2) F)) (a : F)
    (g : Polynomial F) :
    ((Q.map (subst p₀ α β).toRingHom).map (mapRingHom (evalRingHom a))).eval g =
      restrictLine (p₀ + a • α) β g Q := by
  unfold restrictLine
  rw [Polynomial.map_map, infra_mapRingHom_comp_subst]

lemma infra_TD_mono {P : Polynomial (Polynomial F)} {S T : ℕ}
    (hP : ∀ m, P.coeff m ≠ 0 → (P.coeff m).natDegree + m ≤ S) (hST : S ≤ T) :
    ∀ m, P.coeff m ≠ 0 → (P.coeff m).natDegree + m ≤ T :=
  fun m hm => (hP m hm).trans hST

lemma infra_TD_zero (T : ℕ) :
    ∀ m, (0 : Polynomial (Polynomial F)).coeff m ≠ 0 →
      ((0 : Polynomial (Polynomial F)).coeff m).natDegree + m ≤ T := by
  intro m hm; simp at hm

lemma infra_TD_add {P Q : Polynomial (Polynomial F)} {T : ℕ}
    (hP : ∀ m, P.coeff m ≠ 0 → (P.coeff m).natDegree + m ≤ T)
    (hQ : ∀ m, Q.coeff m ≠ 0 → (Q.coeff m).natDegree + m ≤ T) :
    ∀ m, (P + Q).coeff m ≠ 0 → ((P + Q).coeff m).natDegree + m ≤ T := by
  intro m hm
  rw [coeff_add] at hm ⊢
  by_cases h1 : P.coeff m = 0
  · rw [h1, zero_add] at hm ⊢; exact hQ m hm
  by_cases h2 : Q.coeff m = 0
  · rw [h2, add_zero] at hm ⊢; exact hP m hm
  have := natDegree_add_le (P.coeff m) (Q.coeff m)
  have := hP m h1
  have := hQ m h2
  omega

lemma infra_TD_mul {P Q : Polynomial (Polynomial F)} {S T : ℕ}
    (hP : ∀ m, P.coeff m ≠ 0 → (P.coeff m).natDegree + m ≤ S)
    (hQ : ∀ m, Q.coeff m ≠ 0 → (Q.coeff m).natDegree + m ≤ T) :
    ∀ m, (P * Q).coeff m ≠ 0 → ((P * Q).coeff m).natDegree + m ≤ S + T := by
  intro m hm
  rw [coeff_mul] at hm ⊢
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hm' : m ≤ S + T := by
    have a1 := hP x.1 (left_ne_zero_of_mul hx0)
    have a2 := hQ x.2 (right_ne_zero_of_mul hx0)
    omega
  have : (∑ y ∈ Finset.HasAntidiagonal.antidiagonal m, P.coeff y.1 * Q.coeff y.2).natDegree ≤ S + T - m := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun y hy => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy
    by_cases hy0 : P.coeff y.1 * Q.coeff y.2 = 0
    · rw [hy0, natDegree_zero]; exact Nat.zero_le _
    · have a1 := hP y.1 (left_ne_zero_of_mul hy0)
      have a2 := hQ y.2 (right_ne_zero_of_mul hy0)
      have := natDegree_mul_le (p := P.coeff y.1) (q := Q.coeff y.2)
      omega
  omega

lemma infra_TD_one :
    ∀ m, (1 : Polynomial (Polynomial F)).coeff m ≠ 0 →
      ((1 : Polynomial (Polynomial F)).coeff m).natDegree + m ≤ 0 := by
  intro m hm
  rw [coeff_one] at hm ⊢
  split_ifs at hm ⊢ with h
  · subst h; simp
  · exact absurd rfl hm

lemma infra_TD_CC (c : F) :
    ∀ m, (C (C c) : Polynomial (Polynomial F)).coeff m ≠ 0 →
      ((C (C c) : Polynomial (Polynomial F)).coeff m).natDegree + m ≤ 0 := by
  intro m hm
  rw [coeff_C] at hm ⊢
  split_ifs at hm ⊢ with h
  · subst h; simp
  · exact absurd rfl hm

lemma infra_TD_CX :
    ∀ m, (C X : Polynomial (Polynomial F)).coeff m ≠ 0 →
      ((C X : Polynomial (Polynomial F)).coeff m).natDegree + m ≤ 1 := by
  intro m hm
  rw [coeff_C] at hm ⊢
  split_ifs at hm ⊢ with h
  · subst h; simp
  · exact absurd rfl hm

lemma infra_TD_X :
    ∀ m, (X : Polynomial (Polynomial F)).coeff m ≠ 0 →
      ((X : Polynomial (Polynomial F)).coeff m).natDegree + m ≤ 1 := by
  intro m hm
  rw [coeff_X] at hm ⊢
  split_ifs at hm ⊢ with h
  · subst h; simp
  · exact absurd rfl hm

lemma infra_TD_pow {P : Polynomial (Polynomial F)} {T : ℕ}
    (hP : ∀ m, P.coeff m ≠ 0 → (P.coeff m).natDegree + m ≤ T) (n : ℕ) :
    ∀ m, (P ^ n).coeff m ≠ 0 → ((P ^ n).coeff m).natDegree + m ≤ n * T := by
  induction n with
  | zero => simp only [pow_zero, zero_mul]; exact infra_TD_one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact infra_TD_mul ih hP

lemma infra_TD_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial F)) (d : ι → ℕ)
    (h : ∀ i ∈ s, ∀ m, (f i).coeff m ≠ 0 → ((f i).coeff m).natDegree + m ≤ d i) :
    ∀ m, (∏ i ∈ s, f i).coeff m ≠ 0 → ((∏ i ∈ s, f i).coeff m).natDegree + m ≤ ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using infra_TD_one (F := F)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact infra_TD_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma infra_TD_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial F)) (T : ℕ)
    (h : ∀ i ∈ s, ∀ m, (f i).coeff m ≠ 0 → ((f i).coeff m).natDegree + m ≤ T) :
    ∀ m, (∑ i ∈ s, f i).coeff m ≠ 0 → ((∑ i ∈ s, f i).coeff m).natDegree + m ≤ T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact infra_TD_zero T
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact infra_TD_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma infra_TD_gen (a b c : F) :
    ∀ m, (C (C a) + C (C b) * C X + C (C c) * X : Polynomial (Polynomial F)).coeff m ≠ 0 →
      ((C (C a) + C (C b) * C X + C (C c) * X : Polynomial (Polynomial F)).coeff m).natDegree + m
        ≤ 1 := by
  refine infra_TD_add (infra_TD_add (infra_TD_mono (infra_TD_CC a) (Nat.zero_le 1)) ?_) ?_
  · simpa using infra_TD_mul (infra_TD_CC b) infra_TD_CX
  · simpa using infra_TD_mul (infra_TD_CC c) infra_TD_X

/-- Total degree is preserved in the form needed by `DLT.lifting`. -/
lemma subst_coeff_natDegree (p₀ α β : Fin 2 → F) (q : MvPolynomial (Fin 2) F) (m : ℕ) :
    ((subst p₀ α β q).coeff m).natDegree + m ≤ q.totalDegree ∨ (subst p₀ α β q).coeff m = 0 := by
  suffices H : ∀ m, (subst p₀ α β q).coeff m ≠ 0 →
      ((subst p₀ α β q).coeff m).natDegree + m ≤ q.totalDegree by
    by_cases h0 : (subst p₀ α β q).coeff m = 0
    · exact Or.inr h0
    · exact Or.inl (H m h0)
  have hq : subst p₀ α β q = ∑ s ∈ q.support,
      subst p₀ α β (MvPolynomial.monomial s (MvPolynomial.coeff s q)) := by
    conv_lhs => rw [q.as_sum]
    rw [map_sum]
  rw [hq]
  refine infra_TD_sum _ _ _ (fun s hs => ?_)
  rw [subst, MvPolynomial.aeval_monomial, Polynomial.algebraMap_apply, Polynomial.algebraMap_eq,
    Finsupp.prod]
  have h1 := infra_TD_prod s.support
    (fun i => (C (C (p₀ i)) + C (C (α i)) * C X + C (C (β i)) * X : Polynomial (Polynomial F)) ^ s i)
    (fun i => s i * 1) (fun i _ => infra_TD_pow (infra_TD_gen _ _ _) (s i))
  have h2 := infra_TD_mul (infra_TD_CC (MvPolynomial.coeff s q)) h1
  refine infra_TD_mono h2 ?_
  simp only [zero_add, mul_one]
  exact MvPolynomial.le_totalDegree hs

/-- The affine coordinate forms of the basis `(α, β)` at origin `p₀`, as polynomials. -/
noncomputable def lamPoly (p₀ α β : Fin 2 → F) : MvPolynomial (Fin 2) F :=
  MvPolynomial.C (det2 α β)⁻¹ * ((MvPolynomial.X 0 - MvPolynomial.C (p₀ 0)) * MvPolynomial.C (β 1) -
    (MvPolynomial.X 1 - MvPolynomial.C (p₀ 1)) * MvPolynomial.C (β 0))

noncomputable def muPoly (p₀ α β : Fin 2 → F) : MvPolynomial (Fin 2) F :=
  MvPolynomial.C (det2 α β)⁻¹ * (MvPolynomial.C (α 0) * (MvPolynomial.X 1 - MvPolynomial.C (p₀ 1)) -
    MvPolynomial.C (α 1) * (MvPolynomial.X 0 - MvPolynomial.C (p₀ 0)))

/-- Inverse of `subst`: `V ↦ lam`, `W ↦ mu`. -/
noncomputable def unsubst (p₀ α β : Fin 2 → F) :
    Polynomial (Polynomial F) →+* MvPolynomial (Fin 2) F :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (lamPoly p₀ α β)) (muPoly p₀ α β)

lemma eval_lamPoly (p₀ α β x : Fin 2 → F) :
    MvPolynomial.eval x (lamPoly p₀ α β) = lam α β (x - p₀) := by
  simp only [lamPoly, lam, det2, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Pi.sub_apply]
  rw [div_eq_inv_mul]

lemma eval_muPoly (p₀ α β x : Fin 2 → F) :
    MvPolynomial.eval x (muPoly p₀ α β) = mu α β (x - p₀) := by
  simp only [muPoly, mu, det2, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Pi.sub_apply]
  rw [div_eq_inv_mul]

lemma infra_unsubst_gen {p₀ α β : Fin 2 → F} (h : det2 α β ≠ 0) (i : Fin 2) :
    unsubst p₀ α β (C (C (p₀ i)) + C (C (α i)) * C X + C (C (β i)) * X) = MvPolynomial.X i := by
  simp only [unsubst, map_add, map_mul, coe_eval₂RingHom, eval₂_C, eval₂_X]
  simp only [lamPoly, muPoly]
  have hd : MvPolynomial.C (det2 α β)⁻¹ * (MvPolynomial.C (α 0) * MvPolynomial.C (β 1) -
      MvPolynomial.C (α 1) * MvPolynomial.C (β 0)) = (1 : MvPolynomial (Fin 2) F) := by
    rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul, ← MvPolynomial.C_sub, ← MvPolynomial.C_mul,
      show (α 0 * β 1 - α 1 * β 0) = det2 α β from rfl, inv_mul_cancel₀ h, MvPolynomial.C_1]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    linear_combination (MvPolynomial.X 0 - MvPolynomial.C (p₀ 0)) * hd
  · simp only [Fin.mk_one, Fin.isValue]
    linear_combination (MvPolynomial.X 1 - MvPolynomial.C (p₀ 1)) * hd

lemma unsubst_subst {p₀ α β : Fin 2 → F} (h : det2 α β ≠ 0) (q : MvPolynomial (Fin 2) F) :
    unsubst p₀ α β (subst p₀ α β q) = q := by
  have : (unsubst p₀ α β).comp (subst p₀ α β).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [subst, unsubst]
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, subst,
        MvPolynomial.aeval_X, RingHom.id_apply]
      exact infra_unsubst_gen h i
  exact congrArg (fun f => f q) this

lemma subst_injective {p₀ α β : Fin 2 → F} (h : det2 α β ≠ 0) :
    Function.Injective (subst p₀ α β) :=
  Function.LeftInverse.injective (g := unsubst p₀ α β) (unsubst_subst h)

lemma eval_unsubst (p₀ α β : Fin 2 → F) (B : Polynomial (Polynomial F)) (x : Fin 2 → F) :
    MvPolynomial.eval x (unsubst p₀ α β B) =
      (B.eval (C (mu α β (x - p₀)))).eval (lam α β (x - p₀)) := by
  induction B using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, eval_add, hp, hq]
  | monomial n c =>
    simp only [unsubst, coe_eval₂RingHom, eval₂_monomial, eval_monomial, map_mul, map_pow,
      eval_mul, eval_pow, eval_C, eval_muPoly]
    congr 1
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval₂_eq_sum_range, map_sum]
    simp only [map_mul, map_pow, MvPolynomial.eval_C, eval_lamPoly]

lemma infra_totalDegree_affine (c a b : F) :
    (MvPolynomial.C c + MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) F).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ((MvPolynomial.totalDegree_add _ _).trans
    (max_le ?_ ?_)) ?_)
  · simp
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp

lemma infra_totalDegree_lamPoly (p₀ α β : Fin 2 → F) : (lamPoly p₀ α β).totalDegree ≤ 1 := by
  have : lamPoly p₀ α β = MvPolynomial.C (-(det2 α β)⁻¹ * (p₀ 0 * β 1 - p₀ 1 * β 0)) +
      MvPolynomial.C ((det2 α β)⁻¹ * β 1) * MvPolynomial.X 0 +
      MvPolynomial.C (-(det2 α β)⁻¹ * β 0) * MvPolynomial.X 1 := by
    simp only [lamPoly, map_mul, map_neg, map_sub]
    ring
  rw [this]
  exact infra_totalDegree_affine _ _ _

lemma infra_totalDegree_muPoly (p₀ α β : Fin 2 → F) : (muPoly p₀ α β).totalDegree ≤ 1 := by
  have : muPoly p₀ α β = MvPolynomial.C (-(det2 α β)⁻¹ * (α 0 * p₀ 1 - α 1 * p₀ 0)) +
      MvPolynomial.C (-(det2 α β)⁻¹ * α 1) * MvPolynomial.X 0 +
      MvPolynomial.C ((det2 α β)⁻¹ * α 0) * MvPolynomial.X 1 := by
    simp only [muPoly, map_mul, map_neg, map_sub]
    ring
  rw [this]
  exact infra_totalDegree_affine _ _ _

lemma infra_totalDegree_eval₂_le (c : Polynomial F) (L : MvPolynomial (Fin 2) F)
    (hL : L.totalDegree ≤ 1) : (c.eval₂ MvPolynomial.C L).totalDegree ≤ c.natDegree := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j hj => ?_)
  rw [Finset.mem_range] at hj
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  have := Nat.mul_le_mul_left j hL
  omega

lemma totalDegree_unsubst (p₀ α β : Fin 2 → F) (B : Polynomial (Polynomial F)) (k : ℕ)
    (h1 : B.natDegree ≤ k) (h2 : ∀ n, (B.coeff n).natDegree ≤ k) :
    (unsubst p₀ α β B).totalDegree ≤ 2 * k := by
  rw [unsubst, coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun n hn => ?_)
  rw [Finset.mem_range] at hn
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have a1 := infra_totalDegree_eval₂_le (B.coeff n) _ (infra_totalDegree_lamPoly p₀ α β)
  have a2 := (MvPolynomial.totalDegree_pow (muPoly p₀ α β) n).trans
    (Nat.mul_le_mul_left n (infra_totalDegree_muPoly p₀ α β))
  have a3 := h2 n
  rw [coe_eval₂RingHom]
  omega

/-- `subst ∘ unsubst`: the substitution `V ↦ lam(p₀' + V' α' + W' β' - p₀)`,
`W ↦ mu(…)`, written with the inner variable `V' = C X` and outer `W' = X`. -/
lemma subst_unsubst (p₀ α β p₀' α' β' : Fin 2 → F) (B : Polynomial (Polynomial F)) :
    subst p₀' α' β' (unsubst p₀ α β B) =
      B.eval₂ (Polynomial.eval₂RingHom (C.comp C)
          (C (C (lam α β (p₀' - p₀))) + C (C (lam α β α')) * C X + C (C (lam α β β')) * X))
        (C (C (mu α β (p₀' - p₀))) + C (C (mu α β α')) * C X + C (C (mu α β β')) * X) := by
  have : (subst p₀' α' β').toRingHom.comp (unsubst p₀ α β) =
      Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (C.comp C)
          (C (C (lam α β (p₀' - p₀))) + C (C (lam α β α')) * C X + C (C (lam α β β')) * X))
        (C (C (mu α β (p₀' - p₀))) + C (C (mu α β α')) * C X + C (C (mu α β β')) * X) := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' ?_ ?_) ?_
    · ext c
      simp [unsubst, subst]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, unsubst,
        coe_eval₂RingHom, eval₂_C, eval₂_X]
      simp only [lamPoly, subst, lam, det2, map_mul, map_sub, MvPolynomial.aeval_C,
        MvPolynomial.aeval_X, Polynomial.algebraMap_apply, Polynomial.algebraMap_eq, Pi.sub_apply,
        div_eq_mul_inv]
      ring
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, unsubst,
        coe_eval₂RingHom, eval₂_X]
      simp only [muPoly, subst, mu, det2, map_mul, map_sub, MvPolynomial.aeval_C,
        MvPolynomial.aeval_X, Polynomial.algebraMap_apply, Polynomial.algebraMap_eq, Pi.sub_apply,
        div_eq_mul_inv]
      ring
  exact congrArg (fun f => f B) this

end Infra
end DLT

end Part7

section Part8
open Polynomial

namespace DLT

section Min
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `Q` vanishes (with `Z = G^n`) on every line `(j, b)` of `L2`. -/
def VanishOn {r : ℕ} (w v : Fin r → Fin 2 → F) (G : Fin r → F → Polynomial F)
    (L2 : Finset (Fin r × F)) (n : ℕ) (Q : Polynomial (MvPolynomial (Fin 2) F)) : Prop :=
  ∀ jb ∈ L2, restrictLine (jb.2 • w jb.1) (v jb.1) ((G jb.1 jb.2) ^ n) Q = 0

/-- A restriction to a line of degree `≤ D` vanishing at more than `D` points of the line is zero. -/
lemma restrict_eq_zero_of_many {r : ℕ} (w v : Fin r → Fin 2 → F)
    (hwv : ∀ i, det2 (w i) (v i) ≠ 0) (j : Fin r) (b : F) (g : Polynomial F) (D : ℕ)
    (R : Polynomial (MvPolynomial (Fin 2) F)) (hdeg : (restrictLine (b • w j) (v j) g R).natDegree ≤ D)
    (Pts : Finset (Fin 2 → F)) (hon : ∀ x ∈ Pts, lam (w j) (v j) x = b)
    (hzero : ∀ x ∈ Pts, ptEval R x (g.eval (mu (w j) (v j) x)) = 0) (hcard : D < Pts.card) :
    restrictLine (b • w j) (v j) g R = 0 := by
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (Pts.image (mu (w j) (v j)))
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    rw [restrictLine_eval]
    have hx' : b • w j + mu (w j) (v j) x • v j = x := by
      rw [← hon x hx]; exact (decomp (hwv j) x).symm
    rw [hx']
    exact hzero x hx
  · rw [Finset.card_image_of_injOn]
    · omega
    · intro x hx y hy hxy
      rw [decomp (hwv j) x, decomp (hwv j) y, hon x hx, hon y hy]
      rw [hxy]

open Classical in
theorem minimal_Q (p : ℕ) [hp : Fact p.Prime] [CharP F p] {r : ℕ} (w v : Fin r → Fin 2 → F)
    (hwv : ∀ i, det2 (w i) (v i) ≠ 0) (G : Fin r → F → Polynomial F) (k : ℕ)
    (hG : ∀ i a, (G i a).natDegree ≤ k) (f : (Fin 2 → F) → F) (K D : ℕ) (hkK : k ≤ K)
    (P2 : Finset (Fin 2 → F)) (L2 : Finset (Fin r × F)) (Inc : (Fin 2 → F) → Fin r → Prop)
    (hInc : ∀ x j, Inc x j → x ∈ P2 ∧ (j, lam (w j) (v j) x) ∈ L2 ∧
      (G j (lam (w j) (v j) x)).eval (mu (w j) (v j) x) = f x)
    (hP2 : ∀ x ∈ P2, ∃ j, Inc x j)
    (hL2 : ∀ jb ∈ L2, D < (Finset.univ.filter fun x =>
      lam (w jb.1) (v jb.1) x = jb.2 ∧ Inc x jb.1).card)
    (hSZ : D * Fintype.card F < P2.card)
    (Q₀ : Polynomial (MvPolynomial (Fin 2) F)) (hQ₀ : Q₀ ≠ 0) (hW : WDeg K D Q₀)
    (hV : VanishOn w v G L2 1 Q₀) :
    ∃ (e : ℕ) (Q : Polynomial (MvPolynomial (Fin 2) F)), Q ≠ 0 ∧ WDeg (p ^ e * K) D Q ∧
      VanishOn w v G L2 (p ^ e) Q ∧ 1 ≤ Q.natDegree ∧
      ∃ x ∈ P2, ptEval (derivative Q) x (f x ^ p ^ e) ≠ 0 := by
  -- the family
  let Fam : ℕ → Prop := fun d => ∃ (e : ℕ) (Q : Polynomial (MvPolynomial (Fin 2) F)), Q ≠ 0 ∧
    WDeg (p ^ e * K) D Q ∧ VanishOn w v G L2 (p ^ e) Q ∧ Q.natDegree = d
  have hex : ∃ d, Fam d := ⟨_, 0, Q₀, hQ₀, by simpa using hW, by simpa using hV, rfl⟩
  obtain ⟨e, Q, hQ0, hQW, hQV, hQd⟩ := Nat.find_spec hex
  have hmin : ∀ d, Fam d → Nat.find hex ≤ d := fun d hd => Nat.find_min' hex hd
  -- degree of the Z-root polynomial
  have hgdeg : ∀ e' j b, ((G j b) ^ p ^ e').natDegree ≤ p ^ e' * K := by
    intro e' j b
    refine (natDegree_pow_le).trans ?_
    exact Nat.mul_le_mul_left _ ((hG j b).trans hkK)
  -- Claim A: no member of the family has Z-degree 0
  have hA : ∀ (e' : ℕ) (Q' : Polynomial (MvPolynomial (Fin 2) F)), Q' ≠ 0 →
      WDeg (p ^ e' * K) D Q' → VanishOn w v G L2 (p ^ e') Q' → Q'.natDegree ≠ 0 := by
    intro e' Q' hQ'0 hQ'W hQ'V hd0
    rw [natDegree_eq_zero] at hd0
    obtain ⟨q', rfl⟩ := hd0
    have hq'0 : q' ≠ 0 := by rintro rfl; exact hQ'0 (by simp)
    have hq'deg : q'.totalDegree ≤ D := by
      have := totalDegree_coeff_le_of_WDeg hQ'W 0
      simpa using this
    -- q' vanishes on P2
    have hvan : ∀ x ∈ P2, MvPolynomial.eval x q' = 0 := by
      intro x hx
      obtain ⟨j, hj⟩ := hP2 x hx
      obtain ⟨-, hjL, -⟩ := hInc x j hj
      have h0 := hQ'V _ hjL
      simp only at h0
      have h1 := congrArg (Polynomial.eval (mu (w j) (v j) x)) h0
      rw [restrictLine_eval, eval_zero] at h1
      rw [← decomp (hwv j) x] at h1
      simpa [ptEval] using h1
    -- Schwartz–Zippel
    have hsz := MvPolynomial.schwartz_zippel_totalDegree hq'0 (Finset.univ : Finset F)
    have hsub : P2 ⊆ (Finset.filter (fun f => MvPolynomial.eval f q' = 0)
        (Fintype.piFinset fun _ ↦ (Finset.univ : Finset F))) := by
      intro x hx
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ, implies_true,
        true_and]
      exact hvan x hx
    have hc := Finset.card_le_card hsub
    have hq : (0 : ℚ≥0) < (Finset.univ : Finset F).card := by
      exact_mod_cast Finset.card_pos.mpr Finset.univ_nonempty
    rw [div_le_div_iff₀ (by positivity) hq] at hsz
    have h2 : ((P2.card : ℚ≥0)) * (Finset.univ : Finset F).card ≤
        (q'.totalDegree : ℚ≥0) * (Finset.univ : Finset F).card ^ 2 := by
      calc ((P2.card : ℚ≥0)) * (Finset.univ : Finset F).card
          ≤ ((Finset.filter (fun f => MvPolynomial.eval f q' = 0)
              (Fintype.piFinset fun _ ↦ (Finset.univ : Finset F))).card : ℚ≥0) *
                (Finset.univ : Finset F).card := by
            gcongr
        _ ≤ _ := hsz
    have h3 : (P2.card : ℚ≥0) ≤ (q'.totalDegree : ℚ≥0) * (Finset.univ : Finset F).card := by
      have := h2
      rw [sq, ← mul_assoc] at this
      exact le_of_mul_le_mul_right this hq
    have h4 : P2.card ≤ D * Fintype.card F := by
      have : (P2.card : ℚ≥0) ≤ (D : ℚ≥0) * Fintype.card F := by
        calc (P2.card : ℚ≥0) ≤ (q'.totalDegree : ℚ≥0) * (Finset.univ : Finset F).card := h3
          _ ≤ (D : ℚ≥0) * Fintype.card F := by
            rw [Finset.card_univ]; gcongr
      exact_mod_cast this
    omega
  have hQd1 : 1 ≤ Q.natDegree := Nat.one_le_iff_ne_zero.mpr (hA e Q hQ0 hQW hQV)
  -- Claim B: the derivative is nonzero
  have hB : derivative Q ≠ 0 := by
    intro hder
    have hpne : p ≠ 0 := hp.out.ne_zero
    have hexp := expand_contract p hder hpne
    set Q' := contract p Q with hQ'
    have hQ'0 : Q' ≠ 0 := by
      intro h; apply hQ0; rw [← hexp, h, map_zero]
    have hQ'W : WDeg (p ^ (e + 1) * K) D Q' := by
      have := WDeg_of_expand (p := p) (Q := Q') (K := p ^ e * K) (D := D) hp.out.pos (by rw [hexp]; exact hQW)
      rwa [← mul_assoc, ← pow_succ'] at this
    have hQ'V : VanishOn w v G L2 (p ^ (e + 1)) Q' := by
      intro jb hjb
      rw [pow_succ, pow_mul, ← restrictLine_expand, hexp]
      exact hQV jb hjb
    have hlt : Q'.natDegree < Q.natDegree := by
      have h1 : Q.natDegree = Q'.natDegree * p := by
        conv_lhs => rw [← hexp]
        rw [natDegree_expand]
      have hp2 : 2 ≤ p := hp.out.two_le
      have : Q'.natDegree ≠ 0 := by
        intro h0; rw [h0, zero_mul] at h1; omega
      rw [h1]
      calc Q'.natDegree = Q'.natDegree * 1 := (mul_one _).symm
        _ < Q'.natDegree * p := Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pos_of_ne_zero this)
    have := hmin _ ⟨e + 1, Q', hQ'0, hQ'W, hQ'V, rfl⟩
    omega
  refine ⟨e, Q, hQ0, hQW, hQV, hQd1, ?_⟩
  -- Claim C
  by_contra hC
  push_neg at hC
  have hDW : WDeg (p ^ e * K) D (derivative Q) := WDeg_derivative hQW
  have hDV : VanishOn w v G L2 (p ^ e) (derivative Q) := by
    intro jb hjb
    apply restrict_eq_zero_of_many w v hwv jb.1 jb.2 _ D _
      (restrictLine_natDegree_le _ _ _ _ _ _ hDW (hgdeg e jb.1 jb.2))
      (Finset.univ.filter fun x => lam (w jb.1) (v jb.1) x = jb.2 ∧ Inc x jb.1)
    · intro x hx; exact (Finset.mem_filter.mp hx).2.1
    · intro x hx
      obtain ⟨-, hxl, hxi⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxP, -, hacc⟩ := hInc x jb.1 hxi
      rw [eval_pow, ← hxl, hacc]
      exact hC x hxP
    · exact hL2 jb hjb
  have hlt : (derivative Q).natDegree < Q.natDegree :=
    natDegree_derivative_lt (by omega)
  have := hmin _ ⟨e, derivative Q, hB, hDW, hDV, rfl⟩
  omega

end Min
end DLT

end Part8

section Part9
open Polynomial

namespace DLT

section Sigma
variable {F : Type*} [Field F]

/-- `V ↦ s`, `W ↦ c₀ s + c₁ t` on `F[V][W] → F[s][t]`. -/
noncomputable def sig1 (c₀ c₁ : F) : Polynomial (Polynomial F) →+* Polynomial (Polynomial F) :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom ((C : Polynomial F →+* Polynomial (Polynomial F)).comp C) (C X))
    (C (C c₀) * C X + C (C c₁) * X)

/-- `V ↦ t`, `W ↦ d₀ s + d₁ t` on `F[V][W] → F[s][t]`. -/
noncomputable def sig2 (d₀ d₁ : F) : Polynomial (Polynomial F) →+* Polynomial (Polynomial F) :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom ((C : Polynomial F →+* Polynomial (Polynomial F)).comp C) X)
    (C (C d₀) * C X + C (C d₁) * X)

lemma eval₂RingHom_CC_CX :
    Polynomial.eval₂RingHom ((C : Polynomial F →+* Polynomial (Polynomial F)).comp C) (C X) =
      (C : Polynomial F →+* Polynomial (Polynomial F)) := by
  apply Polynomial.ringHom_ext <;> simp

lemma eval₂RingHom_CC_X :
    Polynomial.eval₂RingHom ((C : Polynomial F →+* Polynomial (Polynomial F)).comp C) X =
      Polynomial.mapRingHom (C : F →+* Polynomial F) := by
  apply Polynomial.ringHom_ext <;> simp

lemma sig1_eq_comp (c₀ c₁ : F) (B : Polynomial (Polynomial F)) :
    sig1 c₀ c₁ B = B.comp (C (C c₀) * C X + C (C c₁) * X) := by
  simp only [sig1, coe_eval₂RingHom, eval₂RingHom_CC_CX, comp]

lemma sig1_C (c₀ c₁ : F) (p : Polynomial F) : sig1 c₀ c₁ (C p) = C p := by
  rw [sig1_eq_comp, C_comp]

lemma sig2_C (d₀ d₁ : F) (p : Polynomial F) : sig2 d₀ d₁ (C p) = p.map C := by
  simp only [sig2, coe_eval₂RingHom, eval₂_C, eval₂RingHom_CC_X, coe_mapRingHom]

lemma sig1_natDegree_le (c₀ c₁ : F) (B : Polynomial (Polynomial F)) :
    (sig1 c₀ c₁ B).natDegree ≤ B.natDegree := by
  rw [sig1_eq_comp]
  refine natDegree_comp_le.trans ?_
  have : (C (C c₀) * C X + C (C c₁) * X : Polynomial (Polynomial F)).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [← C_mul, natDegree_C]; omega
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  calc B.natDegree * _ ≤ B.natDegree * 1 := Nat.mul_le_mul_left _ this
    _ = B.natDegree := mul_one _

lemma sig1_map_eval (c₀ c₁ : F) (a : F) (B : Polynomial (Polynomial F)) :
    (sig1 c₀ c₁ B).map (evalRingHom a) =
      (B.map (evalRingHom a)).comp (C (c₀ * a) + C c₁ * X) := by
  have h : (Polynomial.mapRingHom (evalRingHom a)).comp (sig1 c₀ c₁) =
      (Polynomial.compRingHom (C (c₀ * a) + C c₁ * X)).comp
        (Polynomial.mapRingHom (evalRingHom a)) := by
    apply Polynomial.ringHom_ext
    · intro p; simp [sig1_C]
    · simp [sig1_eq_comp, C_mul]
  exact congrArg (fun φ => φ B) h

lemma sig2_eval_C (d₀ d₁ : F) (b : F) (B : Polynomial (Polynomial F)) :
    (sig2 d₀ d₁ B).eval (C b) = (B.map (evalRingHom b)).comp (C d₀ * X + C (d₁ * b)) := by
  have h : (Polynomial.evalRingHom (C b)).comp (sig2 d₀ d₁) =
      (Polynomial.compRingHom (C d₀ * X + C (d₁ * b))).comp
        (Polynomial.mapRingHom (evalRingHom b)) := by
    apply Polynomial.ringHom_ext
    · intro p
      simp only [RingHom.coe_comp, Function.comp_apply, sig2_C, coe_evalRingHom, eval_map,
        coe_compRingHom, coe_mapRingHom, Polynomial.map_C, C_comp]
      rw [eval₂_hom]
    · simp only [RingHom.coe_comp, Function.comp_apply, sig2, coe_eval₂RingHom, eval₂_X,
        coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, coe_compRingHom, coe_mapRingHom,
        Polynomial.map_X, X_comp, C_mul]
  exact congrArg (fun φ => φ B) h

lemma swap_sig2 (d₀ d₁ : F) (B : Polynomial (Polynomial F)) :
    Bivariate.swap (sig2 d₀ d₁ B) = sig1 d₁ d₀ B := by
  have h : ((Bivariate.swap (R := F)).toRingHom).comp (sig2 d₀ d₁) = sig1 d₁ d₀ := by
    apply Polynomial.ringHom_ext
    · intro p
      change Bivariate.swap (sig2 d₀ d₁ (C p)) = sig1 d₁ d₀ (C p)
      rw [sig2_C, sig1_C, ← Bivariate.swap_C, Bivariate.swap_swap_apply]
    · change Bivariate.swap (sig2 d₀ d₁ X) = sig1 d₁ d₀ X
      simp only [sig2, coe_eval₂RingHom, eval₂_X, map_add, map_mul, Bivariate.swap_C_C,
        Bivariate.swap_X, Bivariate.swap_Y, sig1_eq_comp, X_comp]
      rw [add_comm]
  exact congrArg (fun φ => φ B) h

lemma sig2_coeff_natDegree_le (d₀ d₁ : F) (B : Polynomial (Polynomial F)) (n : ℕ) :
    ((sig2 d₀ d₁ B).coeff n).natDegree ≤ B.natDegree := by
  have := (A2.sdeg_iff (sig2 d₀ d₁ B) B.natDegree).mpr (by
    rw [swap_sig2]; exact sig1_natDegree_le _ _ _)
  exact this n

end Sigma
end DLT

end Part9

section Part10
open Polynomial

namespace DLT.L2

lemma ev_row {F : Type*} [Field F] (P : Polynomial (Polynomial F)) (s t : F) :
    (P.map (evalRingHom s)).eval t = (P.eval (C t)).eval s := by
  rw [eval_map]
  have h := eval₂_at_apply (p := P) (evalRingHom s) (C t)
  rw [coe_evalRingHom, eval_C] at h
  exact h

lemma eq_of_eval_eq {F : Type*} [Field F] [Fintype F] (p r : Polynomial F) (d : ℕ)
    (hp : p.natDegree ≤ d) (hr : r.natDegree ≤ d) (hd : d < Fintype.card F)
    (h : ∀ x, p.eval x = r.eval x) : p = r := by
  classical
  by_contra hne
  have h0 : p - r ≠ 0 := sub_ne_zero.mpr hne
  have h1 := A2.card_le_of_eval_eq_zero (p - r) h0 Finset.univ (fun x _ => by simp [h x])
  have h2 := natDegree_sub_le p r
  rw [Finset.card_univ] at h1
  omega

lemma card_agree {F : Type*} [Field F] [Fintype F] [DecidableEq F] (p r : Polynomial F) (k : ℕ)
    (hp : p.natDegree ≤ k) (hr : r.natDegree ≤ k) (hne : p ≠ r) :
    (Finset.univ.filter fun x => p.eval x = r.eval x).card ≤ k := by
  have h0 : p - r ≠ 0 := sub_ne_zero.mpr hne
  have h1 := A2.card_le_of_eval_eq_zero (p - r) h0 (Finset.univ.filter fun x => p.eval x = r.eval x)
    (fun x hx => by rw [Finset.mem_filter] at hx; simp [hx.2])
  have h2 := natDegree_sub_le p r
  omega

lemma card_zero_rows {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (E : Polynomial (Polynomial F)) (hE : E ≠ 0) (m : ℕ)
    (hEs : ∀ n, (E.coeff n).natDegree ≤ m) :
    (Finset.univ.filter fun s => E.map (evalRingHom s) = 0).card ≤ m := by
  obtain ⟨n, hn⟩ : ∃ n, E.coeff n ≠ 0 := by
    by_contra h
    push Not at h
    exact hE (Polynomial.ext (fun n => by rw [h n, coeff_zero]))
  have := A2.card_le_of_eval_eq_zero (E.coeff n) hn
    (Finset.univ.filter fun s => E.map (evalRingHom s) = 0) (fun s hs => by
    rw [Finset.mem_filter] at hs
    have := congrArg (fun p => p.coeff n) hs.2
    simpa [coeff_map] using this)
  exact this.trans (hEs n)

lemma deg_of_rows {F : Type*} [Field F] (P : Polynomial (Polynomial F)) (D k : ℕ)
    (hPs : ∀ n, (P.coeff n).natDegree ≤ D) (G : Finset F) (hG : D < G.card)
    (f : F → Polynomial F) (hf : ∀ s ∈ G, (f s).natDegree ≤ k)
    (hrow : ∀ s ∈ G, P.map (evalRingHom s) = f s) : P.natDegree ≤ k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_contra h
  have := A2.card_le_of_eval_eq_zero (P.coeff n) h G (fun s hs => by
    have := congrArg (fun p => p.coeff n) (hrow s hs)
    simp only [coeff_map, coe_evalRingHom] at this
    rw [this]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hf s hs) hn))
  have := hPs n
  omega

lemma locator {F : Type*} [Field F] [Fintype F] [DecidableEq F] (m : ℕ) (B : Finset (F × F))
    (hB : B.card < (m + 1) * (m + 1)) :
    ∃ E : Polynomial (Polynomial F), E ≠ 0 ∧ E.natDegree ≤ m ∧ (∀ n, (E.coeff n).natDegree ≤ m) ∧
      ∀ st ∈ B, (E.eval (C st.2)).eval st.1 = 0 := by
  let M : Matrix B (Fin (m + 1) × Fin (m + 1)) F :=
    fun b ij => b.1.1 ^ (ij.1 : ℕ) * b.1.2 ^ (ij.2 : ℕ)
  have hker : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    exact hB
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc
  let E : Polynomial (Polynomial F) :=
    ∑ ij : Fin (m + 1) × Fin (m + 1), C (C (c ij) * X ^ (ij.1 : ℕ)) * X ^ (ij.2 : ℕ)
  have hcoeff : ∀ n, E.coeff n =
      ∑ ij : Fin (m + 1) × Fin (m + 1), if n = (ij.2 : ℕ) then C (c ij) * X ^ (ij.1 : ℕ) else 0 := by
    intro n
    simp only [E, finsetSum_coeff, coeff_C_mul_X_pow]
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ij0, hij0⟩ := Function.ne_iff.mp hc0
    intro hE
    have h1 := congrArg (fun p => p.coeff (ij0.1 : ℕ)) (hcoeff (ij0.2 : ℕ))
    simp only [hE, coeff_zero, finsetSum_coeff] at h1
    rw [Finset.sum_eq_single ij0] at h1
    · simp at h1
      exact hij0 h1.symm
    · intro ij _ hne
      split_ifs with h
      · rw [coeff_C_mul_X_pow, if_neg]
        intro h'
        exact hne (Prod.ext (Fin.ext h'.symm) (Fin.ext h.symm))
      · rfl
    · simp
  · refine natDegree_sum_le_of_forall_le _ _ (fun ij _ => ?_)
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp ij.2.2)
  · intro n
    rw [hcoeff]
    refine natDegree_sum_le_of_forall_le _ _ (fun ij _ => ?_)
    split_ifs
    · exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp ij.1.2)
    · simp
  · intro st hst
    have h1 := congrFun hc ⟨st, hst⟩
    simp only [Matrix.mulVec, dotProduct, M, Pi.zero_apply] at h1
    simp only [E, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [← h1]
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    ring

end DLT.L2

namespace DLT

/-- Low-error bivariate test along two axis-parallel directions. `F[s][t]`: inner `s`, outer `t`;
`(P.eval (C t)).eval s = P(s,t)`. Row `s` carries `R s ∈ F[t]`, column `t` carries `Col t ∈ F[s]`. -/
theorem le_axis {F : Type*} [Field F] [Fintype F] [DecidableEq F] (k : ℕ) (η : ℝ)
    (hη : η ≤ 1 / 2048) (hq : 64 * (k + 1) ≤ Fintype.card F)
    (R Col : F → Polynomial F) (hR : ∀ s, (R s).natDegree ≤ k) (hC : ∀ t, (Col t).natDegree ≤ k)
    (g : F → F → F)
    (herrR : ((Finset.univ.filter fun st : F × F => (R st.1).eval st.2 ≠ g st.1 st.2).card : ℝ) ≤
      η * (Fintype.card F : ℝ) ^ 2)
    (herrC : ((Finset.univ.filter fun st : F × F => (Col st.2).eval st.1 ≠ g st.1 st.2).card : ℝ) ≤
      η * (Fintype.card F : ℝ) ^ 2) :
    ∃ P : Polynomial (Polynomial F), P.natDegree ≤ k ∧ (∀ n, (P.coeff n).natDegree ≤ k) ∧
      ((Finset.univ.filter fun st : F × F => (P.eval (C st.2)).eval st.1 ≠ g st.1 st.2).card : ℝ) ≤
        5 * η * (Fintype.card F : ℝ) ^ 2 := by
  classical
  set q := Fintype.card F with hqdef
  set errR := Finset.univ.filter fun st : F × F => (R st.1).eval st.2 ≠ g st.1 st.2 with herrRdef
  set errC := Finset.univ.filter fun st : F × F => (Col st.2).eval st.1 ≠ g st.1 st.2 with herrCdef
  set B := Finset.univ.filter fun st : F × F => (R st.1).eval st.2 ≠ (Col st.2).eval st.1 with hBdef
  have hBsub : B ⊆ errR ∪ errC := by
    intro st hst
    simp only [B, errR, errC, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
      at hst ⊢
    by_contra h
    push Not at h
    exact hst (h.1.trans h.2.symm)
  have hBcard : (B.card : ℝ) ≤ 2 * η * (q : ℝ) ^ 2 := by
    have h1 := (Finset.card_le_card hBsub).trans (Finset.card_union_le _ _)
    have h2 : (B.card : ℝ) ≤ errR.card + errC.card := by exact_mod_cast h1
    linarith
  set m := Nat.sqrt B.card with hmdef
  have hmB : m * m ≤ B.card := by have := Nat.sqrt_le' B.card; rw [sq] at this; exact this
  have hBm : B.card < (m + 1) * (m + 1) := by
    have := Nat.lt_succ_sqrt' B.card; rw [sq] at this; exact this
  have hm32 : 32 * m ≤ q := by
    have h1 : ((m * m : ℕ) : ℝ) ≤ (q : ℝ) ^ 2 / 1024 := by
      have : ((m * m : ℕ) : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hmB
      nlinarith [sq_nonneg (q : ℝ)]
    have h2 : (32 * m) * (32 * m) ≤ q * q := by
      have : (((32 * m) * (32 * m) : ℕ) : ℝ) ≤ ((q * q : ℕ) : ℝ) := by
        push_cast at h1 ⊢; nlinarith
      exact_mod_cast this
    exact Nat.mul_self_le_mul_self_iff.mp h2
  have hd : m + k < q := by omega
  have hswap0 : ∀ P : Polynomial (Polynomial F), P ≠ 0 → Bivariate.swap P ≠ 0 := fun P hP h0 =>
    hP ((map_eq_zero_iff _ (Bivariate.swap (R := F)).injective).mp h0)
  obtain ⟨E, hE0, hEt, hEs, hEB⟩ := L2.locator m B hBm
  have hEsw : (Bivariate.swap E).natDegree ≤ m := (A2.sdeg_iff E m).mp hEs
  have hEcol : ∀ t, (E.eval (C t)).natDegree ≤ m := fun t => by
    rw [← A2.swap_map_eval]; exact natDegree_map_le.trans hEsw
  have hΨ : ∀ s t, (E.eval (C t)).eval s * (R s).eval t = (E.eval (C t)).eval s * (Col t).eval s := by
    intro s t
    by_cases h : (s, t) ∈ B
    · have := hEB _ h
      simp only at this
      rw [this, zero_mul, zero_mul]
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h
      rw [h]
  obtain ⟨N, hNt, hNs, hN⟩ := rows_cols_poly (m + k) hd
    (fun s t => (E.eval (C t)).eval s * (R s).eval t)
    (fun s => ⟨E.map (evalRingHom s) * R s,
      natDegree_mul_le.trans (add_le_add (natDegree_map_le.trans hEt) (hR s)),
      fun t => by rw [eval_mul, L2.ev_row]⟩)
    (fun t => ⟨E.eval (C t) * Col t,
      natDegree_mul_le.trans (add_le_add (hEcol t) (hC t)),
      fun s => by rw [eval_mul, hΨ]⟩)
  have hNsw : (Bivariate.swap N).natDegree ≤ m + k := (A2.sdeg_iff N _).mp hNs
  have hrowN : ∀ s, N.map (evalRingHom s) = E.map (evalRingHom s) * R s := fun s =>
    L2.eq_of_eval_eq _ _ (m + k) (natDegree_map_le.trans hNt)
      (natDegree_mul_le.trans (add_le_add (natDegree_map_le.trans hEt) (hR s))) hd
      (fun t => by rw [L2.ev_row, hN, eval_mul, L2.ev_row])
  have hcolN : ∀ t, N.eval (C t) = E.eval (C t) * Col t := fun t =>
    L2.eq_of_eval_eq _ _ (m + k)
      (by rw [← A2.swap_map_eval]; exact natDegree_map_le.trans hNsw)
      (natDegree_mul_le.trans (add_le_add (hEcol t) (hC t))) hd
      (fun s => by rw [hN, eval_mul, hΨ])
  have hdvd : E ∣ N := ps_dvd (m + k) E N hE0 (by omega) hNt (fun n => (hEs n).trans (by omega))
    hNs Finset.univ Finset.univ (fun s _ => ⟨R s, hrowN s⟩) (fun t _ => ⟨Col t, hcolN t⟩)
    (by rw [Finset.card_univ]; omega) (by rw [Finset.card_univ]; omega)
  obtain ⟨P, hP⟩ := hdvd
  have hProw : ∀ s, E.map (evalRingHom s) ≠ 0 → P.map (evalRingHom s) = R s := by
    intro s hs
    apply mul_left_cancel₀ hs
    rw [← Polynomial.map_mul, ← hP, hrowN]
  have hPcol : ∀ t, E.eval (C t) ≠ 0 → P.eval (C t) = Col t := by
    intro t ht
    apply mul_left_cancel₀ ht
    rw [← eval_mul, ← hP, hcolN]
  have hZr := L2.card_zero_rows E hE0 m hEs
  have hZc : (Finset.univ.filter fun t => E.eval (C t) = 0).card ≤ m := by
    have := L2.card_zero_rows (Bivariate.swap E) (hswap0 E hE0) m
      ((A2.sdeg_iff _ m).mpr (by rw [Bivariate.swap_swap_apply]; exact hEt))
    simpa only [A2.swap_map_eval] using this
  have hPs : ∀ n, (P.coeff n).natDegree ≤ m + k := by
    rcases eq_or_ne P 0 with hP0 | hP0
    · intro n; simp [hP0]
    rw [A2.sdeg_iff]
    have h1 := hNsw
    rw [hP, map_mul, natDegree_mul (hswap0 E hE0) (hswap0 P hP0)] at h1
    omega
  have hGcard : m + k < (Finset.univ.filter fun s => ¬ (E.map (evalRingHom s) = 0)).card := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun s => E.map (evalRingHom s) = 0)
    rw [Finset.card_univ] at this
    omega
  have hGccard : m + k < (Finset.univ.filter fun t => ¬ (E.eval (C t) = 0)).card := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun t => E.eval (C t) = 0)
    rw [Finset.card_univ] at this
    omega
  have hPt : P.natDegree ≤ k := L2.deg_of_rows P (m + k) k hPs _ hGcard R (fun s _ => hR s)
    (fun s hs => hProw s (by simpa using hs))
  have hPs' : ∀ n, (P.coeff n).natDegree ≤ k := by
    rw [A2.sdeg_iff]
    refine L2.deg_of_rows (Bivariate.swap P) (m + k) k
      ((A2.sdeg_iff _ _).mpr (by rw [Bivariate.swap_swap_apply]; omega)) _ hGccard Col
      (fun t _ => hC t) (fun t ht => ?_)
    rw [A2.swap_map_eval]
    exact hPcol t (by simpa using ht)
  refine ⟨P, hPt, hPs', ?_⟩
  set badRows := Finset.univ.filter fun s => P.map (evalRingHom s) ≠ R s with hbrdef
  set badCols := Finset.univ.filter fun t => P.eval (C t) ≠ Col t with hbcdef
  have hbr : badRows.card ≤ m := by
    refine (Finset.card_le_card ?_).trans hZr
    intro s hs
    simp only [badRows, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    by_contra h
    exact hs (hProw s h)
  have hbc : badCols.card ≤ m := by
    refine (Finset.card_le_card ?_).trans hZc
    intro t ht
    simp only [badCols, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    by_contra h
    exact ht (hPcol t h)
  -- each bad row contributes many points of `B`
  have hinner : ∀ s ∈ badRows, q - k - m ≤ (Finset.univ.filter fun t =>
      (P.map (evalRingHom s)).eval t ≠ (R s).eval t ∧ t ∉ badCols).card := by
    intro s hs
    simp only [badRows, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    have hagree := L2.card_agree (P.map (evalRingHom s)) (R s) k
      (natDegree_map_le.trans hPt) (hR s) hs
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun t => (P.map (evalRingHom s)).eval t = (R s).eval t)
    rw [Finset.card_univ] at hsplit
    have hsd := Finset.le_card_sdiff badCols
      (Finset.univ.filter fun t => ¬ (P.map (evalRingHom s)).eval t = (R s).eval t)
    have hsub : (Finset.univ.filter fun t => ¬ (P.map (evalRingHom s)).eval t = (R s).eval t) \
        badCols ⊆ (Finset.univ.filter fun t =>
          (P.map (evalRingHom s)).eval t ≠ (R s).eval t ∧ t ∉ badCols) := by
      intro t ht
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ht
    have := Finset.card_le_card hsub
    omega
  set S := (badRows ×ˢ Finset.univ).filter fun st : F × F =>
    (P.map (evalRingHom st.1)).eval st.2 ≠ (R st.1).eval st.2 ∧ st.2 ∉ badCols with hSdef
  have hSB : S ⊆ B := by
    intro st hst
    simp only [S, B, badCols, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      not_not] at hst ⊢
    obtain ⟨-, h1, h2⟩ := hst
    rw [L2.ev_row, h2] at h1
    exact fun h => h1 h.symm
  have hScard : badRows.card * (q - k - m) ≤ S.card := by
    have h1 : S.card = ∑ s ∈ badRows, (Finset.univ.filter fun t =>
        (P.map (evalRingHom s)).eval t ≠ (R s).eval t ∧ t ∉ badCols).card := by
      rw [hSdef, Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Finset.card_filter]
    rw [h1]
    have := Finset.card_nsmul_le_sum badRows _ _ hinner
    simpa [smul_eq_mul] using this
  have hbB : badRows.card * (q - k - m) ≤ B.card := hScard.trans (Finset.card_le_card hSB)
  have hbq : badRows.card * q ≤ 2 * B.card := by
    calc badRows.card * q ≤ badRows.card * (2 * (q - k - m)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (badRows.card * (q - k - m)) := by ring
      _ ≤ 2 * B.card := by omega
  have hfin : (Finset.univ.filter fun st : F × F => (P.eval (C st.2)).eval st.1 ≠ g st.1 st.2) ⊆
      errR ∪ badRows ×ˢ Finset.univ := by
    intro st hst
    simp only [errR, badRows, Finset.mem_filter, Finset.mem_union, Finset.mem_product,
      Finset.mem_univ, true_and, and_true] at hst ⊢
    by_cases h : P.map (evalRingHom st.1) = R st.1
    · left
      rw [← h, L2.ev_row]
      exact hst
    · right; exact h
  have hc1 := (Finset.card_le_card hfin).trans (Finset.card_union_le _ _)
  rw [Finset.card_product, Finset.card_univ] at hc1
  have hc1' : ((Finset.univ.filter fun st : F × F =>
      (P.eval (C st.2)).eval st.1 ≠ g st.1 st.2).card : ℝ) ≤
      errR.card + (badRows.card : ℝ) * q := by exact_mod_cast hc1
  have hbq' : (badRows.card : ℝ) * q ≤ 2 * B.card := by exact_mod_cast hbq
  linarith

end DLT

end Part10

section Part11
open Polynomial

namespace DLT

section Core
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma pow_char_pow_injective (p : ℕ) [Fact p.Prime] [CharP F p] (e : ℕ) {x y : F}
    (h : x ^ p ^ e = y ^ p ^ e) : x = y := by
  have : (x - y) ^ p ^ e = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp this)

lemma det2_ne_lam {α β γ : Fin 2 → F} (hαβ : det2 α β ≠ 0) (hγβ : det2 γ β ≠ 0) :
    lam α β γ ≠ 0 := by
  unfold lam; exact div_ne_zero hγβ hαβ

/-- Number of roots of a nonzero polynomial in a finset. -/
lemma card_roots_le (A : Polynomial F) (hA : A ≠ 0) (S : Finset F) :
    (S.filter fun a => A.eval a = 0).card ≤ A.natDegree := by
  classical
  calc (S.filter fun a => A.eval a = 0).card ≤ A.roots.toFinset.card := by
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_filter] at ha
        simp [Multiset.mem_toFinset, mem_roots hA, IsRoot, ha.2]
    _ ≤ Multiset.card A.roots := Multiset.toFinset_card_le _
    _ ≤ A.natDegree := card_roots' A


lemma natDegree_comp_shift (q : Polynomial F) (c : F) : (q.comp (X + C c)).natDegree = q.natDegree := by
  rw [natDegree_comp]; simp

/-- The lifting step for one family direction `j`. -/
lemma lift_dir (p : ℕ) [Fact p.Prime] [CharP F p] {r : ℕ} (w v : Fin r → Fin 2 → F)
    (hwv : ∀ i, det2 (w i) (v i) ≠ 0) (hvv : ∀ i j, i ≠ j → det2 (v i) (v j) ≠ 0)
    (G : Fin r → F → Polynomial F) (k : ℕ) (hG : ∀ i a, (G i a).natDegree ≤ k)
    (f : (Fin 2 → F) → F) (K D e : ℕ) (hkK : k ≤ K)
    (Q : Polynomial (MvPolynomial (Fin 2) F)) (hQW : WDeg (p ^ e * K) D Q)
    (L2 : Finset (Fin r × F)) (hQV : VanishOn w v G L2 (p ^ e) Q)
    (Inc : (Fin 2 → F) → Fin r → Prop)
    (hInc : ∀ x j, Inc x j → (j, lam (w j) (v j) x) ∈ L2 ∧
      (G j (lam (w j) (v j) x)).eval (mu (w j) (v j) x) = f x)
    (i₀ : Fin r) (a₀ : F) (hL₀ : (i₀, a₀) ∈ L2)
    (hA : restrictLine (a₀ • w i₀) (v i₀) ((G i₀ a₀) ^ p ^ e) (derivative Q) ≠ 0)
    (j : Fin r) (hj : j ≠ i₀) (S : Finset F)
    (hS : ∀ a ∈ S, Inc (a₀ • w i₀ + a • v i₀) i₀ ∧ Inc (a₀ • w i₀ + a • v i₀) j)
    (hcard : 12 * D ^ 2 < (S.filter fun a =>
      (restrictLine (a₀ • w i₀) (v i₀) ((G i₀ a₀) ^ p ^ e) (derivative Q)).eval a ≠ 0).card) :
    ∃ Nt : Polynomial (Polynomial F), Nt.natDegree ≤ p ^ e * k ∧
      (∀ a ∈ S, (restrictLine (a₀ • w i₀) (v i₀) ((G i₀ a₀) ^ p ^ e) (derivative Q)).eval a ≠ 0 →
        Nt.map (evalRingHom a) =
          C ((restrictLine (a₀ • w i₀) (v i₀) ((G i₀ a₀) ^ p ^ e) (derivative Q)).eval a ^
              (2 * (p ^ e * k))) *
            ((G j (lam (w j) (v j) (a₀ • w i₀ + a • v i₀))) ^ p ^ e).comp
              (X + C (mu (w j) (v j) (a₀ • w i₀ + a • v i₀)))) ∧
      ∑ n ∈ Finset.range (Q.natDegree + 1), Q.coeff n *
          (unsubst (a₀ • w i₀) (v i₀) (v j) Nt) ^ n *
          (unsubst (a₀ • w i₀) (v i₀) (v j)
            (C (restrictLine (a₀ • w i₀) (v i₀) ((G i₀ a₀) ^ p ^ e) (derivative Q)))) ^
              (2 * (p ^ e * k) * (Q.natDegree - n)) = 0 := by
  set p₀ := a₀ • w i₀
  set A := restrictLine p₀ (v i₀) ((G i₀ a₀) ^ p ^ e) (derivative Q) with hAdef
  have hdet : det2 (v i₀) (v j) ≠ 0 := hvv i₀ j (Ne.symm hj)
  set P := Q.map (subst p₀ (v i₀) (v j)).toRingHom with hP
  have hinj : Function.Injective (subst p₀ (v i₀) (v j)).toRingHom := subst_injective hdet
  have hPdeg : P.natDegree = Q.natDegree := natDegree_map_eq_of_injective hinj Q
  have hPA : ((derivative P).map (Polynomial.evalRingHom 0)).eval ((G i₀ a₀) ^ p ^ e) = A := by
    rw [hP, derivative_map, map_subst_anchor]
  have hgdeg : ∀ (i : Fin r) (b : F), ((G i b) ^ p ^ e).natDegree ≤ p ^ e * k := fun i b =>
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hG i b))
  have hJK : p ^ e * k ≤ p ^ e * K := Nat.mul_le_mul_left _ hkK
  obtain ⟨Nt, hNtdeg, hNtspec, hNtid⟩ := lifting (p ^ e * K) (p ^ e * k) D hJK P
    (by
      intro n m hnm
      rw [hP, coeff_map] at hnm ⊢
      by_cases hq : Q.coeff n = 0
      · exfalso; apply hnm; simp [hq]
      have h1 := hQW n hq
      rcases subst_coeff_natDegree p₀ (v i₀) (v j) (Q.coeff n) m with h2 | h2
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2 ⊢; omega
      · exact absurd h2 hnm)
    ((G i₀ a₀) ^ p ^ e) ((hgdeg _ _).trans hJK)
    (by rw [hP, map_subst_anchor]; exact hQV _ hL₀)
    (by rw [hPA]; exact hA)
    S (fun a => ((G j (lam (w j) (v j) (p₀ + a • v i₀))) ^ p ^ e).comp
      (X + C (mu (w j) (v j) (p₀ + a • v i₀))))
    (by
      intro a ha
      obtain ⟨hi₀, hjj⟩ := hS a ha
      obtain ⟨-, hacc₀⟩ := hInc _ _ hi₀
      obtain ⟨hL, hacc⟩ := hInc _ _ hjj
      refine ⟨?_, ?_, ?_⟩
      · rw [natDegree_comp_shift]; exact hgdeg _ _
      · simp only [eval_comp, eval_add, eval_X, eval_C, zero_add, eval_pow]
        rw [hacc, ← hacc₀, lam_comb (hwv i₀), mu_comb (hwv i₀)]
      · rw [hP, map_subst_line]
        have hx := (decomp (hwv j) (p₀ + a • v i₀)).symm
        have key : restrictLine (lam (w j) (v j) (p₀ + a • v i₀) • w j +
            mu (w j) (v j) (p₀ + a • v i₀) • v j) (v j)
            (((G j (lam (w j) (v j) (p₀ + a • v i₀))) ^ p ^ e).comp
              (X + C (mu (w j) (v j) (p₀ + a • v i₀)))) Q = 0 := by
          rw [restrictLine_shift, hQV _ hL, zero_comp]
        rwa [hx] at key)
    (by rw [hPA]; exact hcard)
  rw [hPA] at hNtspec hNtid
  refine ⟨Nt, hNtdeg, fun a ha haA => hNtspec a ha haA, ?_⟩
  -- transport the identity with `unsubst`
  have := congrArg (unsubst p₀ (v i₀) (v j)) hNtid
  rw [map_zero, map_sum] at this
  rw [← this, hPdeg]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, hP, coeff_map]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [unsubst_subst hdet]


lemma aux_field_identity {K : Type*} [Field K] (q u y z : K) (hy : y ≠ 0) :
    q * (u / y) * (y * z) = q * u * z := by
  field_simp

lemma lam_self {α β : Fin 2 → F} (h : det2 α β ≠ 0) : lam α β α = 1 := by
  have := lam_comb h 1 0; simpa using this

lemma lam_other {α β : Fin 2 → F} : lam α β β = 0 := lam_v

lemma mu_self {α β : Fin 2 → F} (h : det2 α β ≠ 0) : mu α β α = 0 := by
  have := mu_comb h 1 0; simpa using this

lemma mu_other {α β : Fin 2 → F} (h : det2 α β ≠ 0) : mu α β β = 1 := mu_v h

lemma lam_zero {α β : Fin 2 → F} : lam α β 0 = 0 := by
  have := lam_smul (w := α) (v := β) 0 0; simpa using this

lemma mu_zero {α β : Fin 2 → F} : mu α β 0 = 0 := by
  have := mu_smul (w := α) (v := β) 0 0; simpa using this

lemma lam_sub {α β : Fin 2 → F} (x y : Fin 2 → F) : lam α β (x - y) = lam α β x - lam α β y := by
  rw [sub_eq_add_neg, lam_add, ← neg_one_smul F y, lam_smul]; ring

lemma mu_sub {α β : Fin 2 → F} (x y : Fin 2 → F) : mu α β (x - y) = mu α β x - mu α β y := by
  rw [sub_eq_add_neg, mu_add, ← neg_one_smul F y, mu_smul]; ring

lemma swap_mapC (h : Polynomial F) : Bivariate.swap (h.map C) = C h := by
  rw [← Bivariate.swap_C, Bivariate.swap_swap_apply]

lemma eval_C_mapC (h : Polynomial F) (t : F) : (h.map C).eval (C t) = C (h.eval t) := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

set_option maxHeartbeats 2000000 in
open Classical in
theorem he_core (p : ℕ) [hp : Fact p.Prime] [CharP F p] {r : ℕ} (w v : Fin r → Fin 2 → F)
    (hwv : ∀ i, det2 (w i) (v i) ≠ 0) (hvv : ∀ i j, i ≠ j → det2 (v i) (v j) ≠ 0)
    (G : Fin r → F → Polynomial F) (k : ℕ) (hG : ∀ i a, (G i a).natDegree ≤ k)
    (f : (Fin 2 → F) → F) (K D : ℕ) (hkK : k ≤ K) (hK : 1 ≤ K)
    (P2 : Finset (Fin 2 → F)) (L2 : Finset (Fin r × F)) (Inc : (Fin 2 → F) → Fin r → Prop)
    (hInc : ∀ x j, Inc x j → x ∈ P2 ∧ (j, lam (w j) (v j) x) ∈ L2 ∧
      (G j (lam (w j) (v j) x)).eval (mu (w j) (v j) x) = f x)
    (n₁ d₁ : ℕ)
    (hdeg1 : ∀ x ∈ P2, d₁ ≤ (Finset.univ.filter fun j => Inc x j).card)
    (hdeg2 : ∀ jb ∈ L2, n₁ ≤ (Finset.univ.filter fun x =>
      lam (w jb.1) (v jb.1) x = jb.2 ∧ Inc x jb.1).card)
    (hn₁ : D < n₁) (hd₁ : 2 ≤ d₁) (hSZ : D * Fintype.card F < P2.card)
    (hbig1 : 2 * Fintype.card F * (D / K + 1) < n₁ * (d₁ - 1))
    (hbig2 : 2 * r * (12 * D ^ 2 + 2 * D) ≤ n₁ * (d₁ - 1))
    (Q₀ : Polynomial (MvPolynomial (Fin 2) F)) (hQ₀ : Q₀ ≠ 0) (hW : WDeg K D Q₀)
    (hV : VanishOn w v G L2 1 Q₀) :
    ∃ Qf : MvPolynomial (Fin 2) F, Qf.totalDegree ≤ 2 * k ∧
      n₁ * (n₁ * (d₁ - 1)) ≤
        4 * r * (Finset.univ.filter fun x => MvPolynomial.eval x Qf = f x).card := by
  -- Step 1: the minimal polynomial and an anchor point
  have hP2 : ∀ x ∈ P2, ∃ j, Inc x j := by
    intro x hx
    have := hdeg1 x hx
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter fun j => Inc x j).card)
    exact ⟨j, (Finset.mem_filter.mp hj).2⟩
  obtain ⟨e, Q, hQ0, hQW, hQV, hQd1, x₀, hx₀P, hx₀⟩ := minimal_Q p w v hwv G k hG f K D hkK P2 L2
    Inc hInc hP2 (fun jb hjb => lt_of_lt_of_le hn₁ (hdeg2 jb hjb)) hSZ Q₀ hQ₀ hW hV
  have hKe : 1 ≤ p ^ e * K := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (by omega))
  have hdQ : p ^ e * K * Q.natDegree ≤ D := natDegree_le_of_WDeg hQW
  have hD1 : 1 ≤ D := le_trans (by nlinarith) hdQ
  have hJD : p ^ e * k ≤ D := le_trans (Nat.mul_le_mul_left _ hkK)
    (le_trans (by nlinarith) hdQ)
  have hdQK : Q.natDegree ≤ D / K := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have hpe : 1 ≤ p ^ e := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)
    nlinarith
  -- Step 2: the anchor line
  obtain ⟨i₀, hi₀⟩ := hP2 x₀ hx₀P
  obtain ⟨-, hL₀, hacc₀⟩ := hInc x₀ i₀ hi₀
  set a₀ := lam (w i₀) (v i₀) x₀ with ha₀
  set p₀ := a₀ • w i₀ with hp₀
  set A := restrictLine p₀ (v i₀) ((G i₀ a₀) ^ p ^ e) (derivative Q) with hAdef
  have hA : A ≠ 0 := by
    intro h0
    apply hx₀
    have := congrArg (Polynomial.eval (mu (w i₀) (v i₀) x₀)) h0
    rw [hAdef, restrictLine_eval, eval_zero, eval_pow, hacc₀, hp₀, ha₀,
      ← decomp (hwv i₀) x₀] at this
    exact this
  have hAdeg : A.natDegree ≤ D := restrictLine_natDegree_le _ _ _ _ _ _ (WDeg_derivative hQW)
    (natDegree_pow_le.trans (Nat.mul_le_mul_left _ ((hG _ _).trans hkK)))
  -- Step 3: families
  let pt : F → Fin 2 → F := fun a => p₀ + a • v i₀
  let Sj : Fin r → Finset F := fun j =>
    Finset.univ.filter fun a => Inc (pt a) i₀ ∧ Inc (pt a) j
  let Big : Finset (Fin r) := (Finset.univ.erase i₀).filter fun j => n₁ * (d₁ - 1) ≤ 2 * r * (Sj j).card
  have hr0 : 0 < r := Fin.pos i₀
  have hptmu : ∀ x, lam (w i₀) (v i₀) x = a₀ → pt (mu (w i₀) (v i₀) x) = x := by
    intro x hx
    simp only [pt, hp₀]
    rw [← hx]; exact (decomp (hwv i₀) x).symm
  have hP0 : n₁ ≤ (Finset.univ.filter fun a => Inc (pt a) i₀).card := by
    refine le_trans (hdeg2 (i₀, a₀) hL₀) ?_
    apply Finset.card_le_card_of_injOn (mu (w i₀) (v i₀))
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
      rw [hptmu x hx.1]; exact hx.2
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
      rw [← hptmu x hx.1, ← hptmu y hy.1, hxy]
  have hcount : ∀ a, Inc (pt a) i₀ →
      d₁ - 1 ≤ ((Finset.univ.erase i₀).filter fun j => Inc (pt a) j).card := by
    intro a ha
    have h1 := hdeg1 (pt a) (hInc _ _ ha).1
    rw [Finset.filter_erase, Finset.card_erase_of_mem (by simpa using ha)]
    omega
  have hSum : n₁ * (d₁ - 1) ≤ ∑ j ∈ Finset.univ.erase i₀, (Sj j).card := by
    have e1 : ∑ j ∈ Finset.univ.erase i₀, (Sj j).card =
        ∑ a ∈ Finset.univ.filter (fun a => Inc (pt a) i₀),
          ((Finset.univ.erase i₀).filter fun j => Inc (pt a) j).card := by
      simp only [Sj, Finset.card_filter]
      rw [Finset.sum_comm, Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs with ha
      · exact Finset.sum_congr rfl fun j _ => by simp [ha]
      · exact Finset.sum_eq_zero fun j _ => by simp [ha]
    rw [e1]
    calc n₁ * (d₁ - 1) ≤ (Finset.univ.filter fun a => Inc (pt a) i₀).card * (d₁ - 1) :=
          Nat.mul_le_mul_right _ hP0
      _ = ∑ a ∈ Finset.univ.filter (fun a => Inc (pt a) i₀), (d₁ - 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun a ha => hcount a (Finset.mem_filter.mp ha).2
  have hBig : Q.natDegree < Big.card := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i₀)
      (fun j => n₁ * (d₁ - 1) ≤ 2 * r * (Sj j).card) (fun j => (Sj j).card)
    have hB1 : ∑ j ∈ Big, (Sj j).card ≤ Big.card * Fintype.card F := by
      rw [← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun j _ => Finset.card_le_univ _
    have hB2 : 2 * r * ∑ j ∈ (Finset.univ.erase i₀).filter
        (fun j => ¬ n₁ * (d₁ - 1) ≤ 2 * r * (Sj j).card), (Sj j).card ≤ r * (n₁ * (d₁ - 1)) := by
      rw [Finset.mul_sum]
      calc ∑ j ∈ (Finset.univ.erase i₀).filter
            (fun j => ¬ n₁ * (d₁ - 1) ≤ 2 * r * (Sj j).card), 2 * r * (Sj j).card
          ≤ ∑ j ∈ (Finset.univ.erase i₀).filter
            (fun j => ¬ n₁ * (d₁ - 1) ≤ 2 * r * (Sj j).card), n₁ * (d₁ - 1) :=
            Finset.sum_le_sum fun j hj => by
              have := (Finset.mem_filter.mp hj).2; omega
        _ = ((Finset.univ.erase i₀).filter
            (fun j => ¬ n₁ * (d₁ - 1) ≤ 2 * r * (Sj j).card)).card * (n₁ * (d₁ - 1)) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ r * (n₁ * (d₁ - 1)) := by
            apply Nat.mul_le_mul_right
            calc _ ≤ (Finset.univ : Finset (Fin r)).card :=
                  Finset.card_le_card ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _))
              _ = r := by simp
    have h3 : n₁ * (d₁ - 1) ≤ 2 * Fintype.card F * Big.card := by
      have : 2 * r * (n₁ * (d₁ - 1)) ≤ 2 * r * (Big.card * Fintype.card F) +
          r * (n₁ * (d₁ - 1)) := by
        calc 2 * r * (n₁ * (d₁ - 1)) ≤ 2 * r * ∑ j ∈ Finset.univ.erase i₀, (Sj j).card :=
              Nat.mul_le_mul_left _ hSum
          _ = 2 * r * ∑ j ∈ Big, (Sj j).card + 2 * r * ∑ j ∈ (Finset.univ.erase i₀).filter
              (fun j => ¬ n₁ * (d₁ - 1) ≤ 2 * r * (Sj j).card), (Sj j).card := by
              rw [← hsplit, mul_add]
          _ ≤ _ := add_le_add (Nat.mul_le_mul_left _ hB1) hB2
      have h4 : r * (n₁ * (d₁ - 1)) ≤ r * (2 * Fintype.card F * Big.card) := by nlinarith
      exact Nat.le_of_mul_le_mul_left h4 hr0
    have h5 : D / K + 1 < Big.card := by
      by_contra hcon
      push_neg at hcon
      have : 2 * Fintype.card F * Big.card ≤ 2 * Fintype.card F * (D / K + 1) :=
        Nat.mul_le_mul_left _ hcon
      omega
    omega
  have hSjBig : ∀ j ∈ Big, 12 * D ^ 2 + 2 * D ≤ (Sj j).card := by
    intro j hj
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 : 2 * r * (12 * D ^ 2 + 2 * D) ≤ 2 * r * (Sj j).card := le_trans hbig2 h1
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  -- Step 4: lifting in every big direction
  have hlift : ∀ j ∈ Big, ∃ Nt : Polynomial (Polynomial F), Nt.natDegree ≤ p ^ e * k ∧
      (∀ a ∈ Sj j, A.eval a ≠ 0 →
        Nt.map (evalRingHom a) = C (A.eval a ^ (2 * (p ^ e * k))) *
          ((G j (lam (w j) (v j) (pt a))) ^ p ^ e).comp (X + C (mu (w j) (v j) (pt a)))) ∧
      ∑ n ∈ Finset.range (Q.natDegree + 1), Q.coeff n *
          (unsubst p₀ (v i₀) (v j) Nt) ^ n *
          (unsubst p₀ (v i₀) (v j) (C A)) ^ (2 * (p ^ e * k) * (Q.natDegree - n)) = 0 := by
    intro j hj
    have hji : j ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
    refine lift_dir p w v hwv hvv G k hG f K D e hkK Q hQW L2 hQV Inc
      (fun x j h => (hInc x j h).2) i₀ a₀ hL₀ hA j hji (Sj j)
      (fun a ha => (Finset.mem_filter.mp ha).2) ?_
    have h1 := hSjBig j hj
    have h2 := card_roots_le A hA (Sj j)
    have h3 := Finset.card_filter_add_card_filter_not (s := Sj j)
      (fun a => A.eval a = 0)
    have h4 : (Finset.filter (fun a => ¬ A.eval a = 0) (Sj j)).card =
        ((Sj j).filter fun a => A.eval a ≠ 0).card := rfl
    nlinarith
  choose! Nt hNtdeg hNtspec hNtid using hlift
  set J := p ^ e * k with hJ
  -- Step 5: the lifted roots in the fraction field
  have hDq : D < Fintype.card F := by
    have : P2.card ≤ Fintype.card F * Fintype.card F := by
      calc P2.card ≤ (Finset.univ : Finset (Fin 2 → F)).card := Finset.card_le_univ _
        _ = Fintype.card F * Fintype.card F := by simp [Fintype.card_fun, sq]
    nlinarith
  obtain ⟨a₁, ha₁⟩ : ∃ a, A.eval a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have := card_roots_le A hA Finset.univ
    simp only [hcon, Finset.filter_true, Finset.card_univ] at this
    omega
  let Kf := FractionRing (MvPolynomial (Fin 2) F)
  let ι := algebraMap (MvPolynomial (Fin 2) F) Kf
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  let U : Fin r → MvPolynomial (Fin 2) F := fun j => unsubst p₀ (v i₀) (v j) (Nt j)
  let Aψ : Fin r → MvPolynomial (Fin 2) F := fun j => unsubst p₀ (v i₀) (v j) (C A)
  have hBigne : ∀ j ∈ Big, j ≠ i₀ := fun j hj =>
    (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
  have hAψ : ∀ j ∈ Big, Aψ j ≠ 0 := by
    intro j hjB h0
    have hj := hBigne j hjB
    have := congrArg (MvPolynomial.eval (p₀ + (a₁ • v i₀ + (0 : F) • v j))) h0
    simp only [Aψ, eval_unsubst, eval_C, map_zero] at this
    rw [show p₀ + (a₁ • v i₀ + (0 : F) • v j) - p₀ = a₁ • v i₀ + (0 : F) • v j by abel] at this
    rw [lam_comb (hvv i₀ j (Ne.symm hj))] at this
    exact ha₁ this
  have hroot : ∀ j ∈ Big, (Q.map ι).eval (ι (U j) / ι (Aψ j) ^ (2 * J)) = 0 := by
    intro j hj
    have hid := hNtid j hj
    have hne : ι (Aψ j) ≠ 0 := by
      rw [map_ne_zero_iff _ hι]; exact hAψ j hj
    rw [eval_map, eval₂_eq_sum_range]
    have key : ∀ n ∈ Finset.range (Q.natDegree + 1),
        ι (Q.coeff n) * (ι (U j) / ι (Aψ j) ^ (2 * J)) ^ n =
          ι (Q.coeff n * U j ^ n * Aψ j ^ (2 * J * (Q.natDegree - n))) /
            ι (Aψ j) ^ (2 * J * Q.natDegree) := by
      intro n hn
      have hn' : n ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [eq_div_iff (pow_ne_zero _ hne), div_pow, map_mul, map_mul, map_pow, map_pow,
        ← pow_mul]
      have : 2 * J * Q.natDegree = 2 * J * n + 2 * J * (Q.natDegree - n) := by
        rw [← mul_add, Nat.add_sub_cancel' hn']
      rw [this, pow_add]
      have hy : ι (Aψ j) ^ (2 * J * n) ≠ 0 := pow_ne_zero _ hne
      exact aux_field_identity _ _ _ _ hy
    rw [Finset.sum_congr rfl key, ← Finset.sum_div, ← map_sum]
    simp only [U, Aψ]
    rw [hid, map_zero, zero_div]
  -- Step 6: pigeonhole
  have hQne : Q.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hQ0
  have hdegm : (Q.map ι).natDegree = Q.natDegree := natDegree_map_eq_of_injective hι Q
  obtain ⟨j₁, hj₁, j₂, hj₂, hne12, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Big) (t := (Q.map ι).roots.toFinset)
    (f := fun j => ι (U j) / ι (Aψ j) ^ (2 * J))
    (by
      calc (Q.map ι).roots.toFinset.card ≤ Multiset.card (Q.map ι).roots :=
            Multiset.toFinset_card_le _
        _ ≤ (Q.map ι).natDegree := card_roots' _
        _ < Big.card := by rw [hdegm]; exact hBig)
    (by
      intro j hj
      simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hQne, IsRoot.def]
      exact hroot j hj)
  -- Step 7: cross multiplication
  have hcross : U j₁ * Aψ j₂ ^ (2 * J) = U j₂ * Aψ j₁ ^ (2 * J) := by
    have h1 : ι (Aψ j₁) ^ (2 * J) ≠ 0 := pow_ne_zero _ (by
      rw [map_ne_zero_iff _ hι]; exact hAψ j₁ hj₁)
    have h2 : ι (Aψ j₂) ^ (2 * J) ≠ 0 := pow_ne_zero _ (by
      rw [map_ne_zero_iff _ hι]; exact hAψ j₂ hj₂)
    rw [div_eq_div_iff h1 h2] at heq
    apply hι
    simp only [map_mul, map_pow]
    exact heq
  -- Step 8: common coordinates (s, t)
  have hj₁i : j₁ ≠ i₀ := hBigne j₁ hj₁
  have hj₂i : j₂ ≠ i₀ := hBigne j₂ hj₂
  have hd1 : det2 (v i₀) (v j₁) ≠ 0 := hvv i₀ j₁ (Ne.symm hj₁i)
  have hd2 : det2 (v i₀) (v j₂) ≠ 0 := hvv i₀ j₂ (Ne.symm hj₂i)
  set κ := lam (v i₀) (v j₂) (v j₁) with hκdef
  have hκ : κ ≠ 0 := det2_ne_lam hd2 (hvv j₁ j₂ hne12)
  set α' := v i₀ - κ⁻¹ • v j₁ with hα'
  set β' := κ⁻¹ • v j₁ with hβ'
  have hdet' : det2 α' β' ≠ 0 := by
    rw [hα', hβ', sub_eq_add_neg, det2_add_left, ← neg_one_smul F (κ⁻¹ • v j₁),
      det2_smul_left, det2_smul_left, det2_smul_right, det2_smul_right, det2_self]
    simp only [mul_zero, add_zero]
    exact mul_ne_zero (inv_ne_zero hκ) hd1
  -- scalar values
  have l1α : lam (v i₀) (v j₁) α' = 1 := by
    rw [hα', lam_sub, lam_smul, lam_self hd1, lam_other]; ring
  have l1β : lam (v i₀) (v j₁) β' = 0 := by rw [hβ', lam_smul, lam_other, mul_zero]
  have m1α : mu (v i₀) (v j₁) α' = -κ⁻¹ := by
    rw [hα', mu_sub, mu_smul, mu_self hd1, mu_other hd1]; ring
  have m1β : mu (v i₀) (v j₁) β' = κ⁻¹ := by rw [hβ', mu_smul, mu_other hd1, mul_one]
  have l2α : lam (v i₀) (v j₂) α' = 0 := by
    rw [hα', lam_sub, lam_smul, lam_self hd2, ← hκdef]; field_simp; ring
  have l2β : lam (v i₀) (v j₂) β' = 1 := by
    rw [hβ', lam_smul, ← hκdef]; field_simp
  set c₀ : F := -κ⁻¹
  set c₁ : F := κ⁻¹
  set dd₀ : F := mu (v i₀) (v j₂) α'
  set dd₁ : F := mu (v i₀) (v j₂) β'
  let Θ := subst p₀ α' β'
  have hΘ1 : ∀ B, Θ (unsubst p₀ (v i₀) (v j₁) B) = sig1 c₀ c₁ B := by
    intro B
    simp only [Θ]
    rw [subst_unsubst, sub_self, lam_zero, mu_zero, l1α, l1β, m1α, m1β]
    simp only [map_zero, map_one, zero_add, one_mul, zero_mul, add_zero, sig1, c₀, c₁,
      coe_eval₂RingHom]
  have hΘ2 : ∀ B, Θ (unsubst p₀ (v i₀) (v j₂) B) = sig2 dd₀ dd₁ B := by
    intro B
    simp only [Θ]
    rw [subst_unsubst, sub_self, lam_zero, mu_zero, l2α, l2β]
    simp only [map_zero, map_one, zero_add, one_mul, zero_mul, add_zero, sig2, dd₀, dd₁,
      coe_eval₂RingHom]
  have hmain : sig1 c₀ c₁ (Nt j₁) * (A ^ (2 * J)).map C =
      sig2 dd₀ dd₁ (Nt j₂) * C (A ^ (2 * J)) := by
    have := congrArg Θ hcross
    simp only [map_mul, map_pow, U, Aψ, hΘ1, hΘ2, sig1_C, sig2_C] at this
    rw [Polynomial.map_pow, C_pow]
    exact this
  -- Step 9: intersection
  have hAJ : A ^ (2 * J) ≠ 0 := pow_ne_zero _ hA
  obtain ⟨U', hU'⟩ : C (A ^ (2 * J)) ∣ sig1 c₀ c₁ (Nt j₁) :=
    dvd_of_dvd_mul_mapC _ _ hAJ _ (by rw [hmain]; exact dvd_mul_left _ _)
  have hCne : (C (A ^ (2 * J)) : Polynomial (Polynomial F)) ≠ 0 := by
    rwa [Ne, C_eq_zero]
  have hU'2 : U' * (A ^ (2 * J)).map C = sig2 dd₀ dd₁ (Nt j₂) := by
    apply mul_left_cancel₀ hCne
    rw [← mul_assoc, ← hU', hmain, mul_comm]
  -- Step 10: degrees of U'
  have hU't : U'.natDegree ≤ J := by
    have h1 : (sig1 c₀ c₁ (Nt j₁)).natDegree = U'.natDegree := by
      rw [hU', natDegree_C_mul hAJ]
    rw [← h1]
    exact (sig1_natDegree_le _ _ _).trans (hNtdeg j₁ hj₁)
  have hU's : ∀ n, (U'.coeff n).natDegree ≤ J := by
    rw [A2.sdeg_iff]
    have h1 := (A2.sdeg_iff (sig2 dd₀ dd₁ (Nt j₂)) J).mp
      (fun n => (sig2_coeff_natDegree_le _ _ _ n).trans (hNtdeg j₂ hj₂))
    rw [← hU'2, map_mul, swap_mapC, natDegree_mul_C hAJ] at h1
    exact h1
  -- Step 11: restrictions of U' and the p^e-th root
  set Ss := (Sj j₁).filter fun a => A.eval a ≠ 0 with hSs
  set Ts := (Sj j₂).filter fun a => A.eval a ≠ 0 with hTs
  have hrow : ∀ a ∈ Ss, U'.map (evalRingHom a) =
      (((G j₁ (lam (w j₁) (v j₁) (pt a))) ^ p ^ e).comp
        (X + C (mu (w j₁) (v j₁) (pt a)))).comp (C (c₀ * a) + C c₁ * X) := by
    intro a ha
    obtain ⟨haS, haA⟩ := Finset.mem_filter.mp ha
    have h1 := sig1_map_eval c₀ c₁ a (Nt j₁)
    rw [hNtspec j₁ hj₁ a haS haA, hU', Polynomial.map_mul, Polynomial.map_C, mul_comp, C_comp]
      at h1
    have hc : (C ((evalRingHom a) (A ^ (2 * J))) : Polynomial F) ≠ 0 := by
      rw [Ne, C_eq_zero, coe_evalRingHom, eval_pow]; exact pow_ne_zero _ haA
    exact mul_left_cancel₀ hc (by rw [h1, coe_evalRingHom, eval_pow])
  have hcol : ∀ b ∈ Ts, U'.eval (C b) =
      (((G j₂ (lam (w j₂) (v j₂) (pt b))) ^ p ^ e).comp
        (X + C (mu (w j₂) (v j₂) (pt b)))).comp (C dd₀ * X + C (dd₁ * b)) := by
    intro b hb
    obtain ⟨hbS, hbA⟩ := Finset.mem_filter.mp hb
    have h1 := sig2_eval_C dd₀ dd₁ b (Nt j₂)
    rw [hNtspec j₂ hj₂ b hbS hbA, ← hU'2, eval_mul, eval_C_mapC, mul_comp, C_comp] at h1
    have hc : (C (A.eval b ^ (2 * J)) : Polynomial F) ≠ 0 := by
      rw [Ne, C_eq_zero]; exact pow_ne_zero _ hbA
    rw [eval_pow] at h1
    exact mul_right_cancel₀ hc (by rw [h1, mul_comm])
  have hSscard : 12 * D ^ 2 + D ≤ Ss.card := by
    have h1 := hSjBig j₁ hj₁
    have h2 := card_roots_le A hA (Sj j₁)
    have h3 := Finset.card_filter_add_card_filter_not (s := Sj j₁) (fun a => A.eval a = 0)
    have h4 : (Finset.filter (fun a => ¬ A.eval a = 0) (Sj j₁)).card = Ss.card := rfl
    omega
  have hTscard : 12 * D ^ 2 + D ≤ Ts.card := by
    have h1 := hSjBig j₂ hj₂
    have h2 := card_roots_le A hA (Sj j₂)
    have h3 := Finset.card_filter_add_card_filter_not (s := Sj j₂) (fun a => A.eval a = 0)
    have h4 : (Finset.filter (fun a => ¬ A.eval a = 0) (Sj j₂)).card = Ts.card := rfl
    omega
  obtain ⟨Vf, hVt, hVs, hVpow⟩ := frobenius_root p e k U' hU't hU's Ss Ts
    (by nlinarith) (by nlinarith)
    (fun a ha => ⟨((G j₁ (lam (w j₁) (v j₁) (pt a))).comp (X + C (mu (w j₁) (v j₁) (pt a)))).comp
        (C (c₀ * a) + C c₁ * X), by rw [hrow a ha, pow_comp, pow_comp]⟩)
    (fun b hb => ⟨((G j₂ (lam (w j₂) (v j₂) (pt b))).comp (X + C (mu (w j₂) (v j₂) (pt b)))).comp
        (C dd₀ * X + C (dd₁ * b)), by rw [hcol b hb, pow_comp, pow_comp]⟩)
  -- Step 12: the final polynomial and its agreement
  refine ⟨unsubst p₀ α' β' Vf, totalDegree_unsubst p₀ α' β' Vf k hVt hVs, ?_⟩
  let Xa : F → Finset (Fin 2 → F) := fun a => Finset.univ.filter fun x =>
    lam (w j₁) (v j₁) x = lam (w j₁) (v j₁) (pt a) ∧ Inc x j₁
  have hXa : ∀ a ∈ Ss, n₁ ≤ (Xa a).card := by
    intro a ha
    have hInca : Inc (pt a) j₁ := ((Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2).2
    exact hdeg2 (j₁, lam (w j₁) (v j₁) (pt a)) (hInc _ _ hInca).2.1
  have hagree : ∀ a ∈ Ss, ∀ x ∈ Xa a, MvPolynomial.eval x (unsubst p₀ α' β' Vf) = f x := by
    intro a ha x hx
    obtain ⟨hxl, hxI⟩ := (Finset.mem_filter.mp hx).2
    have hacc := (hInc x j₁ hxI).2.2
    set W := mu (w j₁) (v j₁) x - mu (w j₁) (v j₁) (pt a) with hW
    have hxeq : x = pt a + W • v j₁ := by
      have e1 := decomp (hwv j₁) x
      have e2 := decomp (hwv j₁) (pt a)
      rw [hxl] at e1
      rw [e1]
      conv_rhs => rw [e2]
      rw [hW]
      module
    have hxpt : x - p₀ = a • α' + (a + κ * W) • β' := by
      rw [hxeq, hα', hβ', smul_smul, show (a + κ * W) * κ⁻¹ = a * κ⁻¹ + W by field_simp]
      simp only [pt]
      module
    have hl : lam α' β' (x - p₀) = a := by rw [hxpt, lam_comb hdet']
    have hm : mu α' β' (x - p₀) = a + κ * W := by rw [hxpt, mu_comb hdet']
    apply pow_char_pow_injective p e
    rw [eval_unsubst, hl, hm, hVpow, ← DLT.L2.ev_row, hrow a ha]
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_pow]
    have : c₀ * a + c₁ * (a + κ * W) + mu (w j₁) (v j₁) (pt a) = mu (w j₁) (v j₁) x := by
      simp only [c₀, c₁, hW]; field_simp; ring
    rw [this, ← hxl, hacc]
  have hlamv : lam (w j₁) (v j₁) (v i₀) ≠ 0 := det2_ne_lam (hwv j₁) (hvv i₀ j₁ (Ne.symm hj₁i))
  have hdisj : (Ss : Set F).PairwiseDisjoint Xa := by
    intro a _ a' _ haa'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    apply haa'
    have h1 := (Finset.mem_filter.mp hx).2.1
    have h2 := (Finset.mem_filter.mp hx').2.1
    rw [h1] at h2
    simp only [pt, lam_add, lam_smul] at h2
    exact mul_right_cancel₀ hlamv (by linear_combination h2)
  have hsub : Ss.biUnion Xa ⊆
      Finset.univ.filter fun x => MvPolynomial.eval x (unsubst p₀ α' β' Vf) = f x := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hagree a ha x hxa
  have hcardU : Ss.card * n₁ ≤ (Ss.biUnion Xa).card := by
    rw [Finset.card_biUnion hdisj]
    calc Ss.card * n₁ = ∑ a ∈ Ss, n₁ := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ a ∈ Ss, (Xa a).card := Finset.sum_le_sum hXa
  have hSsj : (Sj j₁).card ≤ Ss.card + D := by
    have h2 := card_roots_le A hA (Sj j₁)
    have h3 := Finset.card_filter_add_card_filter_not (s := Sj j₁) (fun a => A.eval a = 0)
    have h4 : (Finset.filter (fun a => ¬ A.eval a = 0) (Sj j₁)).card = Ss.card := rfl
    omega
  have hB1 : n₁ * (d₁ - 1) ≤ 2 * r * (Sj j₁).card := (Finset.mem_filter.mp hj₁).2
  have hfin : n₁ * (d₁ - 1) ≤ 4 * r * Ss.card := by nlinarith
  calc n₁ * (n₁ * (d₁ - 1)) ≤ n₁ * (4 * r * Ss.card) := Nat.mul_le_mul_left _ hfin
    _ = 4 * r * (Ss.card * n₁) := by ring
    _ ≤ 4 * r * (Ss.biUnion Xa).card := Nat.mul_le_mul_left _ hcardU
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card hsub)

end Core
end DLT

end Part11

section Part12
open Polynomial

namespace DLT
namespace HM

open Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Point–line incidences where the line polynomial agrees with `f`. -/
noncomputable def E1 {r : ℕ} (w v : Fin r → Fin 2 → F) (G : Fin r → F → Polynomial F)
    (f : (Fin 2 → F) → F) : Finset ((Fin 2 → F) × (Fin r × F)) :=
  Finset.univ.filter fun e => e.2.2 = lam (w e.2.1) (v e.2.1) e.1 ∧
    (G e.2.1 e.2.2).eval (mu (w e.2.1) (v e.2.1) e.1) = f e.1

lemma mem_E1 {r : ℕ} {w v : Fin r → Fin 2 → F} {G : Fin r → F → Polynomial F}
    {f : (Fin 2 → F) → F} {e : (Fin 2 → F) × (Fin r × F)} :
    e ∈ E1 w v G f ↔ e.2.2 = lam (w e.2.1) (v e.2.1) e.1 ∧
      (G e.2.1 e.2.2).eval (mu (w e.2.1) (v e.2.1) e.1) = f e.1 := by
  simp [E1]

lemma two_lines {r : ℕ} (w v : Fin r → Fin 2 → F) (hwv : ∀ i, det2 (w i) (v i) ≠ 0)
    (hvv : ∀ i j, i ≠ j → det2 (v i) (v j) ≠ 0) {i j : Fin r} {x y : Fin 2 → F}
    (hxy : x ≠ y) (hi : lam (w i) (v i) x = lam (w i) (v i) y)
    (hj : lam (w j) (v j) x = lam (w j) (v j) y) : i = j := by
  by_contra hij
  apply hxy
  have hzi : lam (w i) (v i) (x - y) = 0 := by rw [lam_sub, hi, sub_self]
  have hzj : lam (w j) (v j) (x - y) = 0 := by rw [lam_sub, hj, sub_self]
  have hz : x - y = mu (w i) (v i) (x - y) • v i := by
    have := decomp (hwv i) (x - y); rw [hzi, zero_smul, zero_add] at this; exact this
  have h0 : det2 (x - y) (v j) = 0 := by
    unfold lam at hzj; exact (div_eq_zero_iff.mp hzj).resolve_right (hwv j)
  rw [hz, det2_smul_left] at h0
  have hmu : mu (w i) (v i) (x - y) = 0 := (mul_eq_zero.mp h0).resolve_right (hvv i j hij)
  have : x - y = 0 := by rw [hz, hmu, zero_smul]
  exact sub_eq_zero.mp this

lemma pt_eq_of {r : ℕ} (w v : Fin r → Fin 2 → F) (hwv : ∀ i, det2 (w i) (v i) ≠ 0)
    {i : Fin r} {x y : Fin 2 → F} (hl : lam (w i) (v i) x = lam (w i) (v i) y)
    (hm : mu (w i) (v i) x = mu (w i) (v i) y) : x = y := by
  rw [decomp (hwv i) x, decomp (hwv i) y, hl, hm]

lemma degU {r : ℕ} (w v : Fin r → Fin 2 → F) (G : Fin r → F → Polynomial F)
    (f : (Fin 2 → F) → F) (E : Finset ((Fin 2 → F) × (Fin r × F))) (hE : E ⊆ E1 w v G f)
    (u : Fin 2 → F) : ((E.filter fun e => e.1 = u).card : ℝ) ≤ r := by
  have : (E.filter fun e => e.1 = u).card ≤ (Finset.univ : Finset (Fin r)).card := by
    apply Finset.card_le_card_of_injOn (fun e => e.2.1) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    intro e he e' he' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at he he'
    have h1 := (mem_E1.mp (hE he.1)).1
    have h2 := (mem_E1.mp (hE he'.1)).1
    simp only at h
    refine Prod.ext (he.2.trans he'.2.symm) (Prod.ext h ?_)
    rw [h1, h2, h, he.2, he'.2]
  simpa using this

lemma degV {r : ℕ} (w v : Fin r → Fin 2 → F) (hwv : ∀ i, det2 (w i) (v i) ≠ 0)
    (G : Fin r → F → Polynomial F)
    (f : (Fin 2 → F) → F) (E : Finset ((Fin 2 → F) × (Fin r × F))) (hE : E ⊆ E1 w v G f)
    (l : Fin r × F) : ((E.filter fun e => e.2 = l).card : ℝ) ≤ Fintype.card F := by
  have : (E.filter fun e => e.2 = l).card ≤ (Finset.univ : Finset F).card := by
    apply Finset.card_le_card_of_injOn (fun e => mu (w l.1) (v l.1) e.1)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    intro e he e' he' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at he he'
    have h1 := (mem_E1.mp (hE he.1)).1
    have h2 := (mem_E1.mp (hE he'.1)).1
    rw [he.2] at h1; rw [he'.2] at h2
    exact Prod.ext (pt_eq_of w v hwv (h1.symm.trans h2) h) (he.2.trans he'.2.symm)
  simpa using this

lemma lineCard {r : ℕ} (w v : Fin r → Fin 2 → F) (hwv : ∀ i, det2 (w i) (v i) ≠ 0)
    (G : Fin r → F → Polynomial F) (f : (Fin 2 → F) → F) (S : Finset (Fin 2 → F))
    (l : Fin r × F) : (S.filter fun x => (x, l) ∈ E1 w v G f).card ≤ Fintype.card F := by
  have : (S.filter fun x => (x, l) ∈ E1 w v G f).card ≤ (Finset.univ : Finset F).card := by
    apply Finset.card_le_card_of_injOn (fun x => mu (w l.1) (v l.1) x)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    intro x hx x' hx' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hx'
    have h1 := (mem_E1.mp hx.2).1
    have h2 := (mem_E1.mp hx'.2).1
    exact pt_eq_of w v hwv (h1.symm.trans h2) h
  simpa using this

lemma card_E1_ge {r : ℕ} (w v : Fin r → Fin 2 → F) (G : Fin r → F → Polynomial F)
    (f : (Fin 2 → F) → F) :
    (∑ i, ((Finset.univ.filter fun x =>
        (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card : ℝ)) ≤
      (E1 w v G f).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun e => e.2.1) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  push_cast
  apply Finset.sum_le_sum
  intro i _
  norm_cast
  apply Finset.card_le_card_of_injOn (fun x => (x, (i, lam (w i) (v i) x)))
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
    simp [mem_E1, hx]
  · intro x _ y _ h
    exact (Prod.ext_iff.mp h).1

lemma card_prod_filter {α β : Type*} [DecidableEq α] [DecidableEq β] (A : Finset α) (B : Finset β) (E : Finset (α × β)) :
    ((A ×ˢ B).filter (· ∈ E)).card = ∑ a ∈ A, (B.filter fun b => (a, b) ∈ E).card := by
  rw [Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl fun a _ => (Finset.card_filter _ _).symm

lemma card_prod_filter' {α β : Type*} [DecidableEq α] [DecidableEq β] (A : Finset α) (B : Finset β) (E : Finset (α × β)) :
    ((A ×ˢ B).filter (· ∈ E)).card = ∑ b ∈ B, (A.filter fun a => (a, b) ∈ E).card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  exact Finset.sum_congr rfl fun a _ => (Finset.card_filter _ _).symm

lemma card_pts : ((Finset.univ : Finset (Fin 2 → F)).card : ℝ) = (Fintype.card F : ℝ) ^ 2 := by
  rw [Finset.card_univ, Fintype.card_fun]; simp

lemma card_lines {r : ℕ} :
    ((Finset.univ : Finset (Fin r × F)).card : ℝ) = (r : ℝ) * Fintype.card F := by
  rw [Finset.card_univ, Fintype.card_prod]; simp

lemma prune {r : ℕ} (w v : Fin r → Fin 2 → F) (hwv : ∀ i, det2 (w i) (v i) ≠ 0)
    (G : Fin r → F → Polynomial F) (f : (Fin 2 → F) → F)
    (E : Finset ((Fin 2 → F) × (Fin r × F))) (hE : E ⊆ E1 w v G f)
    (η : ℝ) (hη : 0 < η) (hr : 0 < r)
    (hEc : η * ((r : ℝ) * (Fintype.card F : ℝ) ^ 2) ≤ E.card) :
    ∃ P : Finset (Fin 2 → F), ∃ L : Finset (Fin r × F),
      4 * η / 5 * (Fintype.card F : ℝ) ^ 2 ≤ P.card ∧
      4 * η / 5 * ((r : ℝ) * Fintype.card F) ≤ L.card ∧
      (∀ x ∈ P, η * r / 10 ≤ ((L.filter fun l => (x, l) ∈ E).card : ℝ)) ∧
      (∀ l ∈ L, η * Fintype.card F / 10 ≤ ((P.filter fun x => (x, l) ∈ E).card : ℝ)) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hrq : (0 : ℝ) < r * (Fintype.card F : ℝ) ^ 2 := by positivity
  set η' := (E.card : ℝ) / (r * (Fintype.card F : ℝ) ^ 2) with hη'def
  have hη' : η ≤ η' := by rw [hη'def, le_div_iff₀ hrq]; linarith
  have hEq : (E.card : ℝ) = η' * r * (Fintype.card F : ℝ) ^ 2 := by
    rw [hη'def]; field_simp
  obtain ⟨P, -, L, -, h1, h2, h3, h4⟩ := DerandLDT.lemma_3_18 Finset.univ Finset.univ E
    (fun e _ => by simp) (r : ℝ) (Fintype.card F : ℝ) hr' hq
    (fun u _ => degU w v G f E hE u) (fun l _ => degV w v hwv G f E hE l) η' η'
    (by rw [card_pts, hEq]) (by rw [card_lines, hEq]; ring)
  rw [card_pts] at h1
  rw [card_lines] at h2
  refine ⟨P, L, le_trans ?_ h1, le_trans ?_ h2, fun x hx => le_trans ?_ (h3 x hx),
    fun l hl => le_trans ?_ (h4 l hl)⟩
  · gcongr
  · gcongr
  · gcongr
  · gcongr

lemma num_D {ε K D : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hD1 : 2000000 * K / ε ^ 4 ≤ D)
    (hD2 : D ≤ 2000000 * K / ε ^ 4 + 1) :
    2000000 * K ≤ D * ε ^ 4 ∧ D * ε ^ 4 ≤ 2000000 * K + 1 := by
  have h4 : 0 < ε ^ 4 := by positivity
  have h41 : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le hε1
  constructor
  · rwa [div_le_iff₀ h4] at hD1
  · have := mul_le_mul_of_nonneg_right hD2 h4.le
    rw [add_mul, div_mul_cancel₀ _ h4.ne'] at this
    linarith

lemma num_m {ε D m : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hm1 : 40000 * (D + 1) / ε ^ 4 ≤ m)
    (hm2 : m ≤ 40000 * (D + 1) / ε ^ 4 + 1) :
    40000 * (D + 1) ≤ m * ε ^ 4 ∧ m * ε ^ 4 ≤ 40000 * (D + 1) + 1 := by
  have h4 : 0 < ε ^ 4 := by positivity
  have h41 : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le hε1
  constructor
  · rwa [div_le_iff₀ h4] at hm1
  · have := mul_le_mul_of_nonneg_right hm2 h4.le
    rw [add_mul, div_mul_cancel₀ _ h4.ne'] at this
    linarith

lemma num_KD {ε K D : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (a1 : 2000000 * K ≤ D * ε ^ 4) : 2000000 * K ≤ D := by
  have h4 : 0 < ε ^ 4 := by positivity
  have h41 : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hD : 0 ≤ D := by
    by_contra h; push Not at h; nlinarith
  nlinarith

lemma num_interp {ε K D m : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (a1 : 2000000 * K ≤ D * ε ^ 4) (hm : m * ε ^ 4 ≤ 40000 * (D + 1) + 1) :
    (D + 1) * m < D ^ 3 / (12 * K) := by
  have h4 : 0 < ε ^ 4 := by positivity
  have hD := num_KD hε0 hε1 hK a1
  rw [lt_div_iff₀ (by linarith)]
  have k1 : (D + 1) * m * (12 * K) * ε ^ 4 ≤ (D + 1) * (12 * K) * (40000 * (D + 1) + 1) := by
    have : 0 ≤ (D + 1) * (12 * K) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have k2 : (D + 1) * (12 * K) * (40000 * (D + 1) + 1) < 2000000 * K * D ^ 2 := by
    have : 0 < K * (1520000 * D ^ 2 - 960012 * D - 480012) :=
      mul_pos (by linarith) (by nlinarith)
    nlinarith
  have k3 : 2000000 * K * D ^ 2 ≤ D ^ 3 * ε ^ 4 := by
    have : 0 ≤ D ^ 2 := by positivity
    nlinarith
  exact lt_of_mul_lt_mul_right (by linarith) h4.le

lemma num_sample1 {ε q r K D m d₀ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (hq : 10 ^ 21 * K ^ 2 ≤ q * ε ^ 12) (a2 : D * ε ^ 4 ≤ 2000000 * K + 1)
    (hm : m * ε ^ 4 ≤ 40000 * (D + 1) + 1) (hd0 : d₀ ≤ ε * r / 10) (hd00 : 0 ≤ d₀)
    (hm0 : 0 ≤ m) (hr : 0 ≤ r) :
    m * d₀ ≤ 4 * ε / 5 * (r * q) := by
  have h4 : 0 < ε ^ 4 := by positivity
  have h41 : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le hε1
  have h8 : 0 < ε ^ 8 := by positivity
  have hm8 : m * ε ^ 8 ≤ 81000000000 * K := by
    have e1 : m * ε ^ 8 = (m * ε ^ 4) * ε ^ 4 := by ring
    have e2 : (m * ε ^ 4) * ε ^ 4 ≤ (40000 * (D + 1) + 1) * ε ^ 4 :=
      mul_le_mul_of_nonneg_right hm h4.le
    have e3 : (40000 * (D + 1) + 1) * ε ^ 4 = 40000 * (D * ε ^ 4) + 40001 * ε ^ 4 := by ring
    nlinarith
  have hq9 : 10 ^ 21 * K ≤ q * ε ^ 9 := by
    have : q * ε ^ 12 ≤ q * ε ^ 9 := by
      have hq0 : 0 ≤ q := by
        by_contra h; push Not at h; nlinarith [pow_pos hε0 12]
      apply mul_le_mul_of_nonneg_left _ hq0
      exact pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
    nlinarith
  have hmq : m ≤ 4 * ε * q / 5 := by
    have : m * ε ^ 8 ≤ (4 * ε * q / 5) * ε ^ 8 := by
      have : (4 * ε * q / 5) * ε ^ 8 = 4 / 5 * (q * ε ^ 9) := by ring
      nlinarith
    exact le_of_mul_le_mul_right this h8
  have hdr : d₀ ≤ r := by nlinarith
  calc m * d₀ ≤ (4 * ε * q / 5) * r := mul_le_mul hmq hdr hd00 (by nlinarith)
    _ = _ := by ring

lemma num_sample2 {ε q r D m n₀ d₀ : ℝ} (hε0 : 0 < ε) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r) (hD : 0 ≤ D)
    (hm : 40000 * (D + 1) ≤ m * ε ^ 4) (hn0 : ε * q / 10 ≤ n₀) (hd0 : ε * r / 20 ≤ d₀) :
    200 * (D + 1) * q * r ≤ ε ^ 2 * (n₀ * m * d₀) := by
  have h1 : ε ^ 2 * q * r / 200 ≤ n₀ * d₀ := by
    calc ε ^ 2 * q * r / 200 = (ε * q / 10) * (ε * r / 20) := by ring
      _ ≤ n₀ * d₀ := mul_le_mul hn0 hd0 (by positivity) (by linarith [show 0 ≤ ε * q / 10 by positivity])
  have hm0 : 0 ≤ m := by
    have : 0 ≤ m * ε ^ 4 := by linarith
    by_contra h; push Not at h; nlinarith [pow_pos hε0 4]
  have : ε ^ 2 * (n₀ * m * d₀) = (n₀ * d₀) * ε ^ 2 * m := by ring
  rw [this]
  have h2 : ε ^ 2 * q * r / 200 * ε ^ 2 * m ≤ (n₀ * d₀) * ε ^ 2 * m := by
    apply mul_le_mul_of_nonneg_right _ hm0
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have h3 : ε ^ 2 * q * r / 200 * ε ^ 2 * m = q * r / 200 * (m * ε ^ 4) := by ring
  have h4 : q * r / 200 * (40000 * (D + 1)) ≤ q * r / 200 * (m * ε ^ 4) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  nlinarith

lemma num_bad {ε q r D X L b : ℝ} (hq : 0 < q) (hr : 0 < r) (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hX : 200 * (D + 1) * q * r ≤ ε ^ 2 * X) (hL0 : 0 ≤ L) (hL : L ≤ r * q)
    (hbX : b * X ≤ 8 * L ^ 2) : b ≤ ε ^ 2 * r * q / 25 := by
  have h1 : b * (200 * q * r) ≤ b * (ε ^ 2 * X) := by
    apply mul_le_mul_of_nonneg_left _ hb; nlinarith [mul_pos hq hr]
  have h2 : b * (ε ^ 2 * X) ≤ ε ^ 2 * (8 * (r * q) ^ 2) := by
    have : b * (ε ^ 2 * X) = ε ^ 2 * (b * X) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  rw [le_div_iff₀ (by norm_num)]
  have h3 : b * 25 * (200 * q * r) ≤ ε ^ 2 * r * q * (200 * q * r) := by nlinarith
  exact le_of_mul_le_mul_right h3 (by positivity)

lemma num_qpos {ε q K : ℝ} (hε0 : 0 < ε) (hK : 1 ≤ K) (hq : 10 ^ 21 * K ^ 2 ≤ q * ε ^ 12) :
    0 < q := by
  by_contra h; push Not at h
  have : q * ε ^ 12 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
  nlinarith

lemma num_rpos {ε r : ℝ} (hε0 : 0 < ε) (hr : 10 ^ 13 ≤ r * ε ^ 8) : 0 < r := by
  by_contra h; push Not at h
  have : r * ε ^ 8 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
  nlinarith

lemma num_f1 {ε q K D : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (hq : 10 ^ 21 * K ^ 2 ≤ q * ε ^ 12) (a2 : D * ε ^ 4 ≤ 2000000 * K + 1) :
    250 * D < ε ^ 2 * q := by
  have hq0 := num_qpos hε0 hK hq
  have h4 : 0 < ε ^ 4 := by positivity
  have h6 : ε ^ 12 ≤ ε ^ 6 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have : q * ε ^ 12 ≤ q * ε ^ 6 := mul_le_mul_of_nonneg_left h6 hq0.le
  have hKK : K ≤ K ^ 2 := by nlinarith
  have : 250 * D * ε ^ 4 < ε ^ 2 * q * ε ^ 4 := by
    have e : ε ^ 2 * q * ε ^ 4 = q * ε ^ 6 := by ring
    rw [e]; nlinarith
  exact lt_of_mul_lt_mul_right this h4.le

lemma num_f2 {ε r : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hr : 10 ^ 13 ≤ r * ε ^ 8) :
    10 ^ 13 ≤ ε ^ 2 * r := by
  have hr0 := num_rpos hε0 hr
  have h6 : ε ^ 8 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  nlinarith

lemma num_A {ε q r n₁ d₁ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hr : 10 ^ 13 ≤ r * ε ^ 8)
    (hq0 : 0 ≤ q) (hn : ε ^ 2 / 25 * q / 10 ≤ n₁) (hd : ε ^ 2 / 25 * r / 10 ≤ d₁) :
    ε ^ 4 * q * r / 125000 ≤ n₁ * (d₁ - 1) := by
  have h2 := num_f2 hε0 hε1 hr
  have hd' : ε ^ 2 * r / 500 ≤ d₁ - 1 := by linarith
  calc ε ^ 4 * q * r / 125000 = (ε ^ 2 / 25 * q / 10) * (ε ^ 2 * r / 500) := by ring
    _ ≤ n₁ * (d₁ - 1) := mul_le_mul hn hd' (by positivity)
        (le_trans (by positivity) hn)

lemma num_big1 {ε q r K D Dk : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (hr : 10 ^ 13 ≤ r * ε ^ 8) (hq0 : 0 < q) (a2 : D * ε ^ 4 ≤ 2000000 * K + 1)
    (hDk : Dk ≤ D / K) : 2 * q * (Dk + 1) < ε ^ 4 * q * r / 125000 := by
  have h4 : 0 < ε ^ 4 := by positivity
  have h41 : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hK0 : 0 < K := by linarith
  have hDK : D / K * ε ^ 4 ≤ 2000001 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK0]; nlinarith
  have h1 : 2 * (Dk + 1) * ε ^ 4 ≤ 4000004 := by nlinarith
  have h2 : 2 * (Dk + 1) * ε ^ 4 < ε ^ 4 * r / 125000 * ε ^ 4 := by
    have : ε ^ 4 * r / 125000 * ε ^ 4 = r * ε ^ 8 / 125000 := by ring
    rw [this]; linarith
  have h3 : 2 * (Dk + 1) < ε ^ 4 * r / 125000 := lt_of_mul_lt_mul_right h2 h4.le
  have : ε ^ 4 * q * r / 125000 = q * (ε ^ 4 * r / 125000) := by ring
  rw [this]; nlinarith

lemma num_big2 {ε q r K D : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (hq : 10 ^ 21 * K ^ 2 ≤ q * ε ^ 12) (hr0 : 0 ≤ r) (hD1 : 1 ≤ D)
    (a2 : D * ε ^ 4 ≤ 2000000 * K + 1) :
    2 * r * (12 * D ^ 2 + 2 * D) ≤ ε ^ 4 * q * r / 125000 := by
  have h4 : 0 < ε ^ 4 := by positivity
  have h8 : 0 < ε ^ 8 := by positivity
  have hDe : D * ε ^ 4 ≤ 3000000 * K := by linarith
  have hDe2 : (D * ε ^ 4) ^ 2 ≤ (3000000 * K) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hDe 2
  have h1 : 28 * D ^ 2 * ε ^ 8 ≤ ε ^ 4 * q / 125000 * ε ^ 8 := by
    have e1 : ε ^ 4 * q / 125000 * ε ^ 8 = q * ε ^ 12 / 125000 := by ring
    have e2 : 28 * D ^ 2 * ε ^ 8 = 28 * (D * ε ^ 4) ^ 2 := by ring
    rw [e1, e2]; nlinarith
  have h2 : 28 * D ^ 2 ≤ ε ^ 4 * q / 125000 := le_of_mul_le_mul_right h1 h8
  have h3 : 12 * D ^ 2 + 2 * D ≤ 14 * D ^ 2 := by nlinarith
  have : ε ^ 4 * q * r / 125000 = r * (ε ^ 4 * q / 125000) := by ring
  rw [this]; nlinarith

lemma num_out {ε q r n₁ A ag : ℝ} (hε0 : 0 < ε) (hq0 : 0 ≤ q) (hr0 : 0 < r)
    (hn : ε ^ 2 / 25 * q / 10 ≤ n₁) (hA : ε ^ 4 * q * r / 125000 ≤ A)
    (h : n₁ * A ≤ 4 * r * ag) : ε ^ 6 / 10 ^ 9 * q ^ 2 ≤ ag := by
  have h1 : (ε ^ 2 / 25 * q / 10) * (ε ^ 4 * q * r / 125000) ≤ n₁ * A :=
    mul_le_mul hn hA (by positivity) (le_trans (by positivity) hn)
  have h2 : ε ^ 6 / 10 ^ 9 * q ^ 2 * (4 * r) ≤ ag * (4 * r) := by
    have : ε ^ 6 / 10 ^ 9 * q ^ 2 * (4 * r) ≤ (ε ^ 2 / 25 * q / 10) * (ε ^ 4 * q * r / 125000) := by
      have : (ε ^ 2 / 25 * q / 10) * (ε ^ 4 * q * r / 125000) =
          ε ^ 6 / 10 ^ 9 * q ^ 2 * (4 * r) * (10 ^ 9 / (4 * 31250000)) := by ring
      rw [this]
      have : 0 ≤ ε ^ 6 / 10 ^ 9 * q ^ 2 * (4 * r) := by positivity
      nlinarith
    linarith
  exact le_of_mul_le_mul_right h2 (by positivity)

lemma sample {r : ℕ} (w v : Fin r → Fin 2 → F) (hwv : ∀ i, det2 (w i) (v i) ≠ 0)
    (hvv : ∀ i j, i ≠ j → det2 (v i) (v j) ≠ 0) (G : Fin r → F → Polynomial F)
    (f : (Fin 2 → F) → F)
    (P' : Finset (Fin 2 → F)) (L' : Finset (Fin r × F)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (K : ℕ) (hK : 1 ≤ K)
    (hr : 10 ^ 13 ≤ (r : ℝ) * ε ^ 8)
    (hq : 10 ^ 21 * (K : ℝ) ^ 2 ≤ (Fintype.card F : ℝ) * ε ^ 12)
    (hL'c : 4 * ε / 5 * ((r : ℝ) * Fintype.card F) ≤ L'.card)
    (hP'd : ∀ x ∈ P', ε * r / 10 ≤ ((L'.filter fun l => (x, l) ∈ E1 w v G f).card : ℝ))
    (hL'd : ∀ l ∈ L', ε * Fintype.card F / 10 ≤
      ((P'.filter fun x => (x, l) ∈ E1 w v G f).card : ℝ))
    (D m : ℕ) (a2 : (D : ℝ) * ε ^ 4 ≤ 2000000 * K + 1)
    (hm1 : 40000 * ((D : ℝ) + 1) ≤ m * ε ^ 4)
    (hm2 : (m : ℝ) * ε ^ 4 ≤ 40000 * ((D : ℝ) + 1) + 1) :
    ∃ ω : Fin m → Fin r × F, (∀ t, ω t ∈ L') ∧
      ((L'.filter fun l => ((P'.filter fun x => (x, l) ∈ E1 w v G f).filter fun x =>
        ∃ t, ω t ∈ (L'.filter fun l'' => (x, l'') ∈ E1 w v G f).erase l).card ≤ D).card : ℝ) ≤
        ε ^ 2 * r * Fintype.card F / 25 := by
  set q := Fintype.card F with hqdef
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hq0 : (0 : ℝ) < q := num_qpos hε0 hKr hq
  have hr0 : (0 : ℝ) < r := num_rpos hε0 hr
  set n₀ := ⌈ε * q / 10⌉₊ with hn₀
  set d₀ := ⌈ε * r / 10⌉₊ - 1 with hd₀
  have hn0 : ε * q / 10 ≤ n₀ := Nat.le_ceil _
  have hεr : 20 ≤ ε * r := by
    have h8 : ε ^ 8 ≤ ε := by
      calc ε ^ 8 ≤ ε ^ 1 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
        _ = ε := pow_one ε
    nlinarith
  have hc1 : 1 ≤ ⌈ε * r / 10⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  have hd0R : (d₀ : ℝ) = (⌈ε * r / 10⌉₊ : ℝ) - 1 := by rw [hd₀, Nat.cast_sub hc1]; simp
  have hd0a : ε * r / 20 ≤ d₀ := by
    rw [hd0R]; have := Nat.le_ceil (ε * r / 10); linarith
  have hd0b : (d₀ : ℝ) ≤ ε * r / 10 := by
    rw [hd0R]; have := Nat.ceil_lt_add_one (show 0 ≤ ε * r / 10 by positivity); linarith
  have hLle : (L'.card : ℝ) ≤ r * q := by
    rw [← card_lines]; exact_mod_cast Finset.card_le_univ L'
  have hLne : L'.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < L'.card := lt_of_lt_of_le (by positivity) hL'c
    exact_mod_cast this
  have hX := num_sample2 (D := (D : ℝ)) (m := (m : ℝ)) hε0 hq0.le hr0.le (Nat.cast_nonneg _)
    hm1 hn0 hd0a
  obtain ⟨ω, hω, hineq⟩ := DLT.sampling L' hLne
    (fun l => P'.filter fun x => (x, l) ∈ E1 w v G f)
    (fun l x => (L'.filter fun l'' => (x, l'') ∈ E1 w v G f).erase l)
    (fun l _ x _ => (Finset.erase_subset _ _).trans (Finset.filter_subset _ _))
    (by
      intro l _ x hx x' hx' hxx'
      rw [Finset.disjoint_left]
      intro l'' h1 h2
      simp only [Finset.mem_erase, Finset.mem_filter] at h1 h2 hx hx'
      have a1 := (mem_E1.mp hx.2).1
      have a2 := (mem_E1.mp hx'.2).1
      have a3 := (mem_E1.mp h1.2.2).1
      have a4 := (mem_E1.mp h2.2.2).1
      have hi : l.1 = l''.1 := two_lines w v hwv hvv hxx' (a1.symm.trans a2) (a3.symm.trans a4)
      apply h1.1
      refine (Prod.ext hi.symm ?_)
      rw [a3, a1, hi])
    n₀ d₀ m D
    (fun l hl => Nat.ceil_le.mpr (hL'd l hl))
    (by
      intro l _ x hx
      simp only [Finset.mem_filter] at hx
      have h1 : ⌈ε * r / 10⌉₊ ≤ (L'.filter fun l'' => (x, l'') ∈ E1 w v G f).card :=
        Nat.ceil_le.mpr (hP'd x hx.1)
      have h2 := Finset.pred_card_le_card_erase (s := L'.filter fun l'' => (x, l'') ∈ E1 w v G f)
        (a := l)
      omega)
    (by
      have := num_sample1 (q := (q : ℝ)) (r := (r : ℝ)) (m := (m : ℝ)) hε0 hε1 hKr hq a2 hm2
        hd0b (Nat.cast_nonneg _) (Nat.cast_nonneg _) hr0.le
      exact_mod_cast this.trans hL'c)
    (by
      have h1 : (4 * (D + 1) * L'.card : ℝ) ≤ n₀ * m * d₀ := by
        have e2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
        have hX0 : (0 : ℝ) ≤ n₀ * m * d₀ := by positivity
        have : (4 * (D + 1) * L'.card : ℝ) ≤ 4 * (D + 1) * (r * q) := by
          apply mul_le_mul_of_nonneg_left hLle; positivity
        nlinarith
      exact_mod_cast h1)
  refine ⟨ω, hω, ?_⟩
  push_cast at hineq
  exact num_bad hq0 hr0 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hX (Nat.cast_nonneg _) hLle hineq

lemma interp {r : ℕ} (w v : Fin r → Fin 2 → F) (G : Fin r → F → Polynomial F) (k : ℕ)
    (hG : ∀ i a, (G i a).natDegree ≤ k) (K D m : ℕ) (hkK : k ≤ K) (hK : 1 ≤ K)
    (hKD : 20 * K < D) (hnum : ((D : ℝ) + 1) * m < (D : ℝ) ^ 3 / (12 * K))
    (ω : Fin m → Fin r × F) :
    ∃ Q₀ : Polynomial (MvPolynomial (Fin 2) F), Q₀ ≠ 0 ∧ WDeg K D Q₀ ∧
      ∀ t, restrictLine ((ω t).2 • w (ω t).1) (v (ω t).1) (G (ω t).1 (ω t).2) Q₀ = 0 := by
  obtain ⟨Q, hQ, hW, hS⟩ := interpolate (F := F) K D (Finset.univ.image ω)
    (fun l => l.2 • w l.1) (fun l => v l.1) (fun l => G l.1 l.2)
    (fun l _ => (hG _ _).trans hkK) (by
      have h1 := DerandLDT.lemma_3_2_ii 2 K D hK hKD le_rfl
      have h2 : (Finset.univ.image ω).card ≤ m := by
        calc _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
          _ = m := by simp
      have h3 : ((Finset.range (D + 1) ×ˢ Finset.range (D + 1) ×ˢ Finset.range (D + 1)).filter
          fun m : ℕ × ℕ × ℕ => m.1 + m.2.1 + K * m.2.2 ≤ D ∧ (m.2.2 = 0 ∨ ¬ 2 ∣ m.2.2)).card ≤
          ((Finset.range (D + 1) ×ˢ Finset.range (D + 1) ×ˢ Finset.range (D + 1)).filter
          fun m : ℕ × ℕ × ℕ => m.1 + m.2.1 + K * m.2.2 ≤ D).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, hx.2.1⟩
      have h2' : ((D : ℝ) + 1) * ((Finset.univ.image ω).card : ℝ) ≤ ((D : ℝ) + 1) * m := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); exact_mod_cast h2
      have h3' := (Nat.cast_le (α := ℝ)).mpr h3
      have : (((D + 1) * (Finset.univ.image ω).card : ℕ) : ℝ) <
          (((Finset.range (D + 1) ×ˢ Finset.range (D + 1) ×ˢ Finset.range (D + 1)).filter
          fun m : ℕ × ℕ × ℕ => m.1 + m.2.1 + K * m.2.2 ≤ D).card : ℝ) := by
        push_cast; linarith
      exact_mod_cast this)
  exact ⟨Q, hQ, hW, fun t => hS (ω t) (Finset.mem_image_of_mem ω (Finset.mem_univ t))⟩

lemma vanish {r : ℕ} (w v : Fin r → Fin 2 → F) (hwv : ∀ i, det2 (w i) (v i) ≠ 0)
    (G : Fin r → F → Polynomial F) (k : ℕ) (hG : ∀ i a, (G i a).natDegree ≤ k)
    (f : (Fin 2 → F) → F) (K D : ℕ) (hkK : k ≤ K)
    (Q₀ : Polynomial (MvPolynomial (Fin 2) F)) (hW : WDeg K D Q₀) {m : ℕ}
    (ω : Fin m → Fin r × F)
    (hω : ∀ t, restrictLine ((ω t).2 • w (ω t).1) (v (ω t).1) (G (ω t).1 (ω t).2) Q₀ = 0)
    (P' : Finset (Fin 2 → F)) (L' : Finset (Fin r × F)) (l : Fin r × F)
    (hl : D < ((P'.filter fun x => (x, l) ∈ E1 w v G f).filter fun x =>
        ∃ t, ω t ∈ (L'.filter fun l'' => (x, l'') ∈ E1 w v G f).erase l).card) :
    restrictLine (l.2 • w l.1) (v l.1) ((G l.1 l.2) ^ 1) Q₀ = 0 := by
  rw [pow_one]
  apply restrict_eq_zero_of_many w v hwv l.1 l.2 (G l.1 l.2) D Q₀
    (restrictLine_natDegree_le K D _ _ _ _ hW ((hG _ _).trans hkK)) _ _ _ hl
  · intro x hx
    simp only [Finset.mem_filter] at hx
    exact (mem_E1.mp hx.1.2).1.symm
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_erase] at hx
    obtain ⟨⟨_, hxl⟩, t, _, _, hxt⟩ := hx
    rw [(mem_E1.mp hxl).2]
    obtain ⟨hb, hacc⟩ := mem_E1.mp hxt
    have h0 := congrArg (Polynomial.eval (mu (w (ω t).1) (v (ω t).1) x)) (hω t)
    rw [restrictLine_eval, eval_zero, hacc, hb, ← decomp (hwv _) x] at h0
    exact h0

lemma e2card {r : ℕ} (w v : Fin r → Fin 2 → F) (hwv : ∀ i, det2 (w i) (v i) ≠ 0)
    (G : Fin r → F → Polynomial F) (f : (Fin 2 → F) → F)
    (P' : Finset (Fin 2 → F)) (L' Good bad : Finset (Fin r × F))
    (hsplit : ∀ l ∈ L', l ∈ Good ∨ l ∈ bad) (ε : ℝ) (hε0 : 0 < ε)
    (hP'c : 4 * ε / 5 * (Fintype.card F : ℝ) ^ 2 ≤ P'.card)
    (hP'd : ∀ x ∈ P', ε * r / 10 ≤ ((L'.filter fun l => (x, l) ∈ E1 w v G f).card : ℝ))
    (hbad : (bad.card : ℝ) ≤ ε ^ 2 * r * Fintype.card F / 25) :
    ε ^ 2 / 25 * ((r : ℝ) * (Fintype.card F : ℝ) ^ 2) ≤
      ((P' ×ˢ Good).filter (· ∈ E1 w v G f)).card := by
  set q := Fintype.card F
  have h1 : (P' ×ˢ L').filter (· ∈ E1 w v G f) ⊆
      (P' ×ˢ Good).filter (· ∈ E1 w v G f) ∪ (P' ×ˢ bad).filter (· ∈ E1 w v G f) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union] at he ⊢
    rcases hsplit _ he.1.2 with h | h
    · exact Or.inl ⟨⟨he.1.1, h⟩, he.2⟩
    · exact Or.inr ⟨⟨he.1.1, h⟩, he.2⟩
  have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
  have h3 : (P'.card : ℝ) * (ε * r / 10) ≤ ((P' ×ˢ L').filter (· ∈ E1 w v G f)).card := by
    rw [card_prod_filter]; push_cast
    calc (P'.card : ℝ) * (ε * r / 10) = ∑ x ∈ P', ε * r / 10 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hP'd
  have h4 : ((P' ×ˢ bad).filter (· ∈ E1 w v G f)).card ≤ bad.card * q := by
    rw [card_prod_filter']
    calc _ ≤ ∑ l ∈ bad, q := Finset.sum_le_sum fun l _ => lineCard w v hwv G f P' l
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  have h2' := (Nat.cast_le (α := ℝ)).mpr h2
  have h4' := (Nat.cast_le (α := ℝ)).mpr h4
  push_cast at h2' h4'
  have h5 : 4 * ε / 5 * (q : ℝ) ^ 2 * (ε * r / 10) ≤ (P'.card : ℝ) * (ε * r / 10) :=
    mul_le_mul_of_nonneg_right hP'c (by positivity)
  have h6 : (bad.card : ℝ) * q ≤ ε ^ 2 * r * q / 25 * q :=
    mul_le_mul_of_nonneg_right hbad (by positivity)
  nlinarith

set_option maxHeartbeats 1000000 in
lemma final (p : ℕ) [Fact p.Prime] [CharP F p] {r : ℕ} (w v : Fin r → Fin 2 → F)
    (hwv : ∀ i, det2 (w i) (v i) ≠ 0) (hvv : ∀ i j, i ≠ j → det2 (v i) (v j) ≠ 0)
    (G : Fin r → F → Polynomial F) (k : ℕ) (hG : ∀ i a, (G i a).natDegree ≤ k)
    (f : (Fin 2 → F) → F) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hr : 10 ^ 13 ≤ (r : ℝ) * ε ^ 8)
    (hq : 10 ^ 21 * ((k : ℝ) + 1) ^ 2 ≤ (Fintype.card F : ℝ) * ε ^ 12)
    (D : ℕ) (a2 : (D : ℝ) * ε ^ 4 ≤ 2000000 * ((k : ℝ) + 1) + 1) (hD1 : 1 ≤ D)
    (E : Finset ((Fin 2 → F) × (Fin r × F))) (hE : E ⊆ E1 w v G f)
    (P2 : Finset (Fin 2 → F)) (L2 : Finset (Fin r × F))
    (hP2c : 4 * (ε ^ 2 / 25) / 5 * (Fintype.card F : ℝ) ^ 2 ≤ P2.card)
    (hP2d : ∀ x ∈ P2, ε ^ 2 / 25 * r / 10 ≤ ((L2.filter fun l => (x, l) ∈ E).card : ℝ))
    (hL2d : ∀ l ∈ L2, ε ^ 2 / 25 * Fintype.card F / 10 ≤
      ((P2.filter fun x => (x, l) ∈ E).card : ℝ))
    (Q₀ : Polynomial (MvPolynomial (Fin 2) F)) (hQ₀ : Q₀ ≠ 0) (hW : WDeg (k + 1) D Q₀)
    (hV : VanishOn w v G L2 1 Q₀) :
    ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ 2 * k ∧
      ε ^ 6 / 10 ^ 9 * (Fintype.card F : ℝ) ^ 2 ≤
        ((Finset.univ.filter fun x => MvPolynomial.eval x Q = f x).card : ℝ) := by
  set q := Fintype.card F with hqdef
  have hKr : (1 : ℝ) ≤ (k : ℝ) + 1 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hq0 : (0 : ℝ) < q := num_qpos hε0 hKr hq
  have hr0 : (0 : ℝ) < r := num_rpos hε0 hr
  set n₁ := ⌈ε ^ 2 / 25 * (q : ℝ) / 10⌉₊ with hn₁
  set d₁ := ⌈ε ^ 2 / 25 * (r : ℝ) / 10⌉₊ with hd₁
  have hn1 : ε ^ 2 / 25 * (q : ℝ) / 10 ≤ n₁ := Nat.le_ceil _
  have hd1 : ε ^ 2 / 25 * (r : ℝ) / 10 ≤ d₁ := Nat.le_ceil _
  have f1 := num_f1 (D := (D : ℝ)) hε0 hε1 hKr hq a2
  have f2 := num_f2 hε0 hε1 hr
  have hd12 : 2 ≤ d₁ := Nat.lt_ceil.mpr (by push_cast; linarith)
  have hdsub : ((d₁ - 1 : ℕ) : ℝ) = (d₁ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hA := num_A hε0 hε1 hr hq0.le hn1 hd1
  obtain ⟨Qf, hdeg, hineq⟩ := he_core p w v hwv hvv G k hG f (k + 1) D (by omega) (by omega) P2 L2
    (fun x j => x ∈ P2 ∧ (j, lam (w j) (v j) x) ∈ L2 ∧ (x, (j, lam (w j) (v j) x)) ∈ E)
    (by
      intro x j ⟨hx, hl, he⟩
      exact ⟨hx, hl, by simpa using (mem_E1.mp (hE he)).2⟩)
    n₁ d₁
    (by
      intro x hx
      refine (Nat.ceil_le.mpr (hP2d x hx)).trans ?_
      apply Finset.card_le_card_of_injOn (fun l => l.1)
      · intro l hl
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hl
        have hl2 : l.2 = lam (w l.1) (v l.1) x := (mem_E1.mp (hE hl.2)).1
        have hl' : (l.1, lam (w l.1) (v l.1) x) = l := Prod.ext rfl hl2.symm
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        rw [hl']
        exact ⟨hx, hl.1, hl.2⟩
      · intro l hl l' hl' h
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hl hl'
        have a1 : l.2 = lam (w l.1) (v l.1) x := (mem_E1.mp (hE hl.2)).1
        have a2 : l'.2 = lam (w l'.1) (v l'.1) x := (mem_E1.mp (hE hl'.2)).1
        simp only at h
        refine Prod.ext h ?_
        rw [a1, a2, h])
    (by
      intro l hl
      refine (Nat.ceil_le.mpr (hL2d l hl)).trans (Finset.card_le_card ?_)
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hl2 : l.2 = lam (w l.1) (v l.1) x := (mem_E1.mp (hE hx.2)).1
      have hl' : (l.1, lam (w l.1) (v l.1) x) = l := Prod.ext rfl hl2.symm
      rw [hl']
      exact ⟨hl2.symm, hx.1, hl, hx.2⟩)
    (by
      have : (D : ℝ) < n₁ := by linarith
      exact_mod_cast this)
    hd12
    (by
      have : (D : ℝ) * q < P2.card := by
        have : (D : ℝ) * q < ε ^ 2 / 250 * q * q := by
          apply mul_lt_mul_of_pos_right _ hq0; linarith
        nlinarith
      exact_mod_cast this)
    (by
      have hDk : (((D / (k + 1) : ℕ)) : ℝ) ≤ (D : ℝ) / ((k : ℝ) + 1) := by
        have := Nat.cast_div_le (α := ℝ) (m := D) (n := k + 1); push_cast at this; exact this
      have := num_big1 hε0 hε1 hKr hr hq0 a2 hDk
      have : ((2 * q * (D / (k + 1) + 1) : ℕ) : ℝ) < ((n₁ * (d₁ - 1) : ℕ) : ℝ) := by
        push_cast; rw [hdsub]; linarith
      exact_mod_cast this)
    (by
      have := num_big2 (D := (D : ℝ)) hε0 hε1 hKr hq hr0.le (by exact_mod_cast hD1) a2
      have : ((2 * r * (12 * D ^ 2 + 2 * D) : ℕ) : ℝ) ≤ ((n₁ * (d₁ - 1) : ℕ) : ℝ) := by
        push_cast; rw [hdsub]; linarith
      exact_mod_cast this)
    Q₀ hQ₀ hW hV
  refine ⟨Qf, hdeg, ?_⟩
  have h := (Nat.cast_le (α := ℝ)).mpr hineq
  push_cast at h
  rw [hdsub] at h
  exact num_out hε0 hq0.le hr0 hn1 hA h

end HM

open Classical in
theorem he_main {F : Type*} [Field F] [Fintype F] [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {r : ℕ} (w v : Fin r → Fin 2 → F) (hwv : ∀ i, det2 (w i) (v i) ≠ 0)
    (hvv : ∀ i j, i ≠ j → det2 (v i) (v j) ≠ 0)
    (G : Fin r → F → Polynomial F) (k : ℕ) (hG : ∀ i a, (G i a).natDegree ≤ k)
    (f : (Fin 2 → F) → F) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hacc : ε * ((r : ℝ) * (Fintype.card F : ℝ) ^ 2) ≤
      ∑ i, ((Finset.univ.filter fun x =>
        (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card : ℝ))
    (hr : 10 ^ 13 ≤ (r : ℝ) * ε ^ 8)
    (hq : 10 ^ 21 * ((k : ℝ) + 1) ^ 2 ≤ (Fintype.card F : ℝ) * ε ^ 12) :
    ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ 2 * k ∧
      ε ^ 6 / 10 ^ 9 * (Fintype.card F : ℝ) ^ 2 ≤
        ((Finset.univ.filter fun x => MvPolynomial.eval x Q = f x).card : ℝ) := by
  have hKr : (1 : ℝ) ≤ (k : ℝ) + 1 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hr0 : (0 : ℝ) < r := HM.num_rpos hε0 hr
  have hrN : 0 < r := by exact_mod_cast hr0
  have hε4 : 0 < ε ^ 4 := by positivity
  -- first pruning
  have hE1c : ε * ((r : ℝ) * (Fintype.card F : ℝ) ^ 2) ≤ (HM.E1 w v G f).card :=
    hacc.trans (HM.card_E1_ge w v G f)
  obtain ⟨P', L', hP'c, hL'c, hP'd, hL'd⟩ :=
    HM.prune w v hwv G f _ subset_rfl ε hε0 hrN hE1c
  -- parameters
  set D := ⌈2000000 * ((k : ℝ) + 1) / ε ^ 4⌉₊ with hD
  obtain ⟨a1, a2⟩ := HM.num_D (D := (D : ℝ)) hε0 hε1 (Nat.le_ceil _)
    (Nat.ceil_lt_add_one (by positivity)).le
  set m := ⌈40000 * ((D : ℝ) + 1) / ε ^ 4⌉₊ with hm
  obtain ⟨m1, m2⟩ := HM.num_m (m := (m : ℝ)) hε0 hε1 (Nat.le_ceil _)
    (Nat.ceil_lt_add_one (by positivity)).le
  have hKD := HM.num_KD hε0 hε1 hKr a1
  have hD1 : 1 ≤ D := by
    have : (1 : ℝ) ≤ D := by linarith
    exact_mod_cast this
  -- sampling
  obtain ⟨ω, -, hbad⟩ := HM.sample w v hwv hvv G f P' L' ε hε0 hε1 (k + 1) (by omega) hr
    (by push_cast; exact hq) hL'c hP'd hL'd D m (by push_cast; exact a2) m1 m2
  -- interpolation
  obtain ⟨Q₀, hQ₀, hW, hωv⟩ := HM.interp w v G k hG (k + 1) D m (by omega) (by omega)
    (by
      have : (20 * ((k : ℝ) + 1)) < D := by linarith
      exact_mod_cast this)
    (by push_cast; exact HM.num_interp hε0 hε1 hKr a1 m2) ω
  -- good and bad lines
  set bad := L'.filter fun l => ((P'.filter fun x => (x, l) ∈ HM.E1 w v G f).filter fun x =>
    ∃ t, ω t ∈ (L'.filter fun l'' => (x, l'') ∈ HM.E1 w v G f).erase l).card ≤ D with hbad_def
  set Good := L'.filter fun l => ¬ (((P'.filter fun x => (x, l) ∈ HM.E1 w v G f).filter fun x =>
    ∃ t, ω t ∈ (L'.filter fun l'' => (x, l'') ∈ HM.E1 w v G f).erase l).card ≤ D) with hGood
  have hsplit : ∀ l ∈ L', l ∈ Good ∨ l ∈ bad := by
    intro l hl
    by_cases h : ((P'.filter fun x => (x, l) ∈ HM.E1 w v G f).filter fun x =>
      ∃ t, ω t ∈ (L'.filter fun l'' => (x, l'') ∈ HM.E1 w v G f).erase l).card ≤ D
    · exact Or.inr (Finset.mem_filter.mpr ⟨hl, h⟩)
    · exact Or.inl (Finset.mem_filter.mpr ⟨hl, h⟩)
  have hE2c := HM.e2card w v hwv G f P' L' Good bad hsplit ε hε0 hP'c hP'd hbad
  set E₂ := (P' ×ˢ Good).filter (· ∈ HM.E1 w v G f) with hE₂
  have hE₂sub : E₂ ⊆ HM.E1 w v G f := fun e he => (Finset.mem_filter.mp he).2
  -- second pruning
  obtain ⟨P2, L2, hP2c, -, hP2d, hL2d⟩ :=
    HM.prune w v hwv G f E₂ hE₂sub (ε ^ 2 / 25) (by positivity) hrN hE2c
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hL2G : ∀ l ∈ L2, l ∈ Good := by
    intro l hl
    have h := hL2d l hl
    have hpos : 0 < (P2.filter fun x => (x, l) ∈ E₂).card := by
      have : (0 : ℝ) < ((P2.filter fun x => (x, l) ∈ E₂).card : ℝ) :=
        lt_of_lt_of_le (by positivity) h
      exact_mod_cast this
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    have := (Finset.mem_filter.mp hx).2
    exact (Finset.mem_product.mp (Finset.mem_filter.mp this).1).2
  have hV : VanishOn w v G L2 1 Q₀ := by
    intro l hl
    have hg := hL2G l hl
    rw [hGood, Finset.mem_filter] at hg
    exact HM.vanish w v hwv G k hG f (k + 1) D (by omega) Q₀ hW ω hωv P' L' l
      (lt_of_not_ge hg.2)
  exact HM.final p w v hwv hvv G k hG f ε hε0 hε1 hr hq D a2 hD1 E₂ hE₂sub P2 L2 hP2c hP2d hL2d
    Q₀ hQ₀ hW hV

end DLT

end Part12

section Part13
open Polynomial

namespace DLT.L3

section Subst
variable {F : Type*} [Field F]

/-- The linear form `x ↦ lam w v x` as a multivariate polynomial. -/
noncomputable def lform (w v : Fin 2 → F) : MvPolynomial (Fin 2) F :=
  MvPolynomial.C (v 1 / det2 w v) * MvPolynomial.X 0 -
    MvPolynomial.C (v 0 / det2 w v) * MvPolynomial.X 1

lemma eval_lform (w v x : Fin 2 → F) : MvPolynomial.eval x (lform w v) = lam w v x := by
  simp only [lform, map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, lam, det2]
  ring

lemma totalDegree_lform (w v : Fin 2 → F) : (lform w v).totalDegree ≤ 1 := by
  unfold lform
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_) <;>
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

lemma totalDegree_eval₂_le (ℓ : MvPolynomial (Fin 2) F) (hℓ : ℓ.totalDegree ≤ 1) (p : F[X]) :
    (p.eval₂ MvPolynomial.C ℓ).totalDegree ≤ p.natDegree := by
  rw [eval₂_eq_sum_range]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun n hn => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  have := Finset.mem_range.mp hn
  nlinarith

/-- Substitute `ℓ₁` for the inner and `ℓ₂` for the outer variable. -/
noncomputable def subst (ℓ₁ ℓ₂ : MvPolynomial (Fin 2) F) (P : F[X][X]) : MvPolynomial (Fin 2) F :=
  P.eval₂ (Polynomial.eval₂RingHom MvPolynomial.C ℓ₁) ℓ₂

lemma eval_subst (ℓ₁ ℓ₂ : MvPolynomial (Fin 2) F) (P : F[X][X]) (x : Fin 2 → F) :
    MvPolynomial.eval x (subst ℓ₁ ℓ₂ P) =
      (P.eval (C (MvPolynomial.eval x ℓ₂))).eval (MvPolynomial.eval x ℓ₁) := by
  unfold subst
  rw [Polynomial.hom_eval₂, ← DLT.L2.ev_row, eval_map]
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_ <;> simp

lemma totalDegree_subst (ℓ₁ ℓ₂ : MvPolynomial (Fin 2) F) (h1 : ℓ₁.totalDegree ≤ 1)
    (h2 : ℓ₂.totalDegree ≤ 1) (P : F[X][X]) (k : ℕ) (hP : P.natDegree ≤ k)
    (hc : ∀ n, (P.coeff n).natDegree ≤ k) : (subst ℓ₁ ℓ₂ P).totalDegree ≤ 2 * k := by
  unfold subst
  rw [eval₂_eq_sum_range]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun n hn => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h3 := totalDegree_eval₂_le ℓ₁ h1 (P.coeff n)
  have h4 := MvPolynomial.totalDegree_pow ℓ₂ n
  have h5 := Finset.mem_range.mp hn
  have h6 := hc n
  rw [coe_eval₂RingHom]
  nlinarith

end Subst

section Coords
variable {F : Type*} [Field F]

/-- Inverse of `x ↦ (lam w1 v1 x, lam w2 v2 x)`. -/
noncomputable def psi (w1 v1 w2 v2 : Fin 2 → F) (st : F × F) : Fin 2 → F :=
  (st.1 * (det2 w1 v1 / det2 v2 v1)) • v2 + (st.2 * (det2 w2 v2 / det2 v1 v2)) • v1

lemma lam_psi (w1 v1 w2 v2 w v : Fin 2 → F) (st : F × F) :
    lam w v (psi w1 v1 w2 v2 st) = st.1 * ((det2 w1 v1 / det2 v2 v1) * lam w v v2) +
      st.2 * ((det2 w2 v2 / det2 v1 v2) * lam w v v1) := by
  simp only [psi, lam_add, lam_smul]; ring

lemma mu_psi (w1 v1 w2 v2 w v : Fin 2 → F) (st : F × F) :
    mu w v (psi w1 v1 w2 v2 st) = st.1 * ((det2 w1 v1 / det2 v2 v1) * mu w v v2) +
      st.2 * ((det2 w2 v2 / det2 v1 v2) * mu w v v1) := by
  simp only [psi, mu_add, mu_smul]; ring

variable {w1 v1 w2 v2 : Fin 2 → F}

lemma lam1_psi (h1 : det2 w1 v1 ≠ 0) (h12 : det2 v1 v2 ≠ 0) (st : F × F) :
    lam w1 v1 (psi w1 v1 w2 v2 st) = st.1 := by
  have h21 : det2 v2 v1 ≠ 0 := by rw [det2_comm]; exact neg_ne_zero.mpr h12
  rw [lam_psi, lam_v, mul_zero, mul_zero, add_zero]
  simp only [lam]
  field_simp

lemma lam2_psi (h2 : det2 w2 v2 ≠ 0) (h12 : det2 v1 v2 ≠ 0) (st : F × F) :
    lam w2 v2 (psi w1 v1 w2 v2 st) = st.2 := by
  rw [lam_psi, lam_v, mul_zero, mul_zero, zero_add]
  simp only [lam]
  field_simp

lemma psi_lam (h1 : det2 w1 v1 ≠ 0) (h2 : det2 w2 v2 ≠ 0) (h12 : det2 v1 v2 ≠ 0)
    (x : Fin 2 → F) : psi w1 v1 w2 v2 (lam w1 v1 x, lam w2 v2 x) = x := by
  have h21 : det2 v2 v1 ≠ 0 := by rw [det2_comm]; exact neg_ne_zero.mpr h12
  have key : ∀ i, det2 x v2 * v1 i - det2 x v1 * v2 i = x i * det2 v1 v2 := by
    intro i; fin_cases i <;> simp [det2] <;> ring
  funext i
  simp only [psi, lam, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [det2_comm v2 v1]
  have h21' : det2 v1 v2 ≠ 0 := h12
  field_simp
  linear_combination key i

/-- The coordinate change `x ↦ (lam₁ x, lam₂ x)`. -/
noncomputable def coordEquiv (h1 : det2 w1 v1 ≠ 0) (h2 : det2 w2 v2 ≠ 0) (h12 : det2 v1 v2 ≠ 0) :
    (Fin 2 → F) ≃ F × F where
  toFun x := (lam w1 v1 x, lam w2 v2 x)
  invFun := psi w1 v1 w2 v2
  left_inv := psi_lam h1 h2 h12
  right_inv st := Prod.ext (lam1_psi h1 h12 st) (lam2_psi h2 h12 st)

lemma card_filter_psi [Fintype F] (h1 : det2 w1 v1 ≠ 0) (h2 : det2 w2 v2 ≠ 0)
    (h12 : det2 v1 v2 ≠ 0) (p : (Fin 2 → F) → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = (Finset.univ.filter fun st => p (psi w1 v1 w2 v2 st)).card := by
  classical
  refine Finset.card_equiv (coordEquiv h1 h2 h12) (fun x => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change p x ↔ p (psi w1 v1 w2 v2 (lam w1 v1 x, lam w2 v2 x))
  rw [psi_lam h1 h2 h12]

end Coords

section Pair
variable {F : Type*} [Field F]

lemma rows_cols_of_pair (k : ℕ) {w1 v1 w2 v2 : Fin 2 → F} (h1 : det2 w1 v1 ≠ 0)
    (h2 : det2 w2 v2 ≠ 0) (h12 : det2 v1 v2 ≠ 0) (G1 G2 : F → F[X])
    (hG1 : ∀ a, (G1 a).natDegree ≤ k) (hG2 : ∀ a, (G2 a).natDegree ≤ k) :
    ∃ R Col : F → F[X], (∀ s, (R s).natDegree ≤ k) ∧ (∀ t, (Col t).natDegree ≤ k) ∧
      (∀ st : F × F, (R st.1).eval st.2 =
        (G1 (lam w1 v1 (psi w1 v1 w2 v2 st))).eval (mu w1 v1 (psi w1 v1 w2 v2 st))) ∧
      (∀ st : F × F, (Col st.2).eval st.1 =
        (G2 (lam w2 v2 (psi w1 v1 w2 v2 st))).eval (mu w2 v2 (psi w1 v1 w2 v2 st))) := by
  set A := (det2 w1 v1 / det2 v2 v1) * mu w1 v1 v2
  set B := (det2 w2 v2 / det2 v1 v2) * mu w1 v1 v1
  set A' := (det2 w1 v1 / det2 v2 v1) * mu w2 v2 v2
  set B' := (det2 w2 v2 / det2 v1 v2) * mu w2 v2 v1
  refine ⟨fun s => (G1 s).comp (C B * X + C (s * A)),
    fun t => (G2 t).comp (C A' * X + C (t * B')), fun s => ?_, fun t => ?_, fun st => ?_,
    fun st => ?_⟩
  · exact natDegree_comp_le.trans (by nlinarith [hG1 s, natDegree_linear_le (a := B) (b := s * A)])
  · exact natDegree_comp_le.trans (by nlinarith [hG2 t, natDegree_linear_le (a := A') (b := t * B')])
  · rw [eval_comp, lam1_psi h1 h12, mu_psi]
    simp only [eval_add, eval_mul, eval_C, eval_X, A, B]
    congr 1; ring
  · rw [eval_comp, lam2_psi h2 h12, mu_psi]
    simp only [eval_add, eval_mul, eval_C, eval_X, A', B']
    congr 1; ring

omit [Field F] in
lemma card_univ_vec [Fintype F] :
    ((Finset.univ : Finset (Fin 2 → F)).card : ℝ) = (Fintype.card F : ℝ) ^ 2 := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; push_cast; rfl

lemma le_pair [Fintype F] [DecidableEq F] (k : ℕ) (η : ℝ) (hη : η ≤ 1 / 2048)
    (hq : 64 * (k + 1) ≤ Fintype.card F) {w1 v1 w2 v2 : Fin 2 → F} (h1 : det2 w1 v1 ≠ 0)
    (h2 : det2 w2 v2 ≠ 0) (h12 : det2 v1 v2 ≠ 0) (G1 G2 : F → F[X])
    (hG1 : ∀ a, (G1 a).natDegree ≤ k) (hG2 : ∀ a, (G2 a).natDegree ≤ k) (f : (Fin 2 → F) → F)
    (hrej1 : ((Finset.univ.filter fun x => (G1 (lam w1 v1 x)).eval (mu w1 v1 x) ≠ f x).card : ℝ) ≤
      η * (Fintype.card F : ℝ) ^ 2)
    (hrej2 : ((Finset.univ.filter fun x => (G2 (lam w2 v2 x)).eval (mu w2 v2 x) ≠ f x).card : ℝ) ≤
      η * (Fintype.card F : ℝ) ^ 2) :
    ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ 2 * k ∧
      (1 - 5 * η) * (Fintype.card F : ℝ) ^ 2 ≤
        ((Finset.univ.filter fun x => MvPolynomial.eval x Q = f x).card : ℝ) := by
  classical
  obtain ⟨R, Col, hR, hC, hRe, hCe⟩ := rows_cols_of_pair k h1 h2 h12 G1 G2 hG1 hG2
  set g : F → F → F := fun s t => f (psi w1 v1 w2 v2 (s, t)) with hg
  have herrR : ((Finset.univ.filter fun st : F × F => (R st.1).eval st.2 ≠ g st.1 st.2).card : ℝ)
      ≤ η * (Fintype.card F : ℝ) ^ 2 := by
    have := card_filter_psi h1 h2 h12 (fun x => (G1 (lam w1 v1 x)).eval (mu w1 v1 x) ≠ f x)
    rw [this] at hrej1
    have e : (Finset.univ.filter fun st : F × F => (R st.1).eval st.2 ≠ g st.1 st.2) =
        Finset.univ.filter fun st : F × F => (G1 (lam w1 v1 (psi w1 v1 w2 v2 st))).eval
          (mu w1 v1 (psi w1 v1 w2 v2 st)) ≠ f (psi w1 v1 w2 v2 st) := by
      ext st
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hRe, g]
    rw [e]; exact hrej1
  have herrC : ((Finset.univ.filter fun st : F × F => (Col st.2).eval st.1 ≠ g st.1 st.2).card : ℝ)
      ≤ η * (Fintype.card F : ℝ) ^ 2 := by
    have := card_filter_psi h1 h2 h12 (fun x => (G2 (lam w2 v2 x)).eval (mu w2 v2 x) ≠ f x)
    rw [this] at hrej2
    have e : (Finset.univ.filter fun st : F × F => (Col st.2).eval st.1 ≠ g st.1 st.2) =
        Finset.univ.filter fun st : F × F => (G2 (lam w2 v2 (psi w1 v1 w2 v2 st))).eval
          (mu w2 v2 (psi w1 v1 w2 v2 st)) ≠ f (psi w1 v1 w2 v2 st) := by
      ext st
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hCe, g]
    rw [e]; exact hrej2
  obtain ⟨P, hPdeg, hPc, hPerr⟩ := le_axis k η hη hq R Col hR hC g herrR herrC
  refine ⟨subst (lform w1 v1) (lform w2 v2) P,
    totalDegree_subst _ _ (totalDegree_lform _ _) (totalDegree_lform _ _) P k hPdeg hPc, ?_⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x => MvPolynomial.eval x (subst (lform w1 v1) (lform w2 v2) P) = f x)
  have hD := card_filter_psi h1 h2 h12
    (fun x => ¬ MvPolynomial.eval x (subst (lform w1 v1) (lform w2 v2) P) = f x)
  have hD' : (Finset.univ.filter fun st : F × F =>
      ¬ MvPolynomial.eval (psi w1 v1 w2 v2 st) (subst (lform w1 v1) (lform w2 v2) P) =
        f (psi w1 v1 w2 v2 st)) =
      Finset.univ.filter fun st : F × F => (P.eval (C st.2)).eval st.1 ≠ g st.1 st.2 := by
    ext st
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_subst, eval_lform,
      lam1_psi h1 h12, lam2_psi h2 h12, g]
  rw [← hD', ← hD] at hPerr
  have hsplitR : ((Finset.univ.filter fun x =>
      MvPolynomial.eval x (subst (lform w1 v1) (lform w2 v2) P) = f x).card : ℝ) +
      ((Finset.univ.filter fun x =>
      ¬ MvPolynomial.eval x (subst (lform w1 v1) (lform w2 v2) P) = f x).card : ℝ) =
      (Fintype.card F : ℝ) ^ 2 := by
    rw [← card_univ_vec]; exact_mod_cast hsplit
  linarith

end Pair

section Perfect
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma interp_exists (h : F → F) :
    ∃ p : F[X], p.natDegree ≤ Fintype.card F - 1 ∧ ∀ t, h t = p.eval t := by
  have hinj : Set.InjOn (id : F → F) ↑(Finset.univ : Finset F) := Function.injective_id.injOn
  refine ⟨Lagrange.interpolate Finset.univ id h, ?_, fun t => ?_⟩
  · have := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := id) h hinj
    rw [Finset.card_univ] at this
    by_cases h0 : Lagrange.interpolate Finset.univ id h = 0
    · rw [h0, natDegree_zero]; exact Nat.zero_le _
    · rw [degree_eq_natDegree h0] at this
      have : (Lagrange.interpolate Finset.univ id h).natDegree < Fintype.card F := by
        exact_mod_cast this
      omega
  · exact (Lagrange.eval_interpolate_at_node (v := id) h hinj (Finset.mem_univ t)).symm

lemma perfect_pair (k : ℕ) {w1 v1 w2 v2 : Fin 2 → F} (h1 : det2 w1 v1 ≠ 0)
    (h2 : det2 w2 v2 ≠ 0) (h12 : det2 v1 v2 ≠ 0) (G1 G2 : F → F[X])
    (hG1 : ∀ a, (G1 a).natDegree ≤ k) (hG2 : ∀ a, (G2 a).natDegree ≤ k) (f : (Fin 2 → F) → F)
    (hacc1 : ∀ x, (G1 (lam w1 v1 x)).eval (mu w1 v1 x) = f x)
    (hacc2 : ∀ x, (G2 (lam w2 v2 x)).eval (mu w2 v2 x) = f x) :
    ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ 2 * k ∧ ∀ x, MvPolynomial.eval x Q = f x := by
  obtain ⟨R, Col, hR, hC, hRe, hCe⟩ := rows_cols_of_pair k h1 h2 h12 G1 G2 hG1 hG2
  set Ψ : F → F → F := fun s t => f (psi w1 v1 w2 v2 (s, t)) with hΨ
  have hrow : ∀ s t, Ψ s t = (R s).eval t := fun s t => by
    rw [hRe (s, t), hacc1]
  have hcol : ∀ s t, Ψ s t = (Col t).eval s := fun s t => by
    rw [hCe (s, t), hacc2]
  obtain ⟨d, hdk, hdq, hrow', hcol'⟩ : ∃ d, d ≤ k ∧ d < Fintype.card F ∧
      (∀ s, ∃ p : F[X], p.natDegree ≤ d ∧ ∀ t, Ψ s t = p.eval t) ∧
      (∀ t, ∃ p : F[X], p.natDegree ≤ d ∧ ∀ s, Ψ s t = p.eval s) := by
    by_cases hk : k < Fintype.card F
    · exact ⟨k, le_rfl, hk, fun s => ⟨R s, hR s, hrow s⟩,
        fun t => ⟨Col t, hC t, fun s => hcol s t⟩⟩
    · have := Fintype.card_pos (α := F)
      exact ⟨Fintype.card F - 1, by omega, by omega, fun s => interp_exists (Ψ s),
        fun t => interp_exists (fun s => Ψ s t)⟩
  obtain ⟨N, hNdeg, hNc, hN⟩ := rows_cols_poly d hdq Ψ hrow' hcol'
  refine ⟨subst (lform w1 v1) (lform w2 v2) N,
    (totalDegree_subst _ _ (totalDegree_lform _ _) (totalDegree_lform _ _) N d hNdeg hNc).trans
      (by omega), fun x => ?_⟩
  rw [eval_subst, eval_lform, eval_lform, hN, hΨ]
  simp only
  rw [psi_lam h1 h2 h12]

end Perfect

end DLT.L3

namespace DLT

/-- Low-error regime: average acceptance at least `1 - η` over `r ≥ 2` directions. -/
theorem le_core {F : Type*} [Field F] [Fintype F] [DecidableEq F] (k r : ℕ) (hr : 2 ≤ r)
    (η : ℝ) (hη : η ≤ 1 / 4096) (hq : 64 * (k + 1) ≤ Fintype.card F)
    (w v : Fin r → Fin 2 → F) (hwv : ∀ i, det2 (w i) (v i) ≠ 0)
    (hvv : ∀ i j, i ≠ j → det2 (v i) (v j) ≠ 0)
    (G : Fin r → F → Polynomial F) (hG : ∀ i a, (G i a).natDegree ≤ k) (f : (Fin 2 → F) → F)
    (hacc : (1 - η) * ((r : ℝ) * (Fintype.card F : ℝ) ^ 2) ≤
      ∑ i, ((Finset.univ.filter fun x =>
        (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card : ℝ)) :
    ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ 2 * k ∧
      (1 - 10 * η) * (Fintype.card F : ℝ) ^ 2 ≤
        ((Finset.univ.filter fun x => MvPolynomial.eval x Q = f x).card : ℝ) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set acc : Fin r → ℝ := fun i => ((Finset.univ.filter fun x =>
        (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card : ℝ) with hacc_def
  set rej : Fin r → ℝ := fun i => ((Finset.univ.filter fun x =>
        (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) ≠ f x).card : ℝ) with hrej_def
  have hsplit : ∀ i, acc i + rej i = q ^ 2 := by
    intro i
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 2 → F)))
      (fun x => (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x)
    rw [hqdef, ← L3.card_univ_vec, hacc_def, hrej_def]
    dsimp only
    exact_mod_cast this
  have hrej0 : ∀ i, 0 ≤ rej i := fun i => Nat.cast_nonneg _
  have hq0 : 0 < q := by
    rw [hqdef]; exact_mod_cast Fintype.card_pos
  have hr0 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hsum : ∑ i, rej i ≤ η * (r * q ^ 2) := by
    have h := Finset.sum_add_distrib (s := Finset.univ) (f := acc) (g := rej)
    simp only [hsplit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    linarith
  have hη0 : 0 ≤ η := by
    by_contra hneg
    rw [not_le] at hneg
    have : η * (r * q ^ 2) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hrej0 i)
    linarith
  have : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image Finset.univ rej Finset.univ_nonempty
  have hcard : (Finset.univ.erase i₁).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hne : (Finset.univ.erase i₁).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  obtain ⟨i₂, hi₂mem, hi₂⟩ := Finset.exists_min_image (Finset.univ.erase i₁) rej hne
  have h12 : i₂ ≠ i₁ := Finset.ne_of_mem_erase hi₂mem
  have hle12 : rej i₁ ≤ rej i₂ := hi₁ i₂ (Finset.mem_univ _)
  have hsum2 : ((r : ℝ) - 1) * rej i₂ ≤ ∑ i, rej i := by
    rw [← Finset.add_sum_erase Finset.univ rej (Finset.mem_univ i₁)]
    have := Finset.card_nsmul_le_sum (Finset.univ.erase i₁) rej (rej i₂) hi₂
    rw [hcard, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one] at this
    linarith [hrej0 i₁]
  have hb2 : rej i₂ ≤ 2 * η * q ^ 2 := by
    by_contra hc
    rw [not_le] at hc
    have : 0 < ((r : ℝ) - 1) * (rej i₂ - 2 * η * q ^ 2) := mul_pos (by linarith) (by linarith)
    nlinarith [mul_nonneg hη0 (sq_nonneg q)]
  obtain ⟨Q, hQ, hQ2⟩ := L3.le_pair k (2 * η) (by linarith) hq (hwv i₁) (hwv i₂)
    (hvv i₁ i₂ h12.symm) (G i₁) (G i₂) (hG i₁) (hG i₂) f (by linarith) hb2
  exact ⟨Q, hQ, by linarith⟩

/-- Perfect acceptance along two directions forces a polynomial of degree `≤ 2k`. -/
theorem perfect_core {F : Type*} [Field F] [Fintype F] [DecidableEq F] (k r : ℕ) (hr : 2 ≤ r)
    (w v : Fin r → Fin 2 → F) (hwv : ∀ i, det2 (w i) (v i) ≠ 0)
    (hvv : ∀ i j, i ≠ j → det2 (v i) (v j) ≠ 0)
    (G : Fin r → F → Polynomial F) (hG : ∀ i a, (G i a).natDegree ≤ k) (f : (Fin 2 → F) → F)
    (hacc : ∀ i x, (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x) :
    ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ 2 * k ∧ ∀ x, MvPolynomial.eval x Q = f x := by
  set i₁ : Fin r := ⟨0, by omega⟩
  set i₂ : Fin r := ⟨1, by omega⟩
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  exact L3.perfect_pair k (hwv i₁) (hwv i₂) (hvv i₁ i₂ h12) (G i₁) (G i₂) (hG i₁) (hG i₂) f
    (hacc i₁) (hacc i₂)

end DLT

end Part13

section Part14
open Polynomial

namespace DLT

section Final

/-- Bernoulli-type bound: `(1-η)^n (1 + nη) ≤ 1`. -/
lemma pow_mul_one_add_le (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) (n : ℕ) :
    (1 - η) ^ n * (1 + n * η) ≤ 1 := by
  have hb : 1 + n * η ≤ (1 + η) ^ n := one_add_mul_le_pow (by linarith) n
  have h2 : (1 - η) ^ n * (1 + η) ^ n ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀ (by nlinarith) (by nlinarith)
  calc (1 - η) ^ n * (1 + n * η) ≤ (1 - η) ^ n * (1 + η) ^ n :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg (by linarith) _)
    _ ≤ 1 := h2

lemma pow_le_inv_one_add (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) (n : ℕ) :
    ε ^ n ≤ 1 / (1 + n * (1 - ε)) := by
  have := pow_mul_one_add_le (1 - ε) (by linarith) (by linarith) n
  rw [sub_sub_cancel] at this
  have hpos : (0:ℝ) ≤ n * (1 - ε) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  rw [le_div_iff₀ (by linarith)]
  exact this

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma dirs_le {r : ℕ} (v : Fin r → Fin 2 → F) (hvv : ∀ i j, i ≠ j → det2 (v i) (v j) ≠ 0) :
    r ≤ Fintype.card F + 1 := by
  classical
  let φ : Fin r → Option F := fun i => if v i 0 = 0 then none else some (v i 1 / v i 0)
  have hφ : Function.Injective φ := by
    intro i j hij
    by_contra hne
    apply hvv i j hne
    unfold det2
    simp only [φ] at hij
    split_ifs at hij with hi hj hj
    · rw [hi, hj]; ring
    · field_simp at hij
      have h2 : v i 1 = v j 1 / v j 0 * v i 0 := by
        rw [Option.some.injEq] at hij; field_simp [hi] at hij ⊢; linear_combination hij
      rw [h2]; field_simp; ring
  have := Fintype.card_le_of_injective φ hφ
  simpa using this

lemma trivial_agree (f : (Fin 2 → F) → F) (k : ℕ) :
    ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ 2 * k ∧
      Fintype.card F ≤ (Finset.univ.filter fun x => MvPolynomial.eval x Q = f x).card := by
  classical
  have hsum : ∑ z : F, (Finset.univ.filter fun x => f x = z).card =
      Fintype.card F * Fintype.card F := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (by simp)]
    simp [Fintype.card_fun, sq]
  obtain ⟨z, hz⟩ : ∃ z : F, Fintype.card F ≤ (Finset.univ.filter fun x => f x = z).card := by
    by_contra hcon
    push_neg at hcon
    have : ∑ z : F, (Finset.univ.filter fun x => f x = z).card < ∑ _z : F, Fintype.card F :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun z _ => hcon z
    rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
    exact lt_irrefl _ this
  refine ⟨MvPolynomial.C z, by simp, ?_⟩
  refine le_trans hz (Finset.card_le_card ?_)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, MvPolynomial.eval_C] at hx ⊢
  exact hx.symm


/-- Number of accepted incidences in direction `i`. -/
noncomputable abbrev accCount {r : ℕ} (w v : Fin r → Fin 2 → F) (G : Fin r → F → Polynomial F)
    (f : (Fin 2 → F) → F) (i : Fin r) : ℕ :=
  (Finset.univ.filter fun x => (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card

/-- The constant of the main theorem. -/
def cMain : ℕ := 10 ^ 26

lemma cMain_ge : (4224 : ℝ) ^ 4 + 5 * 10 ^ 25 ≤ cMain := by
  unfold cMain; push_cast; norm_num


lemma pow_mul_n_le (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 - 1 / 4096) (n : ℕ) :
    ε ^ n * (n : ℝ) ≤ 4096 := by
  have := pow_mul_one_add_le (1 - ε) (by linarith) (by linarith) n
  rw [sub_sub_cancel] at this
  have h2 : (n : ℝ) / 4096 ≤ n * (1 - ε) := by
    rw [div_eq_mul_inv]; apply mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have h3 : 0 ≤ ε ^ n := pow_nonneg h0.le _
  nlinarith

lemma case1_bound (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1 / 4096) (c : ℕ) (hc : 20 ≤ c) :
    (1 - η) ^ c ≤ 1 - 10 * η := by
  have h := pow_mul_one_add_le η h0 (by linarith) c
  have hc' : (20 : ℝ) ≤ c := by exact_mod_cast hc
  have hpos : 0 < 1 + (c : ℝ) * η := by positivity
  have hA : 0 ≤ (c : ℝ) - 10 - 10 * c * η := by nlinarith
  have hkey : 1 ≤ (1 - 10 * η) * (1 + c * η) := by nlinarith [mul_nonneg h0 hA]
  by_contra hcon
  push_neg at hcon
  have : (1 - 10 * η) * (1 + c * η) < (1 - η) ^ c * (1 + c * η) :=
    mul_lt_mul_of_pos_right hcon hpos
  linarith


lemma card_points : Fintype.card (Fin 2 → F) = Fintype.card F ^ 2 := by
  simp [Fintype.card_fun]

lemma eps_pow_split (ε : ℝ) (n : ℕ) (hn : n ≤ cMain) : ε ^ cMain = ε ^ (cMain - n) * ε ^ n := by
  rw [← pow_add, Nat.sub_add_cancel hn]

lemma eps_small (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 - 1 / 4096) (n : ℕ) (N : ℝ) (hN : 0 ≤ N)
    (hn : 4096 * N ≤ ((cMain - n : ℕ) : ℝ)) (hnc : 1 ≤ cMain - n) :
    ε ^ (cMain - n) * N ≤ 1 := by
  have h := pow_mul_n_le ε h0 h1 (cMain - n)
  have hpos : 0 < ((cMain - n : ℕ) : ℝ) := by exact_mod_cast hnc
  have h3 : 0 ≤ ε ^ (cMain - n) := pow_nonneg h0.le _
  nlinarith

lemma cMain_sub (n : ℕ) (hn : n ≤ 12) : (4096 * (4 * 10 ^ 21) : ℝ) ≤ ((cMain - n : ℕ) : ℝ) := by
  have h1 : n ≤ cMain := by unfold cMain; omega
  rw [Nat.cast_sub h1]
  have : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  unfold cMain; push_cast; linarith

lemma cMain_sub_pos (n : ℕ) (hn : n ≤ 12) : 1 ≤ cMain - n := by unfold cMain; omega


theorem core_thm : ∀ ε : ℝ, 0 < ε → ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F] (k r : ℕ),
    (k : ℝ) ^ 2 / ε ^ cMain ≤ (Fintype.card F : ℝ) → 1 / ε ^ cMain ≤ (r : ℝ) → 2 ≤ r →
    ∀ (w v : Fin r → Fin 2 → F), (∀ i, det2 (w i) (v i) ≠ 0) →
      (∀ i j, i ≠ j → det2 (v i) (v j) ≠ 0) →
    ∀ (G : Fin r → F → Polynomial F), (∀ i a, (G i a).natDegree ≤ k) → ∀ f : (Fin 2 → F) → F,
    ε * ((r : ℝ) * (Fintype.card F : ℝ) ^ 2) ≤ ∑ i, ((Finset.univ.filter fun x =>
        (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card : ℝ) →
    ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ 2 * k ∧
      ε ^ cMain * (Fintype.card F : ℝ) ^ 2 ≤
        ((Finset.univ.filter fun x => MvPolynomial.eval x Q = f x).card : ℝ) := by
  intro ε hε F _ _ _ k r hq hr hr2 w v hwv hvv G hG f hacc
  set q := Fintype.card F with hqdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hterm : ∀ i, ((Finset.univ.filter fun x =>
      (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card : ℝ) ≤ (q : ℝ) ^ 2 := by
    intro i
    have := Finset.card_le_univ (Finset.univ.filter fun x =>
      (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x)
    rw [card_points] at this
    exact_mod_cast this
  have hSum : ∑ i, ((Finset.univ.filter fun x =>
      (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card : ℝ) ≤ r * (q : ℝ) ^ 2 := by
    calc _ ≤ ∑ _i : Fin r, (q : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = r * (q : ℝ) ^ 2 := by simp
  have hε1 : ε ≤ 1 := by
    have hpos : 0 < (r : ℝ) * (q : ℝ) ^ 2 := by positivity
    by_contra hcon; push_neg at hcon
    nlinarith
  have hc20 : 20 ≤ cMain := by unfold cMain; norm_num
  have hεc : ε ^ cMain ≤ 1 := pow_le_one₀ hε.le hε1
  have hεc0 : 0 < ε ^ cMain := pow_pos hε _
  by_cases hη : 1 - ε ≤ 1 / 4096
  · by_cases hq64 : 64 * (k + 1) ≤ q
    · obtain ⟨Q, hQd, hQa⟩ := le_core k r hr2 (1 - ε) hη hq64 w v hwv hvv G hG f
        (by rw [sub_sub_cancel]; exact hacc)
      refine ⟨Q, hQd, le_trans ?_ hQa⟩
      have := case1_bound (1 - ε) (by linarith) hη cMain hc20
      rw [sub_sub_cancel] at this
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · -- small field
      push_neg at hq64
      have hk2 : (k : ℝ) ^ 2 ≤ q := by
        refine le_trans ?_ hq
        rw [le_div_iff₀ hεc0]
        exact mul_le_of_le_one_right (by positivity) hεc
      have hk2' : k ^ 2 ≤ q := by exact_mod_cast hk2
      have hk64 : k ≤ 64 := by nlinarith
      have hqlt : q < 4224 := by omega
      by_cases hall : ∀ i x, (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x
      · obtain ⟨Q, hQd, hQe⟩ := perfect_core k r hr2 w v hwv hvv G hG f hall
        refine ⟨Q, hQd, ?_⟩
        have : (Finset.univ.filter fun x => MvPolynomial.eval x Q = f x) = Finset.univ := by
          ext x; simp [hQe x]
        rw [this, Finset.card_univ, card_points]
        push_cast
        exact mul_le_of_le_one_left (by positivity) hεc
      · push_neg at hall
        obtain ⟨i₀, x₀, hx₀⟩ := hall
        have hterm' : ((Finset.univ.filter fun x =>
            (G i₀ (lam (w i₀) (v i₀) x)).eval (mu (w i₀) (v i₀) x) = f x).card : ℝ) ≤
              (q : ℝ) ^ 2 - 1 := by
          have h1 : (Finset.univ.filter fun x =>
              (G i₀ (lam (w i₀) (v i₀) x)).eval (mu (w i₀) (v i₀) x) = f x).card <
                Fintype.card (Fin 2 → F) := by
            apply Finset.card_lt_univ_of_notMem (x := x₀)
            simp [hx₀]
          rw [card_points] at h1
          have : (Finset.univ.filter fun x =>
              (G i₀ (lam (w i₀) (v i₀) x)).eval (mu (w i₀) (v i₀) x) = f x).card + 1 ≤ q ^ 2 :=
            h1
          have h2 : ((Finset.univ.filter fun x =>
              (G i₀ (lam (w i₀) (v i₀) x)).eval (mu (w i₀) (v i₀) x) = f x).card : ℝ) + 1 ≤
                (q : ℝ) ^ 2 := by exact_mod_cast this
          linarith
        have hSum' : ∑ i, ((Finset.univ.filter fun x =>
            (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card : ℝ) ≤
              r * (q : ℝ) ^ 2 - 1 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
          have : ∑ i ∈ Finset.univ.erase i₀, ((Finset.univ.filter fun x =>
              (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card : ℝ) ≤
                ((r : ℝ) - 1) * (q : ℝ) ^ 2 := by
            calc _ ≤ ∑ _i ∈ Finset.univ.erase i₀, (q : ℝ) ^ 2 :=
                  Finset.sum_le_sum fun i _ => hterm i
              _ = ((r : ℝ) - 1) * (q : ℝ) ^ 2 := by
                  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
                    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                  push_cast [show 1 ≤ r by omega]; ring
          linarith
        have hrq : (r : ℝ) ≤ q + 1 := by exact_mod_cast dirs_le v hvv
        have hηpos : 1 ≤ (1 - ε) * ((q : ℝ) + 1) * (q : ℝ) ^ 2 := by
          have h1 : 1 ≤ (1 - ε) * ((r : ℝ) * (q : ℝ) ^ 2) := by nlinarith
          have h2 : (1 - ε) * ((r : ℝ) * (q : ℝ) ^ 2) ≤ (1 - ε) * (((q : ℝ) + 1) * (q : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrq (by positivity))
              (by linarith)
          nlinarith
        have hB := pow_mul_one_add_le (1 - ε) (by linarith) (by linarith) cMain
        rw [sub_sub_cancel] at hB
        have hqr : (q : ℝ) < 4224 := by exact_mod_cast hqlt
        have hcbig : ((q : ℝ) + 1) * (q : ℝ) ^ 2 * q ≤ cMain := by
          have : ((q : ℝ) + 1) * (q : ℝ) ^ 2 * q ≤ 4225 * 4224 ^ 2 * 4224 := by
            have h0 : (0 : ℝ) ≤ q := hq0.le
            have e1 : (q : ℝ) + 1 ≤ 4225 := by linarith
            have e2 : (q : ℝ) ^ 2 ≤ 4224 ^ 2 := by nlinarith
            calc ((q : ℝ) + 1) * (q : ℝ) ^ 2 * q ≤ 4225 * 4224 ^ 2 * q := by gcongr
              _ ≤ 4225 * 4224 ^ 2 * 4224 := by gcongr
          unfold cMain; push_cast; linarith
        have hcη : (q : ℝ) ≤ cMain * (1 - ε) := by
          have hpos : 0 < ((q : ℝ) + 1) * (q : ℝ) ^ 2 := by positivity
          have : (q : ℝ) * 1 ≤ (q : ℝ) * ((1 - ε) * ((q : ℝ) + 1) * (q : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hηpos hq0.le
          nlinarith
        have hεq : ε ^ cMain * ((q : ℝ) + 1) ≤ 1 := by nlinarith
        obtain ⟨Q, hQd, hQa⟩ := trivial_agree f k
        have hQa' : (q : ℝ) ≤ ((Finset.univ.filter fun x =>
            MvPolynomial.eval x Q = f x).card : ℝ) := by exact_mod_cast hQa
        refine ⟨Q, hQd, le_trans ?_ hQa'⟩
        nlinarith
  · -- high-error regime
    push_neg at hη
    have hε' : ε ≤ 1 - 1 / 4096 := by linarith
    obtain ⟨p, hchar⟩ := CharP.exists F
    haveI := hchar
    haveI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
    -- the lower bound on r
    have hpow : ∀ n ≤ 12, ε ^ (cMain - n) * (4 * 10 ^ 21) ≤ 1 := fun n hn =>
      eps_small ε hε hε' n _ (by positivity) (cMain_sub n hn) (cMain_sub_pos n hn)
    have hr' : 10 ^ 13 ≤ (r : ℝ) * ε ^ 8 := by
      have h1 := hpow 8 (by norm_num)
      have h2 : 1 ≤ (r : ℝ) * ε ^ cMain := by
        rwa [div_le_iff₀ hεc0] at hr
      rw [eps_pow_split ε 8 (by unfold cMain; norm_num)] at h2
      have h3 : 0 < ε ^ (cMain - 8) := pow_pos hε _
      have h4 : 0 ≤ (r : ℝ) * ε ^ 8 := by positivity
      nlinarith
    have hq' : 10 ^ 21 * ((k : ℝ) + 1) ^ 2 ≤ (q : ℝ) * ε ^ 12 := by
      have h1 := hpow 12 (by norm_num)
      have h3 : 0 < ε ^ (cMain - 12) := pow_pos hε _
      have hsplit := eps_pow_split ε 12 (by unfold cMain; norm_num)
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have hrq : (r : ℝ) ≤ q + 1 := by exact_mod_cast dirs_le v hvv
        have h2 : 1 ≤ (r : ℝ) * ε ^ cMain := by rwa [div_le_iff₀ hεc0] at hr
        rw [hsplit] at h2
        have h5 : ε ^ 12 ≤ 1 := pow_le_one₀ hε.le hε1
        have h6 : 0 < ε ^ 12 := pow_pos hε _
        push_cast
        nlinarith
      · have h2 : (k : ℝ) ^ 2 ≤ (q : ℝ) * ε ^ cMain := by rwa [div_le_iff₀ hεc0] at hq
        rw [hsplit] at h2
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have h6 : 0 ≤ (q : ℝ) * ε ^ 12 := by positivity
        nlinarith
    obtain ⟨Q, hQd, hQa⟩ := he_main p w v hwv hvv G k hG f ε hε hε1 hacc hr' hq'
    refine ⟨Q, hQd, le_trans ?_ hQa⟩
    have h1 : ε ^ (cMain - 6) * (4 * 10 ^ 21) ≤ 1 := hpow 6 (by norm_num)
    have hsplit := eps_pow_split ε 6 (by unfold cMain; norm_num)
    have h3 : 0 < ε ^ (cMain - 6) := pow_pos hε _
    have h6 : 0 < ε ^ 6 := pow_pos hε _
    have : ε ^ cMain ≤ ε ^ 6 / 10 ^ 9 := by
      rw [hsplit, le_div_iff₀ (by norm_num)]
      nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)

end Final
end DLT
end Part14

section Part15

open Polynomial


namespace DLT

theorem main_theorem :
    ∃ c : ℕ, ∀ ε : ℝ, 0 < ε → ∀ (F : Type u) [Field F] [Fintype F] (k r : ℕ),
      (k : ℝ) ^ 2 / ε ^ c ≤ (Fintype.card F : ℝ) → 1 / ε ^ c ≤ (r : ℝ) → 2 ≤ r →
      ∀ U : Finset (Submodule F (Fin 2 → F)), (∀ u ∈ U, Module.finrank F u = 1) → U.card = r →
      ∀ f : (Fin 2 → F) → F,
        (∃ P : LineVsPoint.LineTable F 2 k, ε ≤ DerandLDT.localAgr f P U) →
        ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ 2 * k ∧ ε ^ c ≤ LineVsPoint.agr f Q := by
  refine ⟨cMain, ?_⟩
  intro ε hε F _ _ k r hq hr hr2 U hU hUr f ⟨P, hP⟩
  classical
  obtain ⟨w, v, G, hwv, hvv, hG, heq⟩ := bridge k r U hU hUr P f
  have hpos : (0 : ℝ) ≤ (r : ℝ) * (Fintype.card F : ℝ) ^ 2 := by positivity
  have hacc : ε * ((r : ℝ) * (Fintype.card F : ℝ) ^ 2) ≤ ∑ i, ((Finset.univ.filter fun x =>
      (G i (lam (w i) (v i) x)).eval (mu (w i) (v i) x) = f x).card : ℝ) := by
    rw [← heq]; exact mul_le_mul_of_nonneg_right hP hpos
  obtain ⟨Q, hQd, hQa⟩ := core_thm ε hε F k r hq hr hr2 w v hwv hvv G hG f hacc
  refine ⟨Q, hQd, ?_⟩
  unfold LineVsPoint.agr
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) ^ 2 := by
    have : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    positivity
  rw [le_div_iff₀ hq0]
  convert hQa using 3

end DLT

end Part15

theorem solution :
    ∃ c : ℕ, ∀ ε : ℝ, 0 < ε → ∀ (F : Type u) [Field F] [Fintype F] (k r : ℕ),
      (k : ℝ) ^ 2 / ε ^ c ≤ (Fintype.card F : ℝ) → 1 / ε ^ c ≤ (r : ℝ) → 2 ≤ r →
      ∀ U : Finset (Submodule F (Fin 2 → F)), (∀ u ∈ U, Module.finrank F u = 1) → U.card = r →
      ∀ f : (Fin 2 → F) → F,
        (∃ P : LineVsPoint.LineTable F 2 k, ε ≤ DerandLDT.localAgr f P U) →
        ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ 2 * k ∧ ε ^ c ≤ LineVsPoint.agr f Q :=
  DLT.main_theorem
