-- Prove2me | solution 1 for GaussPolyReg.Approx.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T17:09:46.082487+00:00
-- url     : https://prove2.me/submissions/73f4d372-3eec-4fef-b4d8-4a7457abf925

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Tensors
open MeasureTheory ProbabilityTheory Polynomial
open Equiv
universe u v
noncomputable section
namespace GPR

abbrev γ : Measure ℝ := gaussianReal 0 1

lemma integrable_pow_γ (n : ℕ) : Integrable (fun x : ℝ => x ^ n) γ := by
  have h := memLp_id_gaussianReal (μ := 0) (v := 1) (n : NNReal)
  have h2 := h.integrable_norm_pow'
  exact (integrable_norm_iff (by fun_prop)).1 (by simpa using h2)

lemma integrable_poly_γ (p : ℝ[X]) : Integrable (fun x => p.eval x) γ := by
  simp_rw [Polynomial.eval_eq_sum_range]
  exact integrable_finsetSum _ (fun i _ => (integrable_pow_γ i).const_mul _)

lemma integrable_x_poly_γ (p : ℝ[X]) : Integrable (fun x => x * p.eval x) γ := by
  have := integrable_poly_γ (X * p)
  simpa using this

lemma pdf_hasDeriv (x : ℝ) : HasDerivAt (fun x => gaussianPDFReal 0 1 x) (-x * gaussianPDFReal 0 1 x) x := by
  simp only [gaussianPDFReal_def]
  have h1 : HasDerivAt (fun x : ℝ => -(x - 0)^2 / (2 * ((1:NNReal):ℝ))) (-x) x := by
    have := ((hasDerivAt_id x).sub_const 0).pow 2 |>.neg |>.div_const (2 * ((1:NNReal):ℝ))
    refine this.congr_deriv ?_
    simp
    ring
  have := (h1.exp).const_mul ((√(2 * Real.pi * ((1:NNReal):ℝ)))⁻¹)
  refine this.congr_deriv ?_
  ring

lemma γ_eq : γ = volume.withDensity (gaussianPDF 0 1) := gaussianReal_of_var_ne_zero _ (by simp)

lemma hI (f : ℝ → ℝ) (hf : Integrable f γ) : Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [γ_eq, integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (by simp [gaussianPDF])] at hf
  simpa [toReal_gaussianPDF, smul_eq_mul] using hf

lemma gint (f : ℝ → ℝ) : ∫ x, f x ∂γ = ∫ x, gaussianPDFReal 0 1 x * f x := by
  rw [integral_gaussianReal_eq_integral_smul (by simp)]
  simp [smul_eq_mul]

lemma gibp (p : ℝ[X]) : ∫ x, x * p.eval x ∂γ = ∫ x, (derivative p).eval x ∂γ := by
  rw [gint, gint]
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x => p.eval x)
    (u' := fun x => (derivative p).eval x) (v := fun x => -gaussianPDFReal 0 1 x)
    (v' := fun x => x * gaussianPDFReal 0 1 x)
    (fun x _ => p.hasDerivAt x)
    (fun x _ => by have := (pdf_hasDeriv x).fun_neg; simpa using this)
    (by
      have := hI _ (integrable_x_poly_γ p)
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (by
      have := (hI _ (integrable_poly_γ (derivative p))).neg
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply, Pi.neg_apply]; ring)
    (by
      have := (hI _ (integrable_poly_γ p)).neg
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply, Pi.neg_apply]; ring)
  have e1 : ∀ x, gaussianPDFReal 0 1 x * (x * p.eval x) = p.eval x * (x * gaussianPDFReal 0 1 x) := by
    intro x; ring
  simp_rw [e1, h]
  rw [← integral_neg]
  congr 1; ext x; ring


def He (a : ℕ) : ℝ[X] := (Polynomial.hermite a).map (Int.castRingHom ℝ)

lemma hermite_eq (a : ℕ) (x : ℝ) : GaussPolyReg.Approx.hermite a x = (He a).eval x := by
  simp [GaussPolyReg.Approx.hermite, He, Polynomial.aeval_def, Polynomial.eval_map]

lemma He_zero : He 0 = 1 := by simp [He]

lemma He_succ (n : ℕ) : He (n + 1) = X * He n - derivative (He n) := by
  simp [He, Polynomial.hermite_succ, Polynomial.derivative_map]

lemma derivative_He (n : ℕ) : derivative (He n) = C (n : ℝ) * He (n - 1) := by
  induction n with
  | zero => simp [He_zero]
  | succ n ih =>
    rw [He_succ, derivative_sub, derivative_mul, derivative_X, one_mul, ih]
    cases n with
    | zero => simp [He_zero, He_succ]
    | succ m =>
      simp only [Nat.add_sub_cancel] at ih ⊢
      have h3 : He (m + 1) = X * He m - derivative (He m) := He_succ m
      rw [derivative_mul, derivative_C, zero_mul, zero_add]
      have h4 : C ((m + 1 : ℕ) : ℝ) * He (m + 1) = C ((m + 1 : ℕ) : ℝ) * (X * He m - derivative (He m)) := by rw [← h3]
      have h5 : C ((m + 1 + 1 : ℕ) : ℝ) = C ((m + 1 : ℕ) : ℝ) + 1 := by
        rw [← C_1, ← C_add]; congr 1; push_cast; ring
      rw [h5]
      linear_combination (-1 : ℝ[X]) * h4


def E1 (p : ℝ[X]) : ℝ := ∫ x, p.eval x ∂γ

lemma He_ibp (b : ℕ) (q : ℝ[X]) : E1 (He (b + 1) * q) = E1 (He b * derivative q) := by
  have h1 : E1 (He (b + 1) * q) = E1 (X * (He b * q)) - E1 (derivative (He b) * q) := by
    rw [He_succ, sub_mul]
    simp only [E1, eval_sub]
    rw [integral_sub (integrable_poly_γ _) (integrable_poly_γ _)]
    simp [mul_assoc]
  have h2 : E1 (X * (He b * q)) = E1 (derivative (He b * q)) := by
    calc E1 (X * (He b * q)) = ∫ x, x * (He b * q).eval x ∂γ := by simp [E1]
      _ = E1 (derivative (He b * q)) := gibp _
  rw [h1, h2, derivative_mul]
  simp only [E1, eval_add]
  rw [integral_add (integrable_poly_γ _) (integrable_poly_γ _)]
  simp


lemma E1_C_mul (c : ℝ) (p : ℝ[X]) : E1 (C c * p) = c * E1 p := by
  simp [E1, integral_const_mul]

lemma E1_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    E1 (∑ i ∈ s, f i) = ∑ i ∈ s, E1 (f i) := by
  simp only [E1, eval_finset_sum]
  exact integral_finset_sum _ (fun i _ => integrable_poly_γ _)

lemma E1_one : E1 1 = 1 := by simp [E1]

lemma prod_update_eq {ℓ : ℕ} (a : Fin ℓ → ℕ) (j0 k : Fin ℓ) (hk : k ≠ j0) (b : ℕ) :
    ∏ j, He (Function.update (Function.update a j0 b) k (a k - 1) j) =
      He b * (He (a k - 1) * ∏ j ∈ (Finset.univ.erase j0).erase k, He (a j)) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j0),
    ← Finset.mul_prod_erase (Finset.univ.erase j0) _ (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)]
  have h1 : Function.update (Function.update a j0 b) k (a k - 1) j0 = b := by
    rw [Function.update_of_ne hk.symm]; simp
  have h2 : Function.update (Function.update a j0 b) k (a k - 1) k = a k - 1 := by simp
  rw [h1, h2]
  congr 2
  refine Finset.prod_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_erase] at hj
  rw [Function.update_of_ne hj.1, Function.update_of_ne hj.2.1]

lemma E1_rec {ℓ : ℕ} (a : Fin ℓ → ℕ) (j0 : Fin ℓ) (b : ℕ) (h : a j0 = b + 1) :
    E1 (∏ j, He (a j)) = ∑ k ∈ Finset.univ.erase j0, (a k : ℝ) *
      E1 (∏ j, He (Function.update (Function.update a j0 b) k (a k - 1) j)) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j0), h, He_ibp]
  rw [derivative_prod_finset, Finset.mul_sum, E1_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≠ j0 := (Finset.mem_erase.1 hk).1
  rw [prod_update_eq a j0 k hk' b, derivative_He, ← E1_C_mul]
  congr 1
  ring




section

noncomputable def Mset {V ι : Type*} [Fintype V] [DecidableEq V] {ℓ : ℕ} (g : V → Fin ℓ) (lab : V → ι) :
    Finset (Perm V) := by
  classical
  exact Finset.univ.filter (fun M => (∀ u, M (M u) = u) ∧ (∀ u, g (M u) ≠ g u) ∧
    (∀ u, lab (M u) = lab u))

lemma mem_Mset {V ι : Type*} [Fintype V] [DecidableEq V] {ℓ : ℕ} (g : V → Fin ℓ) (lab : V → ι)
    (M : Perm V) : M ∈ Mset g lab ↔
    (∀ u, M (M u) = u) ∧ (∀ u, g (M u) ≠ g u) ∧ (∀ u, lab (M u) = lab u) := by
  classical
  simp [Mset]

lemma card_Mset_fiber {V ι : Type*} [Fintype V] [DecidableEq V] {ℓ : ℕ} (g : V → Fin ℓ)
    (lab : V → ι) (v0 w : V) (hg : g w ≠ g v0) (hl : lab w = lab v0) :
    ((Mset g lab).filter (fun M => M v0 = w)).card =
      (Mset (fun v : {v // v ≠ v0 ∧ v ≠ w} => g v.1)
        (fun v : {v // v ≠ v0 ∧ v ≠ w} => lab v.1)).card := by
  have hne : v0 ≠ w := fun h => hg (by rw [h])
  symm
  refine Finset.card_bij (fun σ _ => swap v0 w * Perm.ofSubtype σ) ?_ ?_ ?_
  · intro σ hσ
    rw [mem_Mset] at hσ
    obtain ⟨h1, h2, h3⟩ := hσ
    rw [Finset.mem_filter, mem_Mset]
    have key : ∀ u : V, u ≠ v0 → u ≠ w → ∃ u' : {v // v ≠ v0 ∧ v ≠ w}, u'.1 = u := fun u a b => ⟨⟨u, a, b⟩, rfl⟩
    have hM : ∀ u : {v // v ≠ v0 ∧ v ≠ w}, (swap v0 w * Perm.ofSubtype σ) u.1 = (σ u).1 := by
      intro u
      rw [Perm.mul_apply, Perm.ofSubtype_apply_coe]
      exact swap_apply_of_ne_of_ne (σ u).2.1 (σ u).2.2
    have h0 : (swap v0 w * Perm.ofSubtype σ) v0 = w := by
      rw [Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem _ (fun h => h.1 rfl)]
      simp
    have hw : (swap v0 w * Perm.ofSubtype σ) w = v0 := by
      rw [Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem _ (fun h => h.2 rfl)]
      simp
    refine ⟨⟨?_, ?_, ?_⟩, h0⟩
    · intro u
      by_cases a : u = v0
      · subst a; rw [h0, hw]
      by_cases b : u = w
      · subst b; rw [hw, h0]
      obtain ⟨u', rfl⟩ := key u a b
      rw [hM, show (σ u').1 = ((σ u' : {v // v ≠ v0 ∧ v ≠ w}) : V) from rfl]
      rw [hM (σ u'), h1 u']
    · intro u
      by_cases a : u = v0
      · subst a; rw [h0]; exact hg
      by_cases b : u = w
      · subst b; rw [hw]; exact hg.symm
      obtain ⟨u', rfl⟩ := key u a b
      rw [hM]; exact h2 u'
    · intro u
      by_cases a : u = v0
      · subst a; rw [h0]; exact hl
      by_cases b : u = w
      · subst b; rw [hw]; exact hl.symm
      obtain ⟨u', rfl⟩ := key u a b
      rw [hM]; exact h3 u'
  · intro σ _ τ _ h
    exact Perm.ofSubtype_injective (mul_left_cancel h)
  · intro M hM
    rw [Finset.mem_filter, mem_Mset] at hM
    obtain ⟨⟨h1, h2, h3⟩, h0⟩ := hM
    have hw : M w = v0 := by rw [← h0, h1]
    have hp : ∀ x, (M x ≠ v0 ∧ M x ≠ w) ↔ (x ≠ v0 ∧ x ≠ w) := by
      intro x
      constructor
      · rintro ⟨a, b⟩
        refine ⟨fun e => b ?_, fun e => a ?_⟩
        · rw [e, h0]
        · rw [e, hw]
      · rintro ⟨a, b⟩
        refine ⟨fun e => b ?_, fun e => a ?_⟩
        · have := h1 x; rw [e, h0] at this; exact this.symm
        · have := h1 x; rw [e, hw] at this; exact this.symm
    refine ⟨M.subtypePerm hp, ?_, ?_⟩
    · rw [mem_Mset]
      refine ⟨fun u => ?_, fun u => ?_, fun u => ?_⟩
      · apply Subtype.ext; simp [h1]
      · simpa using h2 u.1
      · simpa using h3 u.1
    · ext x
      by_cases a : x = v0
      · rw [a, Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem _ (fun h => h.1 rfl)]; simp [h0]
      by_cases b : x = w
      · rw [b, Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem _ (fun h => h.2 rfl)]; simp [hw]
      have : (Perm.ofSubtype (M.subtypePerm hp)) x = M x :=
        Perm.ofSubtype_subtypePerm_of_mem (p := fun v => v ≠ v0 ∧ v ≠ w) hp (show x ≠ v0 ∧ x ≠ w from ⟨a, b⟩)
      rw [Perm.mul_apply, this]
      exact swap_apply_of_ne_of_ne ((hp x).2 ⟨a, b⟩).1 ((hp x).2 ⟨a, b⟩).2

end



def cnt {V ι : Type*} [Fintype V] [DecidableEq ι] {ℓ : ℕ} (g : V → Fin ℓ) (lab : V → ι)
    (j : Fin ℓ) (i : ι) : ℕ :=
  (Finset.univ.filter (fun v => g v = j ∧ lab v = i)).card

lemma card_sub_aux {V : Type*} [Fintype V] [DecidableEq V] (q P : V → Prop) [DecidablePred q] [DecidablePred P] :
    Fintype.card {u : {v // q v} // P u.1} = (Finset.univ.filter (fun v => q v ∧ P v)).card := by
  rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter q P), Fintype.card_subtype]

lemma cnt_sub {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] {ℓ : ℕ}
    (g : V → Fin ℓ) (lab : V → ι) (v0 w : V) (hg : g w ≠ g v0) (hl : lab w = lab v0)
    (j : Fin ℓ) (i : ι) :
    cnt (fun v : {v // v ≠ v0 ∧ v ≠ w} => g v.1) (fun v : {v // v ≠ v0 ∧ v ≠ w} => lab v.1) j i =
      if i = lab v0 then
        Function.update (Function.update (fun j => cnt g lab j i) (g v0) (cnt g lab (g v0) i - 1))
          (g w) (cnt g lab (g w) i - 1) j
      else cnt g lab j i := by
  have hne : v0 ≠ w := fun h => hg (by rw [h])
  unfold cnt
  rw [← Fintype.card_subtype, card_sub_aux (fun v => v ≠ v0 ∧ v ≠ w) (fun v => g v = j ∧ lab v = i)]
  split_ifs with hi
  · subst hi
    by_cases h1 : j = g w
    · subst h1
      rw [Function.update_self]
      have : Finset.univ.filter (fun v => (v ≠ v0 ∧ v ≠ w) ∧ g v = g w ∧ lab v = lab v0) =
          (Finset.univ.filter (fun v => g v = g w ∧ lab v = lab v0)).erase w := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · rintro ⟨⟨a, b⟩, c⟩; exact ⟨b, c⟩
        · rintro ⟨b, c1, c2⟩; exact ⟨⟨fun e => hg (by rw [← e, c1]), b⟩, c1, c2⟩
      rw [this, Finset.card_erase_of_mem (by simp [hl])]
    by_cases h2 : j = g v0
    · subst h2
      rw [Function.update_of_ne h1, Function.update_self]
      have : Finset.univ.filter (fun v => (v ≠ v0 ∧ v ≠ w) ∧ g v = g v0 ∧ lab v = lab v0) =
          (Finset.univ.filter (fun v => g v = g v0 ∧ lab v = lab v0)).erase v0 := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · rintro ⟨⟨a, b⟩, c⟩; exact ⟨a, c⟩
        · rintro ⟨a, c1, c2⟩; exact ⟨⟨a, fun e => hg (by rw [← e]; exact c1)⟩, c1, c2⟩
      rw [this, Finset.card_erase_of_mem (by simp)]
    · rw [Function.update_of_ne h1, Function.update_of_ne h2]
      congr 1
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, c⟩; exact c
      · rintro ⟨c1, c2⟩
        exact ⟨⟨fun e => h2 (by rw [← c1, e]), fun e => h1 (by rw [← c1, e])⟩, c1, c2⟩
  · congr 1
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, c⟩; exact c
    · rintro ⟨c1, c2⟩
      exact ⟨⟨fun e => hi (by rw [← c2, e]), fun e => hi (by rw [← c2, e, hl])⟩, c1, c2⟩



lemma card_Mset_rec {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] {ℓ : ℕ} (g : V → Fin ℓ)
    (lab : V → ι) (v0 : V) :
    (Mset g lab).card = ∑ w ∈ Finset.univ.filter (fun w => g w ≠ g v0 ∧ lab w = lab v0),
      (Mset (fun v : {v // v ≠ v0 ∧ v ≠ w} => g v.1)
        (fun v : {v // v ≠ v0 ∧ v ≠ w} => lab v.1)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun M : Perm V => M v0)
    (t := Finset.univ.filter (fun w => g w ≠ g v0 ∧ lab w = lab v0))]
  · refine Finset.sum_congr rfl (fun w hw => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact card_Mset_fiber g lab v0 w hw.1 hw.2
  · intro M hM
    have hM' := (mem_Mset g lab M).1 hM
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨hM'.2.1 v0, hM'.2.2 v0⟩

theorem main_count {ι : Type v} [DecidableEq ι] {ℓ : ℕ} :
    ∀ (n : ℕ) {V : Type u} [Fintype V] [DecidableEq V], Fintype.card V = n →
      ∀ (g : V → Fin ℓ) (lab : V → ι) (S : Finset ι), (∀ v, lab v ∈ S) →
        ∏ i ∈ S, E1 (∏ j, He (cnt g lab j i)) = ((Mset g lab).card : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ hn g lab S hS
  by_cases hV : IsEmpty V
  · have h1 : Mset g lab = Finset.univ := by
      ext M
      simp only [Finset.mem_univ, iff_true, mem_Mset]
      exact ⟨fun u => isEmptyElim u, fun u => isEmptyElim u, fun u => isEmptyElim u⟩
    have h2 : ∀ j i, cnt g lab j i = 0 := by
      intro j i
      simp [cnt]
    rw [h1, Finset.card_univ, Fintype.card_perm]
    have : Fintype.card V = 0 := Fintype.card_eq_zero
    simp [h2, He_zero, E1_one, this]
  rw [not_isEmpty_iff] at hV
  obtain ⟨v0⟩ := hV
  set i0 := lab v0 with hi0
  set j0 := g v0 with hj0
  have hmem : i0 ∈ S := hS v0
  set a : Fin ℓ → ℕ := fun j => cnt g lab j i0 with ha
  have ha1 : a j0 = (a j0 - 1) + 1 := by
    have : 0 < a j0 := Finset.card_pos.2 ⟨v0, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, rfl⟩⟩
    omega
  have hrec := E1_rec a j0 (a j0 - 1) ha1
  rw [card_Mset_rec g lab v0, Nat.cast_sum, ← Finset.mul_prod_erase S _ hmem]
  have hterm : ∀ w ∈ Finset.univ.filter (fun w => g w ≠ g v0 ∧ lab w = lab v0),
      (((Mset (fun v : {v // v ≠ v0 ∧ v ≠ w} => g v.1)
        (fun v : {v // v ≠ v0 ∧ v ≠ w} => lab v.1)).card : ℕ) : ℝ) =
      E1 (∏ j, He (Function.update (Function.update a j0 (a j0 - 1)) (g w) (a (g w) - 1) j)) *
        ∏ i ∈ S.erase i0, E1 (∏ j, He (cnt g lab j i)) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rw [← ih (Fintype.card {v // v ≠ v0 ∧ v ≠ w}) (by
        rw [← hn]; exact Fintype.card_subtype_lt (p := fun v => v ≠ v0 ∧ v ≠ w) (x := v0)
          (by simp)) rfl _ _ S (fun v => hS v.1),
      ← Finset.mul_prod_erase S _ hmem]
    congr 1
    · simp only [cnt_sub g lab v0 w hw.1 hw.2, if_pos hi0]
      rfl
    · refine Finset.prod_congr rfl (fun i hi => ?_)
      have : i ≠ lab v0 := (Finset.mem_erase.1 hi).1
      simp only [cnt_sub g lab v0 w hw.1 hw.2, this, if_false]
  rw [Finset.sum_congr rfl hterm, hrec, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (s := Finset.univ.filter (fun w => g w ≠ g v0 ∧ lab w = lab v0))
    (t := Finset.univ.erase j0) (by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simpa using hw.1)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≠ j0 := (Finset.mem_erase.1 hk).1
  rw [Finset.sum_congr rfl (g := fun _ => E1 (∏ j, He (Function.update (Function.update a j0 (a j0 - 1)) k (a k - 1) j)) *
        ∏ i ∈ S.erase i0, E1 (∏ j, He (cnt g lab j i))) (fun w hw => by
      simp only [Finset.mem_filter] at hw
      rw [hw.2])]
  rw [Finset.sum_const, nsmul_eq_mul]
  have : ((Finset.univ.filter (fun w => g w ≠ g v0 ∧ lab w = lab v0)).filter (fun w => g w = k)).card = a k := by
    simp only [ha, cnt]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨by rw [h3]; exact hk', h2⟩, h3⟩
  rw [this]
  ring


lemma hermite_zero_real : GaussPolyReg.Approx.hermite 0 = fun _ => 1 := by
  ext x; rw [hermite_eq, He_zero]; simp

lemma analytic_reduce {I : Type u} [DecidableEq I] (ℓ : ℕ) (α : Fin ℓ → I →₀ ℕ) :
    (∫ x, ∏ j, GaussPolyReg.Approx.heMulti (α j) x ∂GaussPolyReg.Approx.gaussianProduct I) =
      ∏ i ∈ Finset.univ.biUnion (fun j => (α j).support), E1 (∏ j, He (α j i)) := by
  classical
  set S : Finset I := Finset.univ.biUnion (fun j => (α j).support) with hS
  have hfun : ∀ x : I → ℝ, ∏ j, GaussPolyReg.Approx.heMulti (α j) x =
      ∏ i : S, (∏ j, He (α j i)).eval (x i) := by
    intro x
    have h1 : ∀ j, GaussPolyReg.Approx.heMulti (α j) x =
        ∏ i ∈ S, (He (α j i)).eval (x i) := by
      intro j
      unfold GaussPolyReg.Approx.heMulti
      rw [Finsupp.prod_of_support_subset (α j) (s := S)
        (fun i hi => Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hi⟩)
        _ (by intro i _; rw [hermite_zero_real])]
      exact Finset.prod_congr rfl (fun i _ => hermite_eq _ _)
    simp_rw [h1, eval_prod]
    rw [Finset.prod_comm, Finset.prod_coe_sort S (fun i => ∏ j, (He (α j i)).eval (x i))]
  simp_rw [hfun]
  have := MeasureTheory.integral_restrict_infinitePi (μ := fun _ : I => gaussianReal 0 1)
    (s := S) (f := fun y : (i : S) → ℝ => ∏ i : S, (∏ j, He (α j i)).eval (y i))
    (by
      apply Continuous.aestronglyMeasurable
      refine continuous_finsetProd _ (fun i _ => ?_)
      exact (Polynomial.continuous _).comp (continuous_apply i))
  unfold GaussPolyReg.Approx.gaussianProduct
  rw [show (fun x : I → ℝ => ∏ i : S, (∏ j, He (α j i)).eval (x i)) =
    fun x => (fun y : (i : S) → ℝ => ∏ i : S, (∏ j, He (α j i)).eval (y i)) (S.restrict x) from rfl, this]
  rw [MeasureTheory.integral_fintype_prod_eq_prod (fun (i : S) (t : ℝ) => (∏ j, He (α j i)).eval t)]
  exact Finset.prod_coe_sort S (fun i => E1 (∏ j, He (α j i)))


lemma cnt_matching {I : Type u} [DecidableEq I] {ℓ : ℕ} (α : Fin ℓ → I →₀ ℕ)
    [Fintype (GaussPolyReg.Approx.MatchingObjects α)] (j : Fin ℓ) (i : I) :
    cnt (fun u : GaussPolyReg.Approx.MatchingObjects α => u.1)
      (fun u => u.2.1.val) j i = α j i := by
  unfold cnt
  by_cases hi : i ∈ (α j).support
  · have : Finset.univ.filter (fun u : GaussPolyReg.Approx.MatchingObjects α =>
        u.1 = j ∧ u.2.1.val = i) =
        Finset.univ.image (fun t : Fin (α j i) => (⟨j, ⟨i, hi⟩, t⟩ : GaussPolyReg.Approx.MatchingObjects α)) := by
      ext ⟨j', ⟨i', h'⟩, t⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨h1, h2⟩
        replace h1 : j' = j := h1
        replace h2 : i' = i := h2
        subst h1; subst h2
        exact ⟨t, rfl⟩
      · rintro ⟨t', ht⟩
        exact ⟨(congrArg (fun u : GaussPolyReg.Approx.MatchingObjects α => u.1) ht).symm,
          (congrArg (fun u : GaussPolyReg.Approx.MatchingObjects α => u.2.1.val) ht).symm⟩
    rw [this, Finset.card_image_of_injective _ (by
      intro t t' h
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
      simpa using h)]
    simp
  · have : Finset.univ.filter (fun u : GaussPolyReg.Approx.MatchingObjects α =>
        u.1 = j ∧ u.2.1.val = i) = ∅ := by
      ext ⟨j', ⟨i', h'⟩, t⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2⟩
      replace h1 : j' = j := h1
      replace h2 : i' = i := h2
      subst h1; subst h2
      exact hi h'
    rw [this]
    simp [Finsupp.notMem_support_iff.1 hi]

end GPR

theorem solution {I : Type*} (ℓ : ℕ) (α : Fin ℓ → I →₀ ℕ) :
    (∫ x, ∏ j, GaussPolyReg.Approx.heMulti (α j) x ∂GaussPolyReg.Approx.gaussianProduct I) =
      ((GaussPolyReg.Approx.labelMatchings α).card : ℝ) := by
  classical
  rw [GPR.analytic_reduce]
  have hmain := GPR.main_count (ι := I) (ℓ := ℓ) (Fintype.card (GaussPolyReg.Approx.MatchingObjects α))
    (V := GaussPolyReg.Approx.MatchingObjects α) rfl (fun u => u.1) (fun u => u.2.1.val)
    (Finset.univ.biUnion (fun j => (α j).support))
    (fun u => Finset.mem_biUnion.2 ⟨u.1, Finset.mem_univ _, u.2.1.2⟩)
  have hc : ∀ j i, GPR.cnt (fun u : GaussPolyReg.Approx.MatchingObjects α => u.1)
      (fun u => u.2.1.val) j i = α j i := fun j i => GPR.cnt_matching α j i
  simp_rw [hc] at hmain
  rw [hmain]
  congr 2
