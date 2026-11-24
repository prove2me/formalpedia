-- Prove2me | solution 1 for GaussPolyReg.Approx.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T22:29:59.693128+00:00
-- url     : https://prove2.me/submissions/c978347e-906c-437e-b481-648164caff91

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Ultra

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx


def bil {n d : ℕ} (P : Tensor n d) (r : ℕ) (U : (Fin r → Fin n) → ℝ)
    (V : (Fin (d-r) → Fin n) → ℝ) : ℝ :=
  ∑ i, ∑ j, U i * flatten P r i j * V j

def SymTensor {n d : ℕ} (T : Tensor n d) : Prop :=
  ∀ σ : Equiv.Perm (Fin d), ∀ i, T (i ∘ σ) = T i

lemma euclid_norm_eq {J : Type*} [Fintype J] (T : J → ℝ) :
    ‖(WithLp.toLp 2 T : EuclideanSpace ℝ J)‖ = frobenius T := by
  rw [EuclideanSpace.norm_eq]; simp [frobenius]

/-- precomposition with a permutation, as an equivalence of tuples -/
def permArrow {n m : ℕ} (σ : Equiv.Perm (Fin m)) : (Fin m → Fin n) ≃ (Fin m → Fin n) where
  toFun i := i ∘ σ
  invFun i := i ∘ σ.symm
  left_inv i := by funext s; simp
  right_inv i := by funext s; simp

def symAvg {n m : ℕ} (u : (Fin m → Fin n) → ℝ) : Tensor n m :=
  fun i => ((m.factorial : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin m), u (i ∘ σ)

lemma symAvg_sym {n m : ℕ} (u : (Fin m → Fin n) → ℝ) : SymTensor (symAvg u) := by
  intro τ i
  unfold symAvg
  congr 1
  refine (Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => u (i ∘ σ))).symm.trans ?_ |>.symm
  rfl

lemma frobenius_comp {n m : ℕ} (u : (Fin m → Fin n) → ℝ) (σ : Equiv.Perm (Fin m)) :
    frobenius (fun i => u (i ∘ σ)) = frobenius u := by
  unfold frobenius
  congr 1
  exact Equiv.sum_comp (permArrow σ) (fun i => u i ^ 2)

lemma frobenius_symAvg {n m : ℕ} (u : (Fin m → Fin n) → ℝ) :
    frobenius (symAvg u) ≤ frobenius u := by
  have e : (WithLp.toLp 2 (symAvg u) : EuclideanSpace ℝ (Fin m → Fin n)) =
      ((m.factorial : ℝ))⁻¹ • ∑ σ : Equiv.Perm (Fin m),
        (WithLp.toLp 2 (fun i => u (i ∘ σ)) : EuclideanSpace ℝ (Fin m → Fin n)) := by
    ext i
    simp [symAvg, Finset.sum_apply]
  rw [← euclid_norm_eq, e, norm_smul]
  have h := norm_sum_le (Finset.univ : Finset (Equiv.Perm (Fin m)))
    (fun σ => (WithLp.toLp 2 (fun i => u (i ∘ σ)) : EuclideanSpace ℝ (Fin m → Fin n)))
  simp only [euclid_norm_eq, frobenius_comp, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at h
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hf)]
  calc (m.factorial : ℝ)⁻¹ * _ ≤ (m.factorial : ℝ)⁻¹ * (m.factorial * frobenius u) := by gcongr
    _ = frobenius u := by field_simp

lemma symmetrize (n d r : ℕ) (P : Tensor n d)
    (h1 : ∀ (σ : Equiv.Perm (Fin r)) i j, flatten P r (i ∘ σ) j = flatten P r i j)
    (h2 : ∀ (σ : Equiv.Perm (Fin (d-r))) i j, flatten P r i (j ∘ σ) = flatten P r i j)
    (u : EuclideanSpace ℝ (Fin r → Fin n)) (v : EuclideanSpace ℝ (Fin (d-r) → Fin n)) :
    ∃ (U : Tensor n r) (V : Tensor n (d-r)), SymTensor U ∧ SymTensor V ∧
      frobenius U ≤ ‖u‖ ∧ frobenius V ≤ ‖v‖ ∧ bil P r U V = ∑ i, ∑ j, u i * flatten P r i j * v j := by
  refine ⟨symAvg (fun i => u i), symAvg (fun j => v j), symAvg_sym _, symAvg_sym _, ?_, ?_, ?_⟩
  · refine (frobenius_symAvg _).trans (le_of_eq ?_)
    rw [EuclideanSpace.norm_eq]; simp [frobenius]
  · refine (frobenius_symAvg _).trans (le_of_eq ?_)
    rw [EuclideanSpace.norm_eq]; simp [frobenius]
  · have key : ∀ (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin (d-r))),
        ∑ i, ∑ j, u (i ∘ σ) * flatten P r i j * v (j ∘ τ) =
          ∑ i, ∑ j, u i * flatten P r i j * v j := by
      intro σ τ
      rw [← Equiv.sum_comp (permArrow σ.symm)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Equiv.sum_comp (permArrow τ.symm)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [permArrow, Equiv.coe_fn_mk]
      rw [h1, h2]
      have ei : (i ∘ ⇑σ.symm) ∘ ⇑σ = i := by funext s; simp
      have ej : (j ∘ ⇑τ.symm) ∘ ⇑τ = j := by funext s; simp
      rw [ei, ej]
    unfold bil symAvg
    have e : ∀ i j, (((r.factorial : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin r), u (i ∘ σ)) *
        flatten P r i j * (((d-r).factorial : ℝ)⁻¹ * ∑ τ : Equiv.Perm (Fin (d-r)), v (j ∘ τ)) =
        ((r.factorial : ℝ))⁻¹ * ((d-r).factorial : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin r), ∑ τ : Equiv.Perm (Fin (d-r)),
            u (i ∘ σ) * flatten P r i j * v (j ∘ τ) := by
      intro i j
      rw [show ∀ (a b S1 S2 F : ℝ), a * S1 * F * (b * S2) = a * b * (S1 * S2 * F) by
        intros; ring, Finset.sum_mul_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      ring
    simp only [e]
    have sw : ∀ (T : (Fin r → Fin n) → (Fin (d-r) → Fin n) → Equiv.Perm (Fin r) →
        Equiv.Perm (Fin (d-r)) → ℝ),
        ∑ i, ∑ j, ∑ σ, ∑ τ, T i j σ τ = ∑ σ, ∑ τ, ∑ i, ∑ j, T i j σ τ := by
      intro T
      calc ∑ i, ∑ j, ∑ σ, ∑ τ, T i j σ τ = ∑ i, ∑ σ, ∑ j, ∑ τ, T i j σ τ :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ i, ∑ σ, ∑ τ, ∑ j, T i j σ τ :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun σ _ => Finset.sum_comm
        _ = ∑ σ, ∑ i, ∑ τ, ∑ j, T i j σ τ := Finset.sum_comm
        _ = ∑ σ, ∑ τ, ∑ i, ∑ j, T i j σ τ :=
            Finset.sum_congr rfl fun σ _ => Finset.sum_comm
    rw [show ∀ c : ℝ, ∀ T : (Fin r → Fin n) → (Fin (d-r) → Fin n) → Equiv.Perm (Fin r) →
        Equiv.Perm (Fin (d-r)) → ℝ, ∑ i, ∑ j, c * ∑ σ, ∑ τ, T i j σ τ =
          c * ∑ σ, ∑ τ, ∑ i, ∑ j, T i j σ τ by
        intro c T; rw [← sw]; simp [Finset.mul_sum]]
    simp_rw [key, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul]
    have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
    have hf' : (0 : ℝ) < (d-r).factorial := by exact_mod_cast Nat.factorial_pos (d-r)
    field_simp



lemma tupleIndex_comp {n d : ℕ} (i : Fin d → Fin n) (σ : Equiv.Perm (Fin d)) :
    tupleIndex (i ∘ σ) = tupleIndex i := by
  unfold tupleIndex
  exact Equiv.sum_comp σ (fun s => Finsupp.single (i s).val (1 : ℕ))

lemma tupleIndex_concat {n d r : ℕ} (hrd : r ≤ d) (i : Fin r → Fin n) (j : Fin (d-r) → Fin n) :
    tupleIndex (fun s : Fin d => if h : s.val < r then i ⟨s.val, h⟩
      else j ⟨s.val-r, by omega⟩) = tupleIndex i + tupleIndex j := by
  unfold tupleIndex
  let f : ℕ → ℕ →₀ ℕ := fun s => if h : s < r then Finsupp.single (i ⟨s, h⟩).val 1
    else if h' : s < d then Finsupp.single (j ⟨s - r, by omega⟩).val 1 else 0
  have e1 : ∑ s : Fin d, Finsupp.single ((if h : s.val < r then i ⟨s.val, h⟩
      else j ⟨s.val-r, by omega⟩)).val 1 = ∑ s : Fin d, f s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [f]
    split_ifs <;> first | rfl | omega
  have e2 : ∑ s : Fin r, Finsupp.single (i s).val 1 = ∑ s : Fin r, f s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [f, s.isLt]
  have e3 : ∑ s : Fin (d-r), Finsupp.single (j s).val 1 = ∑ s : Fin (d-r), f (r + s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    have h1 : ¬ (r + s.val < r) := by omega
    have h2 : r + s.val < d := by omega
    simp only [f, h1, h2, dite_false, dite_true]
    congr 3
    ext; simp
  rw [e1, e2, e3, Fin.sum_univ_eq_sum_range f, Fin.sum_univ_eq_sum_range f,
    Fin.sum_univ_eq_sum_range (fun s => f (r + s)),
    show Finset.range d = Finset.range (r + (d-r)) by congr 1; omega, Finset.sum_range_add]

lemma coefficientTensor_blockSym (n d r : ℕ) (hrd : r ≤ d) (p : Original) :
    (∀ (σ : Equiv.Perm (Fin r)) i j,
      flatten (coefficientTensor (n := n) (d := d) p) r (i ∘ σ) j =
        flatten (coefficientTensor (n := n) (d := d) p) r i j) ∧
    (∀ (σ : Equiv.Perm (Fin (d-r))) i j,
      flatten (coefficientTensor (n := n) (d := d) p) r i (j ∘ σ) =
        flatten (coefficientTensor (n := n) (d := d) p) r i j) := by
  constructor
  · intro σ i j
    unfold flatten coefficientTensor
    rw [tupleIndex_concat hrd, tupleIndex_concat hrd, tupleIndex_comp]
  · intro σ i j
    unfold flatten coefficientTensor
    rw [tupleIndex_concat hrd, tupleIndex_concat hrd, tupleIndex_comp]


/-! ## Hermite layer -/

def He {n m : ℕ} (i : Fin m → Fin n) : Sample → ℝ := heMulti (tupleIndex i)

def W {n m : ℕ} (i j : Fin m → Fin n) : ℝ := ∫ x, He i x * He j x ∂gaussianProduct ℕ

lemma W_comm {n m : ℕ} (i j : Fin m → Fin n) : W i j = W j i := by
  unfold W; simp_rw [mul_comm (He i _)]

section Analytic
open Polynomial

abbrev γ1 : Measure ℝ := gaussianReal 0 1

lemma integrable_pow_gauss (k : ℕ) : Integrable (fun x : ℝ => x ^ k) γ1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (k : NNReal)).integrable_norm_pow
    (by omega)
  refine h.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  simp [norm_pow]

lemma integrable_poly (f : ℝ[X]) : Integrable (fun x => f.eval x) γ1 := by
  have : (fun x => f.eval x) = fun x => ∑ k ∈ Finset.range (f.natDegree + 1), f.coeff k * x ^ k := by
    funext x; exact eval_eq_sum_range x
  rw [this]
  exact integrable_finsetSum _ fun k _ => (integrable_pow_gauss k).const_mul _

lemma integrable_pdf_poly (f : ℝ[X]) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f.eval x) volume := by
  have h := integrable_poly f
  rw [γ1, gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
  refine h.congr (ae_of_all _ fun x => ?_)
  simp [toReal_gaussianPDF]

def gE (f : ℝ[X]) : ℝ := ∫ x, f.eval x ∂γ1

lemma gE_eq (f : ℝ[X]) : gE f = ∫ x, gaussianPDFReal 0 1 x * f.eval x := by
  unfold gE; rw [integral_gaussianReal_eq_integral_smul one_ne_zero]; rfl

lemma gE_add (f g : ℝ[X]) : gE (f + g) = gE f + gE g := by
  unfold gE; simp only [eval_add]; exact integral_add (integrable_poly f) (integrable_poly g)

lemma gE_sub (f g : ℝ[X]) : gE (f - g) = gE f - gE g := by
  unfold gE; simp only [eval_sub]; exact integral_sub (integrable_poly f) (integrable_poly g)

lemma gE_C (a : ℝ) : gE (C a) = a := by simp [gE]

lemma hasDerivAt_pdf (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x :=
    ((hasDerivAt_pow 2 x).neg.div_const 2).congr_deriv (by norm_num; ring)
  have := (h.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  have e : gaussianPDFReal 0 1 = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    funext y; simp [gaussianPDFReal]
  simp only [e]
  exact this.congr_deriv (by ring)

/-- Gaussian integration by parts (Stein's identity) for polynomials. -/
lemma gE_X_mul (f : ℝ[X]) : gE (X * f) = gE (derivative f) := by
  rw [gE_eq, gE_eq]
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x => f.eval x)
    (u' := fun x => (derivative f).eval x) (v := gaussianPDFReal 0 1)
    (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => Polynomial.hasDerivAt f x) (fun x _ => hasDerivAt_pdf x)
    (by
      have := (integrable_pdf_poly (-(X * f)))
      refine this.congr (ae_of_all _ fun x => ?_)
      simp; ring)
    (by
      have := (integrable_pdf_poly (derivative f))
      refine this.congr (ae_of_all _ fun x => ?_)
      simp; ring)
    (by
      have := (integrable_pdf_poly f)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp; ring)
  have e1 : ∫ x, gaussianPDFReal 0 1 x * (X * f).eval x =
      -∫ x, f.eval x * (-x * gaussianPDFReal 0 1 x) := by
    rw [← integral_neg]; congr 1; funext x; simp; ring
  have e2 : ∫ x, gaussianPDFReal 0 1 x * (derivative f).eval x =
      ∫ x, (derivative f).eval x * gaussianPDFReal 0 1 x := by
    congr 1; funext x; ring
  rw [e1, e2, h, neg_neg]

def Hr (a : ℕ) : ℝ[X] := (Polynomial.hermite a).map (Int.castRingHom ℝ)

lemma hermite_eq_Hr (a : ℕ) (x : ℝ) : hermite a x = (Hr a).eval x := by
  simp [hermite, Hr, aeval_def, eval₂_eq_eval_map]

lemma Hr_succ (a : ℕ) : Hr (a + 1) = X * Hr a - derivative (Hr a) := by
  simp [Hr, Polynomial.hermite_succ, Polynomial.derivative_map]

lemma natDegree_Hr (a : ℕ) : (Hr a).natDegree = a := by
  unfold Hr
  rw [natDegree_map_eq_of_injective (RingHom.injective_int _), Polynomial.natDegree_hermite]

lemma coeff_Hr_self (a : ℕ) : (Hr a).coeff a = 1 := by
  simp [Hr, Polynomial.coeff_hermite_self]

lemma gE_Hr_mul (c : ℕ) : ∀ q : ℝ[X], q.natDegree ≤ c →
    gE (Hr c * q) = c.factorial * q.coeff c := by
  induction c with
  | zero =>
    intro q hq
    rw [eq_C_of_natDegree_le_zero hq]
    simp [Hr, gE_C]
  | succ c ih =>
    intro q hq
    have hd : (derivative q).natDegree ≤ c := by
      have := natDegree_derivative_le q; omega
    rw [Hr_succ, sub_mul, gE_sub, mul_assoc, gE_X_mul, derivative_mul, gE_add, add_sub_cancel_left,
      ih _ hd, coeff_derivative, Nat.factorial_succ]
    push_cast; ring


lemma multiDegree_eq_degree (α : ℕ →₀ ℕ) : multiDegree α = Finsupp.degree α := rfl

lemma gE_Hr_Hr (a b : ℕ) : gE (Hr a * Hr b) = if a = b then (a.factorial : ℝ) else 0 := by
  rcases le_or_gt b a with h | h
  · rw [gE_Hr_mul a (Hr b) (by rw [natDegree_Hr]; exact h)]
    split_ifs with hab
    · subst hab; rw [coeff_Hr_self]; ring
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_Hr]; omega)]; ring
  · rw [mul_comm, gE_Hr_mul b (Hr a) (by rw [natDegree_Hr]; exact h.le),
      coeff_eq_zero_of_natDegree_lt (by rw [natDegree_Hr]; omega), if_neg (by omega)]
    ring

lemma gE_Hr_three (a b c : ℕ) (h : a + b ≤ c) :
    gE (Hr c * (Hr a * Hr b)) = if c = a + b then (c.factorial : ℝ) else 0 := by
  have hd : (Hr a * Hr b).natDegree ≤ a + b :=
    (natDegree_mul_le).trans (by rw [natDegree_Hr, natDegree_Hr])
  rw [gE_Hr_mul c _ (hd.trans h)]
  split_ifs with hc
  · subst hc
    have := coeff_mul_degree_add_degree (Hr a) (Hr b)
    rw [natDegree_Hr, natDegree_Hr] at this
    rw [this, leadingCoeff, leadingCoeff, natDegree_Hr, natDegree_Hr, coeff_Hr_self,
      coeff_Hr_self]; ring
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; ring

lemma integrable_coordProd (N : ℕ) (f : ℕ → ℝ[X]) :
    Integrable (fun x : Sample => ∏ m ∈ Finset.range N, (f m).eval (x m))
      (gaussianProduct ℕ) := by
  set s := Finset.range N
  let F : (Π i : s, ℝ) → ℝ := fun y => ∏ m : s, (f m).eval (y m)
  have hF : Continuous F := by fun_prop
  have e : (fun x : Sample => ∏ m ∈ s, (f m).eval (x m)) = F ∘ s.restrict := by
    funext x; simp only [F, Function.comp, Finset.restrict]
    exact (Finset.prod_coe_sort s (fun m => (f m).eval (x m))).symm
  rw [e, gaussianProduct]
  rw [← integrable_map_measure (μ := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
    hF.aestronglyMeasurable (Finset.measurable_restrict s).aemeasurable,
    Measure.infinitePi_map_restrict]
  exact Integrable.fintype_prod (f := fun (m : s) t => (f m).eval t)
    (fun m => integrable_poly (f m))

lemma integral_coordProd (N : ℕ) (f : ℕ → ℝ[X]) :
    ∫ x : Sample, ∏ m ∈ Finset.range N, (f m).eval (x m) ∂gaussianProduct ℕ =
      ∏ m ∈ Finset.range N, gE (f m) := by
  set s := Finset.range N
  let F : (Π i : s, ℝ) → ℝ := fun y => ∏ m : s, (f m).eval (y m)
  have hF : Continuous F := by fun_prop
  have e : (fun x : Sample => ∏ m ∈ s, (f m).eval (x m)) = fun x => F (s.restrict x) := by
    funext x; simp only [F, Finset.restrict]
    exact (Finset.prod_coe_sort s (fun m => (f m).eval (x m))).symm
  have h1 := integral_restrict_infinitePi (μ := fun _ : ℕ => gaussianReal 0 1) (s := s)
    (f := F) hF.aestronglyMeasurable
  rw [e, gaussianProduct, h1]
  rw [integral_fintype_prod_eq_prod (f := fun (m : s) t => (f m).eval t)]
  exact Finset.prod_coe_sort s (fun m => gE (f m))

lemma heMulti_eq (α : ℕ →₀ ℕ) (N : ℕ) (h : α.support ⊆ Finset.range N) (x : Sample) :
    heMulti α x = ∏ m ∈ Finset.range N, (Hr (α m)).eval (x m) := by
  unfold heMulti
  rw [Finsupp.prod_of_support_subset α h _ (fun m _ => by simp [hermite])]
  simp_rw [hermite_eq_Hr]

lemma multiFactorial_eq (α : ℕ →₀ ℕ) (N : ℕ) (h : α.support ⊆ Finset.range N) :
    (multiFactorial α : ℝ) = ∏ m ∈ Finset.range N, ((α m).factorial : ℝ) := by
  unfold multiFactorial
  rw [Finsupp.prod_of_support_subset α h _ (fun m _ => by simp)]
  push_cast; rfl

lemma exists_N (α β γ : ℕ →₀ ℕ) : ∃ N, α.support ⊆ Finset.range N ∧
    β.support ⊆ Finset.range N ∧ γ.support ⊆ Finset.range N := by
  refine ⟨(α.support ∪ β.support ∪ γ.support).sup id + 1, ?_, ?_, ?_⟩ <;>
  · intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (f := id) (by simp [hk])

lemma heMulti_continuous (α : ℕ →₀ ℕ) : Continuous (heMulti α) := by
  obtain ⟨N, h, -, -⟩ := exists_N α 0 0
  have : heMulti α = fun x => ∏ m ∈ Finset.range N, (Hr (α m)).eval (x m) :=
    funext (heMulti_eq α N h)
  rw [this]; fun_prop

lemma memLp_heMulti (α : ℕ →₀ ℕ) : MemLp (heMulti α) 2 (gaussianProduct ℕ) := by
  obtain ⟨N, h, -, -⟩ := exists_N α 0 0
  rw [memLp_two_iff_integrable_sq (heMulti_continuous α).aestronglyMeasurable]
  refine (integrable_coordProd N (fun m => Hr (α m) * Hr (α m))).congr (ae_of_all _ fun x => ?_)
  simp only [heMulti_eq α N h x, eval_mul, Finset.prod_mul_distrib, sq]

lemma memLp_heMulti_mul (α β : ℕ →₀ ℕ) :
    MemLp (fun x => heMulti α x * heMulti β x) 2 (gaussianProduct ℕ) := by
  obtain ⟨N, h, h', -⟩ := exists_N α β 0
  have hc : Continuous (fun x => heMulti α x * heMulti β x) :=
    (heMulti_continuous α).mul (heMulti_continuous β)
  rw [memLp_two_iff_integrable_sq hc.aestronglyMeasurable]
  refine (integrable_coordProd N (fun m => (Hr (α m) * Hr (β m)) * (Hr (α m) * Hr (β m)))).congr
    (ae_of_all _ fun x => ?_)
  simp only [heMulti_eq α N h x, heMulti_eq β N h' x, eval_mul, Finset.prod_mul_distrib, sq]

lemma integral_heMulti_mul (α β : ℕ →₀ ℕ) :
    ∫ x, heMulti α x * heMulti β x ∂gaussianProduct ℕ =
      if α = β then (multiFactorial α : ℝ) else 0 := by
  obtain ⟨N, h, h', -⟩ := exists_N α β 0
  have e : (fun x => heMulti α x * heMulti β x) =
      fun x : Sample => ∏ m ∈ Finset.range N, (Hr (α m) * Hr (β m)).eval (x m) := by
    funext x; simp only [heMulti_eq α N h x, heMulti_eq β N h' x, eval_mul,
      Finset.prod_mul_distrib]
  rw [e, integral_coordProd]
  simp_rw [gE_Hr_Hr]
  split_ifs with hab
  · subst hab
    rw [multiFactorial_eq α N h]
    exact Finset.prod_congr rfl fun m _ => if_pos rfl
  · obtain ⟨m, hm⟩ : ∃ m, α m ≠ β m := by
      by_contra hc; push Not at hc; exact hab (Finsupp.ext hc)
    have hmN : m ∈ Finset.range N := by
      by_contra hn
      have h1 : α m = 0 := Finsupp.notMem_support_iff.mp (fun hh => hn (h hh))
      have h2 : β m = 0 := Finsupp.notMem_support_iff.mp (fun hh => hn (h' hh))
      exact hm (h1.trans h2.symm)
    exact Finset.prod_eq_zero hmN (if_neg hm)

lemma exists_gt_of_ne (α β γ : ℕ →₀ ℕ)
    (h : multiDegree γ = multiDegree α + multiDegree β) (hne : γ ≠ α + β) :
    ∃ m, α m + β m < γ m := by
  by_contra hc
  push Not at hc
  have hle : γ ≤ α + β := fun m => by simpa using hc m
  have h1 : Finsupp.degree (α + β) = Finsupp.degree γ + Finsupp.degree (α + β - γ) := by
    rw [← map_add, add_tsub_cancel_of_le hle]
  rw [map_add, ← multiDegree_eq_degree, ← multiDegree_eq_degree, ← multiDegree_eq_degree,
    ← h] at h1
  have h2 : Finsupp.degree (α + β - γ) = 0 := by omega
  rw [Finsupp.degree_eq_zero_iff] at h2
  apply hne
  exact le_antisymm hle (tsub_eq_zero_iff_le.mp h2)

lemma integral_heMulti_three (α β γ : ℕ →₀ ℕ)
    (h : multiDegree γ = multiDegree α + multiDegree β) :
    ∫ x, heMulti γ x * (heMulti α x * heMulti β x) ∂gaussianProduct ℕ =
      ∫ x, heMulti γ x * heMulti (α + β) x ∂gaussianProduct ℕ := by
  rw [integral_heMulti_mul]
  obtain ⟨N, hα, hβ, hγ⟩ := exists_N α β γ
  have e : (fun x => heMulti γ x * (heMulti α x * heMulti β x)) =
      fun x : Sample => ∏ m ∈ Finset.range N,
        (Hr (γ m) * (Hr (α m) * Hr (β m))).eval (x m) := by
    funext x; simp only [heMulti_eq α N hα x, heMulti_eq β N hβ x, heMulti_eq γ N hγ x,
      eval_mul, Finset.prod_mul_distrib]
  rw [e, integral_coordProd]
  split_ifs with hab
  · rw [multiFactorial_eq γ N hγ]
    refine Finset.prod_congr rfl fun m _ => ?_
    have hm : γ m = α m + β m := by rw [hab]; rfl
    rw [gE_Hr_three _ _ _ hm.ge, if_pos hm]
  · obtain ⟨m, hm⟩ := exists_gt_of_ne α β γ h hab
    have hmN : m ∈ Finset.range N := hγ (Finsupp.mem_support_iff.mpr (by omega))
    refine Finset.prod_eq_zero hmN ?_
    rw [gE_Hr_three _ _ _ hm.le, if_neg (by omega)]

end Analytic

/-! ## combinatorics of tuples -/

lemma tupleIndex_apply {n m : ℕ} (i : Fin m → Fin n) (k : ℕ) :
    tupleIndex i k = (Finset.univ.filter fun s => (i s).val = k).card := by
  unfold tupleIndex
  rw [Finsupp.finset_sum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.single_apply]

lemma multiDegree_tupleIndex {n m : ℕ} (i : Fin m → Fin n) :
    multiDegree (tupleIndex i) = m := by
  unfold multiDegree tupleIndex
  rw [← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp

lemma tupleIndex_support {n m : ℕ} (i : Fin m → Fin n) :
    ∀ k ∈ (tupleIndex i).support, k < n := by
  intro k hk
  rw [Finsupp.mem_support_iff, tupleIndex_apply] at hk
  obtain ⟨s, hs⟩ := Finset.card_ne_zero.mp hk
  rw [Finset.mem_filter] at hs
  rw [← hs.2]; exact (i s).isLt

lemma card_fiber_eq {n m : ℕ} (i : Fin m → Fin n) (c : Fin n) :
    Fintype.card {s // i s = c} = tupleIndex i c.val := by
  rw [tupleIndex_apply, Fintype.card_subtype]
  congr 1
  ext s; simp [Fin.ext_iff]

lemma exists_perm_of_tupleIndex_eq {n m : ℕ} (i j : Fin m → Fin n)
    (h : tupleIndex i = tupleIndex j) : ∃ τ : Equiv.Perm (Fin m), i = j ∘ τ := by
  have e : ∀ c : Fin n, {s // j s = c} ≃ {s // i s = c} := fun c =>
    Fintype.equivOfCardEq (by rw [card_fiber_eq, card_fiber_eq, h])
  refine ⟨(Equiv.ofFiberEquiv e).symm, ?_⟩
  funext s
  have := Equiv.ofFiberEquiv_map e ((Equiv.ofFiberEquiv e).symm s)
  simp only [Equiv.apply_symm_apply] at this
  simp [this]

lemma multiFactorial_tupleIndex {n m : ℕ} (j : Fin m → Fin n) :
    multiFactorial (tupleIndex j) = ∏ c : Fin n, (Fintype.card {s // j s = c}).factorial := by
  unfold multiFactorial
  rw [Finsupp.prod_of_support_subset _ (s := Finset.range n)
    (fun k hk => Finset.mem_range.mpr (tupleIndex_support j k hk)) _ (fun _ _ => rfl)]
  rw [← Fin.prod_univ_eq_prod_range (fun k => ((tupleIndex j) k).factorial)]
  simp_rw [card_fiber_eq]

lemma card_fiber_mul {n m : ℕ} (j : Fin m → Fin n) :
    (Finset.univ.filter fun i : Fin m → Fin n => tupleIndex i = tupleIndex j).card *
      multiFactorial (tupleIndex j) = m.factorial := by
  classical
  set F := Finset.univ.filter fun i : Fin m → Fin n => tupleIndex i = tupleIndex j
  have hstab : ∀ i ∈ F, (Finset.univ.filter fun σ : Equiv.Perm (Fin m) => j ∘ σ = i).card =
      multiFactorial (tupleIndex j) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨τ, rfl⟩ := exists_perm_of_tupleIndex_eq i j hi.2
    rw [multiFactorial_tupleIndex, ← DomMulAct.stabilizer_card, ← Fintype.card_coe]
    refine Fintype.card_congr ?_
    exact {
      toFun := fun σ => ⟨σ.1 * τ⁻¹, by
        have h := (Finset.mem_filter.mp σ.2).2
        rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, h]
        funext s; simp⟩
      invFun := fun g => ⟨g.1 * τ, by
        rw [Finset.mem_filter, Equiv.Perm.coe_mul, ← Function.comp_assoc, g.2]
        exact ⟨Finset.mem_univ _, rfl⟩⟩
      left_inv := fun σ => by ext; simp
      right_inv := fun g => by ext; simp }
  have hmaps : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))), j ∘ σ ∈ F := by
    intro σ _
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, tupleIndex_comp j σ⟩
  have := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at this
  rw [this, Finset.sum_congr rfl hstab, Finset.sum_const, smul_eq_mul]

lemma exists_tuple {n d : ℕ} (α : ℕ →₀ ℕ) (hd : multiDegree α = d)
    (hs : ∀ k ∈ α.support, k < n) : ∃ i : Fin d → Fin n, tupleIndex i = α := by
  induction d generalizing α with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    have : α = 0 := by
      ext k
      by_contra hk
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hk
      have hk' : k ∈ α.support := Finsupp.mem_support_iff.mpr hk
      have : α k ≤ multiDegree α := by
        unfold multiDegree
        exact Finset.single_le_sum (f := fun k => α k) (fun _ _ => Nat.zero_le _) hk'
      omega
    simp [this, tupleIndex]
  | succ d ih =>
    have hne : α.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      rw [Finsupp.support_eq_empty] at h
      simp [h, multiDegree] at hd
    obtain ⟨k, hk⟩ := hne
    have hk1 : Finsupp.single k 1 ≤ α := by
      intro x
      rw [Finsupp.single_apply]
      split_ifs with h
      · subst h; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk)
      · exact Nat.zero_le _
    set β := α - Finsupp.single k 1
    have hαβ : α = β + Finsupp.single k 1 := (tsub_add_cancel_of_le hk1).symm
    have hβd : multiDegree β = d := by
      have : multiDegree α = multiDegree β + 1 := by
        unfold multiDegree
        rw [hαβ, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
        simp
      omega
    have hβs : ∀ k ∈ β.support, k < n := by
      intro x hx
      apply hs
      rw [Finsupp.mem_support_iff] at hx ⊢
      intro h0; apply hx
      have : β x ≤ α x := by rw [hαβ]; simp
      omega
    obtain ⟨i, hi⟩ := ih β hβd hβs
    refine ⟨Fin.snoc i ⟨k, hs k hk⟩, ?_⟩
    unfold tupleIndex at hi ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [hi, ← hαβ]

lemma sum_W {n m : ℕ} (P : Tensor n m) (hP : SymTensor P) (j : Fin m → Fin n) :
    ∑ i, P i * W i j = m.factorial * P j := by
  simp only [W, He, integral_heMulti_mul]
  rw [show ∑ i, P i * (if tupleIndex i = tupleIndex j then (multiFactorial (tupleIndex i) : ℝ)
      else 0) = ∑ i ∈ Finset.univ.filter (fun i : Fin m → Fin n => tupleIndex i = tupleIndex j),
        P j * (multiFactorial (tupleIndex j) : ℝ) from ?_]
  · rw [Finset.sum_const, nsmul_eq_mul, ← card_fiber_mul j]; push_cast; ring
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · obtain ⟨τ, rfl⟩ := exists_perm_of_tupleIndex_eq i j h
    rw [hP, h]
  · simp

lemma coefficientTensor_sym (n d : ℕ) (p : Original) :
    SymTensor (coefficientTensor (n := n) (d := d) p) := by
  intro σ i
  unfold coefficientTensor
  rw [tupleIndex_comp]

/-! ## structure of the finite chaos -/

lemma finiteChaos_le_chaos (n d : ℕ) : finiteChaos n d ≤ chaos d := by
  unfold finiteChaos chaos gradedChaos
  refine le_trans (Submodule.span_mono ?_) (Submodule.le_topologicalClosure _)
  rintro q ⟨α, hα, -, hq⟩
  refine ⟨α, ?_, hq⟩
  rw [← hα]; simp [grade, multiDegree]

lemma rep_of_mem {n d : ℕ} (q : Original) (hq : q ∈ finiteChaos n d) :
    ∃ c : Tensor n d, (q : Sample → ℝ) =ᵐ[gaussianProduct ℕ] fun x => ∑ i, c i * He i x := by
  unfold finiteChaos at hq
  induction hq using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, hs, hx⟩ := hx
    obtain ⟨i, hi⟩ := exists_tuple (n := n) α hα hs
    refine ⟨fun i' => if i' = i then 1 else 0, ?_⟩
    filter_upwards [hx] with y hy
    simp [hy, He, hi]
  | zero =>
    refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (gaussianProduct ℕ)] with y hy
    simp [hy]
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨c', hc'⟩ := hy
    refine ⟨c + c', ?_⟩
    filter_upwards [Lp.coeFn_add x y, hc, hc'] with z hz h1 h2
    rw [hz, Pi.add_apply, h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]; ring
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    refine ⟨a • c, ?_⟩
    filter_upwards [Lp.coeFn_smul a x, hc] with z hz h1
    rw [hz, Pi.smul_apply, h1, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma exists_of_rep {n d : ℕ} (c : Tensor n d) : ∃ q ∈ finiteChaos n d,
    (q : Sample → ℝ) =ᵐ[gaussianProduct ℕ] fun x => ∑ i, c i * He i x := by
  refine ⟨∑ i, c i • (memLp_heMulti (tupleIndex i)).toLp, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨tupleIndex i, multiDegree_tupleIndex i, tupleIndex_support i,
      (memLp_heMulti (tupleIndex i)).coeFn_toLp⟩
  · have h : ∀ i : Fin d → Fin n, (⇑(c i • (memLp_heMulti (tupleIndex i)).toLp) : Sample → ℝ)
        =ᵐ[gaussianProduct ℕ] fun x => c i * He i x := fun i => by
      filter_upwards [Lp.coeFn_smul (c i) (memLp_heMulti (tupleIndex i)).toLp,
        (memLp_heMulti (tupleIndex i)).coeFn_toLp] with z hz h1
      rw [hz, Pi.smul_apply, h1, smul_eq_mul]; rfl
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => c i • (memLp_heMulti (tupleIndex i)).toLp),
      ae_all_iff.mpr h] with z hz h1
    rw [hz]
    exact Finset.sum_congr rfl fun i _ => h1 i

lemma integral_rep_mul {n d : ℕ} (q : Original) (c : Tensor n d)
    (hc : (q : Sample → ℝ) =ᵐ[gaussianProduct ℕ] fun x => ∑ i, c i * He i x)
    (g : Sample → ℝ) (hg : ∀ i : Fin d → Fin n, Integrable (fun x => He i x * g x) (gaussianProduct ℕ)) :
    ∫ x, q x * g x ∂gaussianProduct ℕ = ∑ i, c i * ∫ x, He i x * g x ∂gaussianProduct ℕ := by
  have h := integral_congr_ae (μ := gaussianProduct ℕ) (hc.mul (Filter.EventuallyEq.refl _ g))
  simp only [Pi.mul_apply] at h
  rw [h]
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ => ((hg i).const_mul (c i)).congr
    (ae_of_all _ fun x => by simp only; ring))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul]
  congr 1; funext x; ring

lemma integrable_He_mul_He {n m m' : ℕ} (i : Fin m → Fin n) (j : Fin m' → Fin n) :
    Integrable (fun x => He i x * He j x) (gaussianProduct ℕ) :=
  (memLp_heMulti _).integrable_mul (memLp_heMulti _)

lemma coefficientTensor_rep {n d : ℕ} (q : Original) (c : Tensor n d)
    (hc : (q : Sample → ℝ) =ᵐ[gaussianProduct ℕ] fun x => ∑ i, c i * He i x) :
    coefficientTensor (n := n) (d := d) q =
      fun j => (∑ i, c i * W i j) / Real.sqrt (d.factorial : ℝ) := by
  funext j
  unfold coefficientTensor
  show (∫ x, q x * He j x ∂gaussianProduct ℕ) / _ = _
  rw [integral_rep_mul q c hc (He j) (fun i => integrable_He_mul_He i j)]
  rfl

lemma sqrt_fact_pos (d : ℕ) : 0 < Real.sqrt (d.factorial : ℝ) :=
  Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos d)

lemma sqrt_fact_sq (d : ℕ) : Real.sqrt (d.factorial : ℝ) * Real.sqrt (d.factorial : ℝ) =
    d.factorial := Real.mul_self_sqrt (by positivity)

lemma integral_mul_He_eq {n d : ℕ} (q : Original) (j : Fin d → Fin n) :
    ∫ x, q x * He j x ∂gaussianProduct ℕ =
      Real.sqrt (d.factorial : ℝ) * coefficientTensor (n := n) (d := d) q j := by
  unfold coefficientTensor He
  have := sqrt_fact_pos d
  field_simp

lemma norm_sq_eq_integral (q : Original) : ‖q‖ ^ 2 = ∫ x, q x * q x ∂gaussianProduct ℕ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [sq]

lemma norm_eq_frobenius (n d : ℕ) (q : Original) (hq : q ∈ finiteChaos n d) :
    ‖q‖ = frobenius (coefficientTensor (n := n) (d := d) q) := by
  obtain ⟨c, hc⟩ := rep_of_mem q hq
  set P := coefficientTensor (n := n) (d := d) q with hP
  have h1 : ∫ x, q x * q x ∂gaussianProduct ℕ = Real.sqrt (d.factorial : ℝ) * ∑ i, c i * P i := by
    rw [show (fun x => q x * q x) = fun x => q x * q x from rfl]
    have e : ∫ x, q x * q x ∂gaussianProduct ℕ = ∑ i, c i * ∫ x, He i x * q x ∂gaussianProduct ℕ :=
      integral_rep_mul q c hc q (fun i => (memLp_heMulti _).integrable_mul (Lp.memLp q))
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [mul_comm (He i _)]
    rw [integral_mul_He_eq]; ring
  have h2 : ∑ j, P j ^ 2 = Real.sqrt (d.factorial : ℝ) * ∑ i, c i * P i := by
    have hPj : ∀ j, P j = (∑ i, c i * W i j) / Real.sqrt (d.factorial : ℝ) := fun j => by
      rw [hP, coefficientTensor_rep q c hc]
    have hs := sqrt_fact_pos d
    calc ∑ j, P j ^ 2 = ∑ j, P j * ((∑ i, c i * W i j) / Real.sqrt (d.factorial : ℝ)) := by
          refine Finset.sum_congr rfl fun j _ => ?_; rw [sq]; congr 1; exact hPj j
      _ = (∑ i, c i * ∑ j, P j * W j i) / Real.sqrt (d.factorial : ℝ) := by
          simp only [Finset.mul_sum, Finset.sum_div]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [W_comm]; ring
      _ = (∑ i, c i * (d.factorial * P i)) / Real.sqrt (d.factorial : ℝ) := by
          simp_rw [sum_W P (coefficientTensor_sym n d q)]
      _ = Real.sqrt (d.factorial : ℝ) * ∑ i, c i * P i := by
          rw [Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          have e := sqrt_fact_sq d
          rw [div_eq_iff hs.ne']
          linear_combination (-(c i * P i)) * e
  have h3 : ‖q‖ ^ 2 = ∑ j, P j ^ 2 := by rw [norm_sq_eq_integral, h1, h2]
  unfold frobenius
  rw [← h3, Real.sqrt_sq (norm_nonneg _)]

lemma exists_of_symTensor (n r : ℕ) (T : Tensor n r) (hT : SymTensor T) :
    ∃ q ∈ finiteChaos n r, coefficientTensor (n := n) (d := r) q = T := by
  obtain ⟨q, hq, hc⟩ := exists_of_rep (n := n) (d := r) (fun i => T i / Real.sqrt (r.factorial : ℝ))
  refine ⟨q, hq, ?_⟩
  rw [coefficientTensor_rep q _ hc]
  funext j
  have hs := sqrt_fact_pos r
  have e : ∑ i, T i / Real.sqrt (r.factorial : ℝ) * W i j =
      (∑ i, T i * W i j) / Real.sqrt (r.factorial : ℝ) := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [e, sum_W T hT, div_div, sqrt_fact_sq]
  have : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  field_simp

/-! ## the pairing identity -/

lemma pairing_proj (d : ℕ) (p : Original) (hp : p ∈ chaos d) (w : Original) :
    pairing p (chaosProjection d w) = pairing p w := by
  have e : ∀ q : Original, pairing p q = inner ℝ p q := fun q => by
    rw [L2.inner_def]; simp [pairing, mul_comm]
  rw [e, e]
  letI : (chaos d).HasOrthogonalProjection := by
    unfold chaos gradedChaos
    infer_instance
  unfold chaosProjection
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (⟨p, hp⟩ : chaos d) w

def cat {n d r : ℕ} (j : Fin r → Fin n) (k : Fin (d-r) → Fin n) : Fin d → Fin n :=
  fun s => if h : s.val < r then j ⟨s.val, h⟩ else k ⟨s.val-r, by omega⟩

lemma bil_smul {n d : ℕ} (P : Tensor n d) (r : ℕ) (a b : ℝ) (f : (Fin r → Fin n) → ℝ)
    (g : (Fin (d-r) → Fin n) → ℝ) :
    bil P r (fun j => a * f j) (fun k => b * g k) = a * b * bil P r f g := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma bil_left {n d r : ℕ} (P : Tensor n d)
    (h1 : ∀ (σ : Equiv.Perm (Fin r)) i j, flatten P r (i ∘ σ) j = flatten P r i j)
    (a : Tensor n r) (g : (Fin (d-r) → Fin n) → ℝ) :
    bil P r (fun j => ∑ i, a i * W i j) g = r.factorial * bil P r a g := by
  unfold bil
  have key : ∀ k, ∑ j, (∑ i, a i * W i j) * flatten P r j k =
      r.factorial * ∑ i, a i * flatten P r i k := by
    intro k
    have hs : SymTensor (fun j => flatten P r j k) := fun σ j => h1 σ j k
    calc ∑ j, (∑ i, a i * W i j) * flatten P r j k
        = ∑ i, a i * ∑ j, flatten P r j k * W j i := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [W_comm]; ring
      _ = ∑ i, a i * (r.factorial * flatten P r i k) := by
          simp_rw [sum_W (fun j => flatten P r j k) hs]
      _ = r.factorial * ∑ i, a i * flatten P r i k := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (f := fun i j => a i * flatten P r i j * g j), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, key k, mul_assoc, Finset.sum_mul]

lemma bil_right {n d r : ℕ} (P : Tensor n d)
    (h2 : ∀ (σ : Equiv.Perm (Fin (d-r))) i j, flatten P r i (j ∘ σ) = flatten P r i j)
    (f : (Fin r → Fin n) → ℝ) (b : Tensor n (d-r)) :
    bil P r f (fun k => ∑ l, b l * W l k) = (d-r).factorial * bil P r f b := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : SymTensor (fun k => flatten P r i k) := fun σ k => h2 σ i k
  calc ∑ k, f i * flatten P r i k * ∑ l, b l * W l k
      = f i * ∑ l, b l * ∑ k, flatten P r i k * W k l := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
        rw [W_comm]; ring
    _ = f i * ∑ l, b l * ((d-r).factorial * flatten P r i l) := by
        simp_rw [sum_W (fun k => flatten P r i k) hs]
    _ = (d-r).factorial * ∑ k, f i * flatten P r i k * b k := by
        rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; ring

lemma integral_p_three {n d r : ℕ} (hrd : r ≤ d) (p : Original) (c : Tensor n d)
    (hc : (p : Sample → ℝ) =ᵐ[gaussianProduct ℕ] fun x => ∑ i, c i * He i x)
    (j : Fin r → Fin n) (k : Fin (d-r) → Fin n) :
    ∫ x, p x * (He j x * He k x) ∂gaussianProduct ℕ =
      Real.sqrt (d.factorial : ℝ) * flatten (coefficientTensor (n := n) (d := d) p) r j k := by
  have hint : ∀ i : Fin d → Fin n, Integrable (fun x => He i x * (He j x * He k x))
      (gaussianProduct ℕ) := fun i => (memLp_heMulti _).integrable_mul (memLp_heMulti_mul _ _)
  rw [integral_rep_mul p c hc _ hint]
  have e : ∀ i : Fin d → Fin n, ∫ x, He i x * (He j x * He k x) ∂gaussianProduct ℕ =
      ∫ x, He i x * He (cat (d := d) j k) x ∂gaussianProduct ℕ := by
    intro i
    have hdeg : multiDegree (tupleIndex i) = multiDegree (tupleIndex j) +
        multiDegree (tupleIndex k) := by
      rw [multiDegree_tupleIndex, multiDegree_tupleIndex, multiDegree_tupleIndex]; omega
    unfold He
    rw [integral_heMulti_three _ _ _ hdeg]
    unfold cat
    rw [tupleIndex_concat hrd]
  simp_rw [e]
  rw [← integral_rep_mul p c hc _ (fun i => integrable_He_mul_He i _), integral_mul_He_eq]
  rfl

lemma pairing_identity (d r : ℕ) (hr0 : 0 < r) (hrd : r < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (p u v : Original), p ∈ finiteChaos n d →
      u ∈ finiteChaos n r → v ∈ finiteChaos n (d-r) →
      pairing p (topProduct r (d-r) u v) =
        K * bil (coefficientTensor (n := n) (d := d) p) r
          (coefficientTensor (n := n) (d := r) u)
          (coefficientTensor (n := n) (d := d-r) v) := by
  refine ⟨Real.sqrt (d.factorial : ℝ) / (Real.sqrt (r.factorial : ℝ) *
    Real.sqrt ((d-r).factorial : ℝ)), by
      have := sqrt_fact_pos d; have := sqrt_fact_pos r; have := sqrt_fact_pos (d-r); positivity, ?_⟩
  intro n p u v hp hu hv
  obtain ⟨c, hc⟩ := rep_of_mem p hp
  obtain ⟨a, ha⟩ := rep_of_mem u hu
  obtain ⟨b, hb⟩ := rep_of_mem v hv
  set P := coefficientTensor (n := n) (d := d) p
  -- step 1: projection
  have hae : (fun x => ∑ j, ∑ k, a j * b k * (He j x * He k x)) =ᵐ[gaussianProduct ℕ]
      fun x => u x * v x := by
    filter_upwards [ha, hb] with x hx hy
    rw [hx, hy, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hmem : MemLp (fun x => u x * v x) 2 (gaussianProduct ℕ) :=
    (memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun k _ =>
      (memLp_heMulti_mul (tupleIndex j) (tupleIndex k)).const_mul (a j * b k)).ae_eq hae
  have e1 : pairing p (topProduct r (d-r) u v) =
      ∫ x, p x * (u x * v x) ∂gaussianProduct ℕ := by
    unfold topProduct
    rw [show r + (d-r) = d by omega, pairing_proj d p (finiteChaos_le_chaos n d hp)]
    unfold pairing toOriginal
    rw [dif_pos hmem]
    exact integral_congr_ae ((Filter.EventuallyEq.refl _ _).mul (hmem.coeFn_toLp))
  -- step 2: expand
  have e2 : ∫ x, p x * (u x * v x) ∂gaussianProduct ℕ =
      Real.sqrt (d.factorial : ℝ) * bil P r a b := by
    have h : (fun x => p x * (u x * v x)) =ᵐ[gaussianProduct ℕ]
        fun x => ∑ j, ∑ k, a j * b k * (p x * (He j x * He k x)) := by
      filter_upwards [hae] with x hx
      rw [← hx, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [He]; ring
    rw [integral_congr_ae h]
    have hi : ∀ (j : Fin r → Fin n) (k : Fin (d-r) → Fin n),
        Integrable (fun x => p x * (He j x * He k x)) (gaussianProduct ℕ) :=
      fun j k => (Lp.memLp p).integrable_mul (memLp_heMulti_mul _ _)
    rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ fun k _ =>
      (hi j k).const_mul _)]
    simp_rw [integral_finset_sum _ (fun k _ => (hi _ k).const_mul _), integral_const_mul,
      integral_p_three hrd.le p c hc]
    unfold bil
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- step 3: coefficient tensors of u and v
  have hU : coefficientTensor (n := n) (d := r) u =
      fun j => (Real.sqrt (r.factorial : ℝ))⁻¹ * ∑ i, a i * W i j := by
    rw [coefficientTensor_rep u a ha]; funext j; ring
  have hV : coefficientTensor (n := n) (d := d-r) v =
      fun j => (Real.sqrt ((d-r).factorial : ℝ))⁻¹ * ∑ i, b i * W i j := by
    rw [coefficientTensor_rep v b hb]; funext j; ring
  obtain ⟨h1, h2⟩ := coefficientTensor_blockSym n d r hrd.le p
  rw [e1, e2, hU, hV, bil_smul, bil_left P h1, bil_right P h2]
  have h0 := sqrt_fact_pos d; have h3 := sqrt_fact_pos r; have h4 := sqrt_fact_pos (d-r)
  have er := sqrt_fact_sq r
  have es := sqrt_fact_sq (d-r)
  generalize Real.sqrt (r.factorial : ℝ) = x at *
  generalize Real.sqrt ((d-r).factorial : ℝ) = y at *
  rw [← er, ← es]
  field_simp

lemma flat_nonneg {n d : ℕ} (P : Tensor n d) (r : ℕ) : 0 ≤ flattenNorm P r := by
  unfold flattenNorm
  apply Real.sSup_nonneg
  rintro a ⟨u, v, -, -, rfl⟩
  exact abs_nonneg _

lemma flat_bdd {n d : ℕ} (P : Tensor n d) (r : ℕ) :
    BddAbove {a : ℝ | ∃ (u : EuclideanSpace ℝ (Fin r → Fin n))
      (v : EuclideanSpace ℝ (Fin (d-r) → Fin n)),
      ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧ a = |∑ i, ∑ j, u i * flatten P r i j * v j|} := by
  refine ⟨∑ i, ∑ j, |flatten P r i j|, ?_⟩
  rintro a ⟨u, v, hu, hv, rfl⟩
  have hu' : ∀ i, |u i| ≤ 1 := fun i => by
    have := PiLp.norm_apply_le u i
    simpa using this.trans hu
  have hv' : ∀ j, |v j| ≤ 1 := fun j => by
    have := PiLp.norm_apply_le v j
    simpa using this.trans hv
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul]
  calc |u i| * |flatten P r i j| * |v j| ≤ 1 * |flatten P r i j| * 1 := by
        gcongr; exacts [hu' i, hv' j]
    _ = |flatten P r i j| := by ring

lemma sum_smul {n d : ℕ} (P : Tensor n d) (r : ℕ) (c c' : ℝ)
    (u : EuclideanSpace ℝ (Fin r → Fin n)) (v : EuclideanSpace ℝ (Fin (d-r) → Fin n)) :
    ∑ i, ∑ j, (c • u) i * flatten P r i j * (c' • v) j =
      c * c' * ∑ i, ∑ j, u i * flatten P r i j * v j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

lemma bil_le {n d : ℕ} (P : Tensor n d) (r : ℕ)
    (u : EuclideanSpace ℝ (Fin r → Fin n)) (v : EuclideanSpace ℝ (Fin (d-r) → Fin n)) :
    |∑ i, ∑ j, u i * flatten P r i j * v j| ≤ flattenNorm P r * ‖u‖ * ‖v‖ := by
  by_cases hu : ‖u‖ = 0
  · have : u = 0 := norm_eq_zero.mp hu
    subst this
    simp
  by_cases hv : ‖v‖ = 0
  · have : v = 0 := norm_eq_zero.mp hv
    subst this
    simp
  have hu' : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  have hv' : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have h1 : ‖(‖u‖⁻¹ • u)‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu]
  have h2 : ‖(‖v‖⁻¹ • v)‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv]
  have := le_csSup (flat_bdd P r) ⟨_, _, h1, h2, rfl⟩
  rw [sum_smul, abs_mul, abs_mul, abs_inv, abs_inv, abs_norm, abs_norm] at this
  have h3 : ‖u‖⁻¹ * ‖v‖⁻¹ * |∑ i, ∑ j, u i * flatten P r i j * v j| ≤ flattenNorm P r := by
    unfold flattenNorm; simpa [mul_assoc] using this
  have h4 := mul_le_mul_of_nonneg_left h3 (mul_pos hu' hv').le
  have e : ‖u‖ * ‖v‖ * (‖u‖⁻¹ * ‖v‖⁻¹ * |∑ i, ∑ j, u i * flatten P r i j * v j|) =
      |∑ i, ∑ j, u i * flatten P r i j * v j| := by field_simp
  rw [e] at h4
  linarith

lemma exists_big {n d : ℕ} (P : Tensor n d) (r : ℕ) (a : ℝ) (ha : a < flattenNorm P r) :
    ∃ (u : EuclideanSpace ℝ (Fin r → Fin n))
      (v : EuclideanSpace ℝ (Fin (d-r) → Fin n)),
      ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧ a < |∑ i, ∑ j, u i * flatten P r i j * v j| := by
  unfold flattenNorm at ha
  obtain ⟨_, ⟨u, v, hu, hv, rfl⟩, h⟩ := exists_lt_of_lt_csSup
    (by exact ⟨_, 0, 0, by simp, by simp, rfl⟩) ha
  exact ⟨u, v, hu, hv, h⟩

lemma exists_chaos_big (n d r : ℕ) (hrd : r < d) (p : Original) (a : ℝ)
    (ha : a < flattenNorm (coefficientTensor (n := n) (d := d) p) r) :
    ∃ q ∈ finiteChaos n r, ∃ q' ∈ finiteChaos n (d-r), ‖q‖ ≤ 1 ∧ ‖q'‖ ≤ 1 ∧
      a < |bil (coefficientTensor (n := n) (d := d) p) r
        (coefficientTensor (n := n) (d := r) q)
        (coefficientTensor (n := n) (d := d-r) q')| := by
  obtain ⟨u, v, hu, hv, h⟩ := exists_big _ r a ha
  obtain ⟨h1, h2⟩ := coefficientTensor_blockSym n d r hrd.le p
  obtain ⟨U, V, hU, hV, hUn, hVn, hb⟩ := symmetrize n d r _ h1 h2 u v
  obtain ⟨q, hq, hqU⟩ := exists_of_symTensor n r U hU
  obtain ⟨q', hq', hqV⟩ := exists_of_symTensor n (d-r) V hV
  refine ⟨q, hq, q', hq', ?_, ?_, ?_⟩
  · rw [norm_eq_frobenius n r q hq, hqU]; exact hUn.trans hu
  · rw [norm_eq_frobenius n (d-r) q' hq', hqV]; exact hVn.trans hv
  · rw [hqU, hqV, hb]; exact h

theorem lemma_3_6_main (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (d : ℕ) (p : Sequence) (hp : boundedHom d p) :
    primitive U d p ↔ ∀ r, 0 < r → r < d →
      Tendsto (fun n => flattenNorm (coefficientTensor (n := n) (d := d) (p n)) r)
        (U : Filter ℕ) (𝓝 0) := by
  obtain ⟨hpc, C, hC⟩ := hp
  constructor
  · rintro ⟨-, hprim⟩ r hr0 hrd
    obtain ⟨K, hK, hKid⟩ := pairing_identity d r hr0 hrd
    by_contra hnt
    rw [Metric.tendsto_nhds] at hnt
    push_neg at hnt
    obtain ⟨ε, hε, hne⟩ := hnt
    have hev : ∀ᶠ n in (U : Filter ℕ), ε ≤ flattenNorm (coefficientTensor (n := n) (d := d) (p n)) r := by
      filter_upwards [hne] with n hn
      simpa [abs_of_nonneg (flat_nonneg _ _)] using hn
    have key : ∀ n, ∃ q q' : Original, q ∈ finiteChaos n r ∧ q' ∈ finiteChaos n (d-r) ∧
        ‖q‖ ≤ 1 ∧ ‖q'‖ ≤ 1 ∧ (ε ≤ flattenNorm (coefficientTensor (n := n) (d := d) (p n)) r →
          ε / 2 < |bil (coefficientTensor (n := n) (d := d) (p n)) r
            (coefficientTensor (n := n) (d := r) q)
            (coefficientTensor (n := n) (d := d-r) q')|) := by
      intro n
      by_cases h : ε ≤ flattenNorm (coefficientTensor (n := n) (d := d) (p n)) r
      · obtain ⟨q, hq, q', hq', h1, h2, h3⟩ := exists_chaos_big n d r hrd (p n) (ε/2) (by linarith)
        exact ⟨q, q', hq, hq', h1, h2, fun _ => h3⟩
      · exact ⟨0, 0, Submodule.zero_mem _, Submodule.zero_mem _, by simp, by simp, fun h' => absurd h' h⟩
    choose u v hu hv hu1 hv1 hbig using key
    have := hprim r hr0 hrd u v ⟨hu, 1, hu1⟩ ⟨hv, 1, hv1⟩
    rw [Metric.tendsto_nhds] at this
    have h2 := this (K * (ε / 2)) (by positivity)
    have hall : ∀ᶠ n in (U : Filter ℕ), False := by
      filter_upwards [h2, hev] with n h2n hn
      rw [hKid n (p n) (u n) (v n) (hpc n) (hu n) (hv n)] at h2n
      have := hbig n hn
      rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hK] at h2n
      nlinarith
    obtain ⟨n, hn⟩ := hall.exists
    exact hn
  · intro hflat
    refine ⟨⟨hpc, C, hC⟩, fun r hr0 hrd u v hu hv => ?_⟩
    obtain ⟨K, hK, hKid⟩ := pairing_identity d r hr0 hrd
    obtain ⟨huc, Cu, hCu⟩ := hu
    obtain ⟨hvc, Cv, hCv⟩ := hv
    have hf := hflat r hr0 hrd
    have hb : ∀ n, ‖pairing (p n) (topProduct r (d-r) (u n) (v n))‖ ≤
        K * Cu * Cv * flattenNorm (coefficientTensor (n := n) (d := d) (p n)) r := by
      intro n
      rw [hKid n (p n) (u n) (v n) (hpc n) (huc n) (hvc n), Real.norm_eq_abs, abs_mul,
        abs_of_pos hK]
      have h1 := bil_le (coefficientTensor (n := n) (d := d) (p n)) r
        (WithLp.toLp 2 (coefficientTensor (n := n) (d := r) (u n)))
        (WithLp.toLp 2 (coefficientTensor (n := n) (d := d-r) (v n)))
      rw [euclid_norm_eq, euclid_norm_eq, ← norm_eq_frobenius n r _ (huc n),
        ← norm_eq_frobenius n (d-r) _ (hvc n)] at h1
      have h0 := flat_nonneg (coefficientTensor (n := n) (d := d) (p n)) r
      have hu0 := norm_nonneg (u n)
      have hv0 := norm_nonneg (v n)
      change |bil _ r _ _| ≤ _ at h1
      have := mul_le_mul (mul_le_mul_of_nonneg_left (hCu n) h0) (hCv n) hv0
        (mul_nonneg h0 (hu0.trans (hCu n)))
      nlinarith
    refine squeeze_zero_norm hb ?_
    simpa using hf.const_mul (K * Cu * Cv)


end GaussPolyReg.Approx

open GaussPolyReg.Approx in
theorem solution (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (d : ℕ) (p : Sequence) (hp : boundedHom d p) :
    primitive U d p ↔ ∀ r, 0 < r → r < d →
      Tendsto (fun n => flattenNorm (coefficientTensor (n := n) (d := d) (p n)) r)
        (U : Filter ℕ) (𝓝 0) :=
  lemma_3_6_main U hU d p hp
