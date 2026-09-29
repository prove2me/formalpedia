-- Prove2me | solution 1 for GCTOcc.orbit_closure_det_two_eq_forms
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:22:07.958727+00:00
-- url     : https://prove2.me/submissions/40299554-9227-4e68-b9c3-b843a8598bd4

import Mathlib
import Definitions.Def_GCTOcc_occurrence

set_option autoImplicit false

namespace GCTOccA895

open MvPolynomial GCTOcc

noncomputable def lin (a : Fin 2 × Fin 2 → ℂ) : PolyR :=
  ∑ w : Fin 2 × Fin 2, C (a w) * X ((w.1 : ℕ), (w.2 : ℕ))

lemma lin_add (a b : Fin 2 × Fin 2 → ℂ) : lin (a + b) = lin a + lin b := by
  simp [lin, add_mul, Finset.sum_add_distrib]

lemma lin_smul (k : ℂ) (a : Fin 2 × Fin 2 → ℂ) : lin (k • a) = C k * lin a := by
  simp [lin, Finset.mul_sum, mul_assoc]

lemma lin_neg (a : Fin 2 × Fin 2 → ℂ) : lin (-a) = - lin a := by
  simp [lin, Finset.sum_neg_distrib]

lemma lin_sub (a b : Fin 2 × Fin 2 → ℂ) : lin (a - b) = lin a - lin b := by
  rw [sub_eq_add_neg, lin_add, lin_neg, ← sub_eq_add_neg]

lemma detPoly_two : detPoly 2 = X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0) := by
  rw [detPoly, show (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} from by decide,
    Finset.sum_pair (by decide)]
  simp [Fin.prod_univ_two]
  ring

lemma subst_det2 (G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    substLin 2 G (detPoly 2) = lin (G (0, 0)) * lin (G (1, 1)) - lin (G (0, 1)) * lin (G (1, 0)) := by
  rw [detPoly_two]
  simp [substLin, lin]

lemma sos_mem (c : Fin 4 → Fin 2 × Fin 2 → ℂ) :
    ∃ G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      substLin 2 G (detPoly 2) = ∑ i : Fin 4, lin (c i) ^ 2 := by
  let G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun v => ![![c 0 + Complex.I • c 1,
    c 2 + Complex.I • c 3], ![-(c 2 - Complex.I • c 3), c 0 - Complex.I • c 1]] v.1 v.2
  refine ⟨G, ?_⟩
  rw [subst_det2]
  have e00 : G (0, 0) = c 0 + Complex.I • c 1 := rfl
  have e11 : G (1, 1) = c 0 - Complex.I • c 1 := rfl
  have e01 : G (0, 1) = c 2 + Complex.I • c 3 := rfl
  have e10 : G (1, 0) = -(c 2 - Complex.I • c 3) := rfl
  rw [e00, e11, e01, e10, Fin.sum_univ_four, lin_add, lin_sub, lin_add, lin_neg, lin_sub,
    lin_smul, lin_smul]
  have hI : (C Complex.I : PolyR) * C Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  linear_combination (-(lin (c 1)) ^ 2 - lin (c 3) ^ 2) * hI


lemma mono_two (p : PolyR) (hp : IsForm 2 p) (m : (ℕ × ℕ) →₀ ℕ) (hm : m ∈ p.support) :
    ∃ a b : Fin 2 × Fin 2, m = Finsupp.single ((a.1 : ℕ), (a.2 : ℕ)) 1 +
      Finsupp.single ((b.1 : ℕ), (b.2 : ℕ)) 1 := by
  have hdeg : m.degree = 2 := by
    rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]; exact hp.1 (mem_support_iff.mp hm)
  have hcard : Multiset.card (Finsupp.toMultiset m) = 2 := by
    rw [Finsupp.card_toMultiset, ← hdeg]; rfl
  obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp hcard
  have hx : x ∈ m.support := by
    rw [← Finsupp.mem_toMultiset, hxy]; simp
  have hy : y ∈ m.support := by
    rw [← Finsupp.mem_toMultiset, hxy]; simp
  obtain ⟨hx1, hx2⟩ := hp.2 m hm x hx
  obtain ⟨hy1, hy2⟩ := hp.2 m hm y hy
  refine ⟨(⟨x.1, hx1⟩, ⟨x.2, hx2⟩), (⟨y.1, hy1⟩, ⟨y.2, hy2⟩), ?_⟩
  classical
  rw [← Finsupp.toMultiset_toFinsupp m, hxy, Multiset.insert_eq_cons, ← Multiset.singleton_add,
    Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, Multiset.toFinsupp_singleton]

lemma eval_form (p : PolyR) (a b : ((ℕ × ℕ) →₀ ℕ) → Fin 2 × Fin 2)
    (hab : ∀ m ∈ p.support, m = Finsupp.single (((a m).1 : ℕ), ((a m).2 : ℕ)) 1 +
      Finsupp.single (((b m).1 : ℕ), ((b m).2 : ℕ)) 1) (x : ℕ × ℕ → ℂ) :
    eval x p = ∑ m ∈ p.support, coeff m p *
      (x (((a m).1 : ℕ), ((a m).2 : ℕ)) * x (((b m).1 : ℕ), ((b m).2 : ℕ))) := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [eval_monomial]
  congr 1
  conv_lhs => rw [hab m hm]
  rw [Finsupp.prod_add_index' (by simp) (by intros; simp [pow_add])]
  simp

lemma form_sos (p : PolyR) (hp : IsForm 2 p) :
    ∃ c : Fin 4 → Fin 2 × Fin 2 → ℂ, p = ∑ i : Fin 4, lin (c i) ^ 2 := by
  have key := mono_two p hp
  choose! a b hab using key
  let Q : QuadraticForm ℂ (Fin 2 × Fin 2 → ℂ) := ∑ m ∈ p.support,
    coeff m p • QuadraticMap.linMulLin (LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (a m))
      (LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (b m))
  have hQ : ∀ y : Fin 2 × Fin 2 → ℂ, Q y = ∑ m ∈ p.support, coeff m p * (y (a m) * y (b m)) := by
    intro y
    simp [Q, QuadraticMap.linMulLin_apply]
  let _ : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, ⟨f⟩⟩ := QuadraticForm.equivalent_weightedSumSquares Q
  have hf : ∀ y, ∑ i, w i * (f y i * f y i) = Q y := by
    intro y
    rw [← f.map_app y, QuadraticMap.weightedSumSquares_apply]
    simp [smul_eq_mul]
  choose s hs using fun i => IsAlgClosed.exists_eq_mul_self (w i)
  let F : (Fin 2 × Fin 2 → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ (Fin 2 × Fin 2 → ℂ)) → ℂ) :=
    f.toLinearEquiv.toLinearMap
  have hF : ∀ y, F y = f y := fun y => rfl
  have hFsum : ∀ y i, f y i = ∑ v, y v * F (fun j => if v = j then 1 else 0) i := by
    intro y i
    rw [← hF, LinearMap.pi_apply_eq_sum_univ F y]
    simp [Finset.sum_apply]
  have hr : Module.finrank ℂ (Fin 2 × Fin 2 → ℂ) = 4 := by
    simp [Module.finrank_fintype_fun_eq_card]
  let e : Fin 4 ≃ Fin (Module.finrank ℂ (Fin 2 × Fin 2 → ℂ)) := finCongr hr.symm
  refine ⟨fun k v => s (e k) * F (fun j => if v = j then 1 else 0) (e k), ?_⟩
  apply MvPolynomial.funext
  intro x
  rw [eval_form p a b hab x]
  have h1 := hQ (fun v => x ((v.1 : ℕ), (v.2 : ℕ)))
  rw [← h1, ← hf]
  simp only [lin, map_sum, map_pow, map_mul, eval_C, eval_X]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsum : (∑ v : Fin 2 × Fin 2, s (e k) * F (fun j => if v = j then 1 else 0) (e k) *
      x ((v.1 : ℕ), (v.2 : ℕ))) = s (e k) * ∑ v : Fin 2 × Fin 2, x ((v.1 : ℕ), (v.2 : ℕ)) *
      F (fun j => if v = j then 1 else 0) (e k) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
  rw [hs (e k), hFsum _ (e k), hsum]
  ring

lemma lin_row_sub (G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (t : ℂ) (v : Fin 2 × Fin 2) :
    lin ((G - t • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) v) =
      lin (G v) - C t * X ((v.1 : ℕ), (v.2 : ℕ)) := by
  have h1 : (G - t • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) v =
      G v - t • (fun w => if v = w then (1 : ℂ) else 0) := by
    ext w; simp [Matrix.one_apply]
  rw [h1, lin_sub, lin_smul]
  congr 2
  simp [lin]

lemma coeff_perturb (G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (m : (ℕ × ℕ) →₀ ℕ) (t : ℂ) :
    coeff m (substLin 2 (G - t • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) (detPoly 2)) =
      coeff m (substLin 2 G (detPoly 2)) -
        t * coeff m (lin (G (0, 0)) * X (1, 1) + X (0, 0) * lin (G (1, 1)) -
          lin (G (0, 1)) * X (1, 0) - X (0, 1) * lin (G (1, 0))) +
        t ^ 2 * coeff m ((X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0) : PolyR)) := by
  rw [subst_det2, subst_det2, lin_row_sub, lin_row_sub, lin_row_sub, lin_row_sub,
    ← coeff_C_mul, ← coeff_C_mul, ← coeff_sub, ← coeff_add]
  congr 1
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, map_pow]
  ring

end GCTOccA895

open MvPolynomial GCTOcc in
theorem solution (p : PolyR) (hp : IsForm 2 p) :
    p ∈ orbitClosure 2 (detPoly 2) := by
  obtain ⟨c, hc⟩ := GCTOccA895.form_sos p hp
  obtain ⟨G, hG⟩ := GCTOccA895.sos_mem c
  rw [← hc] at hG
  classical
  let t : ℕ → ℂ := fun k => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)
  have ht : Filter.Tendsto t Filter.atTop (nhds 0) := by
    have h0 := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Complex.ofReal_zero] at h0
    exact h0
  have htinj : Function.Injective t := by
    intro i j hij
    have h2 : (1 / ((i : ℝ) + 1)) = 1 / ((j : ℝ) + 1) := Complex.ofReal_injective hij
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    rw [div_eq_div_iff hi.ne' hj.ne'] at h2
    exact_mod_cast (by linarith : (i : ℝ) = j)
  have hfin : {z : ℂ | G.charpoly.IsRoot z}.Finite :=
    Polynomial.finite_setOfPred_isRoot G.charpoly_monic.ne_zero
  have hdet : ∀ z : ℂ, z ∉ {z : ℂ | G.charpoly.IsRoot z} →
      IsUnit (G - z • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)).det := by
    intro z hz
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly] at hz
    have hneg : G - z • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
        -(Matrix.scalar _ z - G) := by
      rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hneg, Matrix.det_neg, isUnit_iff_ne_zero]
    exact mul_ne_zero (by simp) hz
  have hev : ∀ᶠ k in Filter.atTop,
      IsUnit (G - t k • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)).det := by
    have h := (hfin.preimage htinj.injOn).eventually_cofinite_notMem
    rw [Nat.cofinite_eq_atTop] at h
    exact h.mono fun k hk => hdet _ hk
  refine ⟨fun k => if IsUnit (G - t k • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)).det
    then G - t k • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) else 1, ?_, ?_⟩
  · intro k
    dsimp only
    split_ifs with h
    · exact h
    · simp
  · intro m
    have hlim : Filter.Tendsto (fun k => coeff m (substLin 2
        (G - t k • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) (detPoly 2)))
        Filter.atTop (nhds (coeff m p)) := by
      simp_rw [GCTOccA895.coeff_perturb, hG]
      have hcont : Continuous fun z : ℂ => coeff m p -
          z * coeff m (GCTOccA895.lin (G (0, 0)) * X (1, 1) + X (0, 0) * GCTOccA895.lin (G (1, 1)) -
            GCTOccA895.lin (G (0, 1)) * X (1, 0) - X (0, 1) * GCTOccA895.lin (G (1, 0))) +
          z ^ 2 * coeff m ((X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0) : PolyR)) := by
        fun_prop
      have := (hcont.tendsto 0).comp ht
      simpa [Function.comp_def] using this
    refine hlim.congr' ?_
    filter_upwards [hev] with k hk
    simp only [if_pos hk]
