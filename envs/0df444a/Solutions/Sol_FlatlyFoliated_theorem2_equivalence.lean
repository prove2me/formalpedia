-- Prove2me | solution 1 for FlatlyFoliated.theorem2_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:07:15.717892+00:00
-- url     : https://prove2.me/submissions/26a4bd46-9a40-41ba-9b99-7c27c3df0e95

import Theorems.Thm_FlatlyFoliated_decaying_drift_eq_zero

open scoped ContDiff
open FlatlyFoliated

namespace FFEq

private lemma smooth_pd {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (pd i u) :=
  (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

private lemma smooth_comp {w : R3 → R3} (hw : ContDiff ℝ ∞ w) (i : Fin 3) :
    ContDiff ℝ ∞ (comp w i) :=
  (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hw

private lemma smooth_lap {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (lap u) :=
  ContDiff.sum (fun i _ => smooth_pd (smooth_pd hu i) i)

private lemma smooth_div {w : R3 → R3} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (divg w) :=
  ContDiff.sum (fun i _ => smooth_pd (smooth_comp hw i) i)

private lemma grad_apply (u : R3 → ℝ) (x : R3) (i : Fin 3) : grad u x i = pd i u x := by
  simp [grad, Pi.single_apply]

private lemma smooth_grad {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (grad u) := by
  unfold grad
  exact ContDiff.sum (fun i _ => (smooth_pd hu i).smul contDiff_const)

private lemma pd_comm {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i j : Fin 3) :
    pd i (pd j u) = pd j (pd i u) := by
  funext x
  have key : ∀ a b : Fin 3, pd a (pd b u) x =
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro a b
    unfold pd
    have hd := (hu.fderiv_right (m := ∞) le_rfl).differentiable (by simp) x
    rw [(hd.hasFDerivAt.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single b (1 : ℝ)) x)).fderiv]
    simp
  rw [key, key]
  exact hu.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top) _ _

private lemma pd_add {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (i : Fin 3) : pd i (fun x => u x + v x) = fun x => pd i u x + pd i v x := by
  funext x
  simp only [pd, fderiv_fun_add (hu.differentiable (by simp) x) (hv.differentiable (by simp) x),
    add_apply]

private lemma pd_sub {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (i : Fin 3) : pd i (fun x => u x - v x) = fun x => pd i u x - pd i v x := by
  funext x
  simp only [pd, fderiv_fun_sub (hu.differentiable (by simp) x) (hv.differentiable (by simp) x),
    sub_apply]

private lemma pd_mul {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (i : Fin 3) : pd i (fun x => u x * v x) = fun x => pd i u x * v x + u x * pd i v x := by
  funext x
  unfold pd
  rw [((hu.differentiable (by simp) x).hasFDerivAt.fun_mul
    (hv.differentiable (by simp) x).hasFDerivAt).fderiv]
  simp
  ring

private lemma pd_sum {s : Type*} [Fintype s] {u : s → R3 → ℝ}
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (i : Fin 3) :
    pd i (fun x => ∑ j, u j x) = fun x => ∑ j, pd i (u j) x := by
  funext x
  unfold pd
  rw [(HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (hu j |>.differentiable (by simp) x).hasFDerivAt)).fderiv]
  simp

private lemma pd_const (c : ℝ) (i : Fin 3) : pd i (fun _ : R3 => c) = 0 := by
  ext x
  simp [pd]

private lemma pd_zero (i : Fin 3) : pd i (0 : R3 → ℝ) = 0 := by
  ext x
  simp [pd]

private lemma pd_smul {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (c : ℝ) (i : Fin 3) :
    pd i (fun x => c * u x) = fun x => c * pd i u x := by
  rw [pd_mul contDiff_const hu, pd_const]
  simp

private lemma lap_pd {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    lap (pd i u) = pd i (lap u) := by
  unfold lap
  rw [pd_sum (fun j => smooth_pd (smooth_pd hu j) j)]
  funext x
  apply Finset.sum_congr rfl
  intro j _
  rw [pd_comm (smooth_pd hu j) i j, pd_comm hu i j]

private lemma lap_add {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    lap (fun x => u x + v x) = fun x => lap u x + lap v x := by
  unfold lap
  simp_rw [pd_add hu hv, pd_add (smooth_pd hu _) (smooth_pd hv _)]
  ext x
  exact Finset.sum_add_distrib

private lemma lap_sub {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    lap (fun x => u x - v x) = fun x => lap u x - lap v x := by
  unfold lap
  simp_rw [pd_sub hu hv, pd_sub (smooth_pd hu _) (smooth_pd hv _)]
  ext x
  simp only [Finset.sum_sub_distrib]

private lemma lap_div {z : R3 → R3} (hz : ContDiff ℝ ∞ z) :
    (fun x => ∑ i, pd i (lap (comp z i)) x) = lap (divg z) := by
  funext x
  simp_rw [← lap_pd (smooth_comp hz _)]
  unfold lap divg
  simp_rw [pd_sum (fun j => smooth_pd (smooth_comp hz j) j),
    pd_sum (fun j => smooth_pd (smooth_pd (smooth_comp hz j) j) _)]
  exact Finset.sum_comm

private lemma div_grad (u : R3 → ℝ) : divg (grad u) = lap u := by
  unfold divg lap comp
  simp_rw [grad_apply]

private lemma div_add {w z : R3 → R3} (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) :
    divg (fun x => w x + z x) = fun x => divg w x + divg z x := by
  change (fun x => ∑ i, pd i (fun y => comp w i y + comp z i y) x) = _
  simp_rw [pd_add (smooth_comp hw _) (smooth_comp hz _)]
  ext x
  exact Finset.sum_add_distrib

private lemma div_sub {w z : R3 → R3} (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) :
    divg (fun x => w x - z x) = fun x => divg w x - divg z x := by
  change (fun x => ∑ i, pd i (fun y => comp w i y - comp z i y) x) = _
  simp_rw [pd_sub (smooth_comp hw _) (smooth_comp hz _)]
  ext x
  simp only [Finset.sum_sub_distrib, divg]

private lemma smooth_Q {f : R3 → ℝ} {z : R3 → R3}
    (hf : ContDiff ℝ ∞ f) (hz : ContDiff ℝ ∞ z) (i j : Fin 3) :
    ContDiff ℝ ∞ (Qmat f z i j) :=
  (smooth_pd (smooth_pd hf i) j).add
    (contDiff_const.mul ((smooth_pd (smooth_comp hz i) j).add
      (smooth_pd (smooth_comp hz j) i)))

private lemma smooth_A {f : R3 → ℝ} {z : R3 → R3}
    (hf : ContDiff ℝ ∞ f) (hz : ContDiff ℝ ∞ z) (i j : Fin 3) :
    ContDiff ℝ ∞ (ellCoeff f z i j) := by
  unfold ellCoeff
  split_ifs
  · exact (smooth_lap hf).sub (smooth_Q hf hz i j)
  · exact contDiff_const.sub (smooth_Q hf hz i j)

private lemma div_A {f : R3 → ℝ} {z : R3 → R3}
    (hf : ContDiff ℝ ∞ f) (hz : ContDiff ℝ ∞ z) (j : Fin 3) (x : R3) :
    ∑ i, pd i (ellCoeff f z i j) x =
      -(1 / 2) * (lap (comp z j) x + pd j (divg z) x) := by
  have hdiag : ∀ i, pd i (fun y => if i = j then lap f y else 0) x =
      if i = j then pd i (lap f) x else 0 := by
    intro i; split_ifs <;> simp_all [pd_const]
  have hQ : ∀ i, pd i (Qmat f z i j) x =
      pd i (pd j (pd i f)) x + (1 / 2) *
        (pd i (pd j (comp z i)) x + pd i (pd i (comp z j)) x) := by
    intro i
    unfold Qmat
    rw [pd_add (smooth_pd (smooth_pd hf i) j)
      (contDiff_const.mul ((smooth_pd (smooth_comp hz i) j).add (smooth_pd (smooth_comp hz j) i))),
      pd_smul ((smooth_pd (smooth_comp hz i) j).add (smooth_pd (smooth_comp hz j) i)),
      pd_add (smooth_pd (smooth_comp hz i) j) (smooth_pd (smooth_comp hz j) i)]
  have hA : ∀ i, pd i (ellCoeff f z i j) x =
      (if i = j then pd i (lap f) x else 0) - pd i (Qmat f z i j) x := by
    intro i
    unfold ellCoeff
    rw [pd_sub (by split_ifs <;> first | exact smooth_lap hf | exact contDiff_const)
      (smooth_Q hf hz i j)]
    dsimp only
    rw [hdiag]
  simp_rw [hA, hQ, pd_comm (smooth_pd hf _) _ j, pd_comm (smooth_comp hz _) _ j]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ j)]
  have hf' : (∑ i, pd j (pd i (pd i f)) x) = pd j (lap f) x := by
    unfold lap
    rw [pd_sum (fun i => smooth_pd (smooth_pd hf i) i)]
  have hz' : (∑ i, pd j (pd i (comp z i)) x) = pd j (divg z) x := by
    unfold divg
    rw [pd_sum (fun i => smooth_pd (smooth_comp hz i) i)]
  rw [Finset.sum_add_distrib, hf', hz']
  change _ = -(1 / 2) * ((∑ i, pd i (pd i (comp z j)) x) + _)
  ring


private lemma flux_identity {f η : R3 → ℝ} {z : R3 → R3}
    (hf : ContDiff ℝ ∞ f) (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (x : R3) :
    (∑ i, pd i (fun y => η y * lap (comp z i) y +
        2 * ∑ j, ellCoeff f z i j y * pd j η y) x) =
      2 * (∑ i, ∑ j, ellCoeff f z i j x * pd j (pd i η) x) +
        η x * lap (divg z) x - ∑ i, pd i η x * pd i (divg z) x := by
  have hterm (i : Fin 3) :
      pd i (fun y => η y * lap (comp z i) y +
        2 * ∑ j, ellCoeff f z i j y * pd j η y) x =
      (pd i η x * lap (comp z i) x + η x * pd i (lap (comp z i)) x) +
        2 * ∑ j, (pd i (ellCoeff f z i j) x * pd j η x +
          ellCoeff f z i j x * pd i (pd j η) x) := by
    rw [pd_add (hη.mul (smooth_lap (smooth_comp hz i)))
      (contDiff_const.mul (ContDiff.sum (fun j _ => (smooth_A hf hz i j).mul (smooth_pd hη j)))),
      pd_mul hη (smooth_lap (smooth_comp hz i)),
      pd_smul (ContDiff.sum (fun j _ => (smooth_A hf hz i j).mul (smooth_pd hη j))),
      pd_sum (fun j => (smooth_A hf hz i j).mul (smooth_pd hη j))]
    simp_rw [pd_mul (smooth_A hf hz i _) (smooth_pd hη _)]
  simp_rw [hterm, Finset.sum_add_distrib, mul_add]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcross : (∑ i, ∑ j, pd i (ellCoeff f z i j) x * pd j η x) =
      ∑ j, (-(1 / 2) * (lap (comp z j) x + pd j (divg z) x)) * pd j η x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, div_A hf hz]
  rw [hcross]
  have hlast : (∑ i, ∑ j, ellCoeff f z i j x * pd i (pd j η) x) =
      ∑ i, ∑ j, ellCoeff f z i j x * pd j (pd i η) x := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [pd_comm hη i j]
  rw [hlast]
  have hl := congrFun (lap_div hz) x
  rw [hl]
  have hc : (∑ j, (-(1 / 2) * (lap (comp z j) x + pd j (divg z) x)) * pd j η x) =
      -(1 / 2) * ((∑ j, pd j η x * lap (comp z j) x) +
        ∑ j, pd j η x * pd j (divg z) x) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc]
  ring

private lemma weighted_identity {f η : R3 → ℝ} {z J : R3 → R3}
    (hf : ContDiff ℝ ∞ f) (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η)
    (hJ : ContDiff ℝ ∞ J)
    (heq : ∀ x i, η x * lap (comp z i) x +
      2 * ∑ j, ellCoeff f z i j x * pd j η x = 16 * Real.pi * (η x ^ 2 * J x i))
    (x : R3) :
    16 * Real.pi * divg (fun y => η y ^ 2 • J y) x =
      2 * (∑ i, ∑ j, ellCoeff f z i j x * pd j (pd i η) x) +
        η x * lap (divg z) x - ∑ i, pd i η x * pd i (divg z) x := by
  have h := flux_identity hf hz hη x
  have heq' (i : Fin 3) :
      (fun y => η y * lap (comp z i) y + 2 * ∑ j, ellCoeff f z i j y * pd j η y) =
      (fun y => 16 * Real.pi * comp (fun y => η y ^ 2 • J y) i y) := by
    ext y
    exact heq y i
  simp_rw [heq'] at h
  have hsm (i : Fin 3) : ContDiff ℝ ∞ (comp (fun y => η y ^ 2 • J y) i) :=
    smooth_comp ((hη.pow 2).smul hJ) i
  simp_rw [pd_smul (hsm _)] at h
  simpa only [← Finset.mul_sum, divg] using h

private lemma Q_decomposition {f : R3 → ℝ} {z : R3 → R3}
    (hf : ContDiff ℝ ∞ f) (hz : ContDiff ℝ ∞ z) (i j : Fin 3) (x : R3) :
    pd j (comp (fun y => grad f y + z y) i) x +
      pd i (comp (fun y => grad f y + z y) j) x = 2 * Qmat f z i j x := by
  have he (i : Fin 3) : comp (fun y => grad f y + z y) i =
      fun y => pd i f y + comp z i y := by ext y; simp [comp, grad_apply]
  rw [he, he, pd_add (smooth_pd hf i) (smooth_comp hz i),
    pd_add (smooth_pd hf j) (smooth_comp hz j), pd_comm hf i j]
  unfold Qmat
  ring

private lemma coeff_sum (f : R3 → ℝ) (z : R3 → R3) (η : R3 → ℝ) (i : Fin 3) (x : R3) :
    (∑ j, ellCoeff f z i j x * pd j η x) =
      lap f x * pd i η x - ∑ j, Qmat f z i j x * pd j η x := by
  unfold ellCoeff
  simp_rw [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  simp

private lemma zero_div_equiv {f η : R3 → ℝ} {z J : R3 → R3} {Λ : ℝ} {μ : R3 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hz : ContDiff ℝ ∞ z) (hη : ∀ x, 0 < η x)
    (hv : divg z = 0) :
    FFREquations Λ μ J (fun y => grad f y + z y) η ↔
      (∀ x, lap f x ^ 2 - ∑ i, ∑ j, Qmat f z i j x ^ 2 =
        (16 * Real.pi * μ x + 2 * Λ) * η x ^ 2) ∧
      (∀ x i, lap (comp z i) x = 16 * Real.pi * J x i * η x -
        (2 / η x) * ∑ j, ellCoeff f z i j x * pd j η x) := by
  have hdiv : divg (fun y => grad f y + z y) = lap f := by
    rw [div_add (smooth_grad hf) hz, div_grad, hv]; simp
  have hlap (i : Fin 3) : lap (comp (fun y => grad f y + z y) i) =
      fun x => pd i (lap f) x + lap (comp z i) x := by
    have he : comp (fun y => grad f y + z y) i = fun x => pd i f x + comp z i x := by
      ext x; simp [comp, grad_apply]
    rw [he, lap_add (smooth_pd hf i) (smooth_comp hz i), lap_pd hf]
  have hsq (x : R3) : (∑ i, ∑ j,
      (pd j (comp (fun y => grad f y + z y) i) x +
        pd i (comp (fun y => grad f y + z y) j) x) ^ 2) =
      4 * ∑ i, ∑ j, Qmat f z i j x ^ 2 := by
    simp_rw [Q_decomposition hf hz, mul_pow]
    norm_num [Finset.mul_sum]
  have hsum (x : R3) (i : Fin 3) : (∑ j,
      (pd j (comp (fun y => grad f y + z y) i) x +
        pd i (comp (fun y => grad f y + z y) j) x) * pd j η x) =
      2 * ∑ j, Qmat f z i j x * pd j η x := by
    simp_rw [Q_decomposition hf hz, mul_assoc, ← Finset.mul_sum]
  constructor
  · intro he
    constructor
    · intro x
      have h := (he x).1
      unfold Eq34 at h
      rw [hdiv, hsq] at h
      have hn := ne_of_gt (hη x)
      field_simp at h
      nlinarith [h]
    · intro x i
      have h := (he x).2 i
      unfold Eq35 at h
      rw [hdiv, hlap, hsum] at h
      rw [coeff_sum]
      have hn := ne_of_gt (hη x)
      field_simp at h ⊢
      nlinarith [h]
  · rintro ⟨h39, h40⟩ x
    constructor
    · unfold Eq34
      rw [hdiv, hsq]
      have hn := ne_of_gt (hη x)
      field_simp
      nlinarith [h39 x]
    · intro i
      unfold Eq35
      rw [hdiv, hlap, hsum]
      have h := h40 x i
      rw [coeff_sum] at h
      have hn := ne_of_gt (hη x)
      field_simp at h ⊢
      nlinarith [h]


private lemma weighted_eq {f η : R3 → ℝ} {z J : R3 → R3}
    (hη : ∀ x, 0 < η x)
    (heq : ∀ x i, lap (comp z i) x = 16 * Real.pi * J x i * η x -
      (2 / η x) * ∑ j, ellCoeff f z i j x * pd j η x) (x : R3) (i : Fin 3) :
    η x * lap (comp z i) x + 2 * ∑ j, ellCoeff f z i j x * pd j η x =
      16 * Real.pi * (η x ^ 2 * J x i) := by
  have h := heq x i
  have hn := ne_of_gt (hη x)
  field_simp at h
  nlinarith [h]

end FFEq

open FFEq

theorem solution (Λ : ℝ) (μ : R3 → ℝ) (J : R3 → R3) (η : R3 → ℝ)
    (_hμ : ContDiff ℝ ∞ μ) (hJ : ContDiff ℝ ∞ J) (hη : ContDiff ℝ ∞ η)
    (hηpos : ∀ x, 0 < η x) :
    (∀ (w : R3 → R3) (f : R3 → ℝ), ContDiff ℝ ∞ w → ContDiff ℝ ∞ f →
        FFREquations Λ μ J w η → (∀ x, lap f x = divg w x) →
        EllipticSystem Λ μ J f (fun x => w x - grad f x) η) ∧
    (∀ (f : R3 → ℝ) (ζ : R3 → R3), ContDiff ℝ ∞ f → ContDiff ℝ ∞ ζ →
        EllipticSystem Λ μ J f ζ η →
        FFREquations Λ μ J (fun x => grad f x + ζ x) η ∧
          ∀ x, lap f x = divg (fun y => grad f y + ζ y) x) := by
  constructor
  · intro w f hw hf he hlf
    let z : R3 → R3 := fun x => w x - grad f x
    have hz : ContDiff ℝ ∞ z := hw.sub (smooth_grad hf)
    have hv : divg z = 0 := by
      rw [show z = (fun x => w x - grad f x) from rfl,
        div_sub hw (smooth_grad hf), div_grad]
      ext x
      simpa only [Pi.zero_apply, sub_eq_zero] using (hlf x).symm
    have he' : FFREquations Λ μ J (fun x => grad f x + z x) η := by
      have heq : (fun x => grad f x + z x) = w := by ext x; simp [z]
      rwa [heq]
    obtain ⟨h39, h40⟩ := (zero_div_equiv hf hz hηpos hv).mp he'
    refine ⟨h39, h40, ?_, ?_⟩
    · intro x
      have h := weighted_identity hf hz hη hJ (weighted_eq hηpos h40) x
      have h0 : lap (0 : R3 → ℝ) = 0 := by ext y; simp [lap, pd_zero]
      rw [hv, h0] at h
      simp only [pd_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, sub_zero] at h
      linarith
    · change Filter.Tendsto (divg z) _ _
      rw [hv]
      exact tendsto_const_nhds
  · intro f z hf hz he
    obtain ⟨h39, h40, h41, hinf⟩ := he
    have hdiff : ∀ x, η x * lap (divg z) x = ∑ i, pd i η x * pd i (divg z) x := by
      intro x
      have h := weighted_identity hf hz hη hJ (weighted_eq hηpos h40) x
      rw [h41 x] at h
      linarith
    have hv : divg z = 0 := funext
      (FlatlyFoliated.decaying_drift_eq_zero η (divg z) hη (smooth_div hz) hηpos hdiff hinf)
    refine ⟨(zero_div_equiv hf hz hηpos hv).mpr ⟨h39, h40⟩, ?_⟩
    intro x
    rw [div_add (smooth_grad hf) hz, div_grad, hv]
    simp
