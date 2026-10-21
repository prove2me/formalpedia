-- Prove2me | solution 1 for CertDRO.NNSmooth.softmax_constants
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:03:47.397354+00:00
-- url     : https://prove2.me/submissions/3a99f6b1-6629-4f97-b9d9-bf801a815779

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Softmax

set_option autoImplicit false

open CertDRO.NNSmooth

namespace SMX

abbrev EK (K : ℕ) := EuclideanSpace ℝ (Fin K)

lemma S_pos {K : ℕ} [Nonempty (Fin K)] (v : EK K) : 0 < ∑ j, Real.exp (v j) :=
  Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty

noncomputable def Gc {K : ℕ} (v : EK K) : EK K →L[ℝ] ℝ :=
  (∑ j, Real.exp (v j))⁻¹ • ∑ j, Real.exp (v j) • (EuclideanSpace.proj j : EK K →L[ℝ] ℝ)

lemma hasFDerivAt_lse {K : ℕ} [Nonempty (Fin K)] (v : EK K) :
    HasFDerivAt (fun v : EK K => Real.log (∑ j, Real.exp (v j))) (Gc v) v := by
  have h1 : ∀ j ∈ Finset.univ, HasFDerivAt (fun v : EK K => Real.exp (v j))
      (Real.exp (v j) • (EuclideanSpace.proj j : EK K →L[ℝ] ℝ)) v := by
    intro j _
    exact ((EuclideanSpace.proj j : EK K →L[ℝ] ℝ).hasFDerivAt).exp
  have h2 := HasFDerivAt.fun_sum h1
  exact h2.log (S_pos v).ne'

lemma softmaxLoss_eq {K : ℕ} [Nonempty (Fin K)] (y : Fin K) (v : EK K) :
    softmaxLoss y v = Real.log (∑ j, Real.exp (v j)) - v y := by
  unfold softmaxLoss
  rw [Real.log_div (Real.exp_pos _).ne' (S_pos v).ne', Real.log_exp]
  ring

lemma Gc_apply {K : ℕ} [Nonempty (Fin K)] (v w : EK K) :
    Gc v w = ∑ j, softmaxProb v j * w j := by
  unfold Gc softmaxProb
  simp [Finset.mul_sum, div_eq_inv_mul, mul_assoc]

lemma hasGrad {K : ℕ} (y : Fin K) (v : EK K) :
    HasGradientAt (softmaxLoss y) (softmaxProb v - EuclideanSpace.single y 1) v := by
  have : Nonempty (Fin K) := ⟨y⟩
  have h1 : HasFDerivAt (softmaxLoss y)
      (Gc v - (EuclideanSpace.proj y : EK K →L[ℝ] ℝ)) v := by
    have : softmaxLoss y = fun v : EK K => Real.log (∑ j, Real.exp (v j)) - v y := by
      funext v; exact softmaxLoss_eq y v
    rw [this]
    exact (hasFDerivAt_lse v).sub (EuclideanSpace.proj y : EK K →L[ℝ] ℝ).hasFDerivAt
  have h2 : Gc v - (EuclideanSpace.proj y : EK K →L[ℝ] ℝ) =
      InnerProductSpace.toDual ℝ (EK K) (softmaxProb v - EuclideanSpace.single y 1) := by
    ext w
    rw [InnerProductSpace.toDual_apply_apply, inner_sub_left]
    simp [Gc_apply, EuclideanSpace.inner_single_left, PiLp.inner_apply, mul_comm]
  rw [h2] at h1
  exact h1


lemma prob_apply {K : ℕ} (v : EK K) (k : Fin K) :
    softmaxProb v k = Real.exp (v k) / ∑ j, Real.exp (v j) := rfl

lemma prob_nonneg {K : ℕ} [Nonempty (Fin K)] (v : EK K) (k : Fin K) : 0 ≤ softmaxProb v k := by
  rw [prob_apply]; exact div_nonneg (Real.exp_pos _).le (S_pos v).le

lemma prob_le_one {K : ℕ} [Nonempty (Fin K)] (v : EK K) (k : Fin K) : softmaxProb v k ≤ 1 := by
  rw [prob_apply, div_le_one (S_pos v)]
  exact Finset.single_le_sum (f := fun j => Real.exp (v j)) (fun j _ => (Real.exp_pos _).le)
    (Finset.mem_univ k)

lemma prob_sum {K : ℕ} [Nonempty (Fin K)] (v : EK K) : ∑ k, softmaxProb v k = 1 := by
  simp only [prob_apply]
  rw [← Finset.sum_div]; exact div_self (S_pos v).ne'

lemma norm_grad_sq_le {K : ℕ} (y : Fin K) (v : EK K) :
    ‖softmaxProb v - EuclideanSpace.single y 1‖ ^ 2 ≤ 2 := by
  have : Nonempty (Fin K) := ⟨y⟩
  rw [EuclideanSpace.norm_sq_eq]
  have h1 : ∀ k, ‖(softmaxProb v - EuclideanSpace.single y 1 : EK K) k‖ ^ 2 =
      softmaxProb v k ^ 2 - 2 * (if k = y then softmaxProb v k else 0) + (if k = y then 1 else 0) := by
    intro k
    simp only [PiLp.sub_apply, EuclideanSpace.single_apply, Real.norm_eq_abs, sq_abs]
    split_ifs <;> ring
  simp only [h1]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : ∑ k, softmaxProb v k ^ 2 ≤ ∑ k, softmaxProb v k :=
    Finset.sum_le_sum (fun k _ => by
      have := prob_nonneg v k; have := prob_le_one v k; nlinarith)
  rw [prob_sum] at h2
  have := prob_nonneg v y
  linarith

lemma norm_grad_le {K : ℕ} (y : Fin K) (v : EK K) :
    ‖softmaxProb v - EuclideanSpace.single y 1‖ ≤ Real.sqrt 2 :=
  le_trans (le_abs_self _) (Real.abs_le_sqrt (norm_grad_sq_le y v))

lemma fderiv_eq {K : ℕ} (y : Fin K) (v : EK K) :
    fderiv ℝ (softmaxLoss y) v =
      InnerProductSpace.toDual ℝ (EK K) (softmaxProb v - EuclideanSpace.single y 1) :=
  HasFDerivAt.fderiv (hasGrad y v)

lemma norm_fderiv_le {K : ℕ} (y : Fin K) (v : EK K) :
    ‖fderiv ℝ (softmaxLoss y) v‖ ≤ Real.sqrt 2 := by
  rw [fderiv_eq, LinearIsometryEquiv.norm_map]; exact norm_grad_le y v

lemma fderiv_sub_norm {K : ℕ} (y : Fin K) (u v : EK K) :
    ‖fderiv ℝ (softmaxLoss y) u - fderiv ℝ (softmaxLoss y) v‖ = ‖softmaxProb u - softmaxProb v‖ := by
  rw [fderiv_eq, fderiv_eq, ← map_sub, LinearIsometryEquiv.norm_map, sub_sub_sub_cancel_right]

lemma lip2 {K : ℕ} (y : Fin K) (u v : EK K) :
    |softmaxLoss y u - softmaxLoss y v| ≤ Real.sqrt 2 * ‖u - v‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := softmaxLoss y) (C := Real.sqrt 2)
    (s := Set.univ) (x := v) (y := u) (fun x _ => (hasGrad y x).differentiableAt)
    (fun x _ => norm_fderiv_le y x) convex_univ trivial trivial
  simpa [Real.norm_eq_abs] using this


noncomputable def Pc {K : ℕ} (v : EK K) : EK K →L[ℝ] EK K :=
  ((EuclideanSpace.equiv (Fin K) ℝ).symm : (Fin K → ℝ) →L[ℝ] EK K).comp
    (ContinuousLinearMap.pi (fun i => softmaxProb v i •
      ((EuclideanSpace.proj i : EK K →L[ℝ] ℝ) - Gc v)))

lemma Pc_apply {K : ℕ} (v w : EK K) (i : Fin K) :
    Pc v w i = softmaxProb v i * (w i - Gc v w) := by
  simp [Pc]

lemma hasFDerivAt_prob {K : ℕ} [Nonempty (Fin K)] (v : EK K) :
    HasFDerivAt (softmaxProb (K := K)) (Pc v) v := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h1 : HasFDerivAt (fun x : EK K => x i - Real.log (∑ j, Real.exp (x j)))
      ((EuclideanSpace.proj i : EK K →L[ℝ] ℝ) - Gc v) v :=
    (EuclideanSpace.proj i : EK K →L[ℝ] ℝ).hasFDerivAt.sub (hasFDerivAt_lse v)
  have h2 := h1.exp
  have e1 : (fun x : EK K => softmaxProb x i) =
      fun x : EK K => Real.exp (x i - Real.log (∑ j, Real.exp (x j))) := by
    funext x
    rw [prob_apply, Real.exp_sub, Real.exp_log (S_pos x)]
  have e2 : Real.exp (v i - Real.log (∑ j, Real.exp (v j))) = softmaxProb v i := by
    rw [prob_apply, Real.exp_sub, Real.exp_log (S_pos v)]
  rw [e1]
  have e3 : (PiLp.proj 2 (fun _ : Fin K => ℝ) i).comp (Pc v) =
      Real.exp (v i - Real.log (∑ j, Real.exp (v j))) •
        ((EuclideanSpace.proj i : EK K →L[ℝ] ℝ) - Gc v) := by
    rw [e2]
    refine ContinuousLinearMap.ext fun w => ?_
    simp [Pc_apply]
  rw [e3]
  exact h2

lemma Pc_norm_le {K : ℕ} [Nonempty (Fin K)] (v w : EK K) : ‖Pc v w‖ ≤ ‖w‖ := by
  set m := Gc v w with hm
  have hm' : m = ∑ j, softmaxProb v j * w j := Gc_apply v w
  have key : ∑ i, softmaxProb v i * (w i - m) ^ 2 = ∑ i, softmaxProb v i * w i ^ 2 - m ^ 2 := by
    have : ∀ i, softmaxProb v i * (w i - m) ^ 2 =
        softmaxProb v i * w i ^ 2 - 2 * m * (softmaxProb v i * w i) + m ^ 2 * softmaxProb v i := by
      intro i; ring
    simp only [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← hm', prob_sum]
    ring
  have h1 : ‖Pc v w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖Pc v w i‖ ^ 2 = ∑ i, (softmaxProb v i * (w i - m)) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pc_apply, Real.norm_eq_abs, sq_abs]
      _ ≤ ∑ i, softmaxProb v i * (w i - m) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := prob_nonneg v i; have := prob_le_one v i
          have h0 : 0 ≤ (w i - m) ^ 2 := sq_nonneg _
          calc (softmaxProb v i * (w i - m)) ^ 2 = softmaxProb v i * softmaxProb v i * (w i - m) ^ 2 := by ring
            _ ≤ softmaxProb v i * 1 * (w i - m) ^ 2 := by gcongr
            _ = _ := by ring
      _ ≤ ∑ i, softmaxProb v i * w i ^ 2 := by rw [key]; nlinarith [sq_nonneg m]
      _ ≤ ∑ i, ‖w i‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]
          have := prob_nonneg v i; have := prob_le_one v i
          nlinarith [sq_nonneg (w i)]
  by_contra h
  push_neg at h
  nlinarith [norm_nonneg w, norm_nonneg (Pc v w)]

lemma prob_lip {K : ℕ} [Nonempty (Fin K)] (u v : EK K) : ‖softmaxProb u - softmaxProb v‖ ≤ ‖u - v‖ := by
  have hb : ∀ x : EK K, ‖Pc x‖ ≤ 1 := fun x =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => by
      simpa using Pc_norm_le x w)
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := softmaxProb (K := K))
    (f' := Pc) (C := 1) (s := Set.univ) (x := v) (y := u)
    (fun x _ => (hasFDerivAt_prob x).hasFDerivWithinAt) (fun x _ => hb x) convex_univ trivial trivial
  simpa using this

lemma fderiv_lip {K : ℕ} (y : Fin K) (u v : EK K) :
    ‖fderiv ℝ (softmaxLoss y) u - fderiv ℝ (softmaxLoss y) v‖ ≤ 1 * ‖u - v‖ := by
  have : Nonempty (Fin K) := ⟨y⟩
  rw [fderiv_sub_norm, one_mul]; exact prob_lip u v


lemma S_single {K : ℕ} (k : Fin K) (t : ℝ) :
    ∑ j, Real.exp ((EuclideanSpace.single k t : EK K) j) = Real.exp t + ((K : ℝ) - 1) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have h1 : ∑ j ∈ Finset.univ.erase k, Real.exp ((EuclideanSpace.single k t : EK K) j) =
      ∑ j ∈ Finset.univ.erase k, (1 : ℝ) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have : j ≠ k := Finset.ne_of_mem_erase hj
    simp [EuclideanSpace.single_apply, this]
  rw [h1]
  have hK : 1 ≤ K := Fin.pos_iff_nonempty.mpr ⟨k⟩
  simp [Finset.card_erase_of_mem, Nat.cast_sub hK]

lemma sup_eq {K : ℕ} (y : Fin K) (hK : 2 ≤ K) :
    (⨆ v : EK K, ‖softmaxProb v - EuclideanSpace.single y 1‖) = Real.sqrt 2 := by
  have hne : Nonempty (Fin K) := ⟨y⟩
  have hbdd : BddAbove (Set.range fun v : EK K => ‖softmaxProb v - EuclideanSpace.single y 1‖) :=
    ⟨Real.sqrt 2, by rintro _ ⟨v, rfl⟩; exact norm_grad_le y v⟩
  apply le_antisymm
  · exact ciSup_le (fun v => norm_grad_le y v)
  · have : Nontrivial (Fin K) := Fin.nontrivial_iff_two_le.2 hK
    obtain ⟨k, hk⟩ := exists_ne y
    set c : ℝ := (K : ℝ) - 1 with hc
    have hc1 : 1 ≤ c := by
      have : (2 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    -- the test vector
    have hz : ‖(EuclideanSpace.single k (1 : ℝ) - EuclideanSpace.single y 1 : EK K)‖ = Real.sqrt 2 := by
      have h0 : ‖(EuclideanSpace.single k (1 : ℝ) - EuclideanSpace.single y 1 : EK K)‖ ^ 2 = 2 := by
        rw [norm_sub_sq_real]
        simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hk]
        norm_num
      rw [← h0]; exact (Real.sqrt_sq (norm_nonneg _)).symm
    have hlow : ∀ t : ℝ, (1 + (Real.exp t - 1) / (Real.exp t + c)) / Real.sqrt 2 ≤
        ‖softmaxProb (EuclideanSpace.single k t : EK K) - EuclideanSpace.single y 1‖ := by
      intro t
      set v : EK K := EuclideanSpace.single k t with hv
      set z : EK K := EuclideanSpace.single k (1 : ℝ) - EuclideanSpace.single y 1 with hzdef
      have hS : ∑ j, Real.exp (v j) = Real.exp t + c := S_single k t
      have hpk : softmaxProb v k = Real.exp t / (Real.exp t + c) := by
        rw [prob_apply, hS]; simp [hv]
      have hpy : softmaxProb v y = 1 / (Real.exp t + c) := by
        rw [prob_apply, hS]; simp [hv, EuclideanSpace.single_apply, hk.symm]
      have hinner : inner ℝ (softmaxProb v - EuclideanSpace.single y 1) z =
          1 + (Real.exp t - 1) / (Real.exp t + c) := by
        have hD : Real.exp t + c ≠ 0 := by positivity
        rw [hzdef, inner_sub_right, EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_right]
        simp [hpk, hpy, EuclideanSpace.single_apply, hk]
        field_simp
        ring
      have hcs := real_inner_le_norm (softmaxProb v - EuclideanSpace.single y 1) z
      rw [hinner, hz] at hcs
      have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      rw [div_le_iff₀ hs]
      exact hcs
    have hlim : Filter.Tendsto (fun t : ℝ => (1 + (Real.exp t - 1) / (Real.exp t + c)) / Real.sqrt 2)
        Filter.atTop (nhds ((1 + 1) / Real.sqrt 2)) := by
      refine Filter.Tendsto.div_const (tendsto_const_nhds.add ?_) _
      have h1 : Filter.Tendsto (fun t : ℝ => Real.exp t + c) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right _ _ Real.tendsto_exp_atTop
      have h2 : Filter.Tendsto (fun t : ℝ => (c + 1) / (Real.exp t + c)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop h1
      have h3 := (tendsto_const_nhds (x := (1 : ℝ))).sub h2
      simp only [sub_zero] at h3
      refine h3.congr fun t => ?_
      have hD : Real.exp t + c ≠ 0 := by positivity
      field_simp
      ring
    have hs : (1 + 1) / Real.sqrt 2 = Real.sqrt 2 := by
      have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      field_simp
      linarith
    rw [hs] at hlim
    exact le_of_tendsto' hlim fun t =>
      le_trans (hlow t) (le_ciSup hbdd (EuclideanSpace.single k t : EK K))

end SMX

theorem solution {K : ℕ} (y : Fin K) :
    (∀ v : EuclideanSpace ℝ (Fin K),
      HasGradientAt (softmaxLoss y) (softmaxProb v - EuclideanSpace.single y 1) v) ∧
    (∀ u v : EuclideanSpace ℝ (Fin K),
      |softmaxLoss y u - softmaxLoss y v| ≤ Real.sqrt 2 * ‖u - v‖) ∧
    (2 ≤ K → (⨆ v : EuclideanSpace ℝ (Fin K),
      ‖softmaxProb v - EuclideanSpace.single y 1‖) = Real.sqrt 2) ∧
    (∀ u v : EuclideanSpace ℝ (Fin K),
      ‖fderiv ℝ (softmaxLoss y) u - fderiv ℝ (softmaxLoss y) v‖ ≤ 1 * ‖u - v‖) :=
  ⟨fun v => SMX.hasGrad y v, fun u v => SMX.lip2 y u v, fun h => SMX.sup_eq y h,
    fun u v => SMX.fderiv_lip y u v⟩
