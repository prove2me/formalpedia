-- Prove2me | solution 1 for CurvatureSubmod.CSSP.lemma_8_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:17:21.44129+00:00
-- url     : https://prove2.me/submissions/47409fba-0554-4e8b-a83e-ead3824c3e5c

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting

namespace RRAux_CurvatureSubmod_CSSP_lemma_8_2

open CurvatureSubmod.CSSP

variable {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m))

theorem final_ineq (smin smax d S : ℝ) (h0 : 0 ≤ smin) (h1 : smin ≤ d) (_hS0 : 0 ≤ S)
    (hS : S ≤ smax ^ 2) :
    -d ^ 2 ≤ (1 - (1 - 1 / (smax / smin) ^ 2)) * (-S) := by
  have e : (1 - (1 - 1 / (smax / smin) ^ 2)) = smin ^ 2 / smax ^ 2 := by
    rw [div_pow, one_div_div]; ring
  rw [e]
  have hd : smin ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ h0 h1 2
  by_cases hm : smax = 0
  · subst hm; simp; positivity
  · have hpos : 0 < smax ^ 2 := by positivity
    have : smin ^ 2 / smax ^ 2 * S ≤ smin ^ 2 := by
      calc smin ^ 2 / smax ^ 2 * S ≤ smin ^ 2 / smax ^ 2 * smax ^ 2 :=
            mul_le_mul_of_nonneg_left hS (by positivity)
        _ = smin ^ 2 := by field_simp
    nlinarith

theorem proj_congr {K K' : Submodule ℝ (EuclideanSpace ℝ (Fin m))} (h : K = K')
    [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection] (x : EuclideanSpace ℝ (Fin m)) :
    K.starProjection x = K'.starProjection x := by
  subst h; rfl

theorem applyA_smul (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    applyA c (r • x) = r • applyA c x := by
  simp [applyA, Finset.smul_sum, smul_smul]

theorem applyA_bound (x : EuclideanSpace ℝ (Fin n)) :
    ‖applyA c x‖ ≤ ‖x‖ * ∑ j, ‖c j‖ := by
  unfold applyA
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x j) (norm_nonneg _)

noncomputable def smax : ℝ := ⨆ x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}, ‖applyA c x.1‖
noncomputable def smin : ℝ := ⨅ x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}, ‖applyA c x.1‖

theorem condNum_eq : condNum c = smax c / smin c := rfl

theorem smin_nonneg : 0 ≤ smin c := Real.iInf_nonneg fun _ => norm_nonneg _

theorem le_smax (x : EuclideanSpace ℝ (Fin n)) : ‖applyA c x‖ ≤ smax c * ‖x‖ := by
  by_cases hx : x = 0
  · subst hx; simp [applyA]
  · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hu : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
    have hb : BddAbove (Set.range fun x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1} =>
        ‖applyA c x.1‖) := by
      refine ⟨∑ j, ‖c j‖, ?_⟩
      rintro _ ⟨y, rfl⟩
      have := applyA_bound c y.1
      rw [y.2, one_mul] at this
      exact this
    have h := le_ciSup hb ⟨_, hu⟩
    simp only at h
    rw [applyA_smul, norm_smul, norm_inv, norm_norm] at h
    unfold smax
    rw [← div_le_iff₀ hxn, div_eq_inv_mul]
    exact h

theorem smin_le (x : EuclideanSpace ℝ (Fin n)) (hx : 1 ≤ ‖x‖) : smin c ≤ ‖applyA c x‖ := by
  have hxn : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx
  have hu : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
  have hb : BddBelow (Set.range fun x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1} =>
      ‖applyA c x.1‖) := ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
  have h := ciInf_le hb ⟨_, hu⟩
  simp only at h
  rw [applyA_smul, norm_smul, norm_inv, norm_norm] at h
  unfold smin
  refine h.trans ?_
  rw [← div_eq_inv_mul]
  exact div_le_self (norm_nonneg _) hx

theorem fA_univ : fA c Finset.univ = 0 := by
  unfold fA
  refine Finset.sum_eq_zero fun i _ => ?_
  have : proj c Finset.univ (c i) = c i := by
    unfold proj
    rw [Submodule.starProjection_eq_self_iff]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  rw [this]; simp

theorem fA_erase (j : Fin n) :
    fA c (Finset.univ.erase j) = ‖c j - proj c (Finset.univ.erase j) (c j)‖ ^ 2 := by
  unfold fA
  rw [Finset.sum_eq_single j]
  · intro i _ hij
    have : proj c (Finset.univ.erase j) (c i) = c i := by
      unfold proj
      rw [Submodule.starProjection_eq_self_iff]
      exact Submodule.subset_span ⟨i, by simp [hij], rfl⟩
    rw [this]; simp
  · simp

theorem proj_empty (x : EuclideanSpace ℝ (Fin m)) : proj c ∅ x = 0 := by
  unfold proj
  rw [proj_congr (K' := ⊥) (by simp [colSpan]), Submodule.starProjection_bot]
  rfl

theorem proj_single (j : Fin n) (x : EuclideanSpace ℝ (Fin m)) :
    proj c {j} x = (ℝ ∙ c j).starProjection x := by
  have hK : colSpan c {j} = ℝ ∙ c j := by
    unfold colSpan; rw [Finset.coe_singleton, Set.image_singleton]
  unfold proj
  exact proj_congr hK x

theorem norm_proj_single_sq (v w : EuclideanSpace ℝ (Fin m)) :
    ‖(ℝ ∙ v).starProjection w‖ ^ 2 = (inner ℝ v w) ^ 2 / ‖v‖ ^ 2 := by
  rw [Submodule.starProjection_singleton, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  by_cases hv : ‖v‖ = 0
  · simp [hv]
  · show (inner ℝ v w / (‖v‖ ^ 2)) ^ 2 * ‖v‖ ^ 2 = _
    field_simp

theorem pythag (K : Submodule ℝ (EuclideanSpace ℝ (Fin m))) [K.HasOrthogonalProjection]
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖x - K.starProjection x‖ ^ 2 = ‖x‖ ^ 2 - ‖K.starProjection x‖ ^ 2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection x K
  have h2 : Kᗮ.starProjection x = x - K.starProjection x := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact Submodule.starProjection_add_starProjection_orthogonal x
  rw [h2] at h
  linarith

theorem marg_empty (j : Fin n) :
    CurvatureSubmod.LocalSearch.marg (fA c) ∅ j =
      -∑ i, (inner ℝ (c j) (c i)) ^ 2 / ‖c j‖ ^ 2 := by
  unfold CurvatureSubmod.LocalSearch.marg fA
  rw [show insert j (∅ : Finset (Fin n)) = {j} from rfl]
  simp only [proj_single, proj_empty, sub_zero]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pythag, norm_proj_single_sq]
  ring

theorem marg_erase (j : Fin n) :
    CurvatureSubmod.LocalSearch.marg (fA c) (Finset.univ.erase j) j =
      -‖c j - proj c (Finset.univ.erase j) (c j)‖ ^ 2 := by
  unfold CurvatureSubmod.LocalSearch.marg
  rw [Finset.insert_erase (Finset.mem_univ j), fA_univ, fA_erase]
  ring

-- the distance from c_j to the span of the others is at least σ_min
theorem smin_le_dist (j : Fin n) :
    smin c ≤ ‖c j - proj c (Finset.univ.erase j) (c j)‖ := by
  have hmem := Submodule.starProjection_apply_mem (colSpan c (Finset.univ.erase j)) (c j)
  obtain ⟨t, ht, α, hα⟩ := (Submodule.mem_span_image_iff_exists_fun ℝ).1
    (hmem : _ ∈ Submodule.span ℝ (c '' ↑(Finset.univ.erase j)))
  classical
  let β : Fin n → ℝ := fun i => if h : i ∈ t then α ⟨i, h⟩ else 0
  have hjt : j ∉ t := fun h => by simpa using ht h
  have hβj : β j = 0 := by simp [β, hjt]
  have hsum : ∑ i, β i • c i = proj c (Finset.univ.erase j) (c j) := by
    unfold proj
    rw [← hα]
    rw [← Finset.sum_subset (Finset.subset_univ t)]
    · rw [← Finset.sum_coe_sort t]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [β, i.2]
    · intro i _ hi; simp [β, hi]
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => (if i = j then 1 else 0) - β i)
  have hAx : applyA c x = c j - proj c (Finset.univ.erase j) (c j) := by
    rw [← hsum]
    simp [applyA, x, sub_smul, Finset.sum_sub_distrib, ite_smul]
  have hx : 1 ≤ ‖x‖ := by
    have := PiLp.norm_apply_le x j
    simpa [x, hβj] using this
  rw [← hAx]
  exact smin_le c x hx

theorem S_le (j : Fin n) :
    ∑ i, (inner ℝ (c j) (c i)) ^ 2 / ‖c j‖ ^ 2 ≤ smax c ^ 2 := by
  rw [← Finset.sum_div]
  set T := ∑ i, (inner ℝ (c j) (c i)) ^ 2 with hT
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => inner ℝ (c j) (c i))
  have hx2 : ‖x‖ ^ 2 = T := by
    rw [EuclideanSpace.real_norm_sq_eq]
  have hinner : inner ℝ (applyA c x) (c j) = T := by
    simp only [applyA, x, sum_inner, inner_smul_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [real_inner_comm, sq]
  have h1 : T ≤ smax c * ‖x‖ * ‖c j‖ := by
    rw [← hinner]
    refine (real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (le_smax c x) (norm_nonneg _)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => sq_nonneg _
  have key : T ≤ smax c ^ 2 * ‖c j‖ ^ 2 :=
    aux T (smax c) ‖x‖ ‖c j‖ hT0 (norm_nonneg _) hx2 h1
  by_cases hN : ‖c j‖ = 0
  · simp [hN]; positivity
  · rw [div_le_iff₀ (by positivity)]
    exact key
where
  aux (T s a N : ℝ) (hT0 : 0 ≤ T) (ha : 0 ≤ a) (hx2 : a ^ 2 = T) (h1 : T ≤ s * a * N) :
      T ≤ s ^ 2 * N ^ 2 := by
    by_cases hT : T = 0
    · rw [hT]; positivity
    · have hTp : 0 < T := lt_of_le_of_ne hT0 (Ne.symm hT)
      have h2 : T ^ 2 ≤ (s * a * N) ^ 2 := pow_le_pow_left₀ hT0 h1 2
      have h3 : (s * a * N) ^ 2 = s ^ 2 * N ^ 2 * T := by rw [← hx2]; ring
      rw [h3, sq] at h2
      exact le_of_mul_le_mul_right (by linarith) hTp

end RRAux_CurvatureSubmod_CSSP_lemma_8_2

open CurvatureSubmod.CSSP in
theorem solution {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m))
    (hc : LinearIndependent ℝ c) :
    CurvatureSubmod.LocalSearch.CurvAtMostDec (fA c) (1 - 1 / condNum c ^ 2) := by
  intro j
  rw [RRAux_CurvatureSubmod_CSSP_lemma_8_2.marg_erase, RRAux_CurvatureSubmod_CSSP_lemma_8_2.marg_empty,
    RRAux_CurvatureSubmod_CSSP_lemma_8_2.condNum_eq]
  exact RRAux_CurvatureSubmod_CSSP_lemma_8_2.final_ineq _ _ _ _
    (RRAux_CurvatureSubmod_CSSP_lemma_8_2.smin_nonneg c)
    (RRAux_CurvatureSubmod_CSSP_lemma_8_2.smin_le_dist c j)
    (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
    (RRAux_CurvatureSubmod_CSSP_lemma_8_2.S_le c j)

#print axioms solution
