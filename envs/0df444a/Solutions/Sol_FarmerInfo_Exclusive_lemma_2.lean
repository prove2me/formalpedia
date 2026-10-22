-- Prove2me | solution 1 for FarmerInfo.Exclusive.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T22:38:59.724054+00:00
-- url     : https://prove2.me/submissions/05d6dfb0-9cb7-4876-bf62-dc0e79a036f0

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

open MeasureTheory ProbabilityTheory Finset

namespace FarmerAux
open FarmerInfo.Exclusive

variable (M : Model)

instance instProbP : IsProbabilityMeasure M.P := by
  unfold Model.P; infer_instance

lemma isGaussian_pi (n : ℕ) (v : NNReal) :
    IsGaussian (Measure.pi fun _ : Fin n => gaussianReal 0 v) := by
  have h1 : ∀ i : Fin n, HasGaussianLaw (fun x : Fin n → ℝ => x i)
      (Measure.pi fun _ : Fin n => gaussianReal 0 v) := by
    intro i
    have hm := (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 v) i)
    refine ⟨?_⟩
    rw [show (fun x : Fin n → ℝ => x i) = Function.eval i from rfl, hm.map_eq]
    infer_instance
  have h2 : iIndepFun (fun i (x : Fin n → ℝ) => x i)
      (Measure.pi fun _ : Fin n => gaussianReal 0 v) :=
    iIndepFun_pi (X := fun _ (x : ℝ) => x) (fun _ => aemeasurable_id)
  have := (h2.hasGaussianLaw h1).isGaussian_map
  simpa using this

instance instGaussP : IsGaussian M.P := by
  unfold Model.P
  have := isGaussian_pi M.n (M.γ⁻¹).toNNReal
  infer_instance

/-- coordinates of the sample space, as continuous linear functionals -/
noncomputable def coordL : Option (Option (Fin M.n)) → (M.Ω →L[ℝ] ℝ)
  | none => ContinuousLinearMap.fst ℝ ℝ _
  | some none => (ContinuousLinearMap.snd ℝ (Fin M.n → ℝ) ℝ).comp (ContinuousLinearMap.snd ℝ ℝ _)
  | some (some k) => (ContinuousLinearMap.proj k).comp
      ((ContinuousLinearMap.fst ℝ (Fin M.n → ℝ) ℝ).comp (ContinuousLinearMap.snd ℝ ℝ _))

noncomputable def coord (j : Option (Option (Fin M.n))) (ω : M.Ω) : ℝ := coordL M j ω

@[simp] lemma coord_none (ω : M.Ω) : coord M none ω = ω.1 := rfl
@[simp] lemma coord_some_none (ω : M.Ω) : coord M (some none) ω = ω.2.2 := rfl
@[simp] lemma coord_some_some (k : Fin M.n) (ω : M.Ω) : coord M (some (some k)) ω = ω.2.1 k := rfl

def basis : Option (Option (Fin M.n)) → M.Ω
  | none => (1, 0, 0)
  | some none => (0, 0, 1)
  | some (some k) => (0, Pi.single k 1, 0)

noncomputable def var : Option (Option (Fin M.n)) → ℝ
  | none => M.α⁻¹
  | some none => M.β⁻¹
  | some (some _) => M.γ⁻¹

lemma decomp (ω : M.Ω) : ω = ∑ j, coord M j ω • basis M j := by
  obtain ⟨u, e, h⟩ := ω
  simp only [Fintype.sum_option, coord_none, coord_some_none, coord_some_some, basis]
  ext
  · simp [Prod.fst_sum]
  · simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Prod.fst_sum,
      Prod.snd_sum, smul_zero, zero_add, Finset.sum_apply]
    rename_i k
    simp [Pi.single_apply]
  · simp [Prod.snd_sum]

lemma clm_decomp (L : M.Ω →L[ℝ] ℝ) (ω : M.Ω) :
    L ω = ∑ j, L (basis M j) * coord M j ω := by
  conv_lhs => rw [decomp M ω]
  simp [map_sum, mul_comm]

lemma memLp_clm (L : M.Ω →L[ℝ] ℝ) : MemLp (fun ω => L ω) 2 M.P :=
  (IsGaussian.hasGaussianLaw_id (μ := M.P)).map_fun L |>.memLp_two

lemma memLp_coord (j) : MemLp (coord M j) 2 M.P := memLp_clm M (coordL M j)

lemma measurable_coord (j) : Measurable (coord M j) := (coordL M j).continuous.measurable

lemma gauss_mean (v : NNReal) : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal

lemma gauss_sq (v : NNReal) : ∫ x, x * x ∂(gaussianReal 0 v) = v := by
  have h := variance_of_integral_eq_zero (μ := gaussianReal 0 v) (X := fun x => x)
    aemeasurable_id (gauss_mean v)
  rw [variance_fun_id_gaussianReal] at h
  rw [h]; congr 1; funext x; ring

lemma pi_eval (v : NNReal) (k : Fin M.n) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ x, f (x k) ∂(Measure.pi fun _ : Fin M.n => gaussianReal 0 v) =
      ∫ x, f x ∂(gaussianReal 0 v) := by
  have hm := measurePreserving_eval (fun _ : Fin M.n => gaussianReal 0 v) k
  conv_rhs => rw [← hm.map_eq]
  rw [integral_map (measurable_pi_apply k).aemeasurable hf.aestronglyMeasurable]

lemma pi_indep (v : NNReal) (k l : Fin M.n) (hkl : k ≠ l) :
    ∫ x, x k * x l ∂(Measure.pi fun _ : Fin M.n => gaussianReal 0 v) = 0 := by
  have h2 : iIndepFun (fun i (x : Fin M.n → ℝ) => x i)
      (Measure.pi fun _ : Fin M.n => gaussianReal 0 v) :=
    iIndepFun_pi (X := fun _ (x : ℝ) => x) (fun _ => aemeasurable_id)
  have h := (h2.indepFun hkl).integral_fun_mul_eq_mul_integral
    (measurable_pi_apply k).aestronglyMeasurable (measurable_pi_apply l).aestronglyMeasurable
  rw [h]
  have : ∫ x, x k ∂(Measure.pi fun _ : Fin M.n => gaussianReal 0 v) = 0 := by
    rw [pi_eval M v k (fun x => x) measurable_id, gauss_mean]
  simp [this]

lemma pi_mean (v : NNReal) (k : Fin M.n) :
    ∫ x, x k ∂(Measure.pi fun _ : Fin M.n => gaussianReal 0 v) = 0 := by
  rw [pi_eval M v k (fun x => x) measurable_id, gauss_mean]

lemma pi_sq (v : NNReal) (k : Fin M.n) :
    ∫ x, x k * x k ∂(Measure.pi fun _ : Fin M.n => gaussianReal 0 v) = v := by
  rw [pi_eval M v k (fun x => x * x) (by fun_prop), gauss_sq]

lemma integral_coord (j) : ∫ ω, coord M j ω ∂M.P = 0 := by
  rcases j with _ | _ | k
  · simp only [coord_none, Model.P]
    rw [integral_fun_fst (f := fun x : ℝ => x)]; simp
  · simp only [coord_some_none, Model.P]
    rw [integral_fun_snd (f := fun z : (Fin M.n → ℝ) × ℝ => z.2),
      integral_fun_snd (f := fun x : ℝ => x)]
    simp
  · simp only [coord_some_some, Model.P]
    rw [integral_fun_snd (f := fun z : (Fin M.n → ℝ) × ℝ => z.1 k),
      integral_fun_fst (f := fun x : Fin M.n → ℝ => x k)]
    simp [pi_mean]

lemma m_uu (hα : 0 < M.α) : ∫ ω, ω.1 * ω.1 ∂M.P = M.α⁻¹ := by
  simp only [Model.P]
  rw [integral_fun_fst (f := fun x : ℝ => x * x)]
  simp [gauss_sq, hα.le]

lemma m_hh (hβ : 0 < M.β) : ∫ ω, ω.2.2 * ω.2.2 ∂M.P = M.β⁻¹ := by
  simp only [Model.P]
  rw [integral_fun_snd (f := fun z : (Fin M.n → ℝ) × ℝ => z.2 * z.2),
    integral_fun_snd (f := fun x : ℝ => x * x)]
  simp [gauss_sq, hβ.le]

lemma m_ee (hγ : 0 < M.γ) (k : Fin M.n) : ∫ ω, ω.2.1 k * ω.2.1 k ∂M.P = M.γ⁻¹ := by
  simp only [Model.P]
  rw [integral_fun_snd (f := fun z : (Fin M.n → ℝ) × ℝ => z.1 k * z.1 k),
    integral_fun_fst (f := fun x : Fin M.n → ℝ => x k * x k)]
  simp [pi_sq, hγ.le]

lemma m_uh : ∫ ω, ω.1 * ω.2.2 ∂M.P = 0 := by
  simp only [Model.P]
  rw [integral_prod_mul (f := fun x : ℝ => x) (g := fun z : (Fin M.n → ℝ) × ℝ => z.2)]
  simp

lemma m_ue (k : Fin M.n) : ∫ ω, ω.1 * ω.2.1 k ∂M.P = 0 := by
  simp only [Model.P]
  rw [integral_prod_mul (f := fun x : ℝ => x) (g := fun z : (Fin M.n → ℝ) × ℝ => z.1 k)]
  simp

lemma m_eh (k : Fin M.n) : ∫ ω, ω.2.1 k * ω.2.2 ∂M.P = 0 := by
  simp only [Model.P]
  rw [integral_fun_snd (f := fun z : (Fin M.n → ℝ) × ℝ => z.1 k * z.2),
    integral_prod_mul (f := fun x : Fin M.n → ℝ => x k) (g := fun x : ℝ => x)]
  simp [pi_mean]

lemma m_ee' (k l : Fin M.n) (hkl : k ≠ l) : ∫ ω, ω.2.1 k * ω.2.1 l ∂M.P = 0 := by
  simp only [Model.P]
  rw [integral_fun_snd (f := fun z : (Fin M.n → ℝ) × ℝ => z.1 k * z.1 l),
    integral_fun_fst (f := fun x : Fin M.n → ℝ => x k * x l)]
  simp [pi_indep M _ k l hkl]

lemma swap_int (f g : M.Ω → ℝ) : ∫ ω, f ω * g ω ∂M.P = ∫ ω, g ω * f ω ∂M.P := by
  congr 1; funext ω; ring

lemma moment2 (hM : M.Standing) (j l) :
    ∫ ω, coord M j ω * coord M l ω ∂M.P = if j = l then var M j else 0 := by
  obtain ⟨_, _, _, hα, hβ, hγ⟩ := hM
  rcases j with _ | _ | k <;> rcases l with _ | _ | l <;>
    simp only [coord_none, coord_some_none, coord_some_some, var, reduceCtorEq, if_false,
      if_true, Option.some.injEq]
  · exact m_uu M hα
  · exact m_uh M
  · exact m_ue M l
  · rw [swap_int]; exact m_uh M
  · exact m_hh M hβ
  · rw [swap_int]; exact m_eh M l
  · rw [swap_int]; exact m_ue M k
  · exact m_eh M k
  · split_ifs with h
    · subst h; exact m_ee M hγ k
    · exact m_ee' M k l h

noncomputable def covL (L1 L2 : M.Ω →L[ℝ] ℝ) : ℝ :=
  ∑ j, L1 (basis M j) * L2 (basis M j) * var M j

lemma integral_clm (L : M.Ω →L[ℝ] ℝ) : ∫ ω, L ω ∂M.P = 0 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (clm_decomp M L))]
  rw [integral_finsetSum _ (fun j _ => ((memLp_coord M j).integrable one_le_two).const_mul _)]
  simp [integral_const_mul, integral_coord]

lemma integral_clm_mul (hM : M.Standing) (L1 L2 : M.Ω →L[ℝ] ℝ) :
    ∫ ω, L1 ω * L2 ω ∂M.P = covL M L1 L2 := by
  have hI : ∀ j l, Integrable (fun ω => coord M j ω * coord M l ω) M.P := fun j l =>
    (memLp_coord M j).integrable_mul (memLp_coord M l)
  have : ∀ ω, L1 ω * L2 ω = ∑ j, ∑ l, (L1 (basis M j) * L2 (basis M l)) *
      (coord M j ω * coord M l ω) := by
    intro ω
    rw [clm_decomp M L1, clm_decomp M L2, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring))
  simp_rw [this]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun l _ => (hI j l).const_mul _))]
  simp_rw [integral_finsetSum _ (fun l _ => (hI _ l).const_mul _), integral_const_mul,
    moment2 M hM]
  unfold covL
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [mul_comm]

lemma covariance_clm (hM : M.Standing) (L1 L2 : M.Ω →L[ℝ] ℝ) :
    cov[fun ω => L1 ω, fun ω => L2 ω; M.P] = covL M L1 L2 := by
  rw [covariance_eq_sub (memLp_clm M L1) (memLp_clm M L2)]
  simp [integral_clm, integral_clm_mul M hM]

/-- Orthogonality: an uncorrelated Gaussian linear functional is orthogonal to every
measurable function of the observed linear functionals. -/
lemma orth (hM : M.Standing) (L : M.Ω →L[ℝ] ℝ) {κ : Type} [Fintype κ]
    (D : κ → (M.Ω →L[ℝ] ℝ)) (h : ∀ j, covL M L (D j) = 0)
    (ψ : (κ → ℝ) → ℝ) (hψ : Measurable ψ) :
    ∫ ω, L ω * ψ (fun j => D j ω) ∂M.P = 0 := by
  let Lf : M.Ω →L[ℝ] (Unit → ℝ) × (κ → ℝ) :=
    (ContinuousLinearMap.pi fun _ : Unit => L).prod (ContinuousLinearMap.pi D)
  have hG : HasGaussianLaw (fun ω => ((fun _ : Unit => L ω), fun j => D j ω)) M.P :=
    (IsGaussian.hasGaussianLaw_id (μ := M.P)).map_fun Lf
  have hind := HasGaussianLaw.indepFun_of_covariance_eval (X := fun (_ : Unit) ω => L ω)
    (Y := fun j ω => D j ω) hG (fun _ j => by rw [covariance_clm M hM]; exact h j)
  have hφ : Measurable (fun v : Unit → ℝ => v ()) := measurable_pi_apply ()
  have hind2 := hind.comp hφ hψ
  have := hind2.integral_fun_mul_eq_mul_integral
    (L.continuous.measurable.aestronglyMeasurable)
    ((hψ.comp (measurable_pi_lambda _ (fun j => (D j).continuous.measurable))).aestronglyMeasurable)
  simp only [Function.comp_def] at this
  rw [this, integral_clm, zero_mul]

/-! ## The game in linear-functional form -/

noncomputable def xL (i : Fin M.n) : M.Ω →L[ℝ] ℝ := coordL M none + coordL M (some (some i))
noncomputable def yL : M.Ω →L[ℝ] ℝ := coordL M none + coordL M (some none)
noncomputable def obsL (I : Finset (Fin M.n)) (i : Fin M.n) : Fin 2 → (M.Ω →L[ℝ] ℝ) :=
  ![xL M i, if i ∈ I then yL M else 0]

@[simp] lemma coordL_apply (j) (ω : M.Ω) : coordL M j ω = coord M j ω := rfl

lemma xL_apply (i : Fin M.n) (ω : M.Ω) : xL M i ω = M.x i ω := by
  simp [xL, Model.x]

lemma yL_apply (ω : M.Ω) : yL M ω = M.y ω := by
  simp [yL, Model.y]

lemma obs_eq (I : Finset (Fin M.n)) (i : Fin M.n) (ω : M.Ω) :
    M.obs I i ω = (obsL M I i 0 ω, obsL M I i 1 ω) := by
  unfold Model.obs obsL
  split_ifs with h <;> simp [xL_apply, yL_apply]

noncomputable def linL (I : Finset (Fin M.n)) (k : Fin M.n) : M.Ω →L[ℝ] ℝ :=
  if k ∈ I then M.A1 (I.card : ℝ) • xL M k + M.A2 (I.card : ℝ) • yL M
  else M.B1 (I.card : ℝ) • xL M k

lemma lin_obs (I : Finset (Fin M.n)) (k : Fin M.n) (ω : M.Ω) :
    M.linProfile I k (M.obs I k ω) = M.A0 + linL M I k ω := by
  unfold Model.linProfile linL
  rw [obs_eq M I k ω]
  split_ifs with h <;> simp [obsL, h, xL_apply, yL_apply, Model.B0] <;> ring

noncomputable def ZL (I : Finset (Fin M.n)) (i : Fin M.n) : M.Ω →L[ℝ] ℝ :=
  coordL M none - M.b • (∑ k, linL M I k) - M.b • linL M I i

lemma Z_eq (hM : M.Standing) (I : Finset (Fin M.n)) (i : Fin M.n) (ω : M.Ω) :
    M.a - M.c + M.u ω - M.b * (∑ k, M.linProfile I k (M.obs I k ω))
      - M.b * M.linProfile I i (M.obs I i ω) = ZL M I i ω := by
  obtain ⟨_, _, hb, _, _, _⟩ := hM
  simp only [lin_obs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ZL, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, coordL_apply, coord_none,
    smul_eq_mul]
  have hA : M.A0 = (M.a - M.c) / (M.b * ((M.n : ℝ) + 1)) := rfl
  have hn1 : (M.n : ℝ) + 1 ≠ 0 := by positivity
  rw [hA]
  simp only [Model.u]
  field_simp
  ring

lemma coord_basis (j l : Option (Option (Fin M.n))) :
    coord M j (basis M l) = if j = l then 1 else 0 := by
  rcases j with _ | _ | k <;> rcases l with _ | _ | l <;>
    simp [basis, Pi.single_apply, eq_comm]

lemma sum_ite_mem (I : Finset (Fin M.n)) (p q : ℝ) :
    ∑ k : Fin M.n, (if k ∈ I then p else q) = (I.card : ℝ) * p + ((M.n : ℝ) - I.card) * q := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have h1 : (Finset.univ.filter (fun i : Fin M.n => i ∈ I)) = I := by ext i; simp
  have h2 : (Finset.univ.filter (fun i : Fin M.n => i ∉ I)) = Finset.univ \ I := by ext i; simp
  have hle : I.card ≤ M.n := by simpa using Finset.card_le_univ I
  rw [h1, h2, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, Nat.cast_sub hle]

lemma linL_none (I : Finset (Fin M.n)) (k : Fin M.n) :
    linL M I k (basis M none) =
      if k ∈ I then M.A1 (I.card : ℝ) + M.A2 (I.card : ℝ) else M.B1 (I.card : ℝ) := by
  unfold linL xL yL
  split_ifs <;> simp [coord_basis]

lemma linL_h (I : Finset (Fin M.n)) (k : Fin M.n) :
    linL M I k (basis M (some none)) = if k ∈ I then M.A2 (I.card : ℝ) else 0 := by
  unfold linL xL yL
  split_ifs <;> simp [coord_basis]

lemma linL_e (I : Finset (Fin M.n)) (k l : Fin M.n) :
    linL M I k (basis M (some (some l))) =
      if l = k then (if k ∈ I then M.A1 (I.card : ℝ) else M.B1 (I.card : ℝ)) else 0 := by
  unfold linL xL yL
  by_cases h1 : k ∈ I <;> by_cases h2 : l = k <;> simp [h1, h2, coord_basis] <;>
    exact fun h => absurd h.symm h2

lemma ZL_basis (I : Finset (Fin M.n)) (i : Fin M.n) (j) :
    ZL M I i (basis M j) = coord M none (basis M j) - M.b * (∑ k, linL M I k (basis M j))
      - M.b * linL M I i (basis M j) := by
  simp [ZL]

lemma Psi_pos (hM : M.Standing) (t : ℝ) (ht : 0 ≤ t) : 0 < M.Psi t := by
  obtain ⟨_, _, _, hα, hβ, hγ⟩ := hM
  unfold Model.Psi; positivity

lemma cov_ZL_obs (hM : M.Standing) (I : Finset (Fin M.n)) (i : Fin M.n) (j : Fin 2) :
    covL M (ZL M I i) (obsL M I i j) = 0 := by
  have hP := Psi_pos M hM (I.card : ℝ) (Nat.cast_nonneg _)
  obtain ⟨_, _, hb, hα, hβ, hγ⟩ := hM
  fin_cases j
  · simp only [covL, Fintype.sum_option, obsL, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    simp only [ZL_basis, linL_none, linL_h, linL_e, sum_ite_mem, xL, ContinuousLinearMap.add_apply,
      coordL_apply, coord_basis, var]
    simp
    split_ifs with h
    · unfold Model.A1 Model.A2 Model.B1
      field_simp
      unfold Model.Psi
      ring
    · unfold Model.A1 Model.A2 Model.B1
      field_simp
      unfold Model.Psi
      ring
  · simp only [obsL, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    split_ifs with h
    · simp only [covL, Fintype.sum_option]
      simp only [ZL_basis, linL_none, linL_h, linL_e, sum_ite_mem, yL, ContinuousLinearMap.add_apply,
        coordL_apply, coord_basis, var]
      simp [h]
      unfold Model.A1 Model.A2 Model.B1
      field_simp
      unfold Model.Psi
      ring
    · simp [covL]

lemma foc_lin (hM : M.Standing) (I : Finset (Fin M.n)) (i : Fin M.n)
    (f : Model.Strategy) (hf : Measurable f) :
    ∫ ω, ZL M I i ω * f (M.obs I i ω) ∂M.P = 0 := by
  simp_rw [obs_eq M I i]
  exact orth M hM (ZL M I i) (obsL M I i) (cov_ZL_obs M hM I i)
    (fun v => f (v 0, v 1)) (hf.comp (by fun_prop))

/-- what the other farmers' choices leave to farmer `i` -/
noncomputable def Yo (I : Finset (Fin M.n)) (σ : Fin M.n → Model.Strategy) (i : Fin M.n)
    (ω : M.Ω) : ℝ :=
  M.a - M.c + M.u ω - M.b * (∑ k, σ k (M.obs I k ω) - σ i (M.obs I i ω))

lemma others_update (I : Finset (Fin M.n)) (σ : Fin M.n → Model.Strategy) (i : Fin M.n)
    (f : Model.Strategy) (ω : M.Ω) :
    ∑ k, (Function.update σ i f) k (M.obs I k ω) - f (M.obs I i ω) =
      ∑ k, σ k (M.obs I k ω) - σ i (M.obs I i ω) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun k => σ k (M.obs I k ω)) (Finset.mem_univ i)]
  simp only [Function.update_self]
  have : ∑ k ∈ Finset.univ.erase i, Function.update σ i f k (M.obs I k ω) =
      ∑ k ∈ Finset.univ.erase i, σ k (M.obs I k ω) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [this]; ring

lemma Yo_update (I : Finset (Fin M.n)) (σ : Fin M.n → Model.Strategy) (i : Fin M.n)
    (f : Model.Strategy) (ω : M.Ω) :
    Yo M I (Function.update σ i f) i ω = Yo M I σ i ω := by
  unfold Yo
  rw [Function.update_self, others_update]

lemma profit_eq (I : Finset (Fin M.n)) (σ : Fin M.n → Model.Strategy) (i : Fin M.n)
    (ω : M.Ω) :
    M.profit I σ i ω = (Yo M I σ i ω - M.b * σ i (M.obs I i ω)) * σ i (M.obs I i ω) := by
  unfold Model.profit Yo; ring

lemma profit_update (I : Finset (Fin M.n)) (σ : Fin M.n → Model.Strategy) (i : Fin M.n)
    (f : Model.Strategy) (ω : M.Ω) :
    M.profit I (Function.update σ i f) i ω =
      (Yo M I σ i ω - M.b * f (M.obs I i ω)) * f (M.obs I i ω) := by
  rw [profit_eq, Yo_update, Function.update_self]

lemma memLp_Yo (I : Finset (Fin M.n)) (σ : Fin M.n → Model.Strategy) (i : Fin M.n)
    (hσ : ∀ k, MemLp (fun ω => σ k (M.obs I k ω)) 2 M.P) :
    MemLp (Yo M I σ i) 2 M.P := by
  unfold Yo
  have hu : MemLp (fun ω : M.Ω => M.u ω) 2 M.P := memLp_coord M none
  have hs : MemLp (fun ω => ∑ k, σ k (M.obs I k ω)) 2 M.P := memLp_finsetSum _ (fun k _ => hσ k)
  have h1 : MemLp (fun ω : M.Ω => M.a - M.c + M.u ω) 2 M.P := (memLp_const (M.a - M.c)).add hu
  have h2 : MemLp (fun ω => M.b * (∑ k, σ k (M.obs I k ω) - σ i (M.obs I i ω))) 2 M.P :=
    (hs.sub (hσ i)).const_mul M.b
  exact h1.sub h2

lemma measurable_lin (I : Finset (Fin M.n)) (k : Fin M.n) : Measurable (M.linProfile I k) := by
  unfold Model.linProfile
  split_ifs <;> fun_prop

lemma memLp_lin (I : Finset (Fin M.n)) (k : Fin M.n) :
    MemLp (fun ω => M.linProfile I k (M.obs I k ω)) 2 M.P := by
  have h : (fun ω => M.linProfile I k (M.obs I k ω)) = fun ω => M.A0 + linL M I k ω := by
    funext ω; exact lin_obs M I k ω
  rw [h]
  exact (memLp_const M.A0).add (memLp_clm M (linL M I k))

lemma admissible_lin (I : Finset (Fin M.n)) (k : Fin M.n) :
    M.Admissible I k (M.linProfile I k) := ⟨measurable_lin M I k, memLp_lin M I k⟩

lemma Yo_lin (hM : M.Standing) (I : Finset (Fin M.n)) (i : Fin M.n) (ω : M.Ω) :
    Yo M I (M.linProfile I) i ω = 2 * M.b * M.linProfile I i (M.obs I i ω) + ZL M I i ω := by
  rw [← Z_eq M hM]; unfold Yo; ring

theorem existence (hM : M.Standing) (I : Finset (Fin M.n)) : M.IsBNE I (M.linProfile I) := by
  refine ⟨admissible_lin M I, fun i f hf => ?_⟩
  obtain ⟨hfm, hfL⟩ := hf
  set q : M.Ω → ℝ := fun ω => M.linProfile I i (M.obs I i ω) with hq
  set g : M.Ω → ℝ := fun ω => f (M.obs I i ω) with hg
  have hqL : MemLp q 2 M.P := memLp_lin M I i
  have hYL : MemLp (Yo M I (M.linProfile I) i) 2 M.P := memLp_Yo M I _ i (memLp_lin M I)
  have hZL : MemLp (fun ω => ZL M I i ω) 2 M.P := memLp_clm M _
  have h1 : Integrable (fun ω => M.profit I (Function.update (M.linProfile I) i f) i ω) M.P := by
    simp_rw [profit_update]
    exact (hYL.sub (hfL.const_mul M.b)).integrable_mul hfL
  have h2 : Integrable (fun ω => M.profit I (M.linProfile I) i ω) M.P := by
    simp_rw [profit_eq]
    exact (hYL.sub (hqL.const_mul M.b)).integrable_mul hqL
  have h3 : Integrable (fun ω => ZL M I i ω * (q ω - g ω)) M.P :=
    hZL.integrable_mul (hqL.sub hfL)
  have h4 : Integrable (fun ω => M.b * ((q ω - g ω) * (q ω - g ω))) M.P :=
    ((hqL.sub hfL).integrable_mul (hqL.sub hfL)).const_mul _
  have hdiff : ∀ ω, M.profit I (M.linProfile I) i ω -
      M.profit I (Function.update (M.linProfile I) i f) i ω =
      ZL M I i ω * (q ω - g ω) + M.b * ((q ω - g ω) * (q ω - g ω)) := by
    intro ω
    rw [profit_update, profit_eq, Yo_lin M hM]
    simp only [hq, hg]; ring
  have hfoc : ∫ ω, ZL M I i ω * (q ω - g ω) ∂M.P = 0 :=
    foc_lin M hM I i (fun p => M.linProfile I i p - f p) ((measurable_lin M I i).sub hfm)
  have hnn : 0 ≤ ∫ ω, M.b * ((q ω - g ω) * (q ω - g ω)) ∂M.P := by
    apply integral_nonneg; intro ω
    have := hM.2.2.1
    exact mul_nonneg this.le (mul_self_nonneg _)
  have : ∫ ω, M.profit I (M.linProfile I) i ω ∂M.P -
      ∫ ω, M.profit I (Function.update (M.linProfile I) i f) i ω ∂M.P ≥ 0 := by
    rw [← integral_sub h2 h1]
    simp_rw [hdiff]
    rw [integral_add h3 h4, hfoc]
    linarith
  linarith

lemma integral_profit_lin (hM : M.Standing) (I : Finset (Fin M.n)) (i : Fin M.n) :
    ∫ ω, M.profit I (M.linProfile I) i ω ∂M.P =
      M.b * (M.A0 ^ 2 + covL M (linL M I i) (linL M I i)) := by
  have hqL : MemLp (fun ω => M.linProfile I i (M.obs I i ω)) 2 M.P := memLp_lin M I i
  have hZL : MemLp (fun ω => ZL M I i ω) 2 M.P := memLp_clm M _
  have hpt : ∀ ω, M.profit I (M.linProfile I) i ω =
      M.b * (M.A0 ^ 2 + 2 * M.A0 * linL M I i ω + linL M I i ω * linL M I i ω) +
        ZL M I i ω * M.linProfile I i (M.obs I i ω) := by
    intro ω
    rw [profit_eq, Yo_lin M hM, lin_obs]; ring
  simp_rw [hpt]
  have hL : MemLp (fun ω => linL M I i ω) 2 M.P := memLp_clm M _
  have hi1 : Integrable (fun ω => linL M I i ω * linL M I i ω) M.P := hL.integrable_mul hL
  have hi2 : Integrable (fun ω => linL M I i ω) M.P := hL.integrable one_le_two
  have hA : Integrable (fun ω => M.b * (M.A0 ^ 2 + 2 * M.A0 * linL M I i ω +
      linL M I i ω * linL M I i ω)) M.P :=
    (((integrable_const _).add (hi2.const_mul _)).add hi1).const_mul _
  have hB : Integrable (fun ω => ZL M I i ω * M.linProfile I i (M.obs I i ω)) M.P :=
    hZL.integrable_mul hqL
  have hC : Integrable (fun ω => M.A0 ^ 2 + 2 * M.A0 * linL M I i ω) M.P :=
    (integrable_const _).add (hi2.const_mul _)
  rw [integral_add hA hB, foc_lin M hM I i _ (measurable_lin M I i),
    integral_const_mul, integral_add hC hi1,
    integral_add (integrable_const _) (hi2.const_mul _), integral_const_mul,
    integral_clm, integral_clm_mul M hM]
  simp

lemma covL_lin (I : Finset (Fin M.n)) (i : Fin M.n) :
    covL M (linL M I i) (linL M I i) =
      if i ∈ I then (M.A1 I.card + M.A2 I.card) ^ 2 * M.α⁻¹ + M.A2 I.card ^ 2 * M.β⁻¹ +
        M.A1 I.card ^ 2 * M.γ⁻¹
      else M.B1 I.card ^ 2 * M.α⁻¹ + M.B1 I.card ^ 2 * M.γ⁻¹ := by
  simp only [covL, Fintype.sum_option, linL_none, linL_h, linL_e, var]
  split_ifs with h <;> simp [h] <;> ring

lemma WJ_lt_WI (hM : M.Standing) (t : ℝ) (ht : 0 ≤ t) : M.WJ t < M.WI t := by
  have hP := Psi_pos M hM t ht
  obtain ⟨_, _, hb, hα, hβ, hγ⟩ := hM
  have key : M.WI t - M.WJ t = 4 * M.β * (4 * M.α ^ 2 + 4 * M.α * M.β + 2 * M.α * M.γ * t +
      6 * M.α * M.γ + 3 * M.β * M.γ + M.γ ^ 2 * t + 2 * M.γ ^ 2) / (M.b * M.Psi t ^ 2) := by
    unfold Model.WI Model.WJ Model.A1 Model.A2 Model.B1 Model.B0
    rw [eq_div_iff (by positivity)]
    field_simp
    unfold Model.Psi
    ring
  have : 0 < M.WI t - M.WJ t := by rw [key]; positivity
  linarith

theorem lemma2 (hM : M.Standing) (I : Finset (Fin M.n)) :
    (∀ i : Fin M.n, i ∈ I →
        (∫ ω, M.profit I (M.linProfile I) i ω ∂M.P) = M.WI (I.card : ℝ)) ∧
      (∀ j : Fin M.n, j ∉ I →
        (∫ ω, M.profit I (M.linProfile I) j ω ∂M.P) = M.WJ (I.card : ℝ)) ∧
      (I.Nonempty → (Finset.univ \ I).Nonempty →
        M.WJ (I.card : ℝ) < M.WI (I.card : ℝ)) := by
  refine ⟨fun i hi => ?_, fun j hj => ?_, fun _ _ => WJ_lt_WI M hM _ (Nat.cast_nonneg _)⟩
  · rw [integral_profit_lin M hM, covL_lin, if_pos hi]
    unfold Model.WI; ring
  · rw [integral_profit_lin M hM, covL_lin, if_neg hj]
    unfold Model.WJ Model.B0; ring

end FarmerAux

open FarmerInfo.Exclusive in
theorem solution (M : Model) (hM : M.Standing) :
    ∀ I : Finset (Fin M.n),
      (∀ i : Fin M.n, i ∈ I →
        (∫ ω, M.profit I (M.linProfile I) i ω ∂M.P) = M.WI (I.card : ℝ)) ∧
      (∀ j : Fin M.n, j ∉ I →
        (∫ ω, M.profit I (M.linProfile I) j ω ∂M.P) = M.WJ (I.card : ℝ)) ∧
      (I.Nonempty → (Finset.univ \ I).Nonempty →
        M.WJ (I.card : ℝ) < M.WI (I.card : ℝ)) :=
  fun I => FarmerAux.lemma2 M hM I
