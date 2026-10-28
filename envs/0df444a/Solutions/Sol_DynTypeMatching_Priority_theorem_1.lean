-- Prove2me | solution 1 for DynTypeMatching.Priority.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T18:35:28.331997+00:00
-- url     : https://prove2.me/submissions/76acd137-fab2-4f4d-a2ec-bb661f197c4e

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model
import Definitions.Def_DynTypeMatching_Priority_Relations

set_option autoImplicit false

namespace DTMPf

open DynTypeMatching.Priority MeasureTheory

variable {m n : ℕ}

def d1 (x x' : Fin m → ℝ) (y y' : Fin n → ℝ) : ℝ :=
  ∑ i, |x i - x' i| + ∑ j, |y j - y' j|

lemma d1_nonneg (x x' : Fin m → ℝ) (y y' : Fin n → ℝ) : 0 ≤ d1 x x' y y' := by
  unfold d1; positivity

lemma d1_comm (x x' : Fin m → ℝ) (y y' : Fin n → ℝ) : d1 x x' y y' = d1 x' x y' y := by
  unfold d1; simp only [abs_sub_comm]

def LipOn (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) (L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ x y x' y', 0 ≤ x → 0 ≤ y → 0 ≤ x' → 0 ≤ y' →
    |f x y - f x' y'| ≤ L * d1 x x' y y'

def cl {k : ℕ} (z : Fin k → ℝ) : Fin k → ℝ := fun i => max (z i) 0

lemma cl_nonneg {k : ℕ} (z : Fin k → ℝ) : 0 ≤ cl z := fun i => le_max_right _ _

lemma cl_of_nonneg {k : ℕ} {z : Fin k → ℝ} (h : 0 ≤ z) : cl z = z := by
  funext i; exact max_eq_left (h i)

lemma sum_abs_le_card_dist {k : ℕ} (z z' : Fin k → ℝ) :
    ∑ i, |z i - z' i| ≤ k * dist z z' := by
  calc ∑ i, |z i - z' i| ≤ ∑ _i : Fin k, dist z z' := by
        apply Finset.sum_le_sum; intro i _
        rw [← Real.dist_eq]; exact dist_le_pi_dist z z' i
    _ = k * dist z z' := by simp

lemma sum_abs_cl_le {k : ℕ} (z z' : Fin k → ℝ) :
    ∑ i, |cl z i - cl z' i| ≤ ∑ i, |z i - z' i| :=
  Finset.sum_le_sum fun i _ => abs_max_sub_max_le_abs _ _ _

def fc (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) (z : (Fin m → ℝ) × (Fin n → ℝ)) : ℝ :=
  f (cl z.1) (cl z.2)

lemma fc_lip {f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ} {L : ℝ} (hf : LipOn f L)
    (z z' : (Fin m → ℝ) × (Fin n → ℝ)) :
    |fc f z - fc f z'| ≤ L * (m + n) * dist z z' := by
  have h1 := hf.2 (cl z.1) (cl z.2) (cl z'.1) (cl z'.2) (cl_nonneg _) (cl_nonneg _)
    (cl_nonneg _) (cl_nonneg _)
  have hd1 : dist z.1 z'.1 ≤ dist z z' := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd2 : dist z.2 z'.2 ≤ dist z z' := by rw [Prod.dist_eq]; exact le_max_right _ _
  have e1 : ∑ i, |cl z.1 i - cl z'.1 i| ≤ m * dist z z' :=
    (sum_abs_cl_le _ _).trans ((sum_abs_le_card_dist _ _).trans
      (mul_le_mul_of_nonneg_left hd1 (Nat.cast_nonneg _)))
  have e2 : ∑ j, |cl z.2 j - cl z'.2 j| ≤ n * dist z z' :=
    (sum_abs_cl_le _ _).trans ((sum_abs_le_card_dist _ _).trans
      (mul_le_mul_of_nonneg_left hd2 (Nat.cast_nonneg _)))
  calc |fc f z - fc f z'| ≤ L * d1 (cl z.1) (cl z'.1) (cl z.2) (cl z'.2) := h1
    _ ≤ L * (m * dist z z' + n * dist z z') :=
        mul_le_mul_of_nonneg_left (add_le_add e1 e2) hf.1
    _ = L * (m + n) * dist z z' := by ring

lemma fc_continuous {f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ} {L : ℝ} (hf : LipOn f L) :
    Continuous (fc f) := by
  have hK : 0 ≤ L * (m + n) := mul_nonneg hf.1 (by positivity)
  refine (LipschitzWith.of_dist_le_mul (K := ⟨L * (m + n), hK⟩) fun z z' => ?_).continuous
  rw [Real.dist_eq]; exact fc_lip hf z z'

lemma int_le_of_ae {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (c : ℝ)
    (h : ∀ᵐ ω ∂μ, f ω ≤ g ω + c) : ∫ ω, f ω ∂μ ≤ ∫ ω, g ω ∂μ + c := by
  have hg' : Integrable (fun ω => g ω + c) μ := hg.add (integrable_const c)
  have h2 := integral_mono_ae hf hg' h
  have h3 : ∫ ω, g ω + c ∂μ = ∫ ω, g ω ∂μ + c := by
    rw [integral_add hg (integrable_const c)]; simp
  linarith

section Arr

variable (μ : Measure ((Fin m → ℝ) × (Fin n → ℝ))) [IsProbabilityMeasure μ]

lemma integrable_fc {f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ} {L : ℝ} (hf : LipOn f L)
    (hint : Integrable (fun ω : (Fin m → ℝ) × (Fin n → ℝ) => ω) μ)
    (z : (Fin m → ℝ) × (Fin n → ℝ)) :
    Integrable (fun ω => fc f (z + ω)) μ := by
  have hc : Continuous (fun ω : (Fin m → ℝ) × (Fin n → ℝ) => fc f (z + ω)) :=
    (fc_continuous hf).comp (by fun_prop)
  refine Integrable.mono' ((integrable_const (|fc f z|)).add
    (hint.norm.const_mul (L * (m + n)))) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have h1 := fc_lip hf (z + ω) z
  have hd : dist (z + ω) z = ‖ω‖ := by rw [dist_eq_norm, add_sub_cancel_left]
  rw [hd] at h1
  have h2 := abs_sub_abs_le_abs_sub (fc f (z + ω)) (fc f z)
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  linarith

/-- the clamped expectation -/
noncomputable def Phi (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) (z : (Fin m → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∫ ω, fc f (z + ω) ∂μ

lemma Phi_continuous {f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ} {L : ℝ} (hf : LipOn f L)
    (hint : Integrable (fun ω : (Fin m → ℝ) × (Fin n → ℝ) => ω) μ) :
    Continuous (Phi μ f) := by
  have hK : 0 ≤ L * (m + n) := mul_nonneg hf.1 (by positivity)
  refine (LipschitzWith.of_dist_le_mul (K := ⟨L * (m + n), hK⟩) fun z z' => ?_).continuous
  rw [Real.dist_eq]
  show |Phi μ f z - Phi μ f z'| ≤ L * (m + n) * dist z z'
  have hp : ∀ a b : (Fin m → ℝ) × (Fin n → ℝ), ∀ ω, fc f (a + ω) ≤ fc f (b + ω) + L * (m + n) * dist a b := by
    intro a b ω
    have := fc_lip hf (a + ω) (b + ω)
    rw [dist_add_right] at this
    linarith [le_abs_self (fc f (a + ω) - fc f (b + ω))]
  have i1 := int_le_of_ae (integrable_fc μ hf hint z) (integrable_fc μ hf hint z') _
    (Filter.Eventually.of_forall (hp z z'))
  have i2 := int_le_of_ae (integrable_fc μ hf hint z') (integrable_fc μ hf hint z) _
    (Filter.Eventually.of_forall (hp z' z))
  rw [dist_comm] at i2
  unfold Phi
  rw [abs_sub_le_iff]; constructor <;> linarith

end Arr

lemma feasible_compact (x : Fin m → ℝ) (y : Fin n → ℝ) :
    IsCompact {Q : Fin m → Fin n → ℝ | Feasible x y Q} := by
  have hcl : IsClosed {Q : Fin m → Fin n → ℝ | Feasible x y Q} := by
    simp only [Feasible, postD, postS, Set.ofPred_and, Set.ofPred_forall]
    refine (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (by fun_prop)).inter
      ((isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop)))
  refine (isCompact_Icc (a := (0 : Fin m → Fin n → ℝ)) (b := fun i _ => x i)).of_isClosed_subset
    hcl ?_
  intro Q hQ
  refine ⟨fun i j => hQ.1 i j, fun i j => ?_⟩
  have h1 := hQ.2.1 i
  simp only [postD] at h1
  have : Q i j ≤ ∑ j', Q i j' := Finset.single_le_sum (fun j' _ => hQ.1 i j') (Finset.mem_univ j)
  show Q i j ≤ x i
  linarith

lemma V_of_lt (M : Model m n) {t : ℕ} (h : M.T < t) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    V M t x y = 0 := by
  rw [V]; simp [h]

lemma V_of_le (M : Model m n) {t : ℕ} (h : t ≤ M.T) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    V M t x y = sSup ((fun Q => H M t Q x y) '' {Q | Feasible x y Q}) := by
  rw [V]; simp [not_lt.mpr h, H]

lemma postD_nonneg {x : Fin m → ℝ} {y : Fin n → ℝ} {Q : Fin m → Fin n → ℝ} (hQ : Feasible x y Q)
    {a : ℝ} (ha : 0 ≤ a) : 0 ≤ a • postD x Q := fun i => by
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; exact mul_nonneg ha (hQ.2.1 i)

lemma postS_nonneg {x : Fin m → ℝ} {y : Fin n → ℝ} {Q : Fin m → Fin n → ℝ} (hQ : Feasible x y Q)
    {a : ℝ} (ha : 0 ≤ a) : 0 ≤ a • postS y Q := fun j => by
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; exact mul_nonneg ha (hQ.2.2 j)

/-- integrand equals clamped version a.e. -/
lemma integrand_ae (M : Model m n) (hM : M.WellPosed) (s : ℕ) (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    {a : Fin m → ℝ} {b : Fin n → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (fun ω : (Fin m → ℝ) × (Fin n → ℝ) => f (a + ω.1) (b + ω.2)) =ᵐ[M.arrival s]
      (fun ω => fc f ((a, b) + ω)) := by
  filter_upwards [hM.arrival_nonneg s] with ω hω
  simp only [fc, Prod.fst_add, Prod.snd_add]
  rw [cl_of_nonneg (add_nonneg ha hω.1), cl_of_nonneg (add_nonneg hb hω.2)]

lemma integrable_V (M : Model m n) (hM : M.WellPosed) (s : ℕ) {f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {L : ℝ} (hf : LipOn f L) {a : Fin m → ℝ} {b : Fin n → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (fun ω : (Fin m → ℝ) × (Fin n → ℝ) => f (a + ω.1) (b + ω.2)) (M.arrival s) := by
  haveI := hM.isProbability s
  exact (integrable_fc (M.arrival s) hf (hM.arrival_integrable s) (a, b)).congr
    (integrand_ae M hM s f ha hb).symm

lemma H_eq_Phi (M : Model m n) (hM : M.WellPosed) (t : ℕ) {x : Fin m → ℝ} {y : Fin n → ℝ}
    {Q : Fin m → Fin n → ℝ} (hQ : Feasible x y Q) :
    H M t Q x y = matchReward M t Q +
      Phi (M.arrival (t + 1)) (V M (t + 1)) (M.α • postD x Q, M.β • postS y Q) := by
  unfold H Phi
  rw [integral_congr_ae (integrand_ae M hM (t + 1) (V M (t + 1))
    (postD_nonneg hQ hM.α_nonneg) (postS_nonneg hQ hM.β_nonneg))]

lemma H_contOn (M : Model m n) (hM : M.WellPosed) (t : ℕ) {L : ℝ} (hL : LipOn (V M (t + 1)) L)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    ContinuousOn (fun Q => H M t Q x y) {Q | Feasible x y Q} := by
  haveI := hM.isProbability (t + 1)
  have hc : Continuous (fun Q : Fin m → Fin n → ℝ => matchReward M t Q +
      Phi (M.arrival (t + 1)) (V M (t + 1)) (M.α • postD x Q, M.β • postS y Q)) := by
    have h1 : Continuous (fun Q : Fin m → Fin n → ℝ => matchReward M t Q) := by
      unfold matchReward; fun_prop
    have h2 : Continuous (fun Q : Fin m → Fin n → ℝ => (M.α • postD x Q, M.β • postS y Q)) := by
      unfold postD postS; fun_prop
    exact h1.add ((Phi_continuous _ hL (hM.arrival_integrable (t + 1))).comp h2)
  exact hc.continuousOn.congr fun Q hQ => H_eq_Phi M hM t hQ

lemma feasible_zero {x : Fin m → ℝ} {y : Fin n → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Feasible x y 0 := by
  refine ⟨fun i j => le_refl _, fun i => ?_, fun j => ?_⟩
  · simp [postD]; exact hx i
  · simp [postS]; exact hy j

lemma exists_opt (M : Model m n) (hM : M.WellPosed) {t : ℕ} (ht : t ≤ M.T) {L : ℝ}
    (hL : LipOn (V M (t + 1)) L) {x : Fin m → ℝ} {y : Fin n → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ Q, IsOptimalDecision M t x y Q ∧ V M t x y = H M t Q x y := by
  obtain ⟨Q, hQ, hmax⟩ := (feasible_compact x y).exists_isMaxOn ⟨0, feasible_zero hx hy⟩
    (H_contOn M hM t hL x y)
  refine ⟨Q, ⟨hQ, fun Q' hQ' => hmax hQ'⟩, ?_⟩
  rw [V_of_le M ht]
  apply IsGreatest.csSup_eq
  refine ⟨⟨Q, hQ, rfl⟩, ?_⟩
  rintro _ ⟨Q', hQ', rfl⟩
  exact hmax hQ'

lemma fut_cmp (M : Model m n) (hM : M.WellPosed) (s : ℕ) {f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {L : ℝ} (hf : LipOn f L) {a a' : Fin m → ℝ} {b b' : Fin n → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') :
    ∫ ω, f (a' + ω.1) (b' + ω.2) ∂M.arrival s ≤
      ∫ ω, f (a + ω.1) (b + ω.2) ∂M.arrival s + L * d1 a a' b b' := by
  have := hM.isProbability s
  refine int_le_of_ae (integrable_V M hM s hf ha' hb') (integrable_V M hM s hf ha hb) _ ?_
  filter_upwards [hM.arrival_nonneg s] with ω hω
  have h := hf.2 (a + ω.1) (b + ω.2) (a' + ω.1) (b' + ω.2) (add_nonneg ha hω.1)
    (add_nonneg hb hω.2) (add_nonneg ha' hω.1) (add_nonneg hb' hω.2)
  have hd : d1 (a + ω.1) (a' + ω.1) (b + ω.2) (b' + ω.2) = d1 a a' b b' := by
    simp [d1, add_sub_add_right_eq_sub]
  rw [hd] at h
  linarith [neg_abs_le (f (a + ω.1) (b + ω.2) - f (a' + ω.1) (b' + ω.2))]

lemma d1_smul {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (u u' : Fin m → ℝ) (v v' : Fin n → ℝ) :
    d1 (a • u) (a • u') (b • v) (b • v') ≤ d1 u u' v v' := by
  unfold d1
  apply add_le_add
  · apply Finset.sum_le_sum; intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_nonneg ha0]
    nlinarith [abs_nonneg (u i - u' i)]
  · apply Finset.sum_le_sum; intro j _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_nonneg hb0]
    nlinarith [abs_nonneg (v j - v' j)]

lemma fac_props {R z : ℝ} (hz : 0 ≤ z) :
    0 ≤ (if R ≤ z then (1:ℝ) else z / R) ∧ (if R ≤ z then (1:ℝ) else z / R) ≤ 1 ∧
    (if R ≤ z then (1:ℝ) else z / R) * R = min R z := by
  split_ifs with h
  · exact ⟨zero_le_one, le_rfl, by rw [one_mul, min_eq_left h]⟩
  · push_neg at h
    have hR : 0 < R := lt_of_le_of_lt hz h
    refine ⟨div_nonneg hz hR.le, (div_le_one hR).2 h.le, ?_⟩
    rw [div_mul_cancel₀ _ hR.ne', min_eq_right h.le]

noncomputable def rs (A : Fin m → Fin n → ℝ) (x : Fin m → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => (if ∑ j', A i j' ≤ x i then (1:ℝ) else x i / ∑ j', A i j') * A i j

noncomputable def cs (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => (if ∑ i', A i' j ≤ y j then (1:ℝ) else y j / ∑ i', A i' j) * A i j

lemma rs_row (A : Fin m → Fin n → ℝ) (x : Fin m → ℝ) (i : Fin m) :
    ∑ j, rs A x i j =
      (if ∑ j', A i j' ≤ x i then (1:ℝ) else x i / ∑ j', A i j') * ∑ j, A i j := by
  simp only [rs]; rw [Finset.mul_sum]

lemma cs_col (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (j : Fin n) :
    ∑ i, cs A y i j =
      (if ∑ i', A i' j ≤ y j then (1:ℝ) else y j / ∑ i', A i' j) * ∑ i, A i j := by
  simp only [cs]; rw [Finset.mul_sum]

lemma scale_feasible {Q' : Fin m → Fin n → ℝ} {x x' : Fin m → ℝ} {y y' : Fin n → ℝ}
    (hQ' : Feasible x' y' Q') (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Feasible x y (cs (rs Q' x) y) ∧ (∀ i j, cs (rs Q' x) y i j ≤ Q' i j) ∧
    ∑ i, ∑ j, (Q' i j - cs (rs Q' x) y i j) ≤ d1 x x' y y' := by
  have f1 := fun i => fac_props (R := ∑ j', Q' i j') (hx i)
  have f2 := fun j => fac_props (R := ∑ i', rs Q' x i' j) (hy j)
  have h1nn : ∀ i j, 0 ≤ rs Q' x i j := fun i j => mul_nonneg (f1 i).1 (hQ'.1 i j)
  have h1le : ∀ i j, rs Q' x i j ≤ Q' i j := fun i j =>
    mul_le_of_le_one_left (hQ'.1 i j) (f1 i).2.1
  have hnn : ∀ i j, 0 ≤ cs (rs Q' x) y i j := fun i j => mul_nonneg (f2 j).1 (h1nn i j)
  have hle : ∀ i j, cs (rs Q' x) y i j ≤ rs Q' x i j := fun i j =>
    mul_le_of_le_one_left (h1nn i j) (f2 j).2.1
  have hrow1 : ∀ i, ∑ j, rs Q' x i j = min (∑ j', Q' i j') (x i) := fun i => by
    rw [rs_row]; exact (f1 i).2.2
  have hcol : ∀ j, ∑ i, cs (rs Q' x) y i j = min (∑ i', rs Q' x i' j) (y j) := fun j => by
    rw [cs_col]; exact (f2 j).2.2
  have hRx' : ∀ i, ∑ j, Q' i j ≤ x' i := fun i => by
    have := hQ'.2.1 i; simp only [postD] at this; linarith
  have hCy' : ∀ j, ∑ i, Q' i j ≤ y' j := fun j => by
    have := hQ'.2.2 j; simp only [postS] at this; linarith
  refine ⟨⟨hnn, fun i => ?_, fun j => ?_⟩, fun i j => (hle i j).trans (h1le i j), ?_⟩
  · simp only [postD]
    have : ∑ j, cs (rs Q' x) y i j ≤ ∑ j, rs Q' x i j := Finset.sum_le_sum fun j _ => hle i j
    have := min_le_right (∑ j', Q' i j') (x i)
    linarith [hrow1 i]
  · simp only [postS]
    have := min_le_right (∑ i', rs Q' x i' j) (y j)
    linarith [hcol j]
  · have e1 : ∑ i, ∑ j, (Q' i j - rs Q' x i j) ≤ ∑ i, |x i - x' i| := by
      apply Finset.sum_le_sum; intro i _
      rw [Finset.sum_sub_distrib, hrow1 i]
      have := hRx' i
      rcases le_total (∑ j', Q' i j') (x i) with h | h
      · rw [min_eq_left h]; simp
      · rw [min_eq_right h, abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
    have e2 : ∑ i, ∑ j, (rs Q' x i j - cs (rs Q' x) y i j) ≤ ∑ j, |y j - y' j| := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum; intro j _
      rw [Finset.sum_sub_distrib, hcol j]
      have : ∑ i, rs Q' x i j ≤ y' j :=
        (Finset.sum_le_sum fun i _ => h1le i j).trans (hCy' j)
      rcases le_total (∑ i', rs Q' x i' j) (y j) with h | h
      · rw [min_eq_left h]; simp
      · rw [min_eq_right h, abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
    have : ∑ i, ∑ j, (Q' i j - cs (rs Q' x) y i j) =
        ∑ i, ∑ j, (Q' i j - rs Q' x i j) + ∑ i, ∑ j, (rs Q' x i j - cs (rs Q' x) y i j) := by
      rw [← Finset.sum_add_distrib]; congr 1; ext i; rw [← Finset.sum_add_distrib]
      congr 1; ext j; ring
    unfold d1; linarith

lemma rsum_le (M : Model m n) (t : ℕ) {Q Q' : Fin m → Fin n → ℝ} (hle : ∀ i j, Q i j ≤ Q' i j) :
    matchReward M t Q' - matchReward M t Q ≤
      (∑ i, ∑ j, |M.r t i j|) * ∑ i, ∑ j, (Q' i j - Q i j) := by
  have key : ∀ i j, M.r t i j * Q' i j - M.r t i j * Q i j ≤
      (∑ i, ∑ j, |M.r t i j|) * (Q' i j - Q i j) := by
    intro i j
    have h1 : |M.r t i j| ≤ ∑ j', |M.r t i j'| :=
      Finset.single_le_sum (f := fun j' => |M.r t i j'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h2 : ∑ j', |M.r t i j'| ≤ ∑ i', ∑ j', |M.r t i' j'| :=
      Finset.single_le_sum (f := fun i' => ∑ j', |M.r t i' j'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h3 := sub_nonneg.2 (hle i j)
    have h4 := le_abs_self (M.r t i j)
    nlinarith
  unfold matchReward
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => key i j

lemma d1_post {x x' : Fin m → ℝ} {y y' : Fin n → ℝ} {Q Q' : Fin m → Fin n → ℝ}
    (hle : ∀ i j, Q i j ≤ Q' i j) :
    d1 (postD x Q) (postD x' Q') (postS y Q) (postS y' Q') ≤
      d1 x x' y y' + 2 * ∑ i, ∑ j, (Q' i j - Q i j) := by
  have h1 : ∀ i, |postD x Q i - postD x' Q' i| ≤ |x i - x' i| + ∑ j, (Q' i j - Q i j) := by
    intro i
    have e : postD x Q i - postD x' Q' i = (x i - x' i) + ∑ j, (Q' i j - Q i j) := by
      simp only [postD, Finset.sum_sub_distrib]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => sub_nonneg.2 (hle i j))]
  have h2 : ∀ j, |postS y Q j - postS y' Q' j| ≤ |y j - y' j| + ∑ i, (Q' i j - Q i j) := by
    intro j
    have e : postS y Q j - postS y' Q' j = (y j - y' j) + ∑ i, (Q' i j - Q i j) := by
      simp only [postS, Finset.sum_sub_distrib]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => sub_nonneg.2 (hle i j))]
  have s1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
  have s2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h2 j
  rw [Finset.sum_add_distrib] at s1 s2
  rw [Finset.sum_comm (f := fun j i => Q' i j - Q i j)] at s2
  unfold d1; linarith

lemma lip_one (M : Model m n) (hM : M.WellPosed) {t : ℕ} (ht : t ≤ M.T) {L : ℝ}
    (hL : LipOn (V M (t + 1)) L) {x x' : Fin m → ℝ} {y y' : Fin n → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hx' : 0 ≤ x') (hy' : 0 ≤ y') :
    V M t x' y' - ((∑ i, ∑ j, |M.r t i j|) + 3 * L) * d1 x x' y y' ≤ V M t x y := by
  obtain ⟨Q', hQ'o, hQ'v⟩ := exists_opt M hM ht hL hx' hy'
  obtain ⟨Q0, hQ0o, hQ0v⟩ := exists_opt M hM ht hL hx hy
  obtain ⟨hF, hle, hE⟩ := scale_feasible (x := x) (y := y) hQ'o.1 hx hy
  have hH := hQ0o.2 _ hF
  rw [← hQ0v] at hH
  have hr := rsum_le M t hle
  have hfut := fut_cmp M hM (t + 1) hL (postD_nonneg hF hM.α_nonneg)
    (postS_nonneg hF hM.β_nonneg) (postD_nonneg hQ'o.1 hM.α_nonneg)
    (postS_nonneg hQ'o.1 hM.β_nonneg)
  have hd := d1_smul hM.α_nonneg hM.α_le_one hM.β_nonneg hM.β_le_one
    (postD x (cs (rs Q' x) y)) (postD x' Q') (postS y (cs (rs Q' x) y)) (postS y' Q')
  have hdu := d1_post (x := x) (x' := x') (y := y) (y' := y') hle
  simp only [H] at hQ'v hH
  have hRm : 0 ≤ ∑ i, ∑ j, |M.r t i j| := by positivity
  have hd0 := d1_nonneg x x' y y'
  have p1 := mul_le_mul_of_nonneg_left hE hRm
  have p2 := mul_le_mul_of_nonneg_left (hd.trans hdu) hL.1
  have p3 := mul_le_mul_of_nonneg_left hE hL.1
  nlinarith

lemma lip_all (M : Model m n) (hM : M.WellPosed) : ∀ t, ∃ L, LipOn (V M t) L := by
  have key : ∀ k t, M.T + 1 - t ≤ k → ∃ L, LipOn (V M t) L := by
    intro k
    induction k with
    | zero =>
      intro t ht
      exact ⟨0, le_rfl, fun x y x' y' _ _ _ _ => by
        rw [V_of_lt M (by omega), V_of_lt M (by omega)]; simp⟩
    | succ k ih =>
      intro t ht
      by_cases h : M.T < t
      · exact ⟨0, le_rfl, fun x y x' y' _ _ _ _ => by rw [V_of_lt M h, V_of_lt M h]; simp⟩
      · push_neg at h
        obtain ⟨L, hL⟩ := ih (t + 1) (by omega)
        refine ⟨(∑ i, ∑ j, |M.r t i j|) + 3 * L,
          add_nonneg (by positivity) (by linarith [hL.1]),
          fun x y x' y' hx hy hx' hy' => ?_⟩
        have a1 := lip_one M hM h hL hx hy hx' hy'
        have a2 := lip_one M hM h hL hx' hy' hx hy
        rw [d1_comm] at a2
        rw [abs_sub_le_iff]; constructor <;> linarith
  intro t; exact key _ t le_rfl

def ev {k : ℕ} (i i' : Fin k) : Fin k → ℝ := Pi.single i' 1 - Pi.single i 1

lemma ev_sum {k : ℕ} (i i' : Fin k) : ∑ a, ev i i' a = 0 := by
  simp [ev, Finset.sum_sub_distrib]

lemma ev_wsum {k : ℕ} (i i' : Fin k) (f : Fin k → ℝ) : ∑ a, f a * ev i i' a = f i' - f i := by
  simp [ev, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

lemma ev_i {k : ℕ} {i i' : Fin k} (h : i ≠ i') : ev i i' i = -1 := by
  simp [ev, Pi.single_apply, h]

lemma ev_i' {k : ℕ} {i i' : Fin k} (h : i ≠ i') : ev i i' i' = 1 := by
  simp [ev, Pi.single_apply, Ne.symm h]

lemma ev_o {k : ℕ} {i i' : Fin k} (a : Fin k) (h1 : a ≠ i) (h2 : a ≠ i') : ev i i' a = 0 := by
  simp [ev, Pi.single_apply, h1, h2]

lemma ev_self {k : ℕ} (i : Fin k) : ev i i = 0 := by simp [ev]

def BndC (M : Model m n) (t : ℕ) (i i' : Fin m) (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ s, t ≤ s → s ≤ M.T → ∀ j, M.α ^ (s - t) * (M.r s i j - M.r s i' j) ≤ c

def BndR (M : Model m n) (t : ℕ) (j j' : Fin n) (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ s, t ≤ s → s ≤ M.T → ∀ i, M.β ^ (s - t) * (M.r s i j - M.r s i j') ≤ c

def ShiftC (M : Model m n) (t : ℕ) : Prop :=
  ∀ (i i' : Fin m) (c : ℝ), BndC M t i i' c → ∀ (x : Fin m → ℝ) (y : Fin n → ℝ), 0 ≤ x → 0 ≤ y →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ x i → V M t x y - δ * c ≤ V M t (x + δ • ev i i') y

def ShiftR (M : Model m n) (t : ℕ) : Prop :=
  ∀ (j j' : Fin n) (c : ℝ), BndR M t j j' c → ∀ (x : Fin m → ℝ) (y : Fin n → ℝ), 0 ≤ x → 0 ≤ y →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ y j → V M t x y - δ * c ≤ V M t x (y + δ • ev j j')

lemma BndC_succ {M : Model m n} {t : ℕ} {i i' : Fin m} {c : ℝ} (h : BndC M t i i' c)
    (hα : 0 < M.α) : BndC M (t + 1) i i' (c / M.α) := by
  refine ⟨div_nonneg h.1 hα.le, fun s hs hsT j => ?_⟩
  rw [le_div_iff₀ hα]
  have h1 := h.2 s (by omega) hsT j
  have e : M.α ^ (s - t) = M.α ^ (s - (t + 1)) * M.α := by
    rw [← pow_succ]; congr 1; omega
  calc M.α ^ (s - (t + 1)) * (M.r s i j - M.r s i' j) * M.α
      = M.α ^ (s - t) * (M.r s i j - M.r s i' j) := by rw [e]; ring
    _ ≤ c := h1

lemma BndR_succ {M : Model m n} {t : ℕ} {j j' : Fin n} {c : ℝ} (h : BndR M t j j' c)
    (hβ : 0 < M.β) : BndR M (t + 1) j j' (c / M.β) := by
  refine ⟨div_nonneg h.1 hβ.le, fun s hs hsT i => ?_⟩
  rw [le_div_iff₀ hβ]
  have h1 := h.2 s (by omega) hsT i
  have e : M.β ^ (s - t) = M.β ^ (s - (t + 1)) * M.β := by
    rw [← pow_succ]; congr 1; omega
  calc M.β ^ (s - (t + 1)) * (M.r s i j - M.r s i j') * M.β
      = M.β ^ (s - t) * (M.r s i j - M.r s i j') := by rw [e]; ring
    _ ≤ c := h1

/-- move part of row `i` to row `i'` -/
def mvC (Q : Fin m → Fin n → ℝ) (i i' : Fin m) (lam : ℝ) : Fin m → Fin n → ℝ :=
  fun a b => Q a b + ev i i' a * ((1 - lam) * Q i b)

/-- move part of column `j` to column `j'` -/
def mvR (Q : Fin m → Fin n → ℝ) (j j' : Fin n) (lam : ℝ) : Fin m → Fin n → ℝ :=
  fun a b => Q a b + ev j j' b * ((1 - lam) * Q a j)

lemma shiftC_step (M : Model m n) (hM : M.WellPosed) {t : ℕ} (ht : t ≤ M.T)
    (IH : ShiftC M (t + 1)) : ShiftC M t := by
  intro i i' c hc x y hx hy δ hδ hδx
  by_cases hii : i = i'
  · subst hii
    rw [ev_self, smul_zero, add_zero]; nlinarith [hc.1]
  obtain ⟨L, hL⟩ := lip_all M hM (t + 1)
  have hxv : ∀ a, (x + δ • ev i i') a = x a + δ * ev i i' a := fun a => by simp
  have hxh0 : 0 ≤ x + δ • ev i i' := by
    intro a; rw [hxv]
    by_cases h1 : a = i
    · subst h1; rw [ev_i hii]; simp only [Pi.zero_apply]; linarith
    · by_cases h2 : a = i'
      · subst h2; rw [ev_i' hii]; have := hx a; simp only [Pi.zero_apply] at this ⊢; linarith
      · rw [ev_o a h1 h2]; simp only [Pi.zero_apply, mul_zero, add_zero]; exact hx a
  obtain ⟨Q, hQo, hQv⟩ := exists_opt M hM ht hL hx hy
  obtain ⟨Q0, hQ0o, hQ0v⟩ := exists_opt M hM ht hL hxh0 hy
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ b, Q i b := ⟨_, rfl⟩
  have fp := fac_props (R := R) (z := x i - δ) (by linarith)
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = (if R ≤ x i - δ then (1:ℝ) else (x i - δ) / R) := ⟨_, rfl⟩
  rw [← hlam] at fp
  obtain ⟨s, hs⟩ : ∃ s, s = R - min R (x i - δ) := ⟨_, rfl⟩
  have hsR : (1 - lam) * R = s := by rw [hs, ← fp.2.2]; ring
  have hRx : R ≤ x i := by have := hQo.1.2.1 i; simp only [postD] at this; linarith
  have hs0 : 0 ≤ s := by rw [hs]; linarith [min_le_left R (x i - δ)]
  have hsδ : s ≤ δ := by
    rw [hs]; rcases le_total R (x i - δ) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hsu : R - (x i - δ) ≤ s := by rw [hs]; linarith [min_le_right R (x i - δ)]
  have hrow : ∀ a, ∑ b, mvC Q i i' lam a b = ∑ b, Q a b + ev i i' a * s := by
    intro a
    simp only [mvC, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← hR, hsR]
  have hcol : ∀ b, ∑ a, mvC Q i i' lam a b = ∑ a, Q a b := by
    intro b
    simp only [mvC, Finset.sum_add_distrib, ← Finset.sum_mul, ev_sum, zero_mul, add_zero]
  have hpD : postD (x + δ • ev i i') (mvC Q i i' lam) = postD x Q + (δ - s) • ev i i' := by
    funext a
    simp only [postD, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hrow]; ring
  have hpS : postS y (mvC Q i i' lam) = postS y Q := by
    funext b; simp only [postS, hcol]
  have hui : δ - s ≤ postD x Q i := by simp only [postD]; rw [← hR]; linarith
  have hFh : Feasible (x + δ • ev i i') y (mvC Q i i' lam) := by
    refine ⟨fun a b => ?_, fun a => ?_, fun b => ?_⟩
    · simp only [mvC]
      have hq := hQo.1.1 a b
      have hqi := hQo.1.1 i b
      by_cases h1 : a = i
      · subst h1; rw [ev_i hii]; nlinarith [fp.1]
      · by_cases h2 : a = i'
        · subst h2; rw [ev_i' hii]; nlinarith [fp.2.1]
        · rw [ev_o a h1 h2]; simpa using hq
    · rw [hpD]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hu := hQo.1.2.1 a
      by_cases h1 : a = i
      · subst h1; rw [ev_i hii]; linarith
      · by_cases h2 : a = i'
        · subst h2; rw [ev_i' hii]; linarith
        · rw [ev_o a h1 h2]; simpa using hu
    · rw [hpS]; exact hQo.1.2.2 b
  -- reward
  have hmr : matchReward M t (mvC Q i i' lam) = matchReward M t Q +
      ∑ b, ((1 - lam) * Q i b) * (M.r t i' b - M.r t i b) := by
    unfold matchReward
    simp only [mvC, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    congr 1; ext b
    have := ev_wsum i i' (fun a => M.r t a b)
    calc ∑ a, M.r t a b * (ev i i' a * ((1 - lam) * Q i b))
        = (∑ a, M.r t a b * ev i i' a) * ((1 - lam) * Q i b) := by
          rw [Finset.sum_mul]; congr 1; ext a; ring
      _ = _ := by rw [this]; ring
  have hw : ∀ b, 0 ≤ (1 - lam) * Q i b := fun b => mul_nonneg (by linarith [fp.2.1]) (hQo.1.1 i b)
  have hcb : ∀ b, M.r t i b - M.r t i' b ≤ c := fun b => by
    have := hc.2 t le_rfl ht b; simpa using this
  have hsum : ∑ b, (1 - lam) * Q i b = s := by rw [← Finset.mul_sum, ← hR, hsR]
  have hmr2 : -(s * c) ≤ ∑ b, ((1 - lam) * Q i b) * (M.r t i' b - M.r t i b) := by
    have h1 : ∑ b, ((1 - lam) * Q i b) * (-c) ≤
        ∑ b, ((1 - lam) * Q i b) * (M.r t i' b - M.r t i b) :=
      Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (by linarith [hcb b]) (hw b)
    rw [← Finset.sum_mul, hsum] at h1; linarith
  -- future
  have iQ := integrable_V M hM (t + 1) hL (postD_nonneg hQo.1 hM.α_nonneg)
    (postS_nonneg hQo.1 hM.β_nonneg)
  have iQh := integrable_V M hM (t + 1) hL (postD_nonneg hFh hM.α_nonneg)
    (postS_nonneg hFh hM.β_nonneg)
  have hg : (fun ω : (Fin m → ℝ) × (Fin n → ℝ) => V M (t + 1)
      (M.α • postD (x + δ • ev i i') (mvC Q i i' lam) + ω.1) (M.β • postS y (mvC Q i i' lam) + ω.2))
      = fun ω => V M (t + 1) ((M.α • postD x Q + ω.1) + (M.α * (δ - s)) • ev i i')
          (M.β • postS y Q + ω.2) := by
    funext ω; rw [hpD, hpS, smul_add, smul_smul]; congr 1; abel
  rw [hg] at iQh
  have := hM.isProbability (t + 1)
  have hint := int_le_of_ae iQ iQh ((δ - s) * c) (by
    filter_upwards [hM.arrival_nonneg (t + 1)] with ω hω
    have hz : 0 ≤ M.α • postD x Q + ω.1 := add_nonneg (postD_nonneg hQo.1 hM.α_nonneg) hω.1
    have hw' : 0 ≤ M.β • postS y Q + ω.2 := add_nonneg (postS_nonneg hQo.1 hM.β_nonneg) hω.2
    by_cases hα : M.α = 0
    · simp only [hα, zero_mul, zero_smul, add_zero, zero_add]; nlinarith [hc.1]
    · have hαp : 0 < M.α := lt_of_le_of_ne hM.α_nonneg (Ne.symm hα)
      have hzi : M.α * (δ - s) ≤ (M.α • postD x Q + ω.1) i := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h0 := hω.1 i; simp only [Pi.zero_apply] at h0
        nlinarith [mul_le_mul_of_nonneg_left hui hαp.le]
      have h1 := IH i i' (c / M.α) (BndC_succ hc hαp) _ _ hz hw' (M.α * (δ - s))
        (mul_nonneg hαp.le (by linarith)) hzi
      have e : M.α * (δ - s) * (c / M.α) = (δ - s) * c := by field_simp
      linarith)
  beta_reduce at hint
  have hH := hQ0o.2 _ hFh
  rw [← hQ0v] at hH
  simp only [H] at hQv hH
  rw [hg, hmr] at hH
  linarith

lemma shiftR_step (M : Model m n) (hM : M.WellPosed) {t : ℕ} (ht : t ≤ M.T)
    (IH : ShiftR M (t + 1)) : ShiftR M t := by
  intro j j' c hc x y hx hy δ hδ hδy
  by_cases hjj : j = j'
  · subst hjj
    rw [ev_self, smul_zero, add_zero]; nlinarith [hc.1]
  obtain ⟨L, hL⟩ := lip_all M hM (t + 1)
  have hyv : ∀ b, (y + δ • ev j j') b = y b + δ * ev j j' b := fun b => by simp
  have hyh0 : 0 ≤ y + δ • ev j j' := by
    intro b; rw [hyv]
    by_cases h1 : b = j
    · subst h1; rw [ev_i hjj]; simp only [Pi.zero_apply]; linarith
    · by_cases h2 : b = j'
      · subst h2; rw [ev_i' hjj]; have := hy b; simp only [Pi.zero_apply] at this ⊢; linarith
      · rw [ev_o b h1 h2]; simp only [Pi.zero_apply, mul_zero, add_zero]; exact hy b
  obtain ⟨Q, hQo, hQv⟩ := exists_opt M hM ht hL hx hy
  obtain ⟨Q0, hQ0o, hQ0v⟩ := exists_opt M hM ht hL hx hyh0
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ a, Q a j := ⟨_, rfl⟩
  have fp := fac_props (R := R) (z := y j - δ) (by linarith)
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = (if R ≤ y j - δ then (1:ℝ) else (y j - δ) / R) := ⟨_, rfl⟩
  rw [← hlam] at fp
  obtain ⟨s, hs⟩ : ∃ s, s = R - min R (y j - δ) := ⟨_, rfl⟩
  have hsR : (1 - lam) * R = s := by rw [hs, ← fp.2.2]; ring
  have hRy : R ≤ y j := by have := hQo.1.2.2 j; simp only [postS] at this; linarith
  have hs0 : 0 ≤ s := by rw [hs]; linarith [min_le_left R (y j - δ)]
  have hsδ : s ≤ δ := by
    rw [hs]; rcases le_total R (y j - δ) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hsu : R - (y j - δ) ≤ s := by rw [hs]; linarith [min_le_right R (y j - δ)]
  have hcol : ∀ b, ∑ a, mvR Q j j' lam a b = ∑ a, Q a b + ev j j' b * s := by
    intro b
    simp only [mvR, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← hR, hsR]
  have hrow : ∀ a, ∑ b, mvR Q j j' lam a b = ∑ b, Q a b := by
    intro a
    simp only [mvR, Finset.sum_add_distrib, ← Finset.sum_mul, ev_sum, zero_mul, add_zero]
  have hpS : postS (y + δ • ev j j') (mvR Q j j' lam) = postS y Q + (δ - s) • ev j j' := by
    funext b
    simp only [postS, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcol]; ring
  have hpD : postD x (mvR Q j j' lam) = postD x Q := by
    funext a; simp only [postD, hrow]
  have hvj : δ - s ≤ postS y Q j := by simp only [postS]; rw [← hR]; linarith
  have hFh : Feasible x (y + δ • ev j j') (mvR Q j j' lam) := by
    refine ⟨fun a b => ?_, fun a => ?_, fun b => ?_⟩
    · simp only [mvR]
      have hq := hQo.1.1 a b
      have hqj := hQo.1.1 a j
      by_cases h1 : b = j
      · subst h1; rw [ev_i hjj]; nlinarith [fp.1]
      · by_cases h2 : b = j'
        · subst h2; rw [ev_i' hjj]; nlinarith [fp.2.1]
        · rw [ev_o b h1 h2]; simpa using hq
    · rw [hpD]; exact hQo.1.2.1 a
    · rw [hpS]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hv := hQo.1.2.2 b
      by_cases h1 : b = j
      · subst h1; rw [ev_i hjj]; linarith
      · by_cases h2 : b = j'
        · subst h2; rw [ev_i' hjj]; linarith
        · rw [ev_o b h1 h2]; simpa using hv
  have hmr : matchReward M t (mvR Q j j' lam) = matchReward M t Q +
      ∑ a, ((1 - lam) * Q a j) * (M.r t a j' - M.r t a j) := by
    unfold matchReward
    simp only [mvR, mul_add, Finset.sum_add_distrib]
    congr 1
    congr 1; ext a
    have := ev_wsum j j' (fun b => M.r t a b)
    calc ∑ b, M.r t a b * (ev j j' b * ((1 - lam) * Q a j))
        = (∑ b, M.r t a b * ev j j' b) * ((1 - lam) * Q a j) := by
          rw [Finset.sum_mul]; congr 1; ext b; ring
      _ = _ := by rw [this]; ring
  have hw : ∀ a, 0 ≤ (1 - lam) * Q a j := fun a => mul_nonneg (by linarith [fp.2.1]) (hQo.1.1 a j)
  have hcb : ∀ a, M.r t a j - M.r t a j' ≤ c := fun a => by
    have := hc.2 t le_rfl ht a; simpa using this
  have hsum : ∑ a, (1 - lam) * Q a j = s := by rw [← Finset.mul_sum, ← hR, hsR]
  have hmr2 : -(s * c) ≤ ∑ a, ((1 - lam) * Q a j) * (M.r t a j' - M.r t a j) := by
    have h1 : ∑ a, ((1 - lam) * Q a j) * (-c) ≤
        ∑ a, ((1 - lam) * Q a j) * (M.r t a j' - M.r t a j) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (by linarith [hcb a]) (hw a)
    rw [← Finset.sum_mul, hsum] at h1; linarith
  have iQ := integrable_V M hM (t + 1) hL (postD_nonneg hQo.1 hM.α_nonneg)
    (postS_nonneg hQo.1 hM.β_nonneg)
  have iQh := integrable_V M hM (t + 1) hL (postD_nonneg hFh hM.α_nonneg)
    (postS_nonneg hFh hM.β_nonneg)
  have hg : (fun ω : (Fin m → ℝ) × (Fin n → ℝ) => V M (t + 1)
      (M.α • postD x (mvR Q j j' lam) + ω.1) (M.β • postS (y + δ • ev j j') (mvR Q j j' lam) + ω.2))
      = fun ω => V M (t + 1) (M.α • postD x Q + ω.1)
          ((M.β • postS y Q + ω.2) + (M.β * (δ - s)) • ev j j') := by
    funext ω; rw [hpD, hpS, smul_add, smul_smul]; congr 1; abel
  rw [hg] at iQh
  have := hM.isProbability (t + 1)
  have hint := int_le_of_ae iQ iQh ((δ - s) * c) (by
    filter_upwards [hM.arrival_nonneg (t + 1)] with ω hω
    have hz : 0 ≤ M.α • postD x Q + ω.1 := add_nonneg (postD_nonneg hQo.1 hM.α_nonneg) hω.1
    have hw' : 0 ≤ M.β • postS y Q + ω.2 := add_nonneg (postS_nonneg hQo.1 hM.β_nonneg) hω.2
    by_cases hβ : M.β = 0
    · simp only [hβ, zero_mul, zero_smul, add_zero, zero_add]; nlinarith [hc.1]
    · have hβp : 0 < M.β := lt_of_le_of_ne hM.β_nonneg (Ne.symm hβ)
      have hzj : M.β * (δ - s) ≤ (M.β • postS y Q + ω.2) j := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h0 := hω.2 j; simp only [Pi.zero_apply] at h0
        nlinarith [mul_le_mul_of_nonneg_left hvj hβp.le]
      have h1 := IH j j' (c / M.β) (BndR_succ hc hβp) _ _ hz hw' (M.β * (δ - s))
        (mul_nonneg hβp.le (by linarith)) hzj
      have e : M.β * (δ - s) * (c / M.β) = (δ - s) * c := by field_simp
      linarith)
  beta_reduce at hint
  have hH := hQ0o.2 _ hFh
  rw [← hQ0v] at hH
  simp only [H] at hQv hH
  rw [hg, hmr] at hH
  linarith

lemma shift_all (M : Model m n) (hM : M.WellPosed) : ∀ t, ShiftC M t ∧ ShiftR M t := by
  have key : ∀ k t, M.T + 1 - t ≤ k → ShiftC M t ∧ ShiftR M t := by
    intro k
    induction k with
    | zero =>
      intro t ht
      refine ⟨fun i i' c hc x y _ _ δ hδ _ => ?_, fun j j' c hc x y _ _ δ hδ _ => ?_⟩
      · rw [V_of_lt M (by omega), V_of_lt M (by omega)]; nlinarith [hc.1]
      · rw [V_of_lt M (by omega), V_of_lt M (by omega)]; nlinarith [hc.1]
    | succ k ih =>
      intro t ht
      by_cases h : M.T < t
      · refine ⟨fun i i' c hc x y _ _ δ hδ _ => ?_, fun j j' c hc x y _ _ δ hδ _ => ?_⟩
        · rw [V_of_lt M h, V_of_lt M h]; nlinarith [hc.1]
        · rw [V_of_lt M h, V_of_lt M h]; nlinarith [hc.1]
      · push_neg at h
        obtain ⟨h1, h2⟩ := ih (t + 1) (by omega)
        exact ⟨shiftC_step M hM h h1, shiftR_step M hM h h2⟩
  intro t; exact key _ t le_rfl

lemma chainC {M : Model m n} {i i' : Fin m} {j : Fin n} (hD : DomCol M i i' j) (hα : 0 ≤ M.α) :
    ∀ d t, 1 ≤ t → t + 1 + d ≤ M.T → ∀ j'', M.α ^ (d + 1) *
      (M.r (t + 1 + d) i j'' - M.r (t + 1 + d) i' j'') ≤ M.r t i j - M.r t i' j := by
  intro d
  induction d with
  | zero => intro t ht1 hT j''; simpa using hD.2.2 t ht1 (by omega) j''
  | succ d ih =>
    intro t ht1 hT j''
    have h1 := ih (t + 1) (by omega) (by omega) j''
    have h2 := hD.2.2 t ht1 (by omega) j
    have e : t + 1 + (d + 1) = t + 1 + 1 + d := by omega
    rw [e, pow_succ]
    calc M.α ^ (d + 1) * M.α * (M.r (t + 1 + 1 + d) i j'' - M.r (t + 1 + 1 + d) i' j'')
        = M.α * (M.α ^ (d + 1) * (M.r (t + 1 + 1 + d) i j'' - M.r (t + 1 + 1 + d) i' j'')) := by
          ring
      _ ≤ M.α * (M.r (t + 1) i j - M.r (t + 1) i' j) := mul_le_mul_of_nonneg_left h1 hα
      _ ≤ _ := h2

lemma chainR {M : Model m n} {i : Fin m} {j j' : Fin n} (hD : DomRow M i j j') (hβ : 0 ≤ M.β) :
    ∀ d t, 1 ≤ t → t + 1 + d ≤ M.T → ∀ i'', M.β ^ (d + 1) *
      (M.r (t + 1 + d) i'' j - M.r (t + 1 + d) i'' j') ≤ M.r t i j - M.r t i j' := by
  intro d
  induction d with
  | zero => intro t ht1 hT i''; simpa using hD.2.2 t ht1 (by omega) i''
  | succ d ih =>
    intro t ht1 hT i''
    have h1 := ih (t + 1) (by omega) (by omega) i''
    have h2 := hD.2.2 t ht1 (by omega) i
    have e : t + 1 + (d + 1) = t + 1 + 1 + d := by omega
    rw [e, pow_succ]
    calc M.β ^ (d + 1) * M.β * (M.r (t + 1 + 1 + d) i'' j - M.r (t + 1 + 1 + d) i'' j')
        = M.β * (M.β ^ (d + 1) * (M.r (t + 1 + 1 + d) i'' j - M.r (t + 1 + 1 + d) i'' j')) := by
          ring
      _ ≤ M.β * (M.r (t + 1) i j - M.r (t + 1) i j') := mul_le_mul_of_nonneg_left h1 hβ
      _ ≤ _ := h2

lemma bndC_of_dom {M : Model m n} (hM : M.WellPosed) {i i' : Fin m} {j : Fin n}
    (hD : DomCol M i i' j) {t : ℕ} (ht1 : 1 ≤ t) (htT : t ≤ M.T) (hα : 0 < M.α) :
    BndC M (t + 1) i i' ((M.r t i j - M.r t i' j) / M.α) := by
  refine ⟨div_nonneg (by linarith [hD.2.1 t ht1 htT]) hα.le, fun s hs hsT j'' => ?_⟩
  rw [le_div_iff₀ hα]
  obtain ⟨d, rfl⟩ : ∃ d, s = t + 1 + d := ⟨s - (t + 1), by omega⟩
  have h := chainC hD hM.α_nonneg d t ht1 hsT j''
  have e : t + 1 + d - (t + 1) = d := by omega
  rw [e]
  calc M.α ^ d * (M.r (t + 1 + d) i j'' - M.r (t + 1 + d) i' j'') * M.α
      = M.α ^ (d + 1) * (M.r (t + 1 + d) i j'' - M.r (t + 1 + d) i' j'') := by ring
    _ ≤ _ := h

lemma bndR_of_dom {M : Model m n} (hM : M.WellPosed) {i : Fin m} {j j' : Fin n}
    (hD : DomRow M i j j') {t : ℕ} (ht1 : 1 ≤ t) (htT : t ≤ M.T) (hβ : 0 < M.β) :
    BndR M (t + 1) j j' ((M.r t i j - M.r t i j') / M.β) := by
  refine ⟨div_nonneg (by linarith [hD.2.1 t ht1 htT]) hβ.le, fun s hs hsT i'' => ?_⟩
  rw [le_div_iff₀ hβ]
  obtain ⟨d, rfl⟩ : ∃ d, s = t + 1 + d := ⟨s - (t + 1), by omega⟩
  have h := chainR hD hM.β_nonneg d t ht1 hsT i''
  have e : t + 1 + d - (t + 1) = d := by omega
  rw [e]
  calc M.β ^ d * (M.r (t + 1 + d) i'' j - M.r (t + 1 + d) i'' j') * M.β
      = M.β ^ (d + 1) * (M.r (t + 1 + d) i'' j - M.r (t + 1 + d) i'' j') := by ring
    _ ≤ _ := h

lemma exp_ineq {a b c d : ℝ} (hc : c < a) (hd : d < a) (h : c + d ≤ a + b) :
    Real.exp c + Real.exp d < Real.exp a + Real.exp b := by
  have hb : Real.exp (c + d - a) ≤ Real.exp b := Real.exp_le_exp.2 (by linarith)
  have e : Real.exp (c + d - a) * Real.exp a = Real.exp c * Real.exp d := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hA := Real.exp_pos a
  have h1 : Real.exp c < Real.exp a := Real.exp_lt_exp.2 hc
  have h2 : Real.exp d < Real.exp a := Real.exp_lt_exp.2 hd
  nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 h2), mul_le_mul_of_nonneg_right hb hA.le]

noncomputable def Psi (M : Model m n) (t : ℕ) (Q : Fin m → Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, Real.exp (M.r t a b) * Q a b

def pert (Q : Fin m → Fin n → ℝ) (ε : ℝ) (p : Fin m → ℝ) (q : Fin n → ℝ) :
    Fin m → Fin n → ℝ := fun a b => Q a b + ε * (p a * q b)

lemma wsum_pert (w Q : Fin m → Fin n → ℝ) (ε : ℝ) (p : Fin m → ℝ) (q : Fin n → ℝ) :
    ∑ a, ∑ b, w a b * pert Q ε p q a b =
      ∑ a, ∑ b, w a b * Q a b + ε * ∑ a, p a * ∑ b, w a b * q b := by
  simp only [pert, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring

lemma row_pert (Q : Fin m → Fin n → ℝ) (ε : ℝ) (p : Fin m → ℝ) (q : Fin n → ℝ) (a : Fin m) :
    ∑ b, pert Q ε p q a b = ∑ b, Q a b + ε * p a * ∑ b, q b := by
  simp only [pert]; rw [Finset.sum_add_distrib]; congr 1
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring

lemma col_pert (Q : Fin m → Fin n → ℝ) (ε : ℝ) (p : Fin m → ℝ) (q : Fin n → ℝ) (b : Fin n) :
    ∑ a, pert Q ε p q a b = ∑ a, Q a b + ε * q b * ∑ a, p a := by
  simp only [pert]; rw [Finset.sum_add_distrib]; congr 1
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring

lemma ev_cases {k : ℕ} {i i' : Fin k} (h : i ≠ i') (a : Fin k) :
    (a = i' ∧ ev i i' a = 1) ∨ (a = i ∧ ev i i' a = -1) ∨ ev i i' a = 0 := by
  by_cases h1 : a = i
  · subst h1; exact Or.inr (Or.inl ⟨rfl, ev_i h⟩)
  · by_cases h2 : a = i'
    · subst h2; exact Or.inl ⟨rfl, ev_i' h⟩
    · exact Or.inr (Or.inr (ev_o a h1 h2))

lemma single_cases {k : ℕ} (j b : Fin k) :
    (b = j ∧ (Pi.single j (1:ℝ) : Fin k → ℝ) b = 1) ∨ (Pi.single j (1:ℝ) : Fin k → ℝ) b = 0 := by
  by_cases h : b = j
  · subst h; left; simp
  · right; simp [Pi.single_apply, h]

lemma sum_single {k : ℕ} (j : Fin k) : ∑ b, (Pi.single j (1:ℝ) : Fin k → ℝ) b = 1 := by simp

lemma wsum_single {k : ℕ} (j : Fin k) (f : Fin k → ℝ) :
    ∑ b, f b * (Pi.single j (1:ℝ) : Fin k → ℝ) b = f j := by
  simp [Pi.single_apply]

lemma ev_swap {k : ℕ} (i i' : Fin k) (a : Fin k) : ev i' i a = - ev i i' a := by
  simp only [ev, Pi.sub_apply]; ring

/-- the improvement setting at period `t` and state `(x, y)`. -/
structure Setting (M : Model m n) (t : ℕ) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (Qo : Fin m → Fin n → ℝ) : Prop where
  ht1 : 1 ≤ t
  htT : t ≤ M.T
  hF : Feasible x y Qo
  himp : ∀ Q', Feasible x y Q' → H M t Qo x y ≤ H M t Q' x y → Psi M t Q' ≤ Psi M t Qo

lemma caseB (M : Model m n) (hMonge : MongeCondition M) {t : ℕ} {x : Fin m → ℝ}
    {y : Fin n → ℝ} {Qo : Fin m → Fin n → ℝ} (S : Setting M t x y Qo)
    {i i' : Fin m} {j j'' : Fin n} (hDC : DomCol M i i' j) (hDR : DomRow M i j j'')
    (h1 : 0 < Qo i' j) (h2 : 0 < Qo i j'') : False := by
  have hii : i' ≠ i := hDC.1
  have hjj : j'' ≠ j := hDR.1
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min (Qo i' j) (Qo i j'') := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min h1 h2
  have hε1 : ε ≤ Qo i' j := by rw [hε]; exact min_le_left _ _
  have hε2 : ε ≤ Qo i j'' := by rw [hε]; exact min_le_right _ _
  have hrow : ∀ a, ∑ b, pert Qo ε (ev i' i) (ev j'' j) a b = ∑ b, Qo a b := by
    intro a; rw [row_pert, ev_sum]; ring
  have hcol : ∀ b, ∑ a, pert Qo ε (ev i' i) (ev j'' j) a b = ∑ a, Qo a b := by
    intro b; rw [col_pert, ev_sum]; ring
  have hpD : postD x (pert Qo ε (ev i' i) (ev j'' j)) = postD x Qo := by
    funext a; simp only [postD, hrow]
  have hpS : postS y (pert Qo ε (ev i' i) (ev j'' j)) = postS y Qo := by
    funext b; simp only [postS, hcol]
  have hF' : Feasible x y (pert Qo ε (ev i' i) (ev j'' j)) := by
    refine ⟨fun a b => ?_, fun a => by rw [hpD]; exact S.hF.2.1 a,
      fun b => by rw [hpS]; exact S.hF.2.2 b⟩
    have hq := S.hF.1 a b
    simp only [pert]
    rcases ev_cases hii a with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha <;>
      rcases ev_cases hjj b with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | hb <;>
      rw [ha, hb] <;> nlinarith
  have hsum : ∀ w : Fin m → Fin n → ℝ, ∑ a, ∑ b, w a b * pert Qo ε (ev i' i) (ev j'' j) a b =
      ∑ a, ∑ b, w a b * Qo a b + ε * ((w i j - w i j'') - (w i' j - w i' j'')) := by
    intro w
    rw [wsum_pert]
    congr 2
    have : ∀ a, ev i' i a * ∑ b, w a b * ev j'' j b = (w a j - w a j'') * ev i' i a := by
      intro a; rw [ev_wsum]; ring
    simp only [this]
    rw [ev_wsum]
  have hmono := hMonge i i' j j'' hDC hDR t S.ht1 S.htT
  have hH : H M t Qo x y ≤ H M t (pert Qo ε (ev i' i) (ev j'' j)) x y := by
    simp only [H, hpD, hpS, matchReward]
    rw [hsum (M.r t)]
    nlinarith
  have hP := S.himp _ hF' hH
  simp only [Psi] at hP
  rw [hsum (fun a b => Real.exp (M.r t a b))] at hP
  have := exp_ineq (b := M.r t i' j'') (hDR.2.1 t S.ht1 S.htT) (hDC.2.1 t S.ht1 S.htT)
    (by linarith)
  nlinarith [mul_pos hε0 (sub_pos.2 this)]

lemma caseA (M : Model m n) (hM : M.WellPosed) {t : ℕ} {x : Fin m → ℝ}
    {y : Fin n → ℝ} {Qo : Fin m → Fin n → ℝ} (S : Setting M t x y Qo)
    (hSC : ShiftC M (t + 1)) {L : ℝ} (hL : LipOn (V M (t + 1)) L)
    {i i' : Fin m} {j : Fin n} (hDC : DomCol M i i' j)
    (h1 : 0 < Qo i' j) (h2 : 0 < postD x Qo i) : False := by
  have hii : i' ≠ i := hDC.1
  have hii' : i ≠ i' := fun h => hii h.symm
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min (Qo i' j) (postD x Qo i) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min h1 h2
  have hε1 : ε ≤ Qo i' j := by rw [hε]; exact min_le_left _ _
  have hε2 : ε ≤ postD x Qo i := by rw [hε]; exact min_le_right _ _
  have hpD : postD x (pert Qo ε (ev i' i) (Pi.single j 1)) = postD x Qo + ε • ev i i' := by
    funext a
    simp only [postD, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [row_pert, sum_single, ev_swap i i' a]; ring
  have hpS : postS y (pert Qo ε (ev i' i) (Pi.single j 1)) = postS y Qo := by
    funext b; simp only [postS]; rw [col_pert, ev_sum]; ring
  have hF' : Feasible x y (pert Qo ε (ev i' i) (Pi.single j 1)) := by
    refine ⟨fun a b => ?_, fun a => ?_, fun b => by rw [hpS]; exact S.hF.2.2 b⟩
    · have hq := S.hF.1 a b
      simp only [pert]
      rcases ev_cases hii a with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha <;>
        rcases single_cases j b with ⟨rfl, hb⟩ | hb <;>
        rw [ha, hb] <;> nlinarith
    · rw [hpD]
      have hu := S.hF.2.1 a
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases ev_cases hii' a with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha <;> rw [ha] <;> nlinarith
  have hsum : ∀ w : Fin m → Fin n → ℝ,
      ∑ a, ∑ b, w a b * pert Qo ε (ev i' i) (Pi.single j 1) a b =
      ∑ a, ∑ b, w a b * Qo a b + ε * (w i j - w i' j) := by
    intro w
    rw [wsum_pert]
    congr 2
    simp only [wsum_single]
    have : ∀ a, ev i' i a * w a j = w a j * ev i' i a := fun a => by ring
    simp only [this]
    rw [ev_wsum]
  have hD : 0 < M.r t i j - M.r t i' j := by linarith [hDC.2.1 t S.ht1 S.htT]
  have iQ := integrable_V M hM (t + 1) hL (postD_nonneg S.hF hM.α_nonneg)
    (postS_nonneg S.hF hM.β_nonneg)
  have iQt := integrable_V M hM (t + 1) hL (postD_nonneg hF' hM.α_nonneg)
    (postS_nonneg hF' hM.β_nonneg)
  have hg : (fun ω : (Fin m → ℝ) × (Fin n → ℝ) => V M (t + 1)
      (M.α • postD x (pert Qo ε (ev i' i) (Pi.single j 1)) + ω.1)
      (M.β • postS y (pert Qo ε (ev i' i) (Pi.single j 1)) + ω.2))
      = fun ω => V M (t + 1) ((M.α • postD x Qo + ω.1) + (M.α * ε) • ev i i')
          (M.β • postS y Qo + ω.2) := by
    funext ω; rw [hpD, hpS, smul_add, smul_smul]; congr 1; abel
  rw [hg] at iQt
  have := hM.isProbability (t + 1)
  have hint := int_le_of_ae iQ iQt (ε * (M.r t i j - M.r t i' j)) (by
    filter_upwards [hM.arrival_nonneg (t + 1)] with ω hω
    have hz : 0 ≤ M.α • postD x Qo + ω.1 := add_nonneg (postD_nonneg S.hF hM.α_nonneg) hω.1
    have hw' : 0 ≤ M.β • postS y Qo + ω.2 := add_nonneg (postS_nonneg S.hF hM.β_nonneg) hω.2
    by_cases hα : M.α = 0
    · simp only [hα, zero_mul, zero_smul, add_zero, zero_add]; nlinarith [mul_pos hε0 hD]
    · have hαp : 0 < M.α := lt_of_le_of_ne hM.α_nonneg (Ne.symm hα)
      have hzi : M.α * ε ≤ (M.α • postD x Qo + ω.1) i := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h0 := hω.1 i; simp only [Pi.zero_apply] at h0
        nlinarith [mul_le_mul_of_nonneg_left hε2 hαp.le]
      have h1 := hSC i i' _ (bndC_of_dom hM hDC S.ht1 S.htT hαp) _ _ hz hw' (M.α * ε)
        (by positivity) hzi
      have e : M.α * ε * ((M.r t i j - M.r t i' j) / M.α) = ε * (M.r t i j - M.r t i' j) := by
        field_simp
      linarith)
  beta_reduce at hint
  have hH : H M t Qo x y ≤ H M t (pert Qo ε (ev i' i) (Pi.single j 1)) x y := by
    simp only [H]
    rw [hg]
    unfold matchReward
    rw [hsum (M.r t)]
    linarith
  have hP := S.himp _ hF' hH
  simp only [Psi] at hP
  rw [hsum (fun a b => Real.exp (M.r t a b))] at hP
  have := Real.exp_lt_exp.2 (hDC.2.1 t S.ht1 S.htT)
  nlinarith [mul_pos hε0 (sub_pos.2 this)]

lemma caseA' (M : Model m n) (hM : M.WellPosed) {t : ℕ} {x : Fin m → ℝ}
    {y : Fin n → ℝ} {Qo : Fin m → Fin n → ℝ} (S : Setting M t x y Qo)
    (hSR : ShiftR M (t + 1)) {L : ℝ} (hL : LipOn (V M (t + 1)) L)
    {i : Fin m} {j j' : Fin n} (hDR : DomRow M i j j')
    (h1 : 0 < Qo i j') (h2 : 0 < postS y Qo j) : False := by
  have hjj : j' ≠ j := hDR.1
  have hjj' : j ≠ j' := fun h => hjj h.symm
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min (Qo i j') (postS y Qo j) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min h1 h2
  have hε1 : ε ≤ Qo i j' := by rw [hε]; exact min_le_left _ _
  have hε2 : ε ≤ postS y Qo j := by rw [hε]; exact min_le_right _ _
  have hpS : postS y (pert Qo ε (Pi.single i 1) (ev j' j)) = postS y Qo + ε • ev j j' := by
    funext b
    simp only [postS, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [col_pert, sum_single, ev_swap j j' b]; ring
  have hpD : postD x (pert Qo ε (Pi.single i 1) (ev j' j)) = postD x Qo := by
    funext a; simp only [postD]; rw [row_pert, ev_sum]; ring
  have hF' : Feasible x y (pert Qo ε (Pi.single i 1) (ev j' j)) := by
    refine ⟨fun a b => ?_, fun a => by rw [hpD]; exact S.hF.2.1 a, fun b => ?_⟩
    · have hq := S.hF.1 a b
      simp only [pert]
      rcases single_cases i a with ⟨rfl, ha⟩ | ha <;>
        rcases ev_cases hjj b with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | hb <;>
        rw [ha, hb] <;> nlinarith
    · rw [hpS]
      have hv := S.hF.2.2 b
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases ev_cases hjj' b with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | hb <;> rw [hb] <;> nlinarith
  have hsum : ∀ w : Fin m → Fin n → ℝ,
      ∑ a, ∑ b, w a b * pert Qo ε (Pi.single i 1) (ev j' j) a b =
      ∑ a, ∑ b, w a b * Qo a b + ε * (w i j - w i j') := by
    intro w
    rw [wsum_pert]
    congr 2
    simp only [ev_wsum]
    have : ∀ a, (Pi.single i (1:ℝ) : Fin m → ℝ) a * (w a j - w a j') =
        (w a j - w a j') * (Pi.single i (1:ℝ) : Fin m → ℝ) a := fun a => by ring
    simp only [this]
    rw [wsum_single]
  have hD : 0 < M.r t i j - M.r t i j' := by linarith [hDR.2.1 t S.ht1 S.htT]
  have iQ := integrable_V M hM (t + 1) hL (postD_nonneg S.hF hM.α_nonneg)
    (postS_nonneg S.hF hM.β_nonneg)
  have iQt := integrable_V M hM (t + 1) hL (postD_nonneg hF' hM.α_nonneg)
    (postS_nonneg hF' hM.β_nonneg)
  have hg : (fun ω : (Fin m → ℝ) × (Fin n → ℝ) => V M (t + 1)
      (M.α • postD x (pert Qo ε (Pi.single i 1) (ev j' j)) + ω.1)
      (M.β • postS y (pert Qo ε (Pi.single i 1) (ev j' j)) + ω.2))
      = fun ω => V M (t + 1) (M.α • postD x Qo + ω.1)
          ((M.β • postS y Qo + ω.2) + (M.β * ε) • ev j j') := by
    funext ω; rw [hpD, hpS, smul_add, smul_smul]; congr 1; abel
  rw [hg] at iQt
  have := hM.isProbability (t + 1)
  have hint := int_le_of_ae iQ iQt (ε * (M.r t i j - M.r t i j')) (by
    filter_upwards [hM.arrival_nonneg (t + 1)] with ω hω
    have hz : 0 ≤ M.α • postD x Qo + ω.1 := add_nonneg (postD_nonneg S.hF hM.α_nonneg) hω.1
    have hw' : 0 ≤ M.β • postS y Qo + ω.2 := add_nonneg (postS_nonneg S.hF hM.β_nonneg) hω.2
    by_cases hβ : M.β = 0
    · simp only [hβ, zero_mul, zero_smul, add_zero, zero_add]; nlinarith [mul_pos hε0 hD]
    · have hβp : 0 < M.β := lt_of_le_of_ne hM.β_nonneg (Ne.symm hβ)
      have hzj : M.β * ε ≤ (M.β • postS y Qo + ω.2) j := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h0 := hω.2 j; simp only [Pi.zero_apply] at h0
        nlinarith [mul_le_mul_of_nonneg_left hε2 hβp.le]
      have h1 := hSR j j' _ (bndR_of_dom hM hDR S.ht1 S.htT hβp) _ _ hz hw' (M.β * ε)
        (by positivity) hzj
      have e : M.β * ε * ((M.r t i j - M.r t i j') / M.β) = ε * (M.r t i j - M.r t i j') := by
        field_simp
      linarith)
  beta_reduce at hint
  have hH : H M t Qo x y ≤ H M t (pert Qo ε (Pi.single i 1) (ev j' j)) x y := by
    simp only [H]
    rw [hg]
    unfold matchReward
    rw [hsum (M.r t)]
    linarith
  have hP := S.himp _ hF' hH
  simp only [Psi] at hP
  rw [hsum (fun a b => Real.exp (M.r t a b))] at hP
  have := Real.exp_lt_exp.2 (hDR.2.1 t S.ht1 S.htT)
  nlinarith [mul_pos hε0 (sub_pos.2 this)]

open Classical in
lemma resD_eq (M : Model m n) (x : Fin m → ℝ) (Q : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    resD M x Q i j = postD x Q i +
      ∑ j'' ∈ Finset.univ.filter (fun j'' => DomRow M i j j''), Q i j'' := by
  unfold resD postD
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j'' => DomRow M i j j'')
    (fun j'' => Q i j'')]
  ring

open Classical in
lemma resS_eq (M : Model m n) (y : Fin n → ℝ) (Q : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    resS M y Q i j = postS y Q j +
      ∑ i'' ∈ Finset.univ.filter (fun i'' => DomCol M i i'' j), Q i'' j := by
  unfold resS postS
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i'' => DomCol M i i'' j)
    (fun i'' => Q i'' j)]
  ring

lemma exists_resp (M : Model m n) (hM : M.WellPosed) (hMonge : MongeCondition M) {t : ℕ}
    (ht1 : 1 ≤ t) (htT : t ≤ M.T) {x : Fin m → ℝ} {y : Fin n → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ Q, IsOptimalDecision M t x y Q ∧ Respects M x y Q := by
  classical
  obtain ⟨L, hL⟩ := lip_all M hM (t + 1)
  obtain ⟨hSC, hSR⟩ := shift_all M hM (t + 1)
  obtain ⟨Qs, hQs, -⟩ := exists_opt M hM htT hL hx hy
  have hOc : IsCompact ({Q : Fin m → Fin n → ℝ | Feasible x y Q} ∩
      (fun Q => H M t Q x y) ⁻¹' {H M t Qs x y}) :=
    (feasible_compact x y).of_isClosed_subset
      ((H_contOn M hM t hL x y).preimage_isClosed_of_isClosed (feasible_compact x y).isClosed
        isClosed_singleton) Set.inter_subset_left
  have hΨ : Continuous (fun Q : Fin m → Fin n → ℝ => Psi M t Q) := by
    unfold Psi; fun_prop
  obtain ⟨Qo, hQoO, hmax⟩ := hOc.exists_isMaxOn ⟨Qs, hQs.1, rfl⟩ hΨ.continuousOn
  have hQoF : Feasible x y Qo := hQoO.1
  have hQoH : H M t Qo x y = H M t Qs x y := hQoO.2
  have S : Setting M t x y Qo := ⟨ht1, htT, hQoF, fun Q' hQ' hle =>
    hmax ⟨hQ', le_antisymm (hQs.2 Q' hQ') (hQoH ▸ hle)⟩⟩
  refine ⟨Qo, ⟨hQoF, fun Q' hQ' => hQoH ▸ hQs.2 Q' hQ'⟩, ?_, ?_⟩
  · intro i i' j hDC
    by_contra hcon
    push_neg at hcon
    have h1 : 0 < Qo i' j := lt_of_le_of_ne (hQoF.1 i' j) (Ne.symm hcon.1)
    by_cases hu : 0 < postD x Qo i
    · exact caseA M hM S hSC hL hDC h1 hu
    · have hu0 : postD x Qo i = 0 := le_antisymm (not_lt.1 hu) (hQoF.2.1 i)
      have hS := hcon.2
      rw [resD_eq, hu0, zero_add] at hS
      obtain ⟨j'', hj'', hpos⟩ : ∃ j'' ∈ Finset.univ.filter (fun j'' => DomRow M i j j''),
          0 < Qo i j'' := by
        by_contra hno
        push_neg at hno
        exact hS (le_antisymm (Finset.sum_nonpos hno)
          (Finset.sum_nonneg fun j'' _ => hQoF.1 i j''))
      rw [Finset.mem_filter] at hj''
      exact caseB M hMonge S hDC hj''.2 h1 hpos
  · intro i j j' hDR
    by_contra hcon
    push_neg at hcon
    have h1 : 0 < Qo i j' := lt_of_le_of_ne (hQoF.1 i j') (Ne.symm hcon.1)
    by_cases hv : 0 < postS y Qo j
    · exact caseA' M hM S hSR hL hDR h1 hv
    · have hv0 : postS y Qo j = 0 := le_antisymm (not_lt.1 hv) (hQoF.2.2 j)
      have hS := hcon.2
      rw [resS_eq, hv0, zero_add] at hS
      obtain ⟨i'', hi'', hpos⟩ : ∃ i'' ∈ Finset.univ.filter (fun i'' => DomCol M i i'' j),
          0 < Qo i'' j := by
        by_contra hno
        push_neg at hno
        exact hS (le_antisymm (Finset.sum_nonpos hno)
          (Finset.sum_nonneg fun i'' _ => hQoF.1 i'' j))
      rw [Finset.mem_filter] at hi''
      exact caseB M hMonge S hi''.2 hDR hpos h1

end DTMPf

open DynTypeMatching.Priority in
theorem solution {m n : ℕ} (M : Model m n) (hM : M.WellPosed) (hMonge : MongeCondition M) :
    ∃ P : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → (Fin m → Fin n → ℝ),
      IsOptimalPolicy M P ∧
        ∀ t, 1 ≤ t → t ≤ M.T → ∀ (x : Fin m → ℝ) (y : Fin n → ℝ), 0 ≤ x → 0 ≤ y →
          Respects M x y (P t x y) := by
  have key : ∀ (t : ℕ) (x : Fin m → ℝ) (y : Fin n → ℝ), ∃ Q : Fin m → Fin n → ℝ,
      1 ≤ t → t ≤ M.T → 0 ≤ x → 0 ≤ y → IsOptimalDecision M t x y Q ∧ Respects M x y Q := by
    intro t x y
    by_cases h : 1 ≤ t ∧ t ≤ M.T ∧ 0 ≤ x ∧ 0 ≤ y
    · obtain ⟨Q, hQ⟩ := DTMPf.exists_resp M hM hMonge h.1 h.2.1 h.2.2.1 h.2.2.2
      exact ⟨Q, fun _ _ _ _ => hQ⟩
    · exact ⟨0, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩
  choose P hP using key
  exact ⟨P, fun t h1 h2 x y hx hy => (hP t x y h1 h2 hx hy).1,
    fun t h1 h2 x y hx hy => (hP t x y h1 h2 hx hy).2⟩
