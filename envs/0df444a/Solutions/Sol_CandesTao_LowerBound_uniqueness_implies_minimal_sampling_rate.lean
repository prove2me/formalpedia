-- Prove2me | solution 1 for CandesTao.LowerBound.uniqueness_implies_minimal_sampling_rate
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T10:44:25.333989+00:00
-- url     : https://prove2.me/submissions/8eddc274-4a61-4e21-b14d-8a380fbd64e0

import Mathlib
import Definitions.Def_CandesTao_LowerBound_Incoherence
import Definitions.Def_CandesTao_LowerBound_SamplingConditions


open scoped BigOperators
open MatrixCompletion CandesTao.LowerBound

namespace CTLowerProof

noncomputable def signedOuter {n : ℕ} (c : ℝ) (b : Fin n → ℝ)
    (J : Finset (Fin n)) : RealMatrix n n :=
  fun i j => c * b i * (if j ∈ J then 1 else 0)

lemma range_outer {n : ℕ} (u v : Fin n → ℝ) (hv : v ≠ 0) :
    LinearMap.range (Matrix.toEuclideanLin (Matrix.vecMulVec u v)) =
      Submodule.span ℝ {WithLp.toLp 2 u} := by
  classical
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨∑ j, v j * x j, ?_⟩
    ext i
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Matrix.vecMulVec, Finset.mul_sum, mul_comm, mul_assoc]
  · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    refine ⟨EuclideanSpace.single j (v j)⁻¹, ?_⟩
    ext i
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.vecMulVec, hj]

lemma singleton_projection_sq {n : ℕ} (v : EuclideanSpace ℝ (Fin n))
    (hv : v ≠ 0) (i : Fin n) :
    ‖(Submodule.span ℝ {v}).starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 =
      v i ^ 2 / ‖v‖ ^ 2 := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [Submodule.starProjection_singleton, EuclideanSpace.inner_single_right]
  simp only [conj_trivial, one_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow]
  change (v i) ^ 2 / (‖v‖ ^ 2) ^ 2 * ‖v‖ ^ 2 = v i ^ 2 / ‖v‖ ^ 2
  field_simp

lemma signed_columnSpace {n : ℕ} (c : ℝ) (b : Fin n → ℝ) (J : Finset (Fin n))
    (hc : c ≠ 0) (hJ : J.Nonempty) :
    columnSpace (signedOuter c b J) = Submodule.span ℝ {WithLp.toLp 2 b} := by
  classical
  have hv : (fun j => if j ∈ J then (1 : ℝ) else 0) ≠ 0 := by
    obtain ⟨j, hj⟩ := hJ
    intro h
    have := congrFun h j
    simp [hj] at this
  change LinearMap.range (Matrix.toEuclideanLin
    (Matrix.vecMulVec (c • b) (fun j => if j ∈ J then 1 else 0))) = _
  rw [range_outer _ _ hv]
  change Submodule.span ℝ {c • WithLp.toLp 2 b} = _
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) _

lemma signed_rowSpace {n : ℕ} (c : ℝ) (b : Fin n → ℝ) (J : Finset (Fin n))
    (hc : c ≠ 0) (hb : b ≠ 0) :
    rowSpace (signedOuter c b J) =
      Submodule.span ℝ {WithLp.toLp 2 (fun j => if j ∈ J then (1 : ℝ) else 0)} := by
  classical
  have hcb : c • b ≠ 0 := smul_ne_zero hc hb
  have heq : (signedOuter c b J).transpose =
      Matrix.vecMulVec (fun j => if j ∈ J then (1 : ℝ) else 0) (c • b) := by
    ext i j
    simp [signedOuter, Matrix.transpose_apply, Matrix.vecMulVec, mul_comm]
  unfold rowSpace
  rw [heq, range_outer _ _ hcb]

lemma signed_outer_incoherent (n r : ℕ) (μ : ℝ) (J : Finset (Fin n))
    (c : ℝ) (b : Fin n → ℝ) (hn : 0 < n) (hr : 1 ≤ r) (hμ : 1 ≤ μ)
    (hcard : (J.card : ℝ) = (n : ℝ) / (μ * r))
    (hc : c ≠ 0) (hb : ∀ i, b i ^ 2 = 1) :
    IncoherentRankAtMost r μ (signedOuter c b J) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmr : 0 < μ * r := mul_pos (by linarith) (by linarith)
  have hJpos : (0 : ℝ) < J.card := by rw [hcard]; positivity
  have hJ : J.Nonempty := Finset.card_pos.mp (by exact_mod_cast hJpos)
  have hb0 : b ≠ 0 := by
    intro h
    have hi := hb ⟨0, hn⟩
    simp [h] at hi
  have hbLp : WithLp.toLp 2 b ≠ (0 : EuclideanSpace ℝ (Fin n)) := by
    intro h
    apply hb0
    exact congrArg WithLp.ofLp h
  have hvLp : WithLp.toLp 2 (fun j => if j ∈ J then (1 : ℝ) else 0) ≠
      (0 : EuclideanSpace ℝ (Fin n)) := by
    obtain ⟨j, hj⟩ := hJ
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x j) h
    simp [hj] at this
  have hbnorm : ‖WithLp.toLp 2 b‖ ^ 2 = (n : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [hb]
  have hvnorm : ‖WithLp.toLp 2 (fun j => if j ∈ J then (1 : ℝ) else 0)‖ ^ 2 =
      (J.card : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp
  have hfrac : 1 / (J.card : ℝ) = μ * r / n := by
    rw [hcard]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · change (Matrix.vecMulVec (c • b) (fun j => if j ∈ J then (1 : ℝ) else 0)).rank ≤ r
    exact (Matrix.rank_vecMulVec_le _ _).trans hr
  · intro i
    simp only [signed_columnSpace c b J hc hJ]
    rw [singleton_projection_sq _ hbLp, hbnorm]
    change b i ^ 2 / n ≤ _
    rw [hb]
    apply div_le_div_of_nonneg_right _ hnR.le
    nlinarith
  · intro j
    simp only [signed_rowSpace c b J hc hb0]
    rw [singleton_projection_sq _ hvLp, hvnorm]
    change (if j ∈ J then (1 : ℝ) else 0) ^ 2 / J.card ≤ _
    split_ifs
    · simpa only [one_pow, hfrac] using le_refl (μ * r / n)
    · simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
      positivity

end CTLowerProof


open scoped BigOperators
open MatrixCompletion CandesTao.LowerBound

namespace CTLowerProof

lemma ambiguous_of_missing_row (n r : ℕ) (μ : ℝ) (J : Finset (Fin n))
    (hn : 0 < n) (hr : 1 ≤ r) (hμ : 1 ≤ μ)
    (hcard : (J.card : ℝ) = (n : ℝ) / (μ * r))
    (Ω : Finset (Fin n × Fin n)) (hmiss : ∃ i, ∀ j ∈ J, (i, j) ∉ Ω) :
    {P : RealMatrix n n × RealMatrix n n |
      P.1 ≠ P.2 ∧ IncoherentRankAtMost r μ P.1 ∧ IncoherentRankAtMost r μ P.2 ∧
        samplingProjection Ω P.1 = samplingProjection Ω P.2}.Infinite := by
  classical
  obtain ⟨a, ha⟩ := hmiss
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmr : 0 < μ * r := mul_pos (by linarith) (by linarith)
  have hJpos : (0 : ℝ) < J.card := by rw [hcard]; positivity
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (by exact_mod_cast hJpos : 0 < J.card)
  let b : Fin n → ℝ := fun i => if i = a then -1 else 1
  let f : ℕ → RealMatrix n n × RealMatrix n n := fun k =>
    (signedOuter ((k : ℝ) + 1) (fun _ => 1) J,
      signedOuter ((k : ℝ) + 1) b J)
  have hinj : Function.Injective f := by
    intro k l h
    have he := congrArg (fun P : RealMatrix n n × RealMatrix n n => P.1 a j) h
    simp only [f, signedOuter, hj, if_true, mul_one] at he
    exact_mod_cast (by linarith : (k : ℝ) = l)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro P ⟨k, rfl⟩
  have hc : (k : ℝ) + 1 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro he
    have he' := congrArg (fun M : RealMatrix n n => M a j) he
    simp only [f, signedOuter, b, hj, if_true, mul_one, mul_neg_one] at he'
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  · exact signed_outer_incoherent n r μ J _ _ hn hr hμ hcard hc (by intro i; norm_num)
  · exact signed_outer_incoherent n r μ J _ _ hn hr hμ hcard hc (by
      intro i
      dsimp [b]
      split_ifs <;> norm_num)
  · ext i l
    by_cases hmem : (i, l) ∈ Ω
    · have hb : i ≠ a ∨ l ∉ J := by
        by_contra! h
        exact ha l h.2 (h.1 ▸ hmem)
      rcases hb with hi | hl
      · simp [samplingProjection, f, signedOuter, b, hmem, hi]
      · simp [samplingProjection, f, signedOuter, hl]
    · simp [samplingProjection, hmem]

end CTLowerProof


set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace CTLowerProof

noncomputable def setWeight {α : Type*} [Fintype α] (p : ℝ) (S : Finset α) : ℝ :=
  p^S.card * (1-p)^(Fintype.card α-S.card)

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem setWeight_prod (p : ℝ) (S : Finset α) :
    setWeight p S = (∏ _i∈S, p) * ∏ _i∈Sᶜ, (1-p) := by
  simp [setWeight, card_compl]

theorem setWeight_sum (p : ℝ) : ∑ S : Finset α, setWeight p S = 1 := by
  simp_rw [setWeight_prod]
  rw [← Fintype.prod_add]
  simp

omit [DecidableEq α] in
theorem setWeight_nonneg {p : ℝ} (hp : 0≤p) (hp1 : p≤1) (S : Finset α) :
    0 ≤ setWeight p S := by unfold setWeight; positivity

noncomputable def rowEquiv (n : ℕ) :
    Finset (Fin n × Fin n) ≃ (Fin n → Finset (Fin n)) where
  toFun Ω i := univ.filter (fun j => (i,j)∈Ω)
  invFun R := univ.filter (fun q => q.2∈R q.1)
  left_inv Ω := by ext q; simp
  right_inv R := by funext i; ext j; simp

@[simp] theorem mem_rowEquiv (n : ℕ) (Ω : Finset (Fin n × Fin n)) (i j : Fin n) :
    j∈rowEquiv n Ω i ↔ (i,j)∈Ω := by simp [rowEquiv]

theorem rowEquiv_card (n : ℕ) (Ω : Finset (Fin n × Fin n)) :
    Ω.card = ∑ i, (rowEquiv n Ω i).card := by
  simp only [rowEquiv, Equiv.coe_fn_mk, Finset.card_filter]
  rw [← Finset.sum_product']
  simp

theorem setWeight_ite (p : ℝ) (S : Finset α) :
    setWeight p S = ∏ a, if a∈S then p else 1-p := by
  rw [setWeight_prod, Finset.prod_ite]
  have hc : univ.filter (fun a : α => a ∉ S) = Sᶜ := by ext a; simp
  simp [hc]

theorem avoid_mass (p : ℝ) (J : Finset α) :
    (∑ S : Finset α, if Disjoint S J then setWeight p S else 0) = (1-p)^J.card := by
  classical
  have hterm (S : Finset α) :
      (∏ a∈S, if a∈J then (0:ℝ) else p) * (∏ _a∈Sᶜ, (1-p)) =
      if Disjoint S J then setWeight p S else 0 := by
    by_cases h : Disjoint S J
    · rw [if_pos h, setWeight_prod]
      congr 1
      apply prod_congr rfl
      intro a ha
      rw [if_neg (fun hj => Finset.disjoint_left.1 h ha hj)]
    · rw [if_neg h]
      obtain ⟨a, ha, hj⟩ := Finset.not_disjoint_iff.1 h
      have hz : (∏ a∈S, if a∈J then (0:ℝ) else p) = 0 := by
        apply prod_eq_zero ha
        simp [hj]
      rw [hz, zero_mul]
  rw [← show (∑ S : Finset α, (∏ a∈S, if a∈J then (0:ℝ) else p) *
      ∏ _a∈Sᶜ, (1-p)) = _ from Finset.sum_congr rfl (fun S _ => hterm S)]
  rw [← Fintype.prod_add]
  have hh (a : α) : (if a∈J then (0:ℝ) else p)+(1-p) = if a∈J then 1-p else 1 := by
    split_ifs <;> ring
  simp_rw [hh]
  rw [Finset.prod_ite]
  simp

theorem row_weight (n : ℕ) (p : ℝ) (Ω : Finset (Fin n×Fin n)) :
    MatrixCompletion.bernoulliObservationWeight p Ω = ∏ i, setWeight p (rowEquiv n Ω i) := by
  change setWeight p Ω = _
  simp_rw [setWeight_ite]
  rw [← Finset.prod_product']
  simp

theorem hit_mass (p : ℝ) (J : Finset α) :
    (∑ S : Finset α, if ¬ Disjoint S J then setWeight p S else 0) = 1-(1-p)^J.card := by
  classical
  have h : (∑ S : Finset α, if Disjoint S J then setWeight p S else 0) +
      (∑ S : Finset α, if ¬ Disjoint S J then setWeight p S else 0) = 1 := by
    rw [← sum_add_distrib]
    convert setWeight_sum (α:=α) p using 1
    apply sum_congr rfl
    intro S _
    by_cases h : Disjoint S J <;> simp [h]
  rw [avoid_mass] at h
  linarith

def MissingRow {n : ℕ} (J : Finset (Fin n)) (Ω : Finset (Fin n×Fin n)) : Prop :=
  ∃ i, ∀ j∈J, (i,j)∉Ω

theorem missing_row_iff (n : ℕ) (J : Finset (Fin n)) (Ω : Finset (Fin n×Fin n)) :
    MissingRow J Ω ↔ ∃ i, Disjoint (rowEquiv n Ω i) J := by
  simp only [MissingRow, Finset.disjoint_left, mem_rowEquiv]
  aesop

theorem all_hit_mass (n : ℕ) (J : Finset (Fin n)) (p : ℝ) :
    (∑ Ω : Finset (Fin n×Fin n), if ¬ MissingRow J Ω then
      MatrixCompletion.bernoulliObservationWeight p Ω else 0) = (1-(1-p)^J.card)^n := by
  classical
  have ht (Ω : Finset (Fin n×Fin n)) :
      (if ¬ MissingRow J Ω then MatrixCompletion.bernoulliObservationWeight p Ω else 0) =
      ∏ i, if ¬ Disjoint (rowEquiv n Ω i) J then setWeight p (rowEquiv n Ω i) else 0 := by
    rw [missing_row_iff]
    by_cases h : ∀ i, ¬ Disjoint (rowEquiv n Ω i) J
    · simpa [not_exists, h] using row_weight n p Ω
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [if_neg (by push Not; exact ⟨i,hi⟩)]
      symm
      exact prod_eq_zero (mem_univ i) (by simp [hi])
  simp_rw [ht]
  rw [Equiv.sum_comp (rowEquiv n) (fun R : Fin n → Finset (Fin n) =>
    ∏ i, if ¬ Disjoint (R i) J then setWeight p (R i) else 0)]
  rw [← Fintype.prod_sum (fun (_i : Fin n) (S : Finset (Fin n)) =>
    if ¬ Disjoint S J then setWeight p S else 0)]
  simp_rw [hit_mass]
  simp

theorem missing_row_probability (n : ℕ) (J : Finset (Fin n)) (p : ℝ) :
    MatrixCompletion.bernoulliEventProb p (MissingRow J) = 1-(1-(1-p)^J.card)^n := by
  classical
  have hh : MatrixCompletion.bernoulliEventProb p (MissingRow J) +
      (∑ Ω : Finset (Fin n×Fin n), if ¬ MissingRow J Ω then
       MatrixCompletion.bernoulliObservationWeight p Ω else 0) = 1 := by
    unfold MatrixCompletion.bernoulliEventProb
    rw [← sum_add_distrib]
    convert setWeight_sum (α:=Fin n×Fin n) p using 1
    apply sum_congr rfl
    intro Ω _
    by_cases h : MissingRow J Ω <;> simp [h, MatrixCompletion.bernoulliObservationWeight, setWeight]
  rw [all_hit_mass] at hh
  linarith

theorem event_mono {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {E F : Finset (Fin n×Fin n) → Prop} (hEF : ∀ Ω, E Ω → F Ω) :
    MatrixCompletion.bernoulliEventProb p E ≤ MatrixCompletion.bernoulliEventProb p F := by
  classical
  unfold MatrixCompletion.bernoulliEventProb
  apply sum_le_sum
  intro Ω _
  have hn : 0 ≤ MatrixCompletion.bernoulliObservationWeight p Ω := setWeight_nonneg hp hp1 Ω
  by_cases he : E Ω
  · simp [he, hEF Ω he]
  · by_cases hf : F Ω <;> simp [he,hf,hn]

end CTLowerProof


set_option autoImplicit false
namespace CTLowerProof
open CandesTao.LowerBound

theorem exp_neg_quadratic (x : ℝ) (hx : 0 ≤ x) : Real.exp (-x) ≤ 1-x+x^2/2 := by
  let f : ℝ → ℝ := fun y => 1-y+y^2/2-Real.exp (-y)
  have hd (y : ℝ) : HasDerivAt f (-1+y+Real.exp (-y)) y := by
    convert! (((hasDerivAt_const y (1:ℝ)).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
      (((hasDerivAt_id y).neg).exp) using 1
    simp
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (fun y _ => (hd y).continuousAt.continuousWithinAt)
    · exact (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
    · intro y hy
      rw [(hd y).deriv]
      linarith [Real.add_one_le_exp (-y)]
  have h := hm (by simp : (0:ℝ) ∈ Set.Ici 0) hx hx
  dsimp [f] at h
  simpa using h

theorem i20_implies_i21 (n m r : ℕ) (μ δ : ℝ) (hn : 0 < n) (hr : 0 < r)
    (hμ : 1 ≤ μ) (hδ : 0 < δ) (hδ' : δ < 1/2)
    (h20 : SamplingConditionI20 n m r μ δ) : SamplingConditionI21 n m r μ δ := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hlog : 0 ≤ Real.log ((n:ℝ)/(2*δ)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by positivity)).2
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hx : 0 ≤ μ*r/n*Real.log ((n:ℝ)/(2*δ)) := by positivity
  have he := exp_neg_quadratic _ hx
  unfold SamplingConditionI20 at h20
  unfold SamplingConditionI21 epsilonI21
  have hid : (1 - 1 / 2 * (μ * r / n) * Real.log (n / (2 * δ))) * μ * n * r *
      Real.log (n / (2 * δ)) = (n:ℝ)^2 *
      (μ*r/n*Real.log (n/(2*δ)) - (μ*r/n*Real.log (n/(2*δ)))^2/2) := by
    field_simp
  rw [hid]
  apply le_trans _ h20
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg (n:ℝ))
  simpa only [neg_mul] using (by linarith [he] :
    μ*r/n*Real.log (n/(2*δ)) - (μ*r/n*Real.log (n/(2*δ)))^2/2 ≤ 1-Real.exp (-(μ*r/n*Real.log (n/(2*δ)))))

theorem sampling_failure_mass (n m r : ℕ) (μ δ : ℝ) (ℓ : ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrn : r ≤ n) (hμ : 1 ≤ μ)
    (hδ : 0 < δ) (hδ' : δ < 1/2) (hℓ : (ℓ:ℝ)=n/(μ*r))
    (hnot : ¬ SamplingConditionI20 n m r μ δ ∨ ¬ SamplingConditionI21 n m r μ δ) :
    0 ≤ (m:ℝ)/(n:ℝ)^2 ∧ (m:ℝ)/(n:ℝ)^2 < 1 ∧
      δ ≤ 1-(1-(1-(m:ℝ)/(n:ℝ)^2)^ℓ)^n := by
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < r) hrn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrR : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hμR : 0 < μ := by linarith
  have hℓR : (0:ℝ) < ℓ := by rw [hℓ]; positivity
  have hℓN : 0 < ℓ := by exact_mod_cast hℓR
  have h20 : ¬ SamplingConditionI20 n m r μ δ := by
    rcases hnot with h | h
    · exact h
    · exact fun z => h (i20_implies_i21 n m r μ δ hn (by omega) hμ hδ hδ' z)
  let p : ℝ := m/(n:ℝ)^2
  let x : ℝ := μ*r/n*Real.log ((n:ℝ)/(2*δ))
  have hmR : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp : p < 1-Real.exp (-x) := by
    unfold SamplingConditionI20 at h20
    dsimp [p,x]
    apply (div_lt_iff₀ (sq_pos_of_pos hnR)).2
    simpa only [neg_mul, mul_comm] using lt_of_not_ge h20
  have hp1 : p < 1 := by linarith [Real.exp_pos (-x)]
  have hxℓ : (ℓ:ℝ)*x = Real.log ((n:ℝ)/(2*δ)) := by
    dsimp [x];rw [hℓ];field_simp
  have hq : 2*δ/n < (1-p)^ℓ := by
    have hh : Real.exp (-x)^ℓ < (1-p)^ℓ :=
      pow_lt_pow_left₀ (by linarith : Real.exp (-x) < 1-p) (Real.exp_nonneg _) (by omega)
    rw [← Real.exp_nat_mul, mul_neg, hxℓ, Real.exp_neg,
      Real.exp_log (by positivity)] at hh
    simpa [one_div, inv_div] using hh
  let q : ℝ := (1-p)^ℓ
  have hq0 : 0 ≤ q := by dsimp [q];positivity
  have hq1 : q ≤ 1 := by dsimp [q];exact pow_le_one₀ (by linarith) (by linarith)
  have hnq : 2*δ < (n:ℝ)*q := by
    have hh := (div_lt_iff₀ hnR).1 hq
    simpa [q,mul_comm] using hh
  have he : (1-q)^n ≤ Real.exp (-(n:ℝ)*q) := by
    have h := Real.one_sub_div_pow_le_exp_neg (n:=n) (t:=(n:ℝ)*q)
      (by nlinarith : (n:ℝ)*q ≤ n)
    simpa [mul_div_cancel_left₀,hnR.ne'] using h
  have he2 : Real.exp (-(n:ℝ)*q) ≤ 1/(1+(n:ℝ)*q) := by
    rw [show -(n:ℝ)*q = -((n:ℝ)*q) by ring,Real.exp_neg,one_div]
    apply (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2
    linarith [Real.add_one_le_exp ((n:ℝ)*q)]
  have hi : 1/(1+(n:ℝ)*q) < 1-δ := by
    apply (div_lt_iff₀ (by positivity)).2
    have hδ1 : 0 < 1-δ := by linarith
    have hmul := mul_lt_mul_of_pos_left hnq hδ1
    nlinarith
  have hlast := lt_of_le_of_lt (he.trans he2) hi
  exact ⟨hp0,hp1,by dsimp [q,p] at hlast;linarith⟩

end CTLowerProof

open MatrixCompletion
namespace CandesTao.LowerBound

theorem uniqueness_implies_minimal_sampling_rate
    (n m r : ℕ) (μ₀ δ : ℝ) (ℓ : ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrn : r ≤ n) (hμ₀ : 1 ≤ μ₀)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hℓ : (ℓ : ℝ) = n / (μ₀ * r))
    (hnot : ¬ SamplingConditionI20 n m r μ₀ δ ∨ ¬ SamplingConditionI21 n m r μ₀ δ) :
    bernoulliEventProb ((m : ℝ) / (n : ℝ) ^ 2)
        (fun Ω : Finset (Fin n × Fin n) =>
          {P : RealMatrix n n × RealMatrix n n |
            P.1 ≠ P.2 ∧ IncoherentRankAtMost r μ₀ P.1 ∧ IncoherentRankAtMost r μ₀ P.2 ∧
              samplingProjection Ω P.1 = samplingProjection Ω P.2}.Infinite) ≥ δ := by
  classical
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < r) hrn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmr : 1 ≤ μ₀ * r := by nlinarith
  have hℓn : ℓ ≤ n := by
    have : (ℓ : ℝ) ≤ n := by
      rw [hℓ]
      exact div_le_self hnR.le hmr
    exact_mod_cast this
  obtain ⟨J, _, hJ⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hℓn)
  have hcard : (J.card : ℝ) = n / (μ₀ * r) := by simpa only [hJ] using hℓ
  obtain ⟨hp, hp1, hmass⟩ := CTLowerProof.sampling_failure_mass n m r μ₀ δ ℓ
    hm hr hrn hμ₀ hδ hδ' hℓ hnot
  have hevent := CTLowerProof.event_mono hp hp1.le (E := CTLowerProof.MissingRow J) (fun Ω hΩ =>
    CTLowerProof.ambiguous_of_missing_row n r μ₀ J hn hr hμ₀ hcard Ω hΩ)
  rw [CTLowerProof.missing_row_probability, hJ] at hevent
  exact hmass.trans hevent

end CandesTao.LowerBound

open CandesTao.LowerBound
theorem solution
    (n m r : ℕ) (μ₀ δ : ℝ) (ℓ : ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrn : r ≤ n) (hμ₀ : 1 ≤ μ₀)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hℓ : (ℓ : ℝ) = n / (μ₀ * r))
    (hnot : ¬ SamplingConditionI20 n m r μ₀ δ ∨ ¬ SamplingConditionI21 n m r μ₀ δ) :
    bernoulliEventProb ((m : ℝ) / (n : ℝ) ^ 2)
        (fun Ω : Finset (Fin n × Fin n) =>
          {P : RealMatrix n n × RealMatrix n n |
            P.1 ≠ P.2 ∧ IncoherentRankAtMost r μ₀ P.1 ∧ IncoherentRankAtMost r μ₀ P.2 ∧
              samplingProjection Ω P.1 = samplingProjection Ω P.2}.Infinite) ≥ δ := CandesTao.LowerBound.uniqueness_implies_minimal_sampling_rate n m r μ₀ δ ℓ hm hr hrn hμ₀ hδ hδ' hℓ hnot

