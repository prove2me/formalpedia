-- Prove2me | solution 1 for CompressedOracleDuality.LabelSymmetric.equation_27
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:46:41.773817+00:00
-- url     : https://prove2.me/submissions/cd116426-c827-480e-af24-982384c9f8bf

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database
import Theorems.Thm_CompressedOracleDuality_LabelSymmetric_equation_24

-- ===== from Solutions/COD/MI.lean =====

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace CODInfo

lemma jensen_log {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (h1 : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * Real.log (x i) ≤ Real.log (∑ i ∈ s, w i * x i) := by
  have := strictConcaveOn_log_Ioi.concaveOn.le_map_sum hw h1 (fun i hi => Set.mem_Ioi.2 (hx i hi))
  simpa [smul_eq_mul] using this

variable {α β : Type*} [Fintype α] [Fintype β]

def pa (P : α × β → ℝ) (a : α) : ℝ := ∑ b', P (a, b')
def qb (P : α × β → ℝ) (b : β) : ℝ := ∑ a', P (a', b)

lemma mi_eq (P : α × β → ℝ) :
    mutualInfoBits P = ∑ x : α × β, P x * Real.logb 2 (P x / (pa P x.1 * qb P x.2)) := by
  rw [mutualInfoBits, ← Fintype.sum_prod_type']; rfl

lemma pa_pos (P : α × β → ℝ) (hP : ∀ x, 0 ≤ P x) (x : α × β) (hx : P x ≠ 0) : 0 < pa P x.1 := by
  have : P x ≤ pa P x.1 := by
    unfold pa; exact Finset.single_le_sum (f := fun b' => P (x.1, b')) (fun b' _ => hP _)
      (Finset.mem_univ x.2)
  exact lt_of_lt_of_le (lt_of_le_of_ne (hP x) (Ne.symm hx)) this

lemma qb_pos (P : α × β → ℝ) (hP : ∀ x, 0 ≤ P x) (x : α × β) (hx : P x ≠ 0) : 0 < qb P x.2 := by
  have : P x ≤ qb P x.2 := by
    unfold qb; exact Finset.single_le_sum (f := fun a' => P (a', x.2)) (fun a' _ => hP _)
      (Finset.mem_univ x.1)
  exact lt_of_lt_of_le (lt_of_le_of_ne (hP x) (Ne.symm hx)) this

/-- Jensen upper bound on mutual information -/
theorem mi_upper (P : α × β → ℝ) (hP : ∀ x, 0 ≤ P x) (h1 : ∑ x, P x = 1) :
    mutualInfoBits P ≤ Real.logb 2 (∑ x : α × β,
      if P x = 0 then 0 else P x ^ 2 / (pa P x.1 * qb P x.2)) := by
  classical
  set s := Finset.univ.filter (fun x : α × β => P x ≠ 0)
  have hs1 : ∑ x ∈ s, P x = 1 := by
    rw [Finset.sum_filter_ne_zero]; exact h1
  rw [mi_eq]
  have e1 : ∑ x : α × β, P x * Real.logb 2 (P x / (pa P x.1 * qb P x.2)) =
      (∑ x ∈ s, P x * Real.log (P x / (pa P x.1 * qb P x.2))) / Real.log 2 := by
    rw [Finset.sum_div, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro x _
    by_cases h : P x = 0
    · simp [h]
    · rw [if_pos h, Real.logb, mul_div_assoc]
  have e2 : ∑ x : α × β, (if P x = 0 then 0 else P x ^ 2 / (pa P x.1 * qb P x.2)) =
      ∑ x ∈ s, P x * (P x / (pa P x.1 * qb P x.2)) := by
    rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro x _
    by_cases h : P x = 0
    · simp [h]
    · rw [if_neg h, if_pos h]; ring
  rw [e1, e2, Real.logb]
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  apply jensen_log s _ _ (fun x _ => hP x) hs1
  intro x hx
  have hx' : P x ≠ 0 := (Finset.mem_filter.1 hx).2
  have := pa_pos P hP x hx'; have := qb_pos P hP x hx'
  have := lt_of_le_of_ne (hP x) (Ne.symm hx')
  positivity

/-- Donsker–Varadhan type lower bound on mutual information -/
theorem mi_lower (P : α × β → ℝ) (hP : ∀ x, 0 ≤ P x) (h1 : ∑ x, P x = 1) (f : α × β → ℝ)
    (hf : ∑ x : α × β, pa P x.1 * qb P x.2 * (2:ℝ) ^ f x ≤ 1) :
    ∑ x, P x * f x ≤ mutualInfoBits P := by
  classical
  set s := Finset.univ.filter (fun x : α × β => P x ≠ 0)
  have hs1 : ∑ x ∈ s, P x = 1 := by rw [Finset.sum_filter_ne_zero]; exact h1
  rw [mi_eq]
  have hpos : ∀ x ∈ s, 0 < P x ∧ 0 < pa P x.1 ∧ 0 < qb P x.2 := by
    intro x hx
    have hx' : P x ≠ 0 := (Finset.mem_filter.1 hx).2
    exact ⟨lt_of_le_of_ne (hP x) (Ne.symm hx'), pa_pos P hP x hx', qb_pos P hP x hx'⟩
  -- restrict both sums to the support
  have e1 : ∑ x, P x * f x = ∑ x ∈ s, P x * f x := by
    rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro x _
    by_cases h : P x = 0
    · simp [h]
    · rw [if_pos h]
  have e2 : ∑ x : α × β, P x * Real.logb 2 (P x / (pa P x.1 * qb P x.2)) =
      ∑ x ∈ s, P x * Real.logb 2 (P x / (pa P x.1 * qb P x.2)) := by
    rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro x _
    by_cases h : P x = 0
    · simp [h]
    · rw [if_pos h]
  rw [e1, e2]
  -- Jensen on `pa qb 2^f / P`
  have hJ := jensen_log s P (fun x => pa P x.1 * qb P x.2 * (2:ℝ) ^ f x / P x)
    (fun x _ => hP x) hs1 (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := hpos x hx; positivity)
  have hsum : ∑ x ∈ s, P x * (pa P x.1 * qb P x.2 * (2:ℝ) ^ f x / P x) ≤ 1 := by
    calc ∑ x ∈ s, P x * (pa P x.1 * qb P x.2 * (2:ℝ) ^ f x / P x)
        = ∑ x ∈ s, pa P x.1 * qb P x.2 * (2:ℝ) ^ f x := by
          apply Finset.sum_congr rfl; intro x hx
          have := (hpos x hx).1; field_simp
      _ ≤ ∑ x, pa P x.1 * qb P x.2 * (2:ℝ) ^ f x := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro x _ _
          have : 0 ≤ pa P x.1 := Finset.sum_nonneg (fun _ _ => hP _)
          have : 0 ≤ qb P x.2 := Finset.sum_nonneg (fun _ _ => hP _)
          positivity
      _ ≤ 1 := hf
  have hsum_pos : 0 < ∑ x ∈ s, P x * (pa P x.1 * qb P x.2 * (2:ℝ) ^ f x / P x) := by
    have hne : s.Nonempty := by
      by_contra hc; rw [Finset.not_nonempty_iff_eq_empty] at hc; rw [hc] at hs1; simp at hs1
    apply Finset.sum_pos _ hne
    intro x hx; obtain ⟨h1, h2, h3⟩ := hpos x hx; positivity
  have hlog : Real.log (∑ x ∈ s, P x * (pa P x.1 * qb P x.2 * (2:ℝ) ^ f x / P x)) ≤ 0 :=
    Real.log_nonpos hsum_pos.le hsum
  -- termwise identity
  have hterm : ∀ x ∈ s, P x * Real.logb 2 (P x / (pa P x.1 * qb P x.2)) =
      P x * f x - P x * Real.log (pa P x.1 * qb P x.2 * (2:ℝ) ^ f x / P x) / Real.log 2 := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hpos x hx
    have h2f : (0:ℝ) < (2:ℝ) ^ f x := by positivity
    rw [Real.logb, Real.log_div h1.ne' (by positivity), Real.log_div (by positivity) h1.ne',
      Real.log_mul (by positivity) h2f.ne', Real.log_rpow (by norm_num)]
    have hl2 : Real.log 2 ≠ 0 := by positivity
    field_simp; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_div]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : (∑ x ∈ s, P x * Real.log (pa P x.1 * qb P x.2 * (2:ℝ) ^ f x / P x)) / Real.log 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (hJ.trans hlog) hl2.le
  linarith

end CODInfo


-- ===== from Solutions/COD/Info.lean =====

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

noncomputable section

namespace CODInfo
open CompressedOracleDuality.LabelSymmetric

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def chi (x : ℝ) : ℝ := if x = 0 then 0 else 1

/-- the orthogonal projection onto the range of `G` -/
def supportProj (G : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc chi G

lemma supportProj_mul_sqrt (G : Matrix ι ι ℂ) (hG : G.PosSemidef) :
    supportProj G * CFC.sqrt G = CFC.sqrt G := by
  have h0 : (0 : Matrix ι ι ℂ) ≤ G := Matrix.nonneg_iff_posSemidef.2 hG
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ G) := fun f => (Set.toFinite _).continuousOn f
  rw [supportProj, CFC.sqrt_eq_real_sqrt G h0,
    cfcₙ_eq_cfc (hf := Real.continuous_sqrt.continuousOn) (hf0 := by simp)]
  rw [← cfc_mul chi Real.sqrt G (hc _) (hc _)]
  congr 1; funext x; unfold chi; split_ifs with h <;> simp [h]

lemma supportProj_trace (G : Matrix ι ι ℂ) (hG : G.IsHermitian) :
    (supportProj G).trace = G.rank := by
  rw [supportProj, hG.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle]
  rw [Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal, hG.rank_eq_card_non_zero_eigs]
  simp only [Function.comp_apply, chi]
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp_all

lemma supportProj_idem (G : Matrix ι ι ℂ) : supportProj G * supportProj G = supportProj G := by
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ G) := fun f => (Set.toFinite _).continuousOn f
  rw [supportProj, ← cfc_mul chi chi G (hc _) (hc _)]
  congr 1; funext x; unfold chi; split_ifs <;> simp

lemma supportProj_herm (G : Matrix ι ι ℂ) : (supportProj G).conjTranspose = supportProj G := by
  have : IsSelfAdjoint (supportProj G) := cfc_predicate chi G
  exact this

lemma sqrt_herm (G : Matrix ι ι ℂ) : (CFC.sqrt G).conjTranspose = CFC.sqrt G := by
  have : (0 : Matrix ι ι ℂ) ≤ CFC.sqrt G := CFC.sqrt_nonneg G
  exact (Matrix.nonneg_iff_posSemidef.1 this).isHermitian

lemma norm_sum_mul_sq_le (x y : ι → ℂ) :
    ‖∑ c, x c * y c‖ ^ 2 ≤ (∑ c, ‖x c‖ ^ 2) * (∑ c, ‖y c‖ ^ 2) := by
  let u : EuclideanSpace ℂ ι := WithLp.toLp 2 fun c => star (x c)
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 y
  have h := norm_inner_le_norm (𝕜 := ℂ) u v
  have hi : inner ℂ u v = ∑ c, x c * y c := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [u, v, dotProduct, mul_comm]
  rw [hi] at h
  have hu : ‖u‖ ^ 2 = ∑ c, ‖x c‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]; simp [u]
  have hv : ‖v‖ ^ 2 = ∑ c, ‖y c‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [← hu, ← hv, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma diag_eq_sum_sq (M : Matrix ι ι ℂ) (hM : M.conjTranspose = M) (hidem : M * M = M) (b : ι) :
    M b b = ((∑ c, ‖M c b‖ ^ 2 : ℝ) : ℂ) := by
  conv_lhs => rw [← hidem, ← hM]
  rw [Matrix.mul_apply]; push_cast
  apply Finset.sum_congr rfl; intro c _
  rw [Matrix.conjTranspose_apply, hM, Complex.star_def, Complex.conj_mul']

lemma diag_eq_sum_sq_row (M : Matrix ι ι ℂ) (hM : M.conjTranspose = M) (a : ι) :
    (M * M) a a = ((∑ c, ‖M a c‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]; push_cast
  apply Finset.sum_congr rfl; intro c _
  have : M c a = star (M a c) := by
    rw [← hM]; rw [Matrix.conjTranspose_apply, hM]
  rw [this, Complex.star_def, Complex.mul_conj']

/-- `|(√G)_{ab}|² ≤ G_{aa} Π_{bb}` -/
theorem jointLaw_le_proj (G : Matrix ι ι ℂ) (hG : G.PosSemidef) (a b : ι) :
    ‖CFC.sqrt G a b‖ ^ 2 ≤ (G a a).re * (supportProj G b b).re := by
  set S := CFC.sqrt G
  set Pr := supportProj G
  have hSP : S * Pr = S := by
    have := congrArg Matrix.conjTranspose (supportProj_mul_sqrt G hG)
    rwa [Matrix.conjTranspose_mul, sqrt_herm, supportProj_herm] at this
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G (Matrix.nonneg_iff_posSemidef.2 hG)
  have h1 : S a b = ∑ c, S a c * Pr c b := by
    conv_lhs => rw [← hSP]
    rw [Matrix.mul_apply]
  have hGa : (G a a).re = ∑ c, ‖S a c‖ ^ 2 := by
    rw [← hSS, diag_eq_sum_sq_row S (sqrt_herm G) a, Complex.ofReal_re]
  have hPb : (Pr b b).re = ∑ c, ‖Pr c b‖ ^ 2 := by
    rw [diag_eq_sum_sq Pr (supportProj_herm G) (supportProj_idem G) b, Complex.ofReal_re]
  rw [h1, hGa, hPb]
  exact norm_sum_mul_sq_le _ _

variable {n : ℕ}

lemma jointLaw_nonneg (G : DBMatrix n) (x : Database n × Database n) : 0 ≤ jointLaw G x :=
  Complex.normSq_nonneg _

lemma jointLaw_eq_sq (G : DBMatrix n) (x : Database n × Database n) :
    jointLaw G x = ‖sqrtGram G x.1 x.2‖ ^ 2 := by
  rw [jointLaw, Complex.normSq_eq_norm_sq]

lemma pa_jointLaw (G : DBMatrix n) (hG : G.PosSemidef) (htr : G.trace = 1) (a : Database n) :
    pa (jointLaw G) a = (G a a).re := (equation_24 G hG htr).2.1 a

lemma qb_jointLaw (G : DBMatrix n) (hG : G.PosSemidef) (htr : G.trace = 1) (b : Database n) :
    qb (jointLaw G) b = (G b b).re := (equation_24 G hG htr).2.2.1 b

lemma sum_diag_re (G : DBMatrix n) (htr : G.trace = 1) : ∑ D, (G D D).re = 1 := by
  have : (G.trace).re = 1 := by rw [htr]; simp
  rw [Matrix.trace, Complex.re_sum] at this; exact this

lemma jointLaw_sum (G : DBMatrix n) (hG : G.PosSemidef) (htr : G.trace = 1) :
    ∑ x, jointLaw G x = 1 := by
  rw [Fintype.sum_prod_type]
  have := fun a => pa_jointLaw G hG htr a
  simp only [pa] at this
  simp_rw [this]; exact sum_diag_re G htr

lemma rank_pos_of_trace (G : DBMatrix n) (htr : G.trace = 1) : 1 ≤ G.rank := by
  by_contra h
  push Not at h
  have h0 : G.rank = 0 := by omega
  have : G = 0 := by
    rw [Matrix.rank] at h0
    have h2 := Submodule.finrank_eq_zero.mp h0
    rw [LinearMap.range_eq_bot] at h2
    have : Matrix.toLin' G = 0 := by rw [Matrix.toLin'_apply']; exact h2
    simpa using congrArg Matrix.toLin'.symm this
  rw [this, Matrix.trace_zero] at htr; exact zero_ne_one htr

theorem info_le_log_rank (G : DBMatrix n) (hG : G.PosSemidef) (htr : G.trace = 1) :
    databaseInformation G ≤ Real.logb 2 G.rank := by
  classical
  set P := jointLaw G
  have hP := jointLaw_nonneg G
  have h1 := jointLaw_sum G hG htr
  have hup := mi_upper P hP h1
  refine hup.trans ?_
  -- bound the χ²-sum by the rank
  have hPr : ∀ b, 0 ≤ (supportProj G b b).re := by
    intro b
    rw [diag_eq_sum_sq _ (supportProj_herm G) (supportProj_idem G) b, Complex.ofReal_re]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound : ∑ x : Database n × Database n,
      (if P x = 0 then 0 else P x ^ 2 / (pa P x.1 * qb P x.2)) ≤ G.rank := by
    calc ∑ x : Database n × Database n, (if P x = 0 then 0 else P x ^ 2 / (pa P x.1 * qb P x.2))
        ≤ ∑ x : Database n × Database n,
          (if qb P x.2 = 0 then 0 else P x * (supportProj G x.2 x.2).re / qb P x.2) := by
          apply Finset.sum_le_sum; intro x _
          by_cases hx : P x = 0
          · rw [if_pos hx]; split_ifs
            · rfl
            · have := hPr x.2; have : 0 ≤ qb P x.2 := Finset.sum_nonneg (fun _ _ => hP _)
              positivity
          · rw [if_neg hx]
            have hpa := pa_pos P hP x hx
            have hqb := qb_pos P hP x hx
            rw [if_neg hqb.ne']
            have hle : P x ≤ pa P x.1 * (supportProj G x.2 x.2).re := by
              have := jointLaw_le_proj G hG x.1 x.2
              rw [pa_jointLaw G hG htr]
              simpa [P, jointLaw_eq_sq, sqrtGram] using this
            rw [div_le_div_iff₀ (by positivity) hqb, sq]
            have hPx : 0 ≤ P x := hP x
            calc P x * P x * qb P x.2 ≤ P x * (pa P x.1 * (supportProj G x.2 x.2).re) * qb P x.2 := by
                  gcongr
              _ = _ := by ring
      _ = ∑ b, (if qb P b = 0 then 0 else (supportProj G b b).re / qb P b * qb P b) := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          apply Finset.sum_congr rfl; intro b _
          split_ifs with hb
          · simp
          · simp only [qb]
            simp only [← Finset.sum_div, ← Finset.sum_mul]; ring
      _ ≤ ∑ b, (supportProj G b b).re := by
          apply Finset.sum_le_sum; intro b _
          split_ifs with hb
          · exact hPr b
          · rw [div_mul_cancel₀ _ hb]
      _ = G.rank := by
          have := supportProj_trace G hG.isHermitian
          have h2 := congrArg Complex.re this
          simpa [Matrix.trace, Complex.re_sum] using h2
  have hr : (0:ℝ) < G.rank := by exact_mod_cast rank_pos_of_trace G htr
  by_cases hs : ∑ x : Database n × Database n,
      (if P x = 0 then 0 else P x ^ 2 / (pa P x.1 * qb P x.2)) = 0
  · rw [hs, Real.logb_zero]
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast rank_pos_of_trace G htr)
  · have hpos : 0 < ∑ x : Database n × Database n,
        (if P x = 0 then 0 else P x ^ 2 / (pa P x.1 * qb P x.2)) := by
      apply lt_of_le_of_ne _ (Ne.symm hs)
      apply Finset.sum_nonneg; intro x _
      split_ifs
      · rfl
      · have : 0 ≤ pa P x.1 := Finset.sum_nonneg (fun _ _ => hP _)
        have : 0 ≤ qb P x.2 := Finset.sum_nonneg (fun _ _ => hP _)
        positivity
    exact Real.logb_le_logb_of_le (by norm_num) hpos hbound

end CODInfo


end

open QAlgorithms CompressedOracleDuality.LabelSymmetric
open scoped BigOperators MatrixOrder ComplexOrder

theorem solution {n S : ℕ} (G : DBMatrix n) (hG : G.PosSemidef)
    (htr : G.trace = 1) (hrank : G.rank ≤ 2 ^ S) :
    databaseInformation G ≤ Real.logb 2 G.rank ∧ Real.logb 2 G.rank ≤ S := by
  refine ⟨CODInfo.info_le_log_rank G hG htr, ?_⟩
  have h1 : (0:ℝ) < G.rank := by exact_mod_cast CODInfo.rank_pos_of_trace G htr
  have h2 : (G.rank : ℝ) ≤ (2:ℝ) ^ S := by exact_mod_cast hrank
  calc Real.logb 2 G.rank ≤ Real.logb 2 ((2:ℝ) ^ S) := Real.logb_le_logb_of_le (by norm_num) h1 h2
    _ = S := by rw [Real.logb_pow]; simp
