-- Prove2me | solution 1 for DRCVRP.Covariance.worstCaseVaR_eq_qcqp
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T15:11:23.405676+00:00
-- url     : https://prove2.me/submissions/941f1233-972b-48ab-b52e-a826b3f99da2

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Covariance_AmbiguitySet

open MeasureTheory Matrix


namespace DRCVRP.Covariance

section qc

variable {n : ℕ}

def QNice (lo hi : Fin n → ℝ) (F : (Fin n → ℝ) → ℝ) : Prop :=
  Measurable F ∧ ∃ C, ∀ q ∈ Set.Icc lo hi, |F q| ≤ C

lemma qnice_const (lo hi : Fin n → ℝ) (c : ℝ) : QNice lo hi (fun _ => c) :=
  ⟨measurable_const, |c|, fun _ _ => le_rfl⟩

lemma qnice_coord (lo hi : Fin n → ℝ) (j : Fin n) : QNice lo hi (fun q => q j) := by
  refine ⟨measurable_pi_apply j, |lo j| + |hi j|, fun q hq => ?_⟩
  have h1 := hq.1 j; have h2 := hq.2 j
  rw [abs_le]; constructor
  · linarith [neg_abs_le (lo j), abs_nonneg (hi j)]
  · linarith [le_abs_self (hi j), abs_nonneg (lo j)]

lemma qnice_add {lo hi : Fin n → ℝ} {F G : (Fin n → ℝ) → ℝ} (hF : QNice lo hi F)
    (hG : QNice lo hi G) : QNice lo hi (fun q => F q + G q) := by
  obtain ⟨mF, C1, h1⟩ := hF; obtain ⟨mG, C2, h2⟩ := hG
  exact ⟨mF.add mG, C1 + C2, fun q hq => (abs_add_le _ _).trans (add_le_add (h1 q hq) (h2 q hq))⟩

lemma qnice_neg {lo hi : Fin n → ℝ} {F : (Fin n → ℝ) → ℝ} (hF : QNice lo hi F) :
    QNice lo hi (fun q => - F q) := by
  obtain ⟨mF, C1, h1⟩ := hF
  exact ⟨mF.neg, C1, fun q hq => by rw [abs_neg]; exact h1 q hq⟩

lemma qnice_sub {lo hi : Fin n → ℝ} {F G : (Fin n → ℝ) → ℝ} (hF : QNice lo hi F)
    (hG : QNice lo hi G) : QNice lo hi (fun q => F q - G q) := by
  have := qnice_add hF (qnice_neg hG)
  simpa [sub_eq_add_neg] using this

lemma qnice_mul {lo hi : Fin n → ℝ} {F G : (Fin n → ℝ) → ℝ} (hF : QNice lo hi F)
    (hG : QNice lo hi G) : QNice lo hi (fun q => F q * G q) := by
  obtain ⟨mF, C1, h1⟩ := hF; obtain ⟨mG, C2, h2⟩ := hG
  refine ⟨mF.mul mG, C1 * C2, fun q hq => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (h1 q hq) (h2 q hq) (abs_nonneg _) ((abs_nonneg _).trans (h1 q hq))

lemma qnice_sum {lo hi : Fin n → ℝ} {ι : Type*} (s : Finset ι) {F : ι → (Fin n → ℝ) → ℝ}
    (hF : ∀ i, QNice lo hi (F i)) : QNice lo hi (fun q => ∑ i ∈ s, F i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using qnice_const lo hi 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact qnice_add (hF a) ih

lemma qnice_ind {lo hi : Fin n → ℝ} {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    QNice lo hi (s.indicator 1) := by
  refine ⟨(measurable_const.indicator hs), 1, fun q _ => ?_⟩
  by_cases h : q ∈ s <;> simp [h]

lemma qnice_integrable {lo hi : Fin n → ℝ} {P : Measure (Fin n → ℝ)} [IsProbabilityMeasure P]
    (hae : ∀ᵐ q ∂P, q ∈ Set.Icc lo hi) {F : (Fin n → ℝ) → ℝ} (hF : QNice lo hi F) :
    Integrable F P := by
  obtain ⟨mF, C, h⟩ := hF
  refine Integrable.of_bound (C := C) mF.aestronglyMeasurable ?_
  filter_upwards [hae] with q hq
  rw [Real.norm_eq_abs]; exact h q hq

lemma qbox_ae {lo hi : Fin n → ℝ} {P : Measure (Fin n → ℝ)} [IsProbabilityMeasure P]
    (hbox : P (Set.Icc lo hi) = 1) : ∀ᵐ q ∂P, q ∈ Set.Icc lo hi := by
  rw [ae_iff]
  have := (prob_compl_eq_zero_iff (μ := P) measurableSet_Icc).2 hbox
  simpa [Set.compl_def] using this


lemma qc_ub {n : ℕ} (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (S : Finset (Fin n)) (P : Measure (Fin n → ℝ)) (hP : P ∈ covarianceSet qlo qhi μ Sig) (y : ℝ) :
    ∃ b : Fin n → ℝ, ∃ t : ℝ, t = 1 - P.real {q | ∑ i ∈ S, q i ≤ y} ∧
      (∀ j, t * (qlo j - μ j) ≤ b j ∧ b j ≤ t * (qhi j - μ j)) ∧
      (∀ j, (1 - t) * (qlo j - μ j) ≤ - b j ∧ - b j ≤ (1 - t) * (qhi j - μ j)) ∧
      t * (y - ∑ j ∈ S, μ j) ≤ ∑ j ∈ S, b j ∧
      (∀ (w : Fin n → ℝ) (α β : ℝ),
        2 * α * (w ⬝ᵥ b) - (α ^ 2 + 2 * α * β) * t - β ^ 2 ≤ w ⬝ᵥ (Sig *ᵥ w)) := by
  obtain ⟨hprob, hbox, hmean, hpsd⟩ := hP
  have hae := qbox_ae hbox
  set s : Set (Fin n → ℝ) := {q | y < ∑ i ∈ S, q i} with hs_def
  have hs : MeasurableSet s := measurableSet_lt measurable_const (by fun_prop)
  set p : (Fin n → ℝ) → ℝ := s.indicator 1 with hp_def
  have hpN : QNice qlo qhi p := qnice_ind hs
  have hI : ∀ {F}, QNice qlo qhi F → Integrable F P := fun h => qnice_integrable hae h
  have hcN : ∀ j, QNice qlo qhi (fun q => q j - μ j) := fun j =>
    qnice_sub (qnice_coord _ _ j) (qnice_const _ _ _)
  set t := P.real s with ht_def
  have ht : t = 1 - P.real {q | ∑ i ∈ S, q i ≤ y} := by
    have : {q : Fin n → ℝ | ∑ i ∈ S, q i ≤ y} = sᶜ := by ext q; simp [s]
    rw [this, probReal_compl_eq_one_sub hs]; ring
  have hEp : ∫ q, p q ∂P = t := integral_indicator_one hs
  set b : Fin n → ℝ := fun j => ∫ q, p q * (q j - μ j) ∂P with hb_def
  have hcen : ∀ j, ∫ q, (q j - μ j) ∂P = 0 := by
    intro j; rw [integral_sub (hI (qnice_coord _ _ j)) (integrable_const _), hmean j]; simp
  have hp01 : ∀ q, p q = 0 ∨ p q = 1 := by intro q; by_cases h : q ∈ s <;> simp [p, h]
  have hp0 : ∀ q, 0 ≤ p q := fun q => by rcases hp01 q with h | h <;> rw [h] <;> norm_num
  have hp1 : ∀ q, p q ≤ 1 := fun q => by rcases hp01 q with h | h <;> rw [h] <;> norm_num
  refine ⟨b, t, ht, ?_, ?_, ?_, ?_⟩
  · intro j
    constructor
    · rw [← hEp, ← integral_mul_const]
      refine integral_mono_ae (hI (qnice_mul hpN (qnice_const _ _ _))) (hI (qnice_mul hpN (hcN j))) ?_
      filter_upwards [hae] with q hq
      exact mul_le_mul_of_nonneg_left (by linarith [hq.1 j]) (hp0 q)
    · rw [← hEp, ← integral_mul_const]
      refine integral_mono_ae (hI (qnice_mul hpN (hcN j))) (hI (qnice_mul hpN (qnice_const _ _ _))) ?_
      filter_upwards [hae] with q hq
      exact mul_le_mul_of_nonneg_left (by linarith [hq.2 j]) (hp0 q)
  · intro j
    have hq1N : QNice qlo qhi (fun q => (1 - p q) * (q j - μ j)) :=
      qnice_mul (qnice_sub (qnice_const _ _ 1) hpN) (hcN j)
    have he : ∫ q, (1 - p q) * (q j - μ j) ∂P = - b j := by
      have : (fun q => (1 - p q) * (q j - μ j)) = fun q => (q j - μ j) - p q * (q j - μ j) := by
        funext q; ring
      rw [this, integral_sub (hI (hcN j)) (hI (qnice_mul hpN (hcN j))), hcen j]; simp [b]
    have he1 : ∫ q, (1 - p q) ∂P = 1 - t := by
      rw [integral_sub (integrable_const _) (hI hpN), hEp]; simp
    rw [← he, ← he1, ← integral_mul_const, ← integral_mul_const]
    constructor
    · refine integral_mono_ae (hI (qnice_mul (qnice_sub (qnice_const _ _ 1) hpN) (qnice_const _ _ _)))
        (hI hq1N) ?_
      filter_upwards [hae] with q hq
      exact mul_le_mul_of_nonneg_left (by linarith [hq.1 j]) (by linarith [hp1 q])
    · refine integral_mono_ae (hI hq1N)
        (hI (qnice_mul (qnice_sub (qnice_const _ _ 1) hpN) (qnice_const _ _ _))) ?_
      filter_upwards [hae] with q hq
      exact mul_le_mul_of_nonneg_left (by linarith [hq.2 j]) (by linarith [hp1 q])
  · have e1 : ∑ j ∈ S, b j = ∫ q, p q * (∑ j ∈ S, q j - ∑ j ∈ S, μ j) ∂P := by
      simp only [b]
      rw [← integral_finset_sum _ (fun j _ => hI (qnice_mul hpN (hcN j)))]
      congr 1; funext q; rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [e1, ← hEp, ← integral_mul_const]
    refine integral_mono (hI (qnice_mul hpN (qnice_const _ _ _)))
      (hI (qnice_mul hpN (qnice_sub (qnice_sum S (fun j => qnice_coord _ _ j)) (qnice_const _ _ _)))) ?_
    intro q
    by_cases h : q ∈ s
    · simp only [p, Set.indicator_of_mem h, Pi.one_apply, one_mul]
      have : y < ∑ i ∈ S, q i := h
      linarith
    · simp [p, Set.indicator_of_notMem h]
  · intro w α β
    set Z : (Fin n → ℝ) → ℝ := fun q => ∑ i, w i * (q i - μ i) with hZ
    have hZN : QNice qlo qhi Z := qnice_sum _ (fun i => qnice_mul (qnice_const _ _ _) (hcN i))
    have hEZ2 : ∫ q, Z q ^ 2 ∂P = w ⬝ᵥ (centredSecondMoment μ P *ᵥ w) := by
      have : (fun q => Z q ^ 2) = fun q => ∑ i, ∑ j, w i * (w j * ((q i - μ i) * (q j - μ j))) := by
        funext q; simp only [Z]; rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [this, integral_finset_sum]
      · simp only [dotProduct, mulVec, centredSecondMoment]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finset_sum, Finset.mul_sum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_const_mul, integral_const_mul]; ring
        · intro j _
          exact hI (qnice_mul (qnice_const _ _ _) (qnice_mul (qnice_const _ _ _)
            (qnice_mul (hcN i) (hcN j))))
      · intro i _
        exact hI (qnice_sum _ fun j => qnice_mul (qnice_const _ _ _) (qnice_mul (qnice_const _ _ _)
          (qnice_mul (hcN i) (hcN j))))
    have hEZ : ∫ q, Z q ∂P = 0 := by
      simp only [Z]
      rw [integral_finset_sum _ (fun i _ => hI (qnice_mul (qnice_const _ _ _) (hcN i)))]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_const_mul, hcen i, mul_zero]
    have hEpZ : ∫ q, p q * Z q ∂P = w ⬝ᵥ b := by
      have : (fun q => p q * Z q) = fun q => ∑ i, w i * (p q * (q i - μ i)) := by
        funext q; simp only [Z]; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [this, integral_finset_sum _ (fun i _ => hI (qnice_mul (qnice_const _ _ _)
        (qnice_mul hpN (hcN i))))]
      simp only [dotProduct, b]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul]
    have hpsd' : w ⬝ᵥ (centredSecondMoment μ P *ᵥ w) ≤ w ⬝ᵥ (Sig *ᵥ w) := by
      have := hpsd.dotProduct_mulVec_nonneg w
      simp only [star_trivial, sub_mulVec, dotProduct_sub] at this
      linarith
    have i1 : Integrable (fun q => 2 * α * (p q * Z q)) P :=
      hI (qnice_mul (qnice_const _ _ _) (qnice_mul hpN hZN))
    have i2 : Integrable (fun q => 2 * β * Z q) P := hI (qnice_mul (qnice_const _ _ _) hZN)
    have i3 : Integrable (fun q => (α ^ 2 + 2 * α * β) * p q) P := hI (qnice_mul (qnice_const _ _ _) hpN)
    have hlow : ∫ q, (2 * α * (p q * Z q) + 2 * β * Z q - (α ^ 2 + 2 * α * β) * p q - β ^ 2) ∂P ≤
        ∫ q, Z q ^ 2 ∂P := by
      refine integral_mono (((i1.add i2).sub i3).sub (integrable_const _))
        ((hI (qnice_mul hZN hZN)).congr (by filter_upwards with q; simp [sq])) ?_
      intro q
      rcases hp01 q with h | h <;> simp only [h] <;>
        nlinarith [sq_nonneg (Z q - α - β), sq_nonneg (Z q - β)]
    have i12 : Integrable (fun q => 2 * α * (p q * Z q) + 2 * β * Z q) P := i1.add i2
    have i123 : Integrable (fun q => 2 * α * (p q * Z q) + 2 * β * Z q - (α ^ 2 + 2 * α * β) * p q) P :=
      i12.sub i3
    rw [integral_sub i123 (integrable_const _), integral_sub i12 i3,
      integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul, hEpZ, hEZ, hEp,
      hEZ2] at hlow
    simp at hlow
    linarith

lemma qc_sig_inv {n : ℕ} {Sig : Matrix (Fin n) (Fin n) ℝ} (hSig : Sig.PosDef) (a : Fin n → ℝ) :
    Sig *ᵥ (Sig⁻¹ *ᵥ a) = a := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hSig.isUnit), one_mulVec]

lemma qc_symm {n : ℕ} {Sig : Matrix (Fin n) (Fin n) ℝ} (hSig : Sig.PosDef) (x w : Fin n → ℝ) :
    w ⬝ᵥ (Sig *ᵥ x) = x ⬝ᵥ (Sig *ᵥ w) := by
  have hT : Sigᵀ = Sig := by
    have := hSig.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]

lemma qc_cs {n : ℕ} {Sig : Matrix (Fin n) (Fin n) ℝ} (hSig : Sig.PosDef) (x q : Fin n → ℝ) :
    (x ⬝ᵥ q) ^ 2 ≤ (x ⬝ᵥ (Sig *ᵥ x)) * (q ⬝ᵥ (Sig⁻¹ *ᵥ q)) := by
  set w := Sig⁻¹ *ᵥ q with hw
  have hq : q = Sig *ᵥ w := (qc_sig_inv hSig q).symm
  have hC : q ⬝ᵥ w = w ⬝ᵥ (Sig *ᵥ w) := by rw [dotProduct_comm, ← hq]
  rw [hC]
  have hx : x ⬝ᵥ q = x ⬝ᵥ (Sig *ᵥ w) := by rw [← hq]
  rw [hx]
  have hpsd := hSig.posSemidef
  have hA : 0 ≤ x ⬝ᵥ (Sig *ᵥ x) := by simpa using hpsd.dotProduct_mulVec_nonneg x
  by_cases hw0 : w = 0
  · simp [hw0]
  have hCpos : 0 < w ⬝ᵥ (Sig *ᵥ w) := by simpa using hSig.dotProduct_mulVec_pos hw0
  have key : ∀ l : ℝ, 0 ≤ x ⬝ᵥ (Sig *ᵥ x) - 2 * l * (x ⬝ᵥ (Sig *ᵥ w)) +
      l ^ 2 * (w ⬝ᵥ (Sig *ᵥ w)) := by
    intro l
    have h := hpsd.dotProduct_mulVec_nonneg (x - l • w)
    simp only [star_trivial, mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
    rw [qc_symm hSig x w] at h
    linarith
  set A := x ⬝ᵥ (Sig *ᵥ x)
  set B := x ⬝ᵥ (Sig *ᵥ w)
  set C := w ⬝ᵥ (Sig *ᵥ w)
  have := key (B / C)
  have e : A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by field_simp; ring
  rw [e] at this
  have : B ^ 2 / C ≤ A := by linarith
  rw [div_le_iff₀ hCpos] at this
  linarith

lemma qc_ub2 {n : ℕ} (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (S : Finset (Fin n)) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hSig : Sig.PosDef)
    (hε0 : 0 < ε) (hε1 : ε < 1) (y : ℝ) (b : Fin n → ℝ) (t : ℝ) (htε : ε < t) (ht1 : t ≤ 1)
    (hF2 : ∀ j, t * (qlo j - μ j) ≤ b j ∧ b j ≤ t * (qhi j - μ j))
    (hF3 : ∀ j, (1 - t) * (qlo j - μ j) ≤ - b j ∧ - b j ≤ (1 - t) * (qhi j - μ j))
    (hF1 : t * (y - ∑ j ∈ S, μ j) ≤ ∑ j ∈ S, b j)
    (hF4 : ∀ (w : Fin n → ℝ) (α β : ℝ),
        2 * α * (w ⬝ᵥ b) - (α ^ 2 + 2 * α * β) * t - β ^ 2 ≤ w ⬝ᵥ (Sig *ᵥ w)) :
    ∃ a : Fin n → ℝ, (a ⬝ᵥ (Sig⁻¹ *ᵥ a) ≤ (1 - ε) / ε ∧
          ∀ j, qLower qlo qhi μ ε j ≤ a j ∧ a j ≤ qUpper qlo qhi μ ε j) ∧
      y ≤ ∑ j ∈ S, μ j + ∑ j ∈ S, a j := by
  have hr : 0 < (1 - ε) / ε := div_pos (by linarith) hε0
  have ht0 : 0 < t := by linarith
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · -- t = 1
    subst h1
    have hb0 : ∀ j, b j = 0 := by
      intro j; have := hF3 j; simp at this; linarith [this.1, this.2]
    refine ⟨0, ⟨by simp; exact hr.le, fun j => ⟨?_, ?_⟩⟩, ?_⟩
    · simp only [qLower, Pi.zero_apply]
      apply max_le
      · have : 0 ≤ (1 - ε) / ε * (qhi j - μ j) := mul_nonneg hr.le (by linarith [(hμ j).2])
        linarith
      · linarith [(hμ j).1]
    · simp only [qUpper, Pi.zero_apply]
      apply le_min
      · exact mul_nonneg hr.le (by linarith [(hμ j).1])
      · linarith [(hμ j).2]
    · simp [hb0] at hF1; simp; linarith
  · set a : Fin n → ℝ := fun j => b j / t with ha
    have hba : ∀ j, b j = t * a j := fun j => by simp only [a]; field_simp
    have hkey : (1 - t) ≤ (1 - ε) / ε * t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε0]; nlinarith
    refine ⟨a, ⟨?_, fun j => ⟨?_, ?_⟩⟩, ?_⟩
    · set w := Sig⁻¹ *ᵥ a with hw
      set c := a ⬝ᵥ w with hc
      have hwb : w ⬝ᵥ b = t * c := by
        have : b = t • a := funext fun j => by simp [hba j]
        rw [this, dotProduct_smul, smul_eq_mul, dotProduct_comm]
      have hwS : w ⬝ᵥ (Sig *ᵥ w) = c := by rw [hw, qc_sig_inv hSig, dotProduct_comm]
      set u := c / (1 - t) with hu
      have hcu : c = u * (1 - t) := by simp only [u]; field_simp
      have h4 := hF4 w u (-t * u)
      rw [hwb, hwS] at h4
      have h5 : u ^ 2 * t * (1 - t) ≤ u * (1 - t) := by rw [hcu] at h4; nlinarith
      have h6 : u ^ 2 * t ≤ u := le_of_mul_le_mul_right (by linarith) (by linarith : (0:ℝ) < 1 - t)
      show c ≤ (1 - ε) / ε
      rw [hcu, le_div_iff₀ hε0]
      rcases le_or_gt u 0 with hu0 | hu0
      · nlinarith
      · have h7 : u * t ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left htε.le hu0.le]
    · obtain ⟨h2a, -⟩ := hF2 j; obtain ⟨-, h3b⟩ := hF3 j
      simp only [qLower]
      apply max_le
      · -- -(r (qhi-μ)) ≤ a j
        rw [hba j] at h3b
        have hpos : 0 < qhi j - μ j := by linarith [(hμ j).2]
        nlinarith [mul_le_mul_of_nonneg_right hkey hpos.le]
      · rw [hba j] at h2a
        nlinarith
    · obtain ⟨-, h2b⟩ := hF2 j; obtain ⟨h3a, -⟩ := hF3 j
      simp only [qUpper]
      apply le_min
      · rw [hba j] at h3a
        have hpos : 0 < μ j - qlo j := by linarith [(hμ j).1]
        nlinarith [mul_le_mul_of_nonneg_right hkey hpos.le]
      · rw [hba j] at h2b
        nlinarith
    · have : ∑ j ∈ S, b j = t * ∑ j ∈ S, a j := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => hba j
      rw [this] at hF1
      have := le_of_mul_le_mul_left hF1 ht0
      linarith

lemma qc_var_le {n : ℕ} (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (S : Finset (Fin n)) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hSig : Sig.PosDef)
    (hε0 : 0 < ε) (hε1 : ε < 1) (P : Measure (Fin n → ℝ)) (hP : P ∈ covarianceSet qlo qhi μ Sig)
    (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ a : Fin n → ℝ, (a ⬝ᵥ (Sig⁻¹ *ᵥ a) ≤ (1 - ε) / ε ∧
          ∀ j, qLower qlo qhi μ ε j ≤ a j ∧ a j ≤ qUpper qlo qhi μ ε j) →
        ∑ j ∈ S, μ j + ∑ j ∈ S, a j ≤ R) :
    MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε) ≤ R := by
  have hprob := hP.1
  unfold MultistageStochastic.valueAtRisk
  set T := {y : ℝ | ENNReal.ofReal (1 - ε) ≤ P {ω | ∑ i ∈ S, ω i ≤ y}} with hT
  by_cases hb : BddBelow T
  · rcases Set.eq_empty_or_nonempty T with he | hne
    · rw [he, Real.sInf_empty]; exact hR0
    by_contra hcon
    push_neg at hcon
    set y := (R + sInf T) / 2
    have hy : y ∉ T := notMem_of_lt_csInf (by simp only [y]; linarith) hb
    simp only [hT, Set.mem_setOf_eq, not_le] at hy
    have hyr : P.real {q | ∑ i ∈ S, q i ≤ y} < 1 - ε := ENNReal.toReal_lt_of_lt_ofReal hy
    obtain ⟨b, t, ht, hF2, hF3, hF1, hF4⟩ := qc_ub qlo qhi μ Sig ε S P hP y
    have htε : ε < t := by rw [ht]; linarith
    have ht1 : t ≤ 1 := by rw [ht]; linarith [measureReal_nonneg (μ := P) (s := {q : Fin n → ℝ | ∑ i ∈ S, q i ≤ y})]
    obtain ⟨a, ha, hya⟩ := qc_ub2 qlo qhi μ Sig ε S hμ hSig hε0 hε1 y b t htε ht1 hF2 hF3 hF1 hF4
    have := hR a ha
    simp only [y] at hya
    linarith
  · rw [Real.sInf_of_not_bddBelow hb]; exact hR0

lemma qc_lb {n : ℕ} (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (S : Finset (Fin n)) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hSig : Sig.PosDef)
    (hε0 : 0 < ε) (hε1 : ε < 1) (q : Fin n → ℝ)
    (hq : q ⬝ᵥ (Sig⁻¹ *ᵥ q) ≤ (1 - ε) / ε ∧
          ∀ j, qLower qlo qhi μ ε j ≤ q j ∧ q j ≤ qUpper qlo qhi μ ε j)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ P ∈ covarianceSet qlo qhi μ Sig,
      ∑ j ∈ S, μ j + s * ∑ j ∈ S, q j ≤
        MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε) := by
  have h1ε : 0 < 1 - ε := by linarith
  set D := ε + s * (1 - ε) with hD
  have hDpos : 0 < D := by positivity
  set k := ε / (1 - ε) with hk
  set t := ε / D with ht
  have hk0 : 0 < k := div_pos hε0 h1ε
  have ht0 : 0 < t := div_pos hε0 hDpos
  have h1t : 1 - t = s * (1 - ε) / D := by simp only [t, D]; field_simp; ring
  have ht1 : 0 < 1 - t := by rw [h1t]; positivity
  have htε : 1 - t < 1 - ε := by
    rw [h1t, div_lt_iff₀ hDpos]; simp only [D]
    nlinarith [mul_pos (mul_pos hε0 h1ε) (by linarith : (0:ℝ) < 1 - s)]
  have hmean_id : t * s = (1 - t) * k := by rw [h1t]; simp only [t, k]; field_simp
  have hcoef : t * s ^ 2 + (1 - t) * k ^ 2 = k * s := by
    rw [h1t]; simp only [t, k, D]; field_simp; ring
  have hkr : k * ((1 - ε) / ε) = 1 := by simp only [k]; field_simp
  set H : Fin n → ℝ := fun j => μ j + s * q j with hH
  set L : Fin n → ℝ := fun j => μ j - k * q j with hL
  set P : Measure (Fin n → ℝ) :=
    ENNReal.ofReal t • Measure.dirac H + ENNReal.ofReal (1 - t) • Measure.dirac L with hP
  have hint : ∀ f : (Fin n → ℝ) → ℝ, ∫ x, f x ∂P = t * f H + (1 - t) * f L := by
    intro f
    rw [hP, integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
      integral_dirac, ENNReal.toReal_ofReal ht0.le, ENNReal.toReal_ofReal ht1.le]
    · simp
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
  have hmeas : ∀ A : Set (Fin n → ℝ),
      P A = ENNReal.ofReal t * A.indicator 1 H + ENNReal.ofReal (1 - t) * A.indicator 1 L := by
    intro A; simp [hP, Measure.dirac_apply]
  have htot : ENNReal.ofReal t + ENNReal.ofReal (1 - t) = 1 := by
    rw [← ENNReal.ofReal_add ht0.le ht1.le]; simp
  obtain ⟨hqS, hqb⟩ := hq
  have hr0 : 0 < (1 - ε) / ε := div_pos h1ε hε0
  have hHbox : H ∈ Set.Icc qlo qhi := by
    constructor <;> intro j <;> simp only [H]
    · have h1 := (hqb j).1; have := le_max_right (-((1 - ε) / ε * (qhi j - μ j))) (qlo j - μ j)
      simp only [qLower] at h1
      have hm := (hμ j).1
      nlinarith [mul_nonneg hs0.le (by linarith : (0:ℝ) ≤ q j - (qlo j - μ j)),
        mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) (by linarith : (0:ℝ) ≤ μ j - qlo j)]
    · have h1 := (hqb j).2; have := min_le_right ((1 - ε) / ε * (μ j - qlo j)) (qhi j - μ j)
      simp only [qUpper] at h1
      have hm := (hμ j).2
      nlinarith [mul_nonneg hs0.le (by linarith : (0:ℝ) ≤ (qhi j - μ j) - q j),
        mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) (by linarith : (0:ℝ) ≤ qhi j - μ j)]
  have hLbox : L ∈ Set.Icc qlo qhi := by
    constructor <;> intro j <;> simp only [L]
    · have h1 := (hqb j).2; have := min_le_left ((1 - ε) / ε * (μ j - qlo j)) (qhi j - μ j)
      simp only [qUpper] at h1
      have : k * q j ≤ k * ((1 - ε) / ε * (μ j - qlo j)) := mul_le_mul_of_nonneg_left (by linarith) hk0.le
      have e : k * ((1 - ε) / ε * (μ j - qlo j)) = μ j - qlo j := by rw [← mul_assoc, hkr, one_mul]
      linarith
    · have h1 := (hqb j).1; have := le_max_left (-((1 - ε) / ε * (qhi j - μ j))) (qlo j - μ j)
      simp only [qLower] at h1
      have : k * (-((1 - ε) / ε * (qhi j - μ j))) ≤ k * q j := mul_le_mul_of_nonneg_left (by linarith) hk0.le
      have e : k * (-((1 - ε) / ε * (qhi j - μ j))) = -(qhi j - μ j) := by
        rw [mul_neg, ← mul_assoc, hkr, one_mul]
      linarith
  have hT : Sigᵀ = Sig := by
    have := hSig.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨P, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · constructor; rw [hmeas]; simp [htot]
  · rw [hmeas, Set.indicator_of_mem hHbox, Set.indicator_of_mem hLbox]; simp [htot]
  · intro j; rw [hint]; simp only [H, L]
    linear_combination (q j) * hmean_id
  · set M0 : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => k * s * (q i * q j) with hM0
    have hM : centredSecondMoment μ P = M0 := by
      funext i j
      simp only [M0, of_apply]
      unfold centredSecondMoment
      rw [hint]; simp only [H, L]
      linear_combination (q i * q j) * hcoef
    rw [hM, posSemidef_iff_dotProduct_mulVec]
    constructor
    · ext i j
      simp only [conjTranspose_apply, star_trivial, Matrix.sub_apply, M0, of_apply]
      rw [show Sig j i = Sig i j from by rw [← transpose_apply Sig j i, hT]]
      ring
    · intro x
      simp only [star_trivial, sub_mulVec, dotProduct_sub]
      have hMx : M0 *ᵥ x = fun i => (k * s * (q ⬝ᵥ x)) * q i := by
        funext i; simp only [M0, of_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hMx]
      have e2 : x ⬝ᵥ (fun i => (k * s * (q ⬝ᵥ x)) * q i) = k * s * (x ⬝ᵥ q) ^ 2 := by
        simp only [dotProduct, Finset.mul_sum, sq, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e2]
      have hcs := qc_cs hSig x q
      have hA : 0 ≤ x ⬝ᵥ (Sig *ᵥ x) := by simpa using hSig.posSemidef.dotProduct_mulVec_nonneg x
      have h3 : (x ⬝ᵥ q) ^ 2 ≤ x ⬝ᵥ (Sig *ᵥ x) * ((1 - ε) / ε) :=
        hcs.trans (mul_le_mul_of_nonneg_left hqS hA)
      have h4 : k * (x ⬝ᵥ q) ^ 2 ≤ x ⬝ᵥ (Sig *ᵥ x) := by
        calc k * (x ⬝ᵥ q) ^ 2 ≤ k * (x ⬝ᵥ (Sig *ᵥ x) * ((1 - ε) / ε)) :=
              mul_le_mul_of_nonneg_left h3 hk0.le
          _ = x ⬝ᵥ (Sig *ᵥ x) := by rw [mul_comm (x ⬝ᵥ _), ← mul_assoc, hkr, one_mul]
      have h5 : 0 ≤ k * (x ⬝ᵥ q) ^ 2 := by positivity
      nlinarith
  · -- VaR lower bound
    have hXH : ∑ i ∈ S, H i = ∑ j ∈ S, μ j + s * ∑ j ∈ S, q j := by
      simp only [H]; rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [← hXH]
    unfold MultistageStochastic.valueAtRisk
    apply le_csInf
    · refine ⟨max (∑ i ∈ S, H i) (∑ i ∈ S, L i), ?_⟩
      simp only [Set.mem_setOf_eq]
      rw [hmeas, Set.indicator_of_mem (by simp), Set.indicator_of_mem (by simp)]
      simp only [Pi.one_apply, mul_one, htot]
      exact ENNReal.ofReal_le_one.2 (by linarith)
    · intro y hy
      simp only [Set.mem_setOf_eq] at hy
      by_contra hlt
      push_neg at hlt
      rw [hmeas, Set.indicator_of_notMem (by simp; linarith)] at hy
      simp only [mul_zero, zero_add] at hy
      have : ENNReal.ofReal (1 - t) * Set.indicator {ω : Fin n → ℝ | ∑ i ∈ S, ω i ≤ y} 1 L ≤
          ENNReal.ofReal (1 - t) := by
        by_cases hL' : L ∈ {ω : Fin n → ℝ | ∑ i ∈ S, ω i ≤ y}
        · simp [Set.indicator_of_mem hL']
        · simp [Set.indicator_of_notMem hL']
      have h2 : ENNReal.ofReal (1 - t) < ENNReal.ofReal (1 - ε) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 htε
      exact absurd (hy.trans this) (not_le.2 h2)

end qc

theorem qcqp_core {n : ℕ} (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (S : Finset (Fin n))
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hSig : Sig.PosDef)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    worstCaseVaR (covarianceSet qlo qhi μ Sig) ε S =
      sSup ((fun q : Fin n → ℝ => ∑ j ∈ S, μ j + ∑ j ∈ S, q j) ''
        {q | q ⬝ᵥ (Sig⁻¹ *ᵥ q) ≤ (1 - ε) / ε ∧
          ∀ j, qLower qlo qhi μ ε j ≤ q j ∧ q j ≤ qUpper qlo qhi μ ε j}) := by
  set F := {q : Fin n → ℝ | q ⬝ᵥ (Sig⁻¹ *ᵥ q) ≤ (1 - ε) / ε ∧
          ∀ j, qLower qlo qhi μ ε j ≤ q j ∧ q j ≤ qUpper qlo qhi μ ε j} with hFdef
  set G := (fun q : Fin n → ℝ => ∑ j ∈ S, μ j + ∑ j ∈ S, q j) '' F with hGdef
  have hr : 0 < (1 - ε) / ε := div_pos (by linarith) hε0
  have hF0 : (0 : Fin n → ℝ) ∈ F := by
    refine ⟨by simp; exact hr.le, fun j => ⟨?_, ?_⟩⟩
    · simp only [qLower, Pi.zero_apply]
      apply max_le
      · have : 0 ≤ (1 - ε) / ε * (qhi j - μ j) := mul_nonneg hr.le (by linarith [(hμ j).2])
        linarith
      · linarith [(hμ j).1]
    · simp only [qUpper, Pi.zero_apply]
      apply le_min
      · exact mul_nonneg hr.le (by linarith [(hμ j).1])
      · linarith [(hμ j).2]
  have hGb : BddAbove G := by
    refine ⟨∑ j ∈ S, μ j + ∑ j ∈ S, (qhi j - μ j), ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have : ∑ j ∈ S, q j ≤ ∑ j ∈ S, (qhi j - μ j) :=
      Finset.sum_le_sum fun j _ => (hq.2 j).2.trans (min_le_right _ _)
    simp only; linarith
  have hGne : G.Nonempty := ⟨_, 0, hF0, rfl⟩
  set R := sSup G
  have hR : ∀ a ∈ F, ∑ j ∈ S, μ j + ∑ j ∈ S, a j ≤ R := fun a ha => le_csSup hGb ⟨a, ha, rfl⟩
  have hμ0 : 0 ≤ ∑ j ∈ S, μ j := Finset.sum_nonneg fun j _ => by linarith [hqlo j, (hμ j).1]
  have hR0 : 0 ≤ R := by have := hR 0 hF0; simp at this; linarith
  have hV : ∀ P ∈ covarianceSet qlo qhi μ Sig,
      MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε) ≤ R :=
    fun P hP => qc_var_le qlo qhi μ Sig ε S hμ hSig hε0 hε1 P hP R hR0 hR
  obtain ⟨P0, hP0, -⟩ := qc_lb qlo qhi μ Sig ε S hμ hSig hε0 hε1 0 hF0 (1/2) (by norm_num) (by norm_num)
  have hWne : ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) ''
      covarianceSet qlo qhi μ Sig).Nonempty := ⟨_, P0, hP0, rfl⟩
  have hWb : BddAbove ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) ''
      covarianceSet qlo qhi μ Sig) := ⟨R, by rintro _ ⟨P, hP, rfl⟩; exact hV P hP⟩
  unfold worstCaseVaR
  apply le_antisymm
  · exact csSup_le hWne (by rintro _ ⟨P, hP, rfl⟩; exact hV P hP)
  · refine csSup_le hGne ?_
    rintro _ ⟨q, hq, rfl⟩
    have hs : ∀ s : ℝ, 0 < s → s < 1 → ∑ j ∈ S, μ j + s * ∑ j ∈ S, q j ≤
        sSup ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) ''
          covarianceSet qlo qhi μ Sig) := by
      intro s hs0 hs1
      obtain ⟨P, hP, hle⟩ := qc_lb qlo qhi μ Sig ε S hμ hSig hε0 hε1 q hq s hs0 hs1
      exact hle.trans (le_csSup hWb ⟨P, hP, rfl⟩)
    simp only
    set W := sSup ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) ''
          covarianceSet qlo qhi μ Sig)
    set Q := ∑ j ∈ S, q j
    rcases le_or_gt Q 0 with hQ | hQ
    · have := hs (1/2) (by norm_num) (by norm_num); linarith
    · by_contra hcon
      push_neg at hcon
      set d := ∑ j ∈ S, μ j + Q - W
      have hd : 0 < d := by simp only [d]; linarith
      set s := max (1/2 : ℝ) (1 - d / (2 * Q))
      have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have hdq : 0 < d / (2 * Q) := by positivity
      have hs1 : s < 1 := max_lt (by norm_num) (by linarith)
      have h1 := hs s hs0 hs1
      have h2 : 1 - d / (2 * Q) ≤ s := le_max_right _ _
      have h3 : (1 - d / (2 * Q)) * Q = Q - d / 2 := by field_simp
      have h4 : (1 - d / (2 * Q)) * Q ≤ s * Q := mul_le_mul_of_nonneg_right h2 hQ.le
      simp only [d] at h3
      linarith

end DRCVRP.Covariance

open DRCVRP.Covariance


theorem solution {n : ℕ} (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (S : Finset (Fin n))
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hSig : Sig.PosDef)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    worstCaseVaR (covarianceSet qlo qhi μ Sig) ε S =
      sSup ((fun q : Fin n → ℝ => ∑ j ∈ S, μ j + ∑ j ∈ S, q j) ''
        {q | q ⬝ᵥ (Sig⁻¹ *ᵥ q) ≤ (1 - ε) / ε ∧
          ∀ j, qLower qlo qhi μ ε j ≤ q j ∧ q j ≤ qUpper qlo qhi μ ε j}) := by
  exact qcqp_core qlo qhi μ Sig ε S hqlo hμ hSig hε0 hε1
