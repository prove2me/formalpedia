-- Prove2me | solution 1 for CHMSPricing.SpmMatroid.sum_price_mul_prob_le_two_spmRevenue
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:17:47.709182+00:00
-- url     : https://prove2.me/submissions/1219121b-b705-46ee-98d0-e26f3412418a

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Spm



namespace CHMSPricing.SpmMatroid
open MeasureTheory Set

namespace RevAux

variable (D : ValueDist)

lemma f_intOn : IntegrableOn D.f (Icc D.lo D.hi) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le D.lo_lt_hi.le).1 D.f_intervalIntegrable

lemma setInt_f : ∫ x in Icc D.lo D.hi, D.f x = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le D.lo_lt_hi.le,
    D.f_integral]

lemma law_univ : D.law univ = 1 := by
  rw [ValueDist.law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (f_intOn D), setInt_f]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (D.f_pos x hx).le

instance law_prob : IsProbabilityMeasure D.law := ⟨law_univ D⟩

lemma law_ac : D.law ≪ volume.restrict (Icc D.lo D.hi) := withDensity_absolutelyContinuous _ _

lemma law_ae_mem : ∀ᵐ x ∂D.law, x ∈ Icc D.lo D.hi :=
  law_ac D (ae_restrict_mem measurableSet_Icc)

lemma law_singleton (t : ℝ) : D.law {t} = 0 :=
  law_ac D (Measure.restrict_le_self.absolutelyContinuous (by simp))

lemma law_Ici (x : ℝ) : (D.law (Ici x)).toReal = 1 - D.cdf x := by
  rw [ValueDist.cdf, ← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    measure_congr (Iio_ae_eq_Iic' (law_singleton D x))]
  simp

end RevAux

section Multi
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance prior_prob (D : ι → ValueDist) : IsProbabilityMeasure (prior D) := by
  unfold prior; infer_instance

lemma prior_update (D : ι → ValueDist) (i : ι) :
    ((prior D).prod (D i).law).map (fun p => Function.update p.1 i p.2) = prior D := by
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (univ.pi s) =
      (univ.pi (Function.update s i univ)) ×ˢ s i := by
    ext ⟨v, x⟩
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [hj] using h1 j
  rw [hpre, Measure.prod_prod, prior, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (D j).law (s j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma integral_prior_update (D : ι → ValueDist) (i : ι) (F : (ι → ℝ) → ℝ)
    (hF : Integrable F (prior D)) :
    ∫ v, F v ∂(prior D) = ∫ v, ∫ x, F (Function.update v i x) ∂(D i).law ∂(prior D) := by
  have hmeas : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) := measurable_update'
  conv_lhs => rw [← prior_update D i]
  rw [← prior_update D i] at hF
  rw [integral_map hmeas.aemeasurable hF.aestronglyMeasurable]
  exact integral_prod (fun p : (ι → ℝ) × ℝ => F (Function.update p.1 i p.2))
    ((integrable_map_measure hF.aestronglyMeasurable hmeas.aemeasurable).1 hF)

end Multi

namespace MatAux
variable {n : ℕ}
lemma A_succ (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k : ℕ)
    (hk : k < n) :
    spmServedBefore J σ p v (k+1) = spmStep J p v (spmServedBefore J σ p v k) (σ ⟨k, hk⟩) := by
  have htake : (List.finRange n).take (k+1) = (List.finRange n).take k ++ [⟨k, hk⟩] := by
    rw [List.take_add_one]
    congr 1
    simp [hk]
  unfold spmServedBefore
  rw [htake, List.foldl_append]
  rfl

lemma A_zero (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) :
    spmServedBefore J σ p v 0 = ∅ := by simp [spmServedBefore]

lemma A_dep (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v w : Fin n → ℝ) (k : ℕ)
    (hk : k ≤ n) (h : ∀ j : Fin n, j.val < k → (p (σ j) ≤ v (σ j) ↔ p (σ j) ≤ w (σ j))) :
    spmServedBefore J σ p v k = spmServedBefore J σ p w k := by
  induction k with
  | zero => rw [A_zero, A_zero]
  | succ k ih =>
    rw [A_succ J σ p v k hk, A_succ J σ p w k hk, ih (by omega) (fun j hj => h j (by omega))]
    have hiff := h ⟨k, hk⟩ (by simp)
    unfold spmStep
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto)

lemma A_feas (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k : ℕ)
    (hk : k ≤ n) : J.Feasible (spmServedBefore J σ p v k) := by
  induction k with
  | zero => rw [A_zero]; exact J.feasible_empty
  | succ k ih =>
    rw [A_succ J σ p v k hk]
    unfold spmStep
    split_ifs with h
    · exact h.1
    · exact ih (by omega)

lemma A_mem (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (j : Fin n)
    (m : ℕ) (hm : m ≤ n) :
    σ j ∈ spmServedBefore J σ p v m ↔ j.val < m ∧ σ j ∈ spmServedBefore J σ p v (j.val+1) := by
  induction m with
  | zero => simp [A_zero]
  | succ m ih =>
    have hmn : m < n := hm
    rw [A_succ J σ p v m hmn]
    unfold spmStep
    rcases lt_trichotomy j.val m with hjm | hjm | hjm
    · have hne : σ j ≠ σ ⟨m, hmn⟩ := fun e => by
        have := congrArg Fin.val (σ.injective e); simp at this; omega
      have := ih hmn.le
      split_ifs <;> simp only [Finset.mem_insert, hne, false_or, this] <;>
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
    · have hj : j = ⟨m, hmn⟩ := Fin.ext hjm
      subst hj
      rw [A_succ J σ p v m hmn]
      unfold spmStep
      simp
    · have hne : σ j ≠ σ ⟨m, hmn⟩ := fun e => by
        have := congrArg Fin.val (σ.injective e); simp at this; omega
      have := ih hmn.le
      split_ifs <;> simp only [Finset.mem_insert, hne, false_or, this] <;>
        constructor <;> rintro ⟨h1, h2⟩ <;> omega

lemma A_mono (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k m : ℕ)
    (hkm : k ≤ m) (hm : m ≤ n) :
    spmServedBefore J σ p v k ⊆ spmServedBefore J σ p v m := by
  induction m with
  | zero =>
    have : k = 0 := by omega
    subst this; exact subset_rfl
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hkm with h | h
    · rw [h]
    · refine (ih (by omega) (by omega)).trans ?_
      rw [A_succ J σ p v m (by omega)]
      unfold spmStep
      split_ifs
      · exact Finset.subset_insert _ _
      · exact subset_rfl

lemma abel_nonneg (a d : ℕ → ℝ) (ha : ∀ k, a (k+1) ≤ a k) (ha0 : ∀ k, 0 ≤ a k)
    (N : ℕ) (hD : ∀ m ≤ N, 0 ≤ ∑ k ∈ Finset.range m, d k) :
    0 ≤ ∑ k ∈ Finset.range N, a k * d k := by
  have key : ∀ M ≤ N, a M * ∑ k ∈ Finset.range M, d k ≤ ∑ k ∈ Finset.range M, a k * d k := by
    intro M
    induction M with
    | zero => intro _; simp
    | succ M ih =>
      intro hM
      have h1 := ih (by omega)
      have h2 := hD (M+1) hM
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [Finset.sum_range_succ] at h2
      have : a (M+1) * (∑ k ∈ Finset.range M, d k + d M) ≤
          a M * (∑ k ∈ Finset.range M, d k + d M) := mul_le_mul_of_nonneg_right (ha M) h2
      nlinarith
  exact le_trans (mul_nonneg (ha0 N) (hD N le_rfl)) (key N le_rfl)

/-- extension of a `Fin n`-indexed function to `ℕ` by zero -/
noncomputable def ext (g : Fin n → ℝ) (k : ℕ) : ℝ := if h : k < n then g ⟨k, h⟩ else 0

lemma sum_prefix (g : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∑ k : Fin n, (if k.val < m then g k else 0) = ∑ k ∈ Finset.range m, ext g k := by
  have h1 := Fin.sum_univ_eq_sum_range (fun k => if k < m then ext g k else 0) n
  have h2 : ∑ k : Fin n, (if k.val < m then g k else 0) =
      ∑ k : Fin n, (if k.val < m then ext g k.val else 0) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [ext]
  rw [h2, h1, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext k; simp [Finset.mem_filter]; omega

lemma sum_all (g : Fin n → ℝ) : ∑ k : Fin n, g k = ∑ k ∈ Finset.range n, ext g k := by
  rw [← sum_prefix g n le_rfl]
  simp

/-- prefix inequality -/
lemma prefix_ineq (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, q i ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∑ i ∈ (spmBlocked J σ p v).filter (fun i => (σ.symm i).val < m), q i ≤
      ((spmServedBefore J σ p v m).card : ℝ) := by
  classical
  set Am := spmServedBefore J σ p v m with hAm
  set Bm := (spmBlocked J σ p v).filter (fun i => (σ.symm i).val < m) with hBm
  have hrank : J.rank (Am ∪ Bm) ≤ Am.card := by
    unfold SetSystem.rank
    refine Finset.sup_le (fun F hF => ?_)
    rw [Finset.mem_filter, Finset.mem_powerset] at hF
    by_contra hlt
    push_neg at hlt
    obtain ⟨e, he, hfe⟩ := hJ F Am hF.2 (A_feas J σ p v m hm) hlt
    rw [Finset.mem_sdiff] at he
    have heB : e ∈ Bm := by
      rcases Finset.mem_union.1 (hF.1 he.1) with h | h
      · exact absurd h he.2
      · exact h
    rw [hBm, Finset.mem_filter] at heB
    have hbl : ¬ J.Feasible (insert e (spmServedBefore J σ p v (σ.symm e : ℕ))) := by
      have := heB.1
      simp only [spmBlocked, spmOffered] at this
      exact (Finset.mem_filter.1 this).2
    exact hbl (J.feasible_mono (Finset.insert_subset_insert _
      (A_mono J σ p v _ m heB.2.le hm)) hfe)
  calc ∑ i ∈ Bm, q i ≤ ∑ i ∈ Am ∪ Bm, q i :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun i _ _ => hq0 i)
    _ ≤ (J.rank (Am ∪ Bm) : ℝ) := hqr _
    _ ≤ Am.card := by exact_mod_cast hrank

theorem blocked_core (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, q i ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) (v : Fin n → ℝ) :
    ∑ i ∈ spmBlocked J σ p v, p i * q i ≤
      ∑ i ∈ spmServed J σ p v, p i := by
  classical
  set B := spmBlocked J σ p v
  set A := spmServed J σ p v
  let x : Fin n → ℝ := fun k => if σ k ∈ B then q (σ k) else 0
  let y : Fin n → ℝ := fun k => if σ k ∈ A then 1 else 0
  let pk : Fin n → ℝ := fun k => p (σ k)
  have hL : ∑ i ∈ B, p i * q i = ∑ k : Fin n, pk k * x k := by
    rw [← Finset.univ_inter B, ← Finset.sum_ite_mem, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [pk, x, mul_ite, mul_zero]
  have hR : ∑ i ∈ A, p i = ∑ k : Fin n, pk k * y k := by
    rw [← Finset.univ_inter A, ← Finset.sum_ite_mem, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [pk, y, mul_ite, mul_zero, mul_one]
  have hext : ∀ g h : Fin n → ℝ, ∑ k : Fin n, g k * h k =
      ∑ k ∈ Finset.range n, ext g k * ext h k := by
    intro g h
    rw [sum_all (fun k => g k * h k)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold ext; split_ifs <;> simp
  have hX : ∀ m ≤ n, ∑ k ∈ Finset.range m, ext x k =
      ∑ i ∈ B.filter (fun i => (σ.symm i).val < m), q i := by
    intro m hm
    rw [← sum_prefix x m hm, ← Finset.univ_inter (B.filter _), ← Finset.sum_ite_mem]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [x, Finset.mem_filter, Equiv.symm_apply_apply]
    split_ifs <;> tauto
  have hY : ∀ m ≤ n, ∑ k ∈ Finset.range m, ext y k =
      ((spmServedBefore J σ p v m).card : ℝ) := by
    intro m hm
    rw [← sum_prefix y m hm, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
      ← Finset.univ_inter (spmServedBefore J σ p v m), ← Finset.sum_ite_mem]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [y, A, spmServed]
    have h1 := A_mem J σ p v k m hm
    have h2 := A_mem J σ p v k n le_rfl
    simp only [k.isLt, true_and] at h2
    by_cases c1 : (k : ℕ) < m <;> by_cases c2 : σ k ∈ spmServedBefore J σ p v n <;>
      simp only [c1, c2, if_true, if_false] <;> simp_all
  have key := abel_nonneg (ext pk) (fun k => ext y k - ext x k) (by
      intro k
      unfold ext
      split_ifs with h1 h2
      · exact hσ _ _ (Fin.mk_le_mk.2 (by omega))
      · omega
      · exact hp0 _
      · exact le_rfl)
    (by intro k; unfold ext; split_ifs <;> simp [pk, hp0]) n (by
      intro m hm
      rw [Finset.sum_sub_distrib, hX m hm, hY m hm, sub_nonneg]
      exact prefix_ineq J hJ q hq0 hqr σ p v m hm)
  rw [hL, hR, hext, hext]
  simp only [mul_sub, Finset.sum_sub_distrib, sub_nonneg] at key
  exact key


lemma meas_A (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ)
    (P : Finset (Fin n) → Prop) (k : ℕ) (hk : k ≤ n) :
    MeasurableSet {v : Fin n → ℝ | P (spmServedBefore J σ p v k)} := by
  classical
  let acc : (Fin n → ℝ) → (Fin n → Bool) := fun v i => decide (p i ≤ v i)
  have hacc : Measurable acc := by
    refine measurable_pi_lambda _ (fun i => ?_)
    refine measurable_to_countable' (fun b => ?_)
    cases b
    · have : (fun v : Fin n → ℝ => decide (p i ≤ v i)) ⁻¹' {false} = {v | v i < p i} := by
        ext v; simp
      rw [this]; exact measurableSet_lt (measurable_pi_apply i) measurable_const
    · have : (fun v : Fin n → ℝ => decide (p i ≤ v i)) ⁻¹' {true} = {v | p i ≤ v i} := by
        ext v; simp
      rw [this]; exact measurableSet_le measurable_const (measurable_pi_apply i)
  have heq : {v : Fin n → ℝ | P (spmServedBefore J σ p v k)} =
      acc ⁻¹' {b | ∃ w, acc w = b ∧ P (spmServedBefore J σ p w k)} := by
    ext v
    simp only [mem_setOf_eq, mem_preimage]
    constructor
    · intro h; exact ⟨v, rfl, h⟩
    · rintro ⟨w, hw, hP⟩
      rwa [A_dep J σ p v w k hk (fun j _ => by
        have := congrFun hw (σ j); simp [acc] at this; exact this.symm)]
  rw [heq]
  exact hacc (Set.toFinite _).measurableSet

lemma mem_succ_iff (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) (k : Fin n) :
    σ k ∈ spmServedBefore J σ p v (k.val+1) ↔
      p (σ k) ≤ v (σ k) ∧ J.Feasible (insert (σ k) (spmServedBefore J σ p v k.val)) := by
  classical
  have hnot : σ k ∉ spmServedBefore J σ p v k.val := by
    rw [A_mem _ σ p v k k.val k.isLt.le]; simp
  have hkk : (⟨k.val, k.isLt⟩ : Fin n) = k := rfl
  rw [A_succ _ σ p v k.val k.isLt, hkk]
  unfold spmStep
  split_ifs with h
  · simp only [Finset.mem_insert, true_or, true_iff]
    exact ⟨h.2, h.1⟩
  · simp only [hnot, false_iff]
    rintro ⟨h1, h2⟩
    exact h ⟨h2, h1⟩

def Sset (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (j : Fin n) :
    Set (Fin n → ℝ) :=
  {v | σ j ∈ spmServedBefore J σ p v (j.val+1)}

def Tset (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (k : Fin n) :
    Set (Fin n → ℝ) :=
  {v | J.Feasible (insert (σ k) (spmServedBefore J σ p v k.val))}

lemma Sset_meas (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (j : Fin n) :
    MeasurableSet (Sset J σ p j) :=
  meas_A J σ p (fun A => σ j ∈ A) _ j.isLt

lemma Tset_meas (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (k : Fin n) :
    MeasurableSet (Tset J σ p k) :=
  meas_A J σ p (fun A => J.Feasible (insert (σ k) A)) _ k.isLt.le

lemma indep (D : Fin n → ValueDist) (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n))
    (p : Fin n → ℝ) (k : Fin n) :
    (prior D (Sset J σ p k)).toReal =
      ((D (σ k)).law (Ici (p (σ k)))).toReal * (prior D (Tset J σ p k)).toReal := by
  classical
  have hS := Sset_meas J σ p k
  have hT := Tset_meas J σ p k
  have hI : Integrable ((Sset J σ p k).indicator (1 : (Fin n → ℝ) → ℝ)) (prior D) :=
    (integrable_const (1:ℝ)).indicator hS
  rw [← measureReal_def, ← integral_indicator_one hS, integral_prior_update D (σ k) _ hI]
  have hTu : ∀ v x, (Function.update v (σ k) x ∈ Tset J σ p k ↔ v ∈ Tset J σ p k) := by
    intro v x
    simp only [Tset, mem_setOf_eq]
    rw [A_dep _ σ p (Function.update v (σ k) x) v k.val k.isLt.le (fun j hj => by
      have hne : σ j ≠ σ k := fun e => by
        have := σ.injective e; rw [this] at hj; exact lt_irrefl _ hj
      rw [Function.update_of_ne hne])]
  have hinner : ∀ v, ∫ x, (Sset J σ p k).indicator 1 (Function.update v (σ k) x)
      ∂(D (σ k)).law = (Tset J σ p k).indicator 1 v *
        ((D (σ k)).law (Ici (p (σ k)))).toReal := by
    intro v
    have : (fun x => (Sset J σ p k).indicator (1 : (Fin n → ℝ) → ℝ)
        (Function.update v (σ k) x)) =
        fun x => (Tset J σ p k).indicator 1 v * (Ici (p (σ k))).indicator 1 x := by
      funext x
      simp only [Set.indicator, Sset, mem_setOf_eq, mem_succ_iff, Function.update_self, mem_Ici,
        Pi.one_apply]
      have := hTu v x
      simp only [Tset, mem_setOf_eq] at this
      by_cases h1 : p (σ k) ≤ x <;> by_cases h2 : v ∈ Tset J σ p k <;>
        simp only [Tset, mem_setOf_eq] at h2 <;> simp [h1, h2, this, Tset]
    rw [this, integral_const_mul, integral_indicator_one measurableSet_Ici, measureReal_def]
  simp_rw [hinner]
  rw [integral_mul_const, integral_indicator_one hT, measureReal_def, mul_comm]

lemma served_sum (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) :
    ∑ i ∈ spmServed J σ p v, p i =
      ∑ k : Fin n, (Sset J σ p k).indicator (fun _ => p (σ k)) v := by
  classical
  have hA : spmServed J σ p v =
      Finset.univ.filter (· ∈ spmServed J σ p v) := by ext; simp
  rw [hA, Finset.sum_filter, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Set.indicator, Sset, mem_setOf_eq, spmServed]
  simp only [A_mem _ σ p v k n le_rfl, k.isLt, true_and]

lemma served_integrable (D : Fin n → ValueDist) (J : SetSystem (Fin n))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    Integrable (fun v => ∑ i ∈ spmServed J σ p v, p i) (prior D) := by
  simp_rw [served_sum]
  exact integrable_finset_sum _ (fun k _ => (integrable_const _).indicator (Sset_meas J σ p k))

lemma rev_eq (D : Fin n → ValueDist) (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n))
    (p : Fin n → ℝ) :
    spmRevenue D J σ p = ∑ k : Fin n, p (σ k) * (prior D (Sset J σ p k)).toReal := by
  unfold spmRevenue
  simp_rw [served_sum]
  rw [integral_finset_sum _ (fun k _ => (integrable_const _).indicator (Sset_meas J σ p k))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_indicator_const _ (Sset_meas J σ p k), measureReal_def, smul_eq_mul, mul_comm]

theorem offer_core (D : Fin n → ValueDist) (J : SetSystem (Fin n))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    spmRevenue D J σ p =
      ∑ i, (prior D {v | spmOffered J σ p v i}).toReal * (1 - (D i).cdf (p i)) * p i := by
  rw [rev_eq]
  conv_rhs => rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [indep, RevAux.law_Ici]
  have : {v | spmOffered J σ p v (σ k)} = Tset J σ p k := by
    ext v; simp [spmOffered, Tset]
  rw [this]; ring

theorem two_core (D : Fin n → ValueDist)
    (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi)
    (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, (1 - (D i).cdf (p i)) ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    ∑ i, p i * (1 - (D i).cdf (p i)) ≤ 2 * spmRevenue D J σ p := by
  classical
  set q : Fin n → ℝ := fun i => 1 - (D i).cdf (p i) with hqdef
  have hq0 : ∀ i, 0 ≤ q i := fun i => by
    simp only [hqdef]; rw [← RevAux.law_Ici]; exact ENNReal.toReal_nonneg
  have hp0 : ∀ i, 0 ≤ p i := fun i => (D i).lo_nonneg.trans (hp i).1
  let O : Fin n → Set (Fin n → ℝ) := fun i => {v | spmOffered J σ p v i}
  have hO : ∀ i, MeasurableSet (O i) := fun i =>
    meas_A J σ p (fun A => J.Feasible (insert i A)) (σ.symm i) (σ.symm i).isLt.le
  let c : Fin n → ℝ := fun i => (prior D (O i)).toReal
  have hblk : ∀ v, ∑ i ∈ spmBlocked J σ p v, p i * q i =
      ∑ i, (O i)ᶜ.indicator (fun _ => p i * q i) v := by
    intro v
    unfold spmBlocked
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Set.indicator, O]
  have hIb : ∀ i, Integrable ((O i)ᶜ.indicator (fun _ => p i * q i)) (prior D) := fun i =>
    (integrable_const _).indicator (hO i).compl
  have hint : ∫ v, ∑ i ∈ spmBlocked J σ p v, p i * q i ∂(prior D) =
      ∑ i, (1 - c i) * (p i * q i) := by
    simp_rw [hblk]
    rw [integral_finset_sum _ (fun i _ => hIb i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_indicator_const _ (hO i).compl, measureReal_def, smul_eq_mul,
      prob_compl_eq_one_sub (hO i), ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
    simp [c]
  have hle : ∫ v, ∑ i ∈ spmBlocked J σ p v, p i * q i ∂(prior D) ≤ spmRevenue D J σ p := by
    unfold spmRevenue
    refine integral_mono ?_ (served_integrable D J σ p)
      (fun v => blocked_core J hJ q hq0 hqr σ p hp0 hσ v)
    simp_rw [hblk]
    exact integrable_finset_sum _ (fun i _ => hIb i)
  have hoff := offer_core D J σ p
  have hsplit : ∑ i, p i * q i = ∑ i, c i * q i * p i + ∑ i, (1 - c i) * (p i * q i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have : ∑ i, c i * q i * p i = spmRevenue D J σ p := hoff.symm
  change ∑ i, p i * q i ≤ _
  linarith

end MatAux
end CHMSPricing.SpmMatroid

open CHMSPricing.SpmMatroid


theorem solution {n : ℕ} (D : Fin n → ValueDist)
    (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi)
    (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, (1 - (D i).cdf (p i)) ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    ∑ i, p i * (1 - (D i).cdf (p i)) ≤ 2 * spmRevenue D J σ p := by
  exact MatAux.two_core D J hJ p hp hqr σ hσ
