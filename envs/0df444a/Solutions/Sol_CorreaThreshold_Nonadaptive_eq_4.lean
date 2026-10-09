-- Prove2me | solution 1 for CorreaThreshold.Nonadaptive.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T17:50:07.540524+00:00
-- url     : https://prove2.me/submissions/7a6661e7-905a-4a06-89d1-9fb16892f29b

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Bernoulli

set_option autoImplicit false
open CorreaThreshold.Nonadaptive
namespace RandomThresholdBernoulli
open scoped Classical
def weight {n : ℕ} (q : Fin n → ℝ) (T : Finset (Fin n)) : ℝ :=
  (∏ i ∈ T, q i) * (∏ i ∈ Tᶜ, (1-q i))
lemma sum_weight {n : ℕ} (q : Fin n → ℝ) : (∑ T : Finset (Fin n), weight q T) = 1 := by
  unfold weight
  rw [← Fintype.prod_add]
  have he : ∀ i, q i+(1-q i) = 1 := by intro i; ring
  simp only [he,Finset.prod_const_one]
lemma weight_nonneg {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (T : Finset (Fin n)) : 0 ≤ weight q T := by
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i hi => (hq i).1
  · exact Finset.prod_nonneg fun i hi => sub_nonneg.mpr (hq i).2
lemma bernExp_const {n : ℕ} (q : Fin n → ℝ) (c : ℝ) : bernExp q (fun _ => c) = c := by
  change (∑ T : Finset (Fin n), weight q T*c) = c
  rw [← Finset.sum_mul,sum_weight,one_mul]
lemma bernExp_mono {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (f g : Finset (Fin n) → ℝ) (h : ∀ T, f T ≤ g T) : bernExp q f ≤ bernExp q g := by
  apply Finset.sum_le_sum
  intro T hT
  exact mul_le_mul_of_nonneg_left (h T) (weight_nonneg q hq T)
lemma bernExp_le_const {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (g : Finset (Fin n) → ℝ) (c : ℝ) (h : ∀ T, g T ≤ c) : bernExp q g ≤ c := by
  exact (bernExp_mono q hq g (fun _ => c) h).trans_eq (bernExp_const q c)
end RandomThresholdBernoulli
#print axioms RandomThresholdBernoulli.sum_weight
#print axioms RandomThresholdBernoulli.weight_nonneg
#print axioms RandomThresholdBernoulli.bernExp_const
#print axioms RandomThresholdBernoulli.bernExp_mono
#print axioms RandomThresholdBernoulli.bernExp_le_const

set_option autoImplicit false
open CorreaThreshold.Nonadaptive RandomThresholdBernoulli
namespace RandomThresholdCoordinate
open scoped Classical
lemma complement_update {n : ℕ} (q : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    (fun j => 1 - Function.update q i x j) = Function.update (fun j => 1-q j) i (1-x) := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h]
lemma weight_update_affine {n : ℕ} (q : Fin n → ℝ) (i : Fin n) (x : ℝ)
    (S : Finset (Fin n)) :
    weight (Function.update q i x) S =
      x * weight (Function.update q i 1) S + (1-x) * weight (Function.update q i 0) S := by
  unfold weight
  simp_rw [complement_update]
  by_cases hi : i ∈ S
  · have hn : i ∉ Sᶜ := by simpa using hi
    rw [Finset.prod_update_of_mem hi, Finset.prod_update_of_notMem hn,
      Finset.prod_update_of_mem hi, Finset.prod_update_of_notMem hn,
      Finset.prod_update_of_mem hi, Finset.prod_update_of_notMem hn]
    ring
  · have hc : i ∈ Sᶜ := by simpa using hi
    rw [Finset.prod_update_of_notMem hi, Finset.prod_update_of_mem hc,
      Finset.prod_update_of_notMem hi, Finset.prod_update_of_mem hc,
      Finset.prod_update_of_notMem hi, Finset.prod_update_of_mem hc]
    ring
lemma bernExp_update_affine {n : ℕ} (q : Fin n → ℝ) (i : Fin n) (x : ℝ)
    (g : Finset (Fin n) → ℝ) :
    bernExp (Function.update q i x) g = x * bernExp (Function.update q i 1) g +
      (1-x) * bernExp (Function.update q i 0) g := by
  change (∑ S : Finset (Fin n), weight (Function.update q i x) S*g S) =
    x*(∑ S : Finset (Fin n), weight (Function.update q i 1) S*g S) +
    (1-x)*(∑ S : Finset (Fin n), weight (Function.update q i 0) S*g S)
  simp_rw [weight_update_affine q i x]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  ring
end RandomThresholdCoordinate
#print axioms RandomThresholdCoordinate.complement_update
#print axioms RandomThresholdCoordinate.weight_update_affine
#print axioms RandomThresholdCoordinate.bernExp_update_affine

set_option autoImplicit false
open CorreaThreshold.Nonadaptive RandomThresholdCoordinate
namespace RandomThresholdEndpoint
open scoped Classical
lemma bernExp_endpoint {n : ℕ} (p : Fin n → ℝ) (i : Fin n) (x u : ℝ)
    (g : Finset (Fin n) → ℝ) (hx : 0 ≤ x ∧ x ≤ u) :
    ∃ y : ℝ, (y = 0 ∨ y = u) ∧
      bernExp (Function.update p i x) g ≤ bernExp (Function.update p i y) g := by
  by_cases h : bernExp (Function.update p i 0) g ≤ bernExp (Function.update p i 1) g
  · refine ⟨u, Or.inr rfl, ?_⟩
    rw [bernExp_update_affine p i x, bernExp_update_affine p i u]
    have hh := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr h)
    nlinarith
  · refine ⟨0, Or.inl rfl, ?_⟩
    rw [bernExp_update_affine p i x]
    have hh := mul_nonneg hx.1 (sub_nonneg.mpr (le_of_not_ge h))
    nlinarith
lemma bernExp_round_subset {n : ℕ} (q π : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ q i)
    (g : Finset (Fin n) → ℝ) (T : Finset (Fin n)) :
    ∃ v : Fin n → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ q i) ∧
      (∀ i ∈ T, v i = 0 ∨ v i = q i) ∧ bernExp π g ≤ bernExp v g := by
  induction T using Finset.induction_on with
  | empty =>
      exact ⟨π, hπ, by simp, le_rfl⟩
  | @insert i T hi ih =>
      obtain ⟨v, hv, hfixed, hdom⟩ := ih
      obtain ⟨y, hy, hstep⟩ := bernExp_endpoint v i (v i) (q i) g (hv i)
      refine ⟨Function.update v i y, ?_, ?_, ?_⟩
      · intro j
        by_cases hj : j = i
        · subst j
          simp only [Function.update_self]
          rcases hy with rfl | rfl
          · exact ⟨le_rfl, hq i⟩
          · exact ⟨hq i, le_rfl⟩
        · simpa [Function.update_of_ne hj] using hv j
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa using hy
        · have hji : j ≠ i := by intro he; subst j; exact hi hj
          simpa [Function.update_of_ne hji] using hfixed j hj
      · have he : Function.update v i (v i) = v := Function.update_eq_self i v
        rw [he] at hstep
        exact hdom.trans hstep
lemma bernExp_vertex_dominates {n : ℕ} (q π : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ q i)
    (g : Finset (Fin n) → ℝ) :
    ∃ v : Fin n → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ q i) ∧
      (∀ i, v i = 0 ∨ v i = q i) ∧ bernExp π g ≤ bernExp v g := by
  obtain ⟨v, hv, hf, hd⟩ := bernExp_round_subset q π hq hπ g Finset.univ
  exact ⟨v, hv, fun i => hf i (Finset.mem_univ i), hd⟩
end RandomThresholdEndpoint
#print axioms RandomThresholdEndpoint.bernExp_endpoint

#print axioms RandomThresholdEndpoint.bernExp_round_subset
#print axioms RandomThresholdEndpoint.bernExp_vertex_dominates

set_option autoImplicit false
open CorreaThreshold.Nonadaptive
namespace RandomThresholdSum
open scoped Classical
lemma sum_containing {n : ℕ} (i : Fin n) (f : Finset (Fin n) → ℝ) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), f S) =
      ∑ T ∈ (Finset.univ.erase i).powerset, f (insert i T) := by
  symm
  apply Finset.sum_bij (fun T _ => insert i T)
  · intro T hT
    simp
  · intro T hT U hU he
    have hiT : i ∉ T := by
      have ht := Finset.mem_powerset.mp hT
      exact fun hi => (Finset.mem_erase.mp (ht hi)).1 rfl
    have hiU : i ∉ U := by
      have hu := Finset.mem_powerset.mp hU
      exact fun hi => (Finset.mem_erase.mp (hu hi)).1 rfl
    have := congrArg (Finset.erase · i) he
    simpa [hiT, hiU] using this
  · intro S hS
    refine ⟨S.erase i, ?_, ?_⟩
    · simp only [Finset.mem_powerset]
      intro j hj
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ j⟩
    · exact Finset.insert_erase (Finset.mem_filter.mp hS).2
  · intro T hT
    rfl
lemma sum_missing {n : ℕ} (i : Fin n) (f : Finset (Fin n) → ℝ) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∉ S), f S) =
      ∑ T ∈ (Finset.univ.erase i).powerset, f T := by
  apply Finset.sum_congr
  · ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset,
      Finset.subset_erase]
    simp
  · intro T hT
    rfl
lemma sum_split {n : ℕ} (i : Fin n) (f : Finset (Fin n) → ℝ) :
    (∑ S : Finset (Fin n), f S) =
      (∑ T ∈ (Finset.univ.erase i).powerset, f (insert i T)) +
      (∑ T ∈ (Finset.univ.erase i).powerset, f T) := by
  rw [← sum_containing, ← sum_missing]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
lemma relax_eq_four {n : ℕ} (b π : Fin n → ℝ) : relaxObj b π = objFour b π := by
  unfold relaxObj objFour
  have expand : ∀ S : Finset (Fin n),
      ((∑ i ∈ S, b i) / (S.card : ℝ)) * (∏ i ∈ S, π i) *
        (∏ i ∈ Sᶜ, (1 - π i)) =
      ∑ i : Fin n, if i ∈ S then
        b i / (S.card : ℝ) * (∏ j ∈ S, π j) * (∏ j ∈ Sᶜ, (1 - π j)) else 0 := by
    intro S
    rw [Finset.sum_div, Finset.sum_mul, Finset.sum_mul]
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter, sum_containing]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hiT : i ∉ T := (Finset.subset_erase.mp (Finset.mem_powerset.mp hT)).2
  have hc : (insert i T)ᶜ = (Finset.univ.erase i) \ T := by
    ext j
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_sdiff,
      Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  rw [Finset.card_insert_of_notMem hiT, Nat.cast_add, Nat.cast_one,
    Finset.prod_insert hiT, hc]
  ring
#print axioms sum_containing
#print axioms sum_missing
#print axioms sum_split
#print axioms relax_eq_four
end RandomThresholdSum

set_option autoImplicit false
open CorreaThreshold.Nonadaptive RandomThresholdBernoulli RandomThresholdCoordinate RandomThresholdSum
namespace RandomThresholdMarginal
open scoped Classical
noncomputable def restWeight {n : ℕ} (q : Fin n → ℝ) (i : Fin n)
    (T : Finset (Fin n)) : ℝ :=
  (∏ j ∈ T, q j) * (∏ j ∈ (Finset.univ.erase i) \ T, (1-q j))
lemma bernExp_split {n : ℕ} (q : Fin n → ℝ) (i : Fin n)
    (g : Finset (Fin n) → ℝ) :
    bernExp q g = ∑ T ∈ (Finset.univ.erase i).powerset,
      restWeight q i T * (q i * g (insert i T) + (1-q i)*g T) := by
  unfold bernExp
  rw [sum_split i, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have hiT : i ∉ T := (Finset.subset_erase.mp (Finset.mem_powerset.mp hT)).2
  have hc : (insert i T)ᶜ = (Finset.univ.erase i) \ T := by
    ext j
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_sdiff,
      Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  have hd : Tᶜ = insert i ((Finset.univ.erase i) \ T) := by
    ext j
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_sdiff,
      Finset.mem_erase, Finset.mem_univ, and_true]
    by_cases hj : j = i
    · subst j; simp [hiT]
    · tauto
  have hiR : i ∉ (Finset.univ.erase i) \ T := by simp
  rw [Finset.prod_insert hiT, hc, hd, Finset.prod_insert hiR]
  unfold restWeight
  ring
lemma restWeight_update {n : ℕ} (q : Fin n → ℝ) (i : Fin n) (x : ℝ)
    (T : Finset (Fin n)) (hiT : i ∉ T) :
    restWeight (Function.update q i x) i T = restWeight q i T := by
  unfold restWeight
  rw [Finset.prod_update_of_notMem hiT, complement_update]
  have hiR : i ∉ (Finset.univ.erase i) \ T := by simp
  rw [Finset.prod_update_of_notMem hiR]
lemma bernExp_update_zero_erase {n : ℕ} (q : Fin n → ℝ) (i : Fin n)
    (g : Finset (Fin n) → ℝ) :
    bernExp (Function.update q i 0) g = bernExp q (fun T => g (T.erase i)) := by
  rw [bernExp_split, bernExp_split]
  apply Finset.sum_congr rfl
  intro T hT
  have hiT : i ∉ T := (Finset.subset_erase.mp (Finset.mem_powerset.mp hT)).2
  rw [restWeight_update q i 0 T hiT]
  simp only [Function.update_self, zero_mul, sub_zero, one_mul,
    Finset.erase_insert hiT, Finset.erase_eq_of_notMem hiT]
  ring
noncomputable def zeroOn {n : ℕ} (q : Fin n → ℝ) (R : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ R then 0 else q i
lemma zeroOn_insert {n : ℕ} (q : Fin n → ℝ) (R : Finset (Fin n)) (i : Fin n) :
    zeroOn q (insert i R) = Function.update (zeroOn q R) i 0 := by
  funext j
  by_cases hj : j = i
  · subst j; simp [zeroOn]
  · simp [zeroOn, hj]
lemma bernExp_zeroOn {n : ℕ} (q : Fin n → ℝ) (R : Finset (Fin n))
    (g : Finset (Fin n) → ℝ) :
    bernExp (zeroOn q R) g = bernExp q (fun T => g (T \ R)) := by
  induction R using Finset.induction_on generalizing g with
  | empty =>
      have he : zeroOn q ∅ = q := by funext i; simp [zeroOn]
      rw [he]
      simp
  | @insert i R hi ih =>
      rw [zeroOn_insert, bernExp_update_zero_erase, ih]
      congr 1
      funext T
      congr 1
      ext j
      simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
      tauto
noncomputable def mask {n : ℕ} (q : Fin n → ℝ) (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then q i else 0
lemma bernExp_mask {n : ℕ} (q : Fin n → ℝ) (S : Finset (Fin n))
    (g : Finset (Fin n) → ℝ) :
    bernExp (mask q S) g = bernExp q (fun T => g (S ∩ T)) := by
  have hm : mask q S = zeroOn q Sᶜ := by
    funext i
    by_cases hi : i ∈ S <;> simp [mask, zeroOn, hi]
  rw [hm, bernExp_zeroOn]
  congr 1
  funext T
  congr 1
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_inter]
  tauto
end RandomThresholdMarginal
#print axioms RandomThresholdMarginal.bernExp_split
#print axioms RandomThresholdMarginal.restWeight_update
#print axioms RandomThresholdMarginal.bernExp_update_zero_erase

#print axioms RandomThresholdMarginal.zeroOn_insert
#print axioms RandomThresholdMarginal.bernExp_zeroOn
#print axioms RandomThresholdMarginal.bernExp_mask

set_option autoImplicit false
open CorreaThreshold.Nonadaptive RandomThresholdSum RandomThresholdEndpoint RandomThresholdMarginal
namespace RandomThresholdOptimization
open scoped Classical
noncomputable def payoff {n : ℕ} (b : Fin n → ℝ) (T : Finset (Fin n)) : ℝ :=
  (∑ i ∈ T, b i) / (T.card : ℝ)
lemma relax_eq_bernExp {n : ℕ} (b π : Fin n → ℝ) :
    relaxObj b π = bernExp π (payoff b) := by
  unfold relaxObj bernExp payoff
  apply Finset.sum_congr rfl
  intro T hT
  ring
lemma masked_objective {n : ℕ} (q b : Fin n → ℝ) (S : Finset (Fin n)) :
    objFour b (mask q S) = bernExp q (selRatio b S) := by
  rw [← relax_eq_four, relax_eq_bernExp, bernExp_mask]
  rfl
lemma vertex_mask {n : ℕ} (q v : Fin n → ℝ) (hv : ∀ i, v i = 0 ∨ v i = q i) :
    ∃ S : Finset (Fin n), v = mask q S := by
  refine ⟨Finset.univ.filter (fun i => v i ≠ 0), ?_⟩
  funext i
  by_cases hi : v i = 0
  · simp [mask, hi]
  · simp only [mask, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
    exact (hv i).resolve_left hi
lemma mask_feasible {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i)
    (S : Finset (Fin n)) : ∀ i, 0 ≤ mask q S i ∧ mask q S i ≤ q i := by
  intro i
  by_cases hi : i ∈ S
  · simp only [mask, if_pos hi]
    exact ⟨hq i, le_rfl⟩
  · simp only [mask, if_neg hi]
    exact ⟨le_rfl, hq i⟩
lemma objective_bound {n : ℕ} (q b : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i)
    (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ q i) :
    objFour b π ≤ objP q b := by
  obtain ⟨v, hv, hf, hd⟩ := bernExp_vertex_dominates q π hq hπ (payoff b)
  obtain ⟨S, hS⟩ := vertex_mask q v hf
  have hdom : objFour b π ≤ objFour b v := by
    rw [← relax_eq_four, ← relax_eq_four, relax_eq_bernExp, relax_eq_bernExp]
    exact hd
  rw [hS, masked_objective] at hdom
  apply hdom.trans
  unfold objP
  exact (Finset.le_sup'_iff Finset.univ_nonempty).mpr ⟨S, Finset.mem_univ S, le_rfl⟩
lemma objective_attained {n : ℕ} (q b : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) :
    ∃ π : Fin n → ℝ, (∀ i, 0 ≤ π i ∧ π i ≤ q i) ∧ objFour b π = objP q b := by
  obtain ⟨S, hS, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun S : Finset (Fin n) => bernExp q (selRatio b S))
  refine ⟨mask q S, mask_feasible q hq S, ?_⟩
  rw [masked_objective]
  exact he.symm
end RandomThresholdOptimization
#print axioms RandomThresholdOptimization.relax_eq_bernExp
#print axioms RandomThresholdOptimization.masked_objective
#print axioms RandomThresholdOptimization.vertex_mask
#print axioms RandomThresholdOptimization.mask_feasible
#print axioms RandomThresholdOptimization.objective_bound
#print axioms RandomThresholdOptimization.objective_attained

set_option autoImplicit false
open CorreaThreshold.Nonadaptive RandomThresholdSum RandomThresholdOptimization

theorem solution {n : ℕ} [NeZero n] (q b : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    (∀ π : Fin n → ℝ, relaxObj b π = objFour b π) ∧
    (∀ π : Fin n → ℝ, (∀ i, 0 ≤ π i ∧ π i ≤ q i) →
      objFour b π ≤ objP q b) ∧
    (∃ π : Fin n → ℝ, (∀ i, 0 ≤ π i ∧ π i ≤ q i) ∧
      objFour b π = objP q b) := by
  exact ⟨fun π => relax_eq_four b π,
    fun π hπ => objective_bound q b (fun i => (hq i).1) π hπ,
    objective_attained q b (fun i => (hq i).1)⟩

#print axioms solution
namespace CorreaThreshold.Nonadaptive

/-- Equation (4) and the equivalence of its optimization problem with (P). -/
example {n : ℕ} [NeZero n] (q b : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    (∀ π : Fin n → ℝ, relaxObj b π = objFour b π) ∧
    (∀ π : Fin n → ℝ, (∀ i, 0 ≤ π i ∧ π i ≤ q i) →
      objFour b π ≤ objP q b) ∧
    (∃ π : Fin n → ℝ, (∀ i, 0 ≤ π i ∧ π i ≤ q i) ∧
      objFour b π = objP q b) := by
  exact solution q b hq

end CorreaThreshold.Nonadaptive

#print axioms solution
