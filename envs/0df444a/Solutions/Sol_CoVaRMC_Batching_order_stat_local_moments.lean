-- Prove2me | solution 1 for CoVaRMC.Batching.order_stat_local_moments
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:24:15.435685+00:00
-- url     : https://prove2.me/submissions/9ca19efd-3abf-407b-bf7e-43b40a0a4130

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaROSM

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

lemma pi_perm (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    (Measure.pi (fun _ : Fin N => ν)).map (fun x => x ∘ σ) = Measure.pi (fun _ => ν) := by
  have hm : Measurable (fun x : Fin N → ℝ => x ∘ σ) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun x : Fin N → ℝ => x ∘ σ) ⁻¹' Set.univ.pi s = Set.univ.pi (fun i => s (σ.symm i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp]
    constructor
    · intro h i; simpa using h (σ.symm i)
    · intro h i; simpa using h (σ i)
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp σ.symm (fun i => ν (s i))

lemma pi_diag_zero (hν : ∀ x, ν {x} = 0) (N : ℕ) (i j : Fin N) (hij : i ≠ j) :
    Measure.pi (fun _ : Fin N => ν) {x | x i = x j} = 0 := by
  have hind : iIndepFun (fun k (x : Fin N → ℝ) => x k) (Measure.pi (fun _ : Fin N => ν)) := by
    have := iIndepFun_pi (μ := fun _ : Fin N => ν) (X := fun _ (y : ℝ) => y)
      (fun _ => measurable_id.aemeasurable)
    exact this
  have hij' := hind.indepFun hij
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).mp hij'
  have hev : ∀ k, (Measure.pi (fun _ : Fin N => ν)).map (fun x => x k) = ν := fun k =>
    (measurePreserving_eval (fun _ : Fin N => ν) k).map_eq
  rw [hev, hev] at hmap
  have hdiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_diagonal
  have : {x : Fin N → ℝ | x i = x j} = (fun x => (x i, x j)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} := rfl
  rw [this, ← Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hdiag, hmap,
    Measure.prod_apply hdiag]
  have : ∀ x : ℝ, Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
    intro x; ext y; simp [eq_comm]
  simp_rw [this, hν, lintegral_zero]

/-- rank: number of strictly smaller coordinates. -/
noncomputable def rk {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : ℕ := (Finset.univ.filter fun j => x j < x i).card

lemma rk_lt {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : rk x i < N := by
  unfold rk
  have : (Finset.univ.filter fun j => x j < x i) ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro h
    have : i ∈ (Finset.univ.filter fun j => x j < x i) := by rw [h]; exact Finset.mem_univ _
    simp at this
  simpa using Finset.card_lt_card this

lemma rk_comp {N : ℕ} (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    rk (x ∘ σ) i = rk x (σ i) := by
  unfold rk
  simp only [Function.comp]
  exact Finset.card_bij' (fun j _ => σ j) (fun j _ => σ.symm j) (by simp) (by simp) (by simp) (by simp)

lemma rk_injective {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i j, i ≠ j → x i ≠ x j) :
    Function.Injective (rk x) := by
  have hmono : ∀ i j, x i < x j → rk x i < rk x j := by
    intro i j hij
    unfold rk
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; linarith
    · intro h
      have : i ∈ (Finset.univ.filter fun k => x k < x j) := by simp [hij]
      rw [← h] at this; simp at this
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne (hx i j hne) with h1 | h1
  · exact absurd h (hmono i j h1).ne
  · exact absurd h (hmono j i h1).ne'

lemma card_rk_lt {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i j, i ≠ j → x i ≠ x j) (s : ℕ) (hs : s ≤ N) :
    (Finset.univ.filter fun i => rk x i < s).card = s := by
  set e : Fin N → Fin N := fun i => ⟨rk x i, rk_lt x i⟩ with hedef
  have he : Function.Injective e := by
    intro i j h; apply rk_injective x hx; simpa [hedef] using congrArg Fin.val h
  have hbij : Function.Bijective e := (Fintype.bijective_iff_injective_and_card e).mpr ⟨he, rfl⟩
  set E := Equiv.ofBijective e hbij
  have : (Finset.univ.filter fun i => rk x i < s) =
      (Finset.univ.filter fun t : Fin N => (t : ℕ) < s).map E.symm.toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv, Equiv.symm_symm]
    rfl
  rw [this, Finset.card_map]
  have h2 : (Finset.univ.filter fun t : Fin N => (t : ℕ) < s) =
      (Finset.range s).attachFin (fun t ht => lt_of_lt_of_le (Finset.mem_range.mp ht) hs) := by
    ext t; simp
  rw [h2, Finset.card_attachFin, Finset.card_range]

lemma measurable_rk {N : ℕ} (i : Fin N) : Measurable (fun x : Fin N → ℝ => (rk x i : ℝ)) := by
  have : (fun x : Fin N → ℝ => (rk x i : ℝ)) =
      fun x => ∑ j : Fin N, Set.indicator {x : Fin N → ℝ | x j < x i} (fun _ => (1 : ℝ)) x := by
    funext x
    unfold rk
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : x j < x i <;> simp [h]
  rw [this]
  exact Finset.measurable_sum _ fun j _ => measurable_const.indicator
    (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))

lemma measurableSet_rk_lt {N : ℕ} (i : Fin N) (s : ℕ) :
    MeasurableSet {x : Fin N → ℝ | rk x i < s} := by
  have : {x : Fin N → ℝ | rk x i < s} = (fun x : Fin N → ℝ => (rk x i : ℝ)) ⁻¹' Set.Iio (s : ℝ) := by
    ext x; simp
  rw [this]; exact measurableSet_Iio.preimage (measurable_rk i)

lemma ae_distinct (hν : ∀ x, ν {x} = 0) (N : ℕ) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin N => ν)), ∀ i j, i ≠ j → x i ≠ x j := by
  rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
  by_cases hij : i = j
  · exact Eventually.of_forall fun x h => absurd hij h
  · have h0 := pi_diag_zero ν hν N i j hij
    rw [measure_eq_zero_iff_ae_notMem] at h0
    filter_upwards [h0] with x hx _
    exact hx

lemma real_perm_eq (N : ℕ) (σ : Equiv.Perm (Fin N)) (A : Set (Fin N → ℝ)) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : Fin N => ν)).real ((fun x => x ∘ σ) ⁻¹' A) =
      (Measure.pi (fun _ : Fin N => ν)).real A := by
  have hm : Measurable (fun x : Fin N → ℝ => x ∘ σ) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  rw [← map_measureReal_apply hm hA, pi_perm]

lemma prob_rk_lt (hν : ∀ x, ν {x} = 0) (N : ℕ) (s : ℕ) (hs : s ≤ N) (i : Fin N) :
    (N : ℝ) * (Measure.pi (fun _ : Fin N => ν)).real {x | rk x i < s} = s := by
  set μ := Measure.pi (fun _ : Fin N => ν)
  have heq : ∀ j : Fin N, μ.real {x | rk x j < s} = μ.real {x | rk x i < s} := by
    intro j
    have h := real_perm_eq ν N (Equiv.swap j i) {x | rk x j < s} (measurableSet_rk_lt j s)
    rw [← h]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, rk_comp, Equiv.swap_apply_left]
  have hsum : ∑ j : Fin N, μ.real {x | rk x j < s} = s := by
    have h1 : ∀ j : Fin N, μ.real {x | rk x j < s} =
        ∫ x, Set.indicator {x | rk x j < s} (fun _ => (1 : ℝ)) x ∂μ := by
      intro j; rw [integral_indicator_const _ (measurableSet_rk_lt j s), smul_eq_mul, mul_one]
    simp_rw [h1]
    rw [← integral_finsetSum _ (fun j _ => (integrable_const (1 : ℝ)).indicator (measurableSet_rk_lt j s))]
    have h2 : (fun x => ∑ j : Fin N, Set.indicator {x | rk x j < s} (fun _ => (1 : ℝ)) x) =ᵐ[μ]
        fun _ => (s : ℝ) := by
      filter_upwards [ae_distinct ν hν N] with x hx
      have hc := card_rk_lt x hx s hs
      have : ∑ j : Fin N, Set.indicator {x | rk x j < s} (fun _ => (1 : ℝ)) x =
          ((Finset.univ.filter fun i => rk x i < s).card : ℝ) := by
        rw [Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : rk x j < s
        · rw [Set.indicator_of_mem (show x ∈ {x | rk x j < s} from h), if_pos h]
        · rw [Set.indicator_of_notMem (show x ∉ {x | rk x j < s} from h), if_neg h]
      rw [this, hc]
    rw [integral_congr_ae h2, integral_const, probReal_univ, one_smul]
  simp_rw [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact hsum

lemma prob_rk_pair (hν : ∀ x, ν {x} = 0) (N : ℕ) (s : ℕ) (hs : s ≤ N) (a b : Fin N) (hab : a ≠ b) :
    ((N : ℝ) * N - N) * (Measure.pi (fun _ : Fin N => ν)).real {x | rk x a < s ∧ rk x b < s} =
      (s : ℝ) * s - s := by
  set μ := Measure.pi (fun _ : Fin N => ν)
  have hmeas : ∀ a b : Fin N, MeasurableSet {x : Fin N → ℝ | rk x a < s ∧ rk x b < s} :=
    fun a b => (measurableSet_rk_lt a s).inter (measurableSet_rk_lt b s)
  have heq : ∀ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
      μ.real {x | rk x p.1 < s ∧ rk x p.2 < s} = μ.real {x | rk x a < s ∧ rk x b < s} := by
    rintro ⟨a', b'⟩ hp
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
    -- a permutation sending `a ↦ a'`, `b ↦ b'`
    set τ1 := Equiv.swap a a'
    set b1 := τ1 b
    set σ := τ1.trans (Equiv.swap b1 b') with hσ
    have hb1a : b1 ≠ a' := by
      intro h; apply hab; apply τ1.injective; simp only [b1] at h; rw [h]; simp [τ1]
    have hσa : σ a = a' := by
      rw [hσ, Equiv.trans_apply]
      have : τ1 a = a' := by simp [τ1]
      rw [this, Equiv.swap_apply_of_ne_of_ne (Ne.symm hb1a) hp]
    have hσb : σ b = b' := by
      rw [hσ, Equiv.trans_apply]
      exact Equiv.swap_apply_left b1 b'
    have h := real_perm_eq ν N σ {x | rk x a < s ∧ rk x b < s} (hmeas a b)
    rw [← h]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, rk_comp, hσa, hσb]
  have hsum : ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
      μ.real {x | rk x p.1 < s ∧ rk x p.2 < s} = (s : ℝ) * s - s := by
    have h1 : ∀ p : Fin N × Fin N, μ.real {x | rk x p.1 < s ∧ rk x p.2 < s} =
        ∫ x, Set.indicator {x | rk x p.1 < s ∧ rk x p.2 < s} (fun _ => (1 : ℝ)) x ∂μ := by
      intro p; rw [integral_indicator_const _ (hmeas p.1 p.2), smul_eq_mul, mul_one]
    simp_rw [h1]
    rw [← integral_finsetSum _ (fun p _ => (integrable_const (1 : ℝ)).indicator (hmeas p.1 p.2))]
    have h2 : (fun x => ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
        Set.indicator {x | rk x p.1 < s ∧ rk x p.2 < s} (fun _ => (1 : ℝ)) x) =ᵐ[μ]
        fun _ => (s : ℝ) * s - s := by
      filter_upwards [ae_distinct ν hν N] with x hx
      have hT := card_rk_lt x hx s hs
      set T := Finset.univ.filter fun i => rk x i < s
      have hcard : ((Finset.univ : Finset (Fin N)).offDiag.filter
          (fun p => rk x p.1 < s ∧ rk x p.2 < s)) = T.offDiag := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and, T]
        tauto
      have : ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
          Set.indicator {x | rk x p.1 < s ∧ rk x p.2 < s} (fun _ => (1 : ℝ)) x =
          (((Finset.univ : Finset (Fin N)).offDiag.filter
            (fun p => rk x p.1 < s ∧ rk x p.2 < s)).card : ℝ) := by
        rw [Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : rk x p.1 < s ∧ rk x p.2 < s
        · rw [Set.indicator_of_mem (show x ∈ {x | rk x p.1 < s ∧ rk x p.2 < s} from h), if_pos h]
        · rw [Set.indicator_of_notMem (show x ∉ {x | rk x p.1 < s ∧ rk x p.2 < s} from h), if_neg h]
      rw [this, hcard, Finset.offDiag_card, hT]
      have : s ≤ s * s := Nat.le_mul_self s
      push_cast [this]
      ring
    rw [integral_congr_ae h2, integral_const, probReal_univ, one_smul]
  rw [Finset.sum_congr rfl heq, Finset.sum_const, Finset.offDiag_card, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have : N ≤ N * N := Nat.le_mul_self N
  push_cast [this] at hsum
  linarith

lemma card_lt_iff {k : ℕ} (w : Fin k → ℝ) (j : Fin k) (z : ℝ) :
    (j : ℕ) + 1 ≤ (Finset.univ.filter fun i => w i < z).card ↔ w (Tuple.sort w j) < z := by
  set σ := Tuple.sort w
  have hmono : Monotone (w ∘ σ) := Tuple.monotone_sort w
  constructor
  · intro hcard
    by_contra hlt
    push Not at hlt
    have hsub : (Finset.univ.filter fun i => w i < z) ⊆ (Finset.Iio j).image σ := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_image]
      refine ⟨σ.symm i, ?_, by simp⟩
      rw [Finset.mem_Iio]
      by_contra hge
      push Not at hge
      have := hmono hge
      simp only [Function.comp, Equiv.apply_symm_apply] at this
      linarith
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iio] at this
    omega
  · intro hj
    have hsub : (Finset.Iic j).image σ ⊆ (Finset.univ.filter fun i => w i < z) := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨l, hl, rfl⟩ := hi
      rw [Finset.mem_Iic] at hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt (hmono hl) hj
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic] at this
    omega

/-- `z ≤ X_(j+1)` iff fewer than `j + 1` entries are `< z`. -/
lemma le_orderStat_iff {k : ℕ} (w : Fin k → ℝ) (j : Fin k) (z : ℝ) :
    z ≤ w (Tuple.sort w j) ↔ (Finset.univ.filter fun i => w i < z).card < (j : ℕ) + 1 := by
  rw [← not_lt, ← card_lt_iff w j z, not_le]

lemma rk_last {m : ℕ} (x : Fin (m + 1) → ℝ) :
    rk x (Fin.last m) = (Finset.univ.filter fun i : Fin m => Fin.init x i < x (Fin.last m)).card := by
  unfold rk
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [lt_irrefl, if_false, add_zero]
  rfl

lemma rk_pair {m : ℕ} (x : Fin (m + 2) → ℝ) :
    rk x (Fin.castSucc (Fin.last m)) =
        (Finset.univ.filter fun i : Fin m => Fin.init (Fin.init x) i < x (Fin.castSucc (Fin.last m))).card
        + (if x (Fin.last (m + 1)) < x (Fin.castSucc (Fin.last m)) then 1 else 0) ∧
    rk x (Fin.last (m + 1)) =
        (Finset.univ.filter fun i : Fin m => Fin.init (Fin.init x) i < x (Fin.last (m + 1))).card
        + (if x (Fin.castSucc (Fin.last m)) < x (Fin.last (m + 1)) then 1 else 0) := by
  constructor
  · unfold rk
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [lt_irrefl, if_false, add_zero]
    rfl
  · unfold rk
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [lt_irrefl, if_false, add_zero]
    rfl

lemma event_single {m : ℕ} (x : Fin (m + 1) → ℝ) (r : Fin m) :
    x (Fin.last m) ≤ Fin.init x (Tuple.sort (Fin.init x) r) ↔ rk x (Fin.last m) < (r : ℕ) + 1 := by
  rw [rk_last, le_orderStat_iff]

lemma event_pair {m : ℕ} (x : Fin (m + 2) → ℝ) (hx : ∀ i j, i ≠ j → x i ≠ x j) (r : Fin m) :
    (x (Fin.castSucc (Fin.last m)) ≤ Fin.init (Fin.init x) (Tuple.sort (Fin.init (Fin.init x)) r) ∧
      x (Fin.last (m + 1)) ≤ Fin.init (Fin.init x) (Tuple.sort (Fin.init (Fin.init x)) r)) ↔
    (rk x (Fin.castSucc (Fin.last m)) < (r : ℕ) + 2 ∧ rk x (Fin.last (m + 1)) < (r : ℕ) + 2) := by
  obtain ⟨ha, hb⟩ := rk_pair x
  rw [le_orderStat_iff, le_orderStat_iff, ha, hb]
  set y := Fin.init (Fin.init x)
  set A := x (Fin.castSucc (Fin.last m))
  set B := x (Fin.last (m + 1))
  have hAB : A ≠ B := hx _ _ (by
    intro h
    have := congrArg Fin.val h
    simp at this)
  set ca := (Finset.univ.filter fun i : Fin m => y i < A).card
  set cb := (Finset.univ.filter fun i : Fin m => y i < B).card
  have hmon : ∀ {P Q : ℝ}, P < Q → (Finset.univ.filter fun i : Fin m => y i < P).card ≤
      (Finset.univ.filter fun i : Fin m => y i < Q).card := by
    intro P Q hPQ
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith
  rcases lt_or_gt_of_ne hAB with h | h
  · have hc : ca ≤ cb := hmon h
    have h1 : ¬ B < A := not_lt.mpr h.le
    simp only [h1, if_false, h, if_true]
    omega
  · have hc : cb ≤ ca := hmon h
    have h1 : ¬ A < B := not_lt.mpr h.le
    simp only [h1, if_false, h, if_true]
    omega

lemma split_last (n : ℕ) (H : (Fin n → ℝ) → ℝ) (hH : Measurable H) (G : (Fin n → ℝ) → ℝ)
    (hG : Measurable G) (hGb : ∀ y, |G y| ≤ 1) :
    ∫ x, Set.indicator {x : Fin (n + 1) → ℝ | x (Fin.last n) ≤ H (Fin.init x)}
        (fun x => G (Fin.init x)) x ∂(Measure.pi (fun _ : Fin (n + 1) => ν)) =
      ∫ y, ν.real (Set.Iic (H y)) * G y ∂(Measure.pi (fun _ : Fin n => ν)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) (Fin.last n)).symm
  have hinit : Measurable (fun x : Fin (n + 1) → ℝ => Fin.init x) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hset : MeasurableSet {x : Fin (n + 1) → ℝ | x (Fin.last n) ≤ H (Fin.init x)} :=
    measurableSet_le (measurable_pi_apply _) (hH.comp hinit)
  set f : (Fin (n + 1) → ℝ) → ℝ := Set.indicator {x : Fin (n + 1) → ℝ | x (Fin.last n) ≤ H (Fin.init x)}
    (fun x => G (Fin.init x)) with hfdef
  have hfm : Measurable f := (hG.comp hinit).indicator hset
  have hfb : ∀ x, |f x| ≤ 1 := by
    intro x; simp only [hfdef, Set.indicator]; split_ifs
    · exact hGb _
    · simp
  rw [← hmp.integral_comp' f]
  have hint : Integrable (fun z => f (e.symm z)) (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
    Integrable.mono' (integrable_const (1 : ℝ)) (hfm.comp e.symm.measurable).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hfb _)
  rw [integral_prod_symm _ hint]
  congr 1
  funext y
  have hsymm : ∀ a, e.symm (a, y) = Fin.snoc (α := fun _ : Fin (n + 1) => ℝ) y a := by
    intro a
    show Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) (Fin.last n) a y = Fin.snoc y a
    exact Fin.insertNth_last' a y
  have : ∀ a, f (e.symm (a, y)) = (Set.Iic (H y)).indicator (fun _ => G y) a := by
    intro a
    rw [hsymm]
    simp only [hfdef, Set.indicator, Set.mem_ofPred_eq, Set.mem_Iic, Fin.init_snoc, Fin.snoc_last]
  simp_rw [this]
  rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul]

lemma measurable_init (n : ℕ) : Measurable (fun x : Fin (n + 1) → ℝ => Fin.init x) :=
  measurable_pi_lambda (fun x : Fin (n + 1) → ℝ => Fin.init x)
    (fun i => measurable_pi_apply (Fin.castSucc i))

/-- `F(z) = ν((-∞, z])`. -/
noncomputable def Fν (z : ℝ) : ℝ := ν.real (Set.Iic z)

lemma Fν_mem (z : ℝ) : 0 ≤ Fν ν z ∧ Fν ν z ≤ 1 :=
  ⟨measureReal_nonneg, by unfold Fν; exact measureReal_le_one⟩

lemma measurable_Fν : Measurable (Fν ν) := by
  have hm : Monotone (Fν ν) := fun a b hab => measureReal_mono (Set.Iic_subset_Iic.mpr hab)
  exact hm.measurable

lemma measurable_os {m : ℕ} (r : Fin m) : Measurable (fun y : Fin m → ℝ => y (Tuple.sort y r)) := by
  have heq : (fun y : Fin m → ℝ => y (Tuple.sort y r)) = fun y =>
      ∑ σ : Equiv.Perm (Fin m), Set.indicator {y : Fin m → ℝ | Tuple.sort y = σ} (fun y => y (σ r)) y := by
    funext y
    rw [Finset.sum_eq_single (Tuple.sort y)]
    · simp
    · intro σ _ hσ
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_ofPred_eq]
      exact fun h => hσ h.symm
    · simp
  rw [heq]
  refine Finset.measurable_sum _ fun σ _ => (measurable_pi_apply _).indicator ?_
  have : {y : Fin m → ℝ | Tuple.sort y = σ} =
      (⋂ i : Fin m, ⋂ j : Fin m, {y | i ≤ j → y (σ i) ≤ y (σ j)}) ∩
      (⋂ i : Fin m, ⋂ j : Fin m, {y | i < j → y (σ i) = y (σ j) → σ i < σ j}) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [eq_comm, Tuple.eq_sort_iff]
    rfl
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  · by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (measurable_pi_apply (σ i)) (measurable_pi_apply (σ j))
    · simp [hij]
  · by_cases hij : i < j
    · by_cases hs : σ i < σ j
      · simp [hs]
      · simp only [hij, hs, true_implies, imp_false]
        exact (measurableSet_eq_fun (measurable_pi_apply (σ i)) (measurable_pi_apply (σ j))).compl
    · simp [hij]

lemma moment1 (hν : ∀ x, ν {x} = 0) (m : ℕ) (r : Fin m) :
    ∫ y, Fν ν (y (Tuple.sort y r)) ∂(Measure.pi (fun _ : Fin m => ν)) = ((r : ℝ) + 1) / (m + 1) := by
  have h := split_last ν m (fun y => y (Tuple.sort y r)) (measurable_os r) (fun _ => 1)
    measurable_const (fun _ => by norm_num)
  simp only [mul_one] at h
  unfold Fν
  have hms : MeasurableSet {x : Fin (m + 1) → ℝ | x (Fin.last m) ≤ Fin.init x (Tuple.sort (Fin.init x) r)} :=
    measurableSet_le (measurable_pi_apply _) ((measurable_os r).comp (measurable_init m))
  rw [← h, integral_indicator_const _ hms, smul_eq_mul, mul_one]
  have hset : {x : Fin (m + 1) → ℝ | x (Fin.last m) ≤ Fin.init x (Tuple.sort (Fin.init x) r)} =
      {x | rk x (Fin.last m) < (r : ℕ) + 1} := by
    ext x; exact event_single x r
  rw [hset]
  have := prob_rk_lt ν hν (m + 1) ((r : ℕ) + 1) (by omega) (Fin.last m)
  push_cast at this
  field_simp
  linarith

lemma moment2 (hν : ∀ x, ν {x} = 0) (m : ℕ) (r : Fin m) :
    ∫ y, Fν ν (y (Tuple.sort y r)) ^ 2 ∂(Measure.pi (fun _ : Fin m => ν)) =
      ((r : ℝ) + 1) * ((r : ℝ) + 2) / ((m + 1) * (m + 2)) := by
  set H : (Fin m → ℝ) → ℝ := fun y => y (Tuple.sort y r) with hH
  have hHm : Measurable H := measurable_os r
  have hinit : ∀ n, Measurable (fun x : Fin (n + 1) → ℝ => Fin.init x) := measurable_init
  -- inner split
  have h1 := split_last ν m H hHm (fun y => Fν ν (H y)) ((measurable_Fν ν).comp hHm)
    (fun y => by rw [abs_of_nonneg (Fν_mem ν _).1]; exact (Fν_mem ν _).2)
  -- outer split
  set G : (Fin (m + 1) → ℝ) → ℝ :=
    Set.indicator {x : Fin (m + 1) → ℝ | x (Fin.last m) ≤ H (Fin.init x)} (fun _ => 1) with hG
  have hGset : MeasurableSet {x : Fin (m + 1) → ℝ | x (Fin.last m) ≤ H (Fin.init x)} :=
    measurableSet_le (measurable_pi_apply _) (hHm.comp (hinit m))
  have hGm : Measurable G := measurable_const.indicator hGset
  have h2 := split_last ν (m + 1) (fun y => H (Fin.init y)) (hHm.comp (hinit m)) G hGm
    (fun y => by simp only [hG, Set.indicator]; split_ifs <;> norm_num)
  have hlhs : ∫ y, Fν ν (H y) ^ 2 ∂(Measure.pi (fun _ : Fin m => ν)) =
      ∫ y, ν.real (Set.Iic (H (Fin.init y))) * G y ∂(Measure.pi (fun _ : Fin (m + 1) => ν)) := by
    have e0 : ∫ y, Fν ν (H y) ^ 2 ∂(Measure.pi (fun _ : Fin m => ν)) =
        ∫ y, ν.real (Set.Iic (H y)) * Fν ν (H y) ∂(Measure.pi (fun _ : Fin m => ν)) := by
      congr 1; funext y; unfold Fν; ring
    rw [e0, ← h1]
    congr 1; funext y
    simp only [hG, Set.indicator, Fν]
    split_ifs <;> simp
  rw [hlhs, ← h2]
  have hpt : ∀ x : Fin (m + 2) → ℝ,
      Set.indicator {x : Fin (m + 2) → ℝ | x (Fin.last (m + 1)) ≤ H (Fin.init (Fin.init x))}
        (fun x => G (Fin.init x)) x =
      Set.indicator {x : Fin (m + 2) → ℝ | x (Fin.castSucc (Fin.last m)) ≤ H (Fin.init (Fin.init x)) ∧
        x (Fin.last (m + 1)) ≤ H (Fin.init (Fin.init x))} (fun _ => (1 : ℝ)) x := by
    intro x
    have hx : Fin.init x (Fin.last m) = x (Fin.castSucc (Fin.last m)) := rfl
    simp only [hG, Set.indicator, Set.mem_ofPred_eq]
    by_cases h1 : x (Fin.last (m + 1)) ≤ H (Fin.init (Fin.init x)) <;>
      by_cases h2 : x (Fin.castSucc (Fin.last m)) ≤ H (Fin.init (Fin.init x)) <;> simp [h1, h2, hx]
  simp_rw [hpt]
  have hmeas : MeasurableSet {x : Fin (m + 2) → ℝ | x (Fin.castSucc (Fin.last m)) ≤ H (Fin.init (Fin.init x)) ∧
        x (Fin.last (m + 1)) ≤ H (Fin.init (Fin.init x))} :=
    (measurableSet_le (measurable_pi_apply _) (hHm.comp ((hinit m).comp (hinit (m + 1))))).inter
      (measurableSet_le (measurable_pi_apply _) (hHm.comp ((hinit m).comp (hinit (m + 1)))))
  rw [integral_indicator_const _ hmeas, smul_eq_mul, mul_one]
  have hae : {x : Fin (m + 2) → ℝ | x (Fin.castSucc (Fin.last m)) ≤ H (Fin.init (Fin.init x)) ∧
        x (Fin.last (m + 1)) ≤ H (Fin.init (Fin.init x))} =ᵐ[Measure.pi (fun _ : Fin (m + 2) => ν)]
      {x | rk x (Fin.castSucc (Fin.last m)) < (r : ℕ) + 2 ∧ rk x (Fin.last (m + 1)) < (r : ℕ) + 2} := by
    filter_upwards [ae_distinct ν hν (m + 2)] with x hx
    exact propext (event_pair x hx r)
  rw [measureReal_congr hae]
  have hab : (Fin.castSucc (Fin.last m) : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    intro h; have := congrArg Fin.val h; simp at this
  have := prob_rk_pair ν hν (m + 2) ((r : ℕ) + 2) (by omega) _ _ hab
  push_cast at this
  have hpos : (0 : ℝ) < ((m : ℝ) + 2) * (m + 2) - (m + 2) := by nlinarith
  field_simp
  nlinarith [this]

end CoVaROSM


namespace CoVaROSM

open CoVaRMC.Batching

lemma integrable_fX (D : JointDensity) : Integrable D.fX := by
  have hfi : Integrable D.f ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]; exact D.integrable
  exact hfi.integral_prod_left

lemma measurable_fX' (D : JointDensity) : Measurable D.fX := by
  have : StronglyMeasurable D.f := D.measurable.stronglyMeasurable
  exact (this.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

lemma law_fst (D : JointDensity) :
    D.law.map Prod.fst = volume.withDensity (fun x => ENNReal.ofReal (D.fX x)) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, withDensity_apply _ hs]
  unfold JointDensity.law
  have hE : MeasurableSet (Prod.fst ⁻¹' s : Set (ℝ × ℝ)) := hs.preimage measurable_fst
  rw [withDensity_apply _ hE]
  have hprod : (Prod.fst ⁻¹' s : Set (ℝ × ℝ)) = s ×ˢ Set.univ := by ext q; simp
  have hr : ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (s ×ˢ Set.univ) =
      ((volume : Measure ℝ).restrict s).prod (volume : Measure ℝ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hfi : Integrable D.f ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]; exact D.integrable
  rw [hprod, Measure.volume_eq_prod, hr, lintegral_prod (fun a => ENNReal.ofReal (D.f a))
    (ENNReal.measurable_ofReal.comp D.measurable).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hfi.prod_right_ae] with x hx
  rw [← ofReal_integral_eq_lintegral_ofReal hx (Eventually.of_forall fun _ => D.nonneg _)]
  rfl

lemma law_fst_singleton (D : JointDensity) (x : ℝ) : (D.law.map Prod.fst) {x} = 0 := by
  rw [law_fst]
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

lemma law_fst_Iic (D : JointDensity) (z : ℝ) : (D.law.map Prod.fst).real (Set.Iic z) = D.FX z := by
  rw [measureReal_def, law_fst, withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_fX D).integrableOn
      (Eventually.of_forall fun x => integral_nonneg fun _ => D.nonneg _)]
  have hnn : ∀ x, 0 ≤ D.fX x := fun x => integral_nonneg fun _ => D.nonneg _
  rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic fun x _ => hnn x)]
  rfl

lemma hasDerivAt_FX (D : JointDensity) (x : ℝ) (hc : ContinuousAt D.fX x) :
    HasDerivAt D.FX (D.fX x) x := by
  have hgi := integrable_fX D
  have hsplit : D.FX = fun y => D.FX x + ∫ w in x..y, D.fX w := by
    funext y
    show ∫ u in Set.Iic y, D.fX u = (∫ u in Set.Iic x, D.fX u) + _
    rw [← intervalIntegral.integral_Iic_sub_Iic hgi.integrableOn hgi.integrableOn]
    ring
  rw [hsplit]
  exact (intervalIntegral.integral_hasDerivAt_right hgi.intervalIntegrable
    ((measurable_fX' D).stronglyMeasurable.stronglyMeasurableAtFilter) hc).const_add _

lemma monotone_FX (D : JointDensity) : Monotone D.FX := by
  intro a b hab
  exact setIntegral_mono_set (integrable_fX D).integrableOn
    (Eventually.of_forall fun x => integral_nonneg fun _ => D.nonneg _)
    (Eventually.of_forall (Set.Iic_subset_Iic.mpr hab))

/-- Local quadratic expansion of `F_X` at `v`, with a radius on which the linear term dominates. -/
lemma local_expansion (D : JointDensity) (v : ℝ) (𝒳 : Set ℝ) (h𝒳 : IsOpen 𝒳) (hv𝒳 : v ∈ 𝒳)
    (hfXc : ContDiffOn ℝ 1 D.fX 𝒳) (hfXpos : ∀ x ∈ 𝒳, 0 < D.fX x) :
    ∃ δ > 0, ∃ K ≥ 0, K * δ ≤ D.fX v / 2 ∧
      ∀ x, |x - v| ≤ δ → |D.FX x - D.FX v - D.fX v * (x - v)| ≤ K * (x - v) ^ 2 := by
  obtain ⟨δ0, hδ0, hball⟩ := Metric.isOpen_iff.mp h𝒳 v hv𝒳
  set δ1 := δ0 / 2 with hδ1
  have hδ1pos : 0 < δ1 := by positivity
  have hcb : Metric.closedBall v δ1 ⊆ 𝒳 := fun x hx =>
    hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith))
  have hdiff : ∀ x ∈ 𝒳, DifferentiableAt ℝ D.fX x := fun x hx =>
    ((hfXc.differentiableOn (by norm_num)) x hx).differentiableAt (h𝒳.mem_nhds hx)
  have hcont : ContinuousOn (deriv D.fX) 𝒳 := hfXc.continuousOn_deriv_of_isOpen h𝒳 (by norm_num)
  obtain ⟨K0, hK0⟩ := (isCompact_closedBall v δ1).exists_bound_of_continuousOn (hcont.mono hcb)
  set K := max K0 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  -- `|f_X(x) - f_X(v)| ≤ K |x - v|` on the ball
  have hlip : ∀ x ∈ Metric.closedBall v δ1, |D.fX x - D.fX v| ≤ K * |x - v| := by
    intro x hx
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := D.fX) (s := Metric.closedBall v δ1)
      (C := K) (fun z hz => hdiff z (hcb hz)) (fun z hz => (hK0 z hz).trans (le_max_left _ _))
      (convex_closedBall v δ1) (Metric.mem_closedBall_self hδ1pos.le) hx
    simpa [Real.norm_eq_abs] using this
  have hFd : ∀ x ∈ 𝒳, HasDerivAt D.FX (D.fX x) x := fun x hx =>
    hasDerivAt_FX D x ((hfXc.continuousOn).continuousAt (h𝒳.mem_nhds hx))
  have htay : ∀ x ∈ Metric.closedBall v δ1,
      |D.FX x - D.FX v - D.fX v * (x - v)| ≤ K * (x - v) ^ 2 := by
    intro x hx
    have hseg : Set.uIcc v x ⊆ Metric.closedBall v δ1 := by
      have hx' := hx
      rw [Real.closedBall_eq_Icc] at hx' ⊢
      exact Set.ordConnected_Icc.uIcc_subset (by constructor <;> linarith) hx'
    set h : ℝ → ℝ := fun z => D.FX z - D.fX v * z with hhdef
    have hhd : ∀ z ∈ Set.uIcc v x, HasDerivAt h (D.fX z - D.fX v) z := by
      intro z hz
      have := (hFd z (hcb (hseg hz))).sub ((hasDerivAt_id z).const_mul (D.fX v))
      rw [mul_one] at this
      exact this
    have hb := Convex.norm_image_sub_le_of_norm_deriv_le (f := h) (s := Set.uIcc v x)
      (C := K * |x - v|) (fun z hz => (hhd z hz).differentiableAt)
      (fun z hz => by
        rw [(hhd z hz).deriv, Real.norm_eq_abs]
        refine (hlip z (hseg hz)).trans ?_
        exact mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hz) hK)
      (convex_uIcc v x) Set.left_mem_uIcc Set.right_mem_uIcc
    simp only [hhdef, Real.norm_eq_abs] at hb
    have : D.FX x - D.fX v * x - (D.FX v - D.fX v * v) = D.FX x - D.FX v - D.fX v * (x - v) := by ring
    rw [this] at hb
    calc |D.FX x - D.FX v - D.fX v * (x - v)| ≤ K * |x - v| * |x - v| := hb
      _ = K * (x - v) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
  have hfv : 0 < D.fX v := hfXpos v hv𝒳
  refine ⟨min δ1 (D.fX v / (2 * (K + 1))), lt_min hδ1pos (by positivity), K, hK, ?_, ?_⟩
  · have h1 : min δ1 (D.fX v / (2 * (K + 1))) ≤ D.fX v / (2 * (K + 1)) := min_le_right _ _
    calc K * min δ1 (D.fX v / (2 * (K + 1))) ≤ K * (D.fX v / (2 * (K + 1))) :=
          mul_le_mul_of_nonneg_left h1 hK
      _ ≤ D.fX v / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  · intro x hx
    apply htay
    rw [Metric.mem_closedBall, Real.dist_eq]
    exact hx.trans (min_le_left _ _)

lemma vm_bound (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (n : ℝ) (hn : 1 ≤ n) (s : ℝ)
    (hs1 : α * n ≤ s) (hs2 : s ≤ α * n + 1) :
    s * (s + 1) / ((n + 1) * (n + 2)) - 2 * α * (s / (n + 1)) + α ^ 2 ≤ 1 / n := by
  have hn0 : 0 < n := by linarith
  set t := s - α * n with ht
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hs : s = α * n + t := by linarith
  have key : n * s * (s + 1) - 2 * α * s * n * (n + 2) + α ^ 2 * n * (n + 1) * (n + 2) ≤
      (n + 1) * (n + 2) := by
    have e : n * s * (s + 1) - 2 * α * s * n * (n + 2) + α ^ 2 * n * (n + 1) * (n + 2) =
        n ^ 2 * (α - α ^ 2) + n * (t ^ 2 + t - 4 * α * t + 2 * α ^ 2) := by
      rw [hs]; ring
    rw [e]
    have h1 : n ^ 2 * (α - α ^ 2) ≤ n ^ 2 / 4 := by
      have : α - α ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (α - 1 / 2)]
      nlinarith [sq_nonneg n]
    have h2 : n * (t ^ 2 + t - 4 * α * t + 2 * α ^ 2) ≤ n * 4 := by
      apply mul_le_mul_of_nonneg_left _ hn0.le
      nlinarith [mul_nonneg hα0.le ht0]
    nlinarith
  have hden : 0 < n * (n + 1) * (n + 2) := by positivity
  have e2 : s * (s + 1) / ((n + 1) * (n + 2)) - 2 * α * (s / (n + 1)) + α ^ 2 =
      (n * s * (s + 1) - 2 * α * s * n * (n + 2) + α ^ 2 * n * (n + 1) * (n + 2)) /
        (n * (n + 1) * (n + 2)) := by
    field_simp
  rw [e2, div_le_div_iff₀ hden hn0]
  nlinarith [key]

set_option maxHeartbeats 1000000 in
theorem osm_main (D : JointDensity) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (v : ℝ) (𝒳 : Set ℝ) (h𝒳 : IsOpen 𝒳) (hv𝒳 : v ∈ 𝒳)
    (hfXc : ContDiffOn ℝ 1 D.fX 𝒳) (hfXpos : ∀ x ∈ 𝒳, 0 < D.fX x) (hv : D.FX v = α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law) :
    ∃ δ > 0, ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      (P {ω | δ < |Xorder S α m 0 ω - v|}).toReal ≤ C / m ∧
      |∫ ω, Set.indicator {ω | |Xorder S α m 0 ω - v| ≤ δ}
          (fun ω => Xorder S α m 0 ω - v) ω ∂P| ≤ C / m ∧
      ∫ ω, Set.indicator {ω | |Xorder S α m 0 ω - v| ≤ δ}
          (fun ω => (Xorder S α m 0 ω - v) ^ 2) ω ∂P ≤ C / m := by
  have hDprob : IsProbabilityMeasure D.law := by
    rw [← hSl (0, 0)]; exact Measure.isProbabilityMeasure_map (hSm _).aemeasurable
  set ν := D.law.map Prod.fst with hνdef
  have hνprob : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hν : ∀ x, ν {x} = 0 := law_fst_singleton D
  have hFν : ∀ z, Fν ν z = D.FX z := law_fst_Iic D
  obtain ⟨δ, hδ, K, hK, hKδ, htay⟩ := local_expansion D v 𝒳 h𝒳 hv𝒳 hfXc hfXpos
  set f0 := D.fX v with hf0def
  have hf0 : 0 < f0 := hfXpos v hv𝒳
  set η := f0 * δ / 2 with hηdef
  have hη : 0 < η := by positivity
  set C := 1 / η ^ 2 + 1 / f0 * (1 + 1 / η ^ 2 + 4 * K / f0 ^ 2) + 4 / f0 ^ 2 with hCdef
  -- deterministic facts about `F_X`
  have P1 : ∀ x, |x - v| ≤ δ → f0 / 2 * |x - v| ≤ |D.FX x - α| := by
    intro x hx
    have h := htay x hx
    rw [hv] at h
    have hKx : K * (x - v) ^ 2 ≤ f0 / 2 * |x - v| := by
      rw [← sq_abs]
      calc K * |x - v| ^ 2 = (K * |x - v|) * |x - v| := by ring
        _ ≤ (K * δ) * |x - v| := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hK) (abs_nonneg _)
        _ ≤ f0 / 2 * |x - v| := mul_le_mul_of_nonneg_right hKδ (abs_nonneg _)
    have : f0 * |x - v| = |f0 * (x - v)| := by rw [abs_mul, abs_of_pos hf0]
    have h3 := abs_sub_abs_le_abs_sub (f0 * (x - v)) (D.FX x - α)
    rw [abs_sub_comm] at h
    have h4 : |f0 * (x - v) - (D.FX x - α)| = |D.FX x - α - f0 * (x - v)| := abs_sub_comm _ _
    linarith
  have P2 : ∀ x, δ < |x - v| → η ≤ |D.FX x - α| := by
    intro x hx
    rcases lt_abs.mp hx with h | h
    · have h1 := P1 (v + δ) (by rw [add_sub_cancel_left, abs_of_pos hδ])
      rw [add_sub_cancel_left, abs_of_pos hδ] at h1
      have hm : D.FX (v + δ) ≤ D.FX x := monotone_FX D (by linarith)
      have hm2 : α ≤ D.FX (v + δ) := by rw [← hv]; exact monotone_FX D (by linarith)
      rw [abs_of_nonneg (by linarith)] at h1
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have h1 := P1 (v - δ) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ])
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ] at h1
      have hm : D.FX x ≤ D.FX (v - δ) := monotone_FX D (by linarith)
      have hm2 : D.FX (v - δ) ≤ α := by rw [← hv]; exact monotone_FX D (by linarith)
      rw [abs_of_nonpos (by linarith)] at h1
      rw [abs_of_nonpos (by linarith)]
      linarith
  have P3 : ∀ x, |x - v| ≤ δ → |(D.FX x - α) - f0 * (x - v)| ≤ K * (x - v) ^ 2 := by
    intro x hx; have h := htay x hx; rw [hv] at h; exact h
  refine ⟨δ, hδ, C, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with m hm1
  have hm : 0 < m := hm1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmR0 : (0 : ℝ) < m := by linarith
  -- the batch and its law
  set Xv : Ω → (Fin m → ℝ) := fun ω j => (S (0, (j : ℕ)) ω).1 with hXvdef
  have hXvm : Measurable Xv := measurable_pi_lambda _ fun j => (hSm _).fst
  have hlaw : P.map Xv = Measure.pi (fun _ : Fin m => ν) := by
    have hind0 : iIndepFun (fun j : Fin m => S (0, (j : ℕ))) P :=
      hSi.precomp (g := fun j : Fin m => ((0 : ℕ), (j : ℕ)))
        (by intro a b h; simp only [Prod.mk.injEq, true_and] at h; exact Fin.ext h)
    have hind : iIndepFun (fun j : Fin m => fun ω => (S (0, (j : ℕ)) ω).1) P :=
      hind0.comp (fun _ => Prod.fst) (fun _ => measurable_fst)
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun j => (hSm _).fst.aemeasurable)).mp hind]
    congr 1; funext j
    rw [hνdef, ← hSl (0, (j : ℕ)), Measure.map_map measurable_fst (hSm _)]
    rfl
  set r := rankIdx α m hm with hrdef
  have hαm : 0 < α * m := mul_pos hα.1 hmR0
  have hceil_pos : 0 < ⌈α * m⌉₊ := Nat.ceil_pos.mpr hαm
  have hceil_le : ⌈α * m⌉₊ ≤ m := Nat.ceil_le.mpr (by nlinarith [hα.2])
  have hr : ((r : ℕ) : ℝ) + 1 = (⌈α * m⌉₊ : ℝ) := by
    have : (r : ℕ) = ⌈α * m⌉₊ - 1 := by simp only [hrdef, rankIdx]; omega
    rw [this]; push_cast [Nat.one_le_iff_ne_zero.mpr hceil_pos.ne']; ring
  have hs1 : α * m ≤ ((r : ℕ) : ℝ) + 1 := by rw [hr]; exact Nat.le_ceil _
  have hs2 : ((r : ℕ) : ℝ) + 1 ≤ α * m + 1 := by rw [hr]; exact (Nat.ceil_lt_add_one hαm.le).le
  set X : Ω → ℝ := fun ω => Xorder S α m 0 ω with hXdef
  have hXeq : ∀ ω, X ω = (fun y : Fin m → ℝ => y (Tuple.sort y r)) (Xv ω) := by
    intro ω; simp only [hXdef, Xorder, dif_pos hm, ImpactInvesting.Portfolio.orderStat]; rfl
  have hXm : Measurable X := by
    have : X = (fun y : Fin m → ℝ => y (Tuple.sort y r)) ∘ Xv := funext hXeq
    rw [this]; exact (measurable_os r).comp hXvm
  set U : Ω → ℝ := fun ω => D.FX (X ω) with hUdef
  have hUm : Measurable U := (monotone_FX D).measurable.comp hXm
  have hU01 : ∀ ω, 0 ≤ U ω ∧ U ω ≤ 1 := fun ω => by
    simp only [hUdef, ← hFν]; exact Fν_mem ν _
  have hint : ∀ (G : Ω → ℝ) (B : ℝ), Measurable G → (∀ ω, |G ω| ≤ B) → Integrable G P :=
    fun G B hG hB => Integrable.mono' (integrable_const B) hG.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB ω)
  have hUi : Integrable U P := hint U 1 hUm (fun ω => by
    rw [abs_of_nonneg (hU01 ω).1]; exact (hU01 ω).2)
  have hU2i : Integrable (fun ω => U ω ^ 2) P := hint _ 1 (hUm.pow_const 2) (fun ω => by
    rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [hU01 ω])
  have hEU : ∫ ω, U ω ∂P = (((r : ℕ) : ℝ) + 1) / (m + 1) := by
    calc ∫ ω, U ω ∂P = ∫ ω, (fun y : Fin m → ℝ => Fν ν (y (Tuple.sort y r))) (Xv ω) ∂P := by
          congr 1; funext ω; simp only [hUdef, hFν, hXeq]
      _ = ∫ y, Fν ν (y (Tuple.sort y r)) ∂(P.map Xv) := (integral_map hXvm.aemeasurable
          ((measurable_Fν ν).comp (measurable_os r)).aestronglyMeasurable).symm
      _ = _ := by rw [hlaw]; exact moment1 ν hν m r
  have hEU2 : ∫ ω, U ω ^ 2 ∂P = (((r : ℕ) : ℝ) + 1) * (((r : ℕ) : ℝ) + 2) / ((m + 1) * (m + 2)) := by
    calc ∫ ω, U ω ^ 2 ∂P = ∫ ω, (fun y : Fin m → ℝ => Fν ν (y (Tuple.sort y r)) ^ 2) (Xv ω) ∂P := by
          congr 1; funext ω; simp only [hUdef, hFν, hXeq]
      _ = ∫ y, Fν ν (y (Tuple.sort y r)) ^ 2 ∂(P.map Xv) := (integral_map hXvm.aemeasurable
          (((measurable_Fν ν).comp (measurable_os r)).pow_const 2).aestronglyMeasurable).symm
      _ = _ := by rw [hlaw]; exact moment2 ν hν m r
  -- second moment of `U - α`
  have hVi : Integrable (fun ω => (U ω - α) ^ 2) P := hint _ 1 ((hUm.sub measurable_const).pow_const 2)
    (fun ω => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := hU01 ω
      nlinarith [hα.1, hα.2])
  have hVm : ∫ ω, (U ω - α) ^ 2 ∂P ≤ 1 / m := by
    have e : (fun ω => (U ω - α) ^ 2) = fun ω => U ω ^ 2 - 2 * α * U ω + α ^ 2 := by
      funext ω; ring
    have i1 : Integrable (fun ω => U ω ^ 2 - 2 * α * U ω) P := hU2i.sub (hUi.const_mul _)
    rw [e, integral_add i1 (integrable_const _),
      integral_sub hU2i (hUi.const_mul _), integral_const_mul, integral_const, probReal_univ, one_smul,
      hEU, hEU2]
    have := vm_bound α hα.1 hα.2 m hmR (((r : ℕ) : ℝ) + 1) hs1 hs2
    have e2 : (((r : ℕ) : ℝ) + 1) * (((r : ℕ) : ℝ) + 2) = (((r : ℕ) : ℝ) + 1) * ((((r : ℕ) : ℝ) + 1) + 1) := by ring
    rw [e2]
    linarith
  have hbias : |∫ ω, U ω ∂P - α| ≤ 1 / m := by
    rw [hEU]
    set s' := ((r : ℕ) : ℝ) + 1
    have key : s' / (m + 1) - α = (s' - α * (m + 1)) / (m + 1) := by field_simp
    have h1 : -1 ≤ s' - α * (m + 1) := by nlinarith [hα.2]
    have h2 : s' - α * (m + 1) ≤ 1 := by nlinarith [hα.1]
    rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < m + 1)]
    calc |s' - α * (m + 1)| / (m + 1) ≤ 1 / (m + 1) :=
          div_le_div_of_nonneg_right (abs_le.mpr ⟨h1, h2⟩) (by positivity)
      _ ≤ 1 / m := one_div_le_one_div_of_le hmR0 (by linarith)
  set A : Set Ω := {ω | |X ω - v| ≤ δ} with hAdef
  set Ac : Set Ω := {ω | δ < |X ω - v|} with hAcdef
  have hAm : MeasurableSet A := measurableSet_le ((hXm.sub measurable_const).abs) measurable_const
  have hAcm : MeasurableSet Ac := measurableSet_lt measurable_const ((hXm.sub measurable_const).abs)
  have hAc_eq : Ac = Aᶜ := by ext ω; simp [hAdef, hAcdef, not_le]
  have hCpos1 : 0 ≤ 1 / η ^ 2 := by positivity
  have hCpos2 : 0 ≤ 1 / f0 * (1 + 1 / η ^ 2 + 4 * K / f0 ^ 2) := by positivity
  have hCpos3 : 0 ≤ 4 / f0 ^ 2 := by positivity
  -- (1) tail bound
  have hT : P.real Ac ≤ 1 / η ^ 2 / m := by
    have hsub : Ac ⊆ {ω | η ^ 2 ≤ (U ω - α) ^ 2} := by
      intro ω hω
      simp only [hAcdef, Set.mem_ofPred_eq] at hω
      have := P2 (X ω) hω
      simp only [Set.mem_ofPred_eq, hUdef]
      rw [← sq_abs (D.FX (X ω) - α)]
      exact pow_le_pow_left₀ hη.le this 2
    have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg (U ω - α))
      hVi (η ^ 2)
    have h1 : P.real Ac ≤ P.real {ω | η ^ 2 ≤ (U ω - α) ^ 2} := measureReal_mono hsub
    have h2 : P.real {ω | η ^ 2 ≤ (U ω - α) ^ 2} ≤ 1 / η ^ 2 / m := by
      have hle : η ^ 2 * P.real {ω | η ^ 2 ≤ (U ω - α) ^ 2} ≤ 1 / m := hmk.trans hVm
      rw [show (1 : ℝ) / η ^ 2 / m = (1 / m) / η ^ 2 by ring, le_div_iff₀ (by positivity)]
      linarith [mul_comm (η ^ 2) (P.real {ω | η ^ 2 ≤ (U ω - α) ^ 2})]
    linarith
  -- (3) truncated second moment
  have hQ : ∫ ω, A.indicator (fun ω => (X ω - v) ^ 2) ω ∂P ≤ 4 / f0 ^ 2 / m := by
    have hQi : Integrable (A.indicator (fun ω => (X ω - v) ^ 2)) P :=
      hint _ (δ ^ 2) (((hXm.sub measurable_const).pow_const 2).indicator hAm) (fun ω => by
        simp only [Set.indicator]; split_ifs with h
        · rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
        · simp [sq_nonneg])
    calc ∫ ω, A.indicator (fun ω => (X ω - v) ^ 2) ω ∂P ≤ ∫ ω, 4 / f0 ^ 2 * (U ω - α) ^ 2 ∂P := by
          apply integral_mono hQi (hVi.const_mul _)
          intro ω
          simp only [Set.indicator]
          split_ifs with h
          · have := P1 (X ω) h
            simp only [hUdef]
            have h2 : (f0 / 2 * |X ω - v|) ^ 2 ≤ |D.FX (X ω) - α| ^ 2 :=
              pow_le_pow_left₀ (by positivity) this 2
            rw [sq_abs, mul_pow, sq_abs] at h2
            rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
            nlinarith
          · positivity
      _ = 4 / f0 ^ 2 * ∫ ω, (U ω - α) ^ 2 ∂P := integral_const_mul _ _
      _ ≤ 4 / f0 ^ 2 * (1 / m) := mul_le_mul_of_nonneg_left hVm hCpos3
      _ = 4 / f0 ^ 2 / m := by ring
  -- (2) truncated bias
  have hB : |∫ ω, A.indicator (fun ω => X ω - v) ω ∂P| ≤
      1 / f0 * (1 + 1 / η ^ 2 + 4 * K / f0 ^ 2) / m := by
    set L := A.indicator (fun ω => X ω - v) with hLdef
    set Rr : Ω → ℝ := A.indicator (fun ω => (U ω - α) - f0 * (X ω - v)) with hRdef
    set Tt : Ω → ℝ := Ac.indicator (fun ω => U ω - α) with hTdef
    have hid : ∀ ω, f0 * L ω = (U ω - α) - Tt ω - Rr ω := by
      intro ω
      by_cases h : ω ∈ A
      · have h' : ω ∉ Ac := by rw [hAc_eq]; exact fun hc => hc h
        simp only [hLdef, hRdef, hTdef, Set.indicator_of_mem h, Set.indicator_of_notMem h']
        ring
      · have h' : ω ∈ Ac := by rw [hAc_eq]; exact h
        simp only [hLdef, hRdef, hTdef, Set.indicator_of_notMem h, Set.indicator_of_mem h']
        ring
    have hLm : Measurable L := (hXm.sub measurable_const).indicator hAm
    have hTm : Measurable Tt := (hUm.sub measurable_const).indicator hAcm
    have hRm : Measurable Rr :=
      ((hUm.sub measurable_const).sub (measurable_const.mul (hXm.sub measurable_const))).indicator hAm
    have hUa : ∀ ω, |U ω - α| ≤ 1 := fun ω => by
      have := hU01 ω; rw [abs_le]; constructor <;> linarith [hα.1, hα.2]
    have hTb : ∀ ω, |Tt ω| ≤ 1 := fun ω => by
      simp only [hTdef, Set.indicator]; split_ifs
      · exact hUa ω
      · simp
    have hRb : ∀ ω, |Rr ω| ≤ A.indicator (fun ω => K * (X ω - v) ^ 2) ω := fun ω => by
      simp only [hRdef, Set.indicator]; split_ifs with h
      · exact P3 (X ω) h
      · simp
    have hRbb : ∀ ω, |Rr ω| ≤ K * δ ^ 2 := fun ω => by
      refine (hRb ω).trans ?_
      by_cases h : ω ∈ A
      · rw [Set.indicator_of_mem h]
        have h' : |X ω - v| ≤ δ := h
        apply mul_le_mul_of_nonneg_left _ hK
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h' 2
      · rw [Set.indicator_of_notMem h]; positivity
    have hUai : Integrable (fun ω => U ω - α) P := hint _ 1 (hUm.sub measurable_const) hUa
    have hTi : Integrable Tt P := hint Tt 1 hTm hTb
    have hRi : Integrable Rr P := hint Rr (K * δ ^ 2) hRm hRbb
    have hLi : Integrable L P := hint L δ hLm (fun ω => by
      simp only [hLdef, Set.indicator]; split_ifs with h
      · exact h
      · simp [hδ.le])
    have hint_eq : f0 * ∫ ω, L ω ∂P = ∫ ω, (U ω - α) ∂P - ∫ ω, Tt ω ∂P - ∫ ω, Rr ω ∂P := by
      have i2 : Integrable (fun a => U a - α - Tt a) P :=
        hint _ 2 ((hUm.sub measurable_const).sub hTm) (fun ω => by
          have := hUa ω; have := hTb ω
          calc |U ω - α - Tt ω| ≤ |U ω - α| + |Tt ω| := abs_sub _ _
            _ ≤ 2 := by linarith)
      rw [← integral_const_mul, ← integral_sub hUai hTi, ← integral_sub i2 hRi]
      congr 1; funext ω; exact hid ω
    have e1 : |∫ ω, (U ω - α) ∂P| ≤ 1 / m := by
      rw [integral_sub hUi (integrable_const _), integral_const, probReal_univ, one_smul]
      exact hbias
    have e2 : |∫ ω, Tt ω ∂P| ≤ 1 / η ^ 2 / m := by
      calc |∫ ω, Tt ω ∂P| ≤ ∫ ω, |Tt ω| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ ω, Ac.indicator (fun _ => (1 : ℝ)) ω ∂P := by
            apply integral_mono hTi.abs ((integrable_const (1 : ℝ)).indicator hAcm)
            intro ω; simp only [hTdef, Set.indicator]; split_ifs
            · exact hUa ω
            · simp
        _ = P.real Ac := by rw [integral_indicator_const _ hAcm, smul_eq_mul, mul_one]
        _ ≤ 1 / η ^ 2 / m := hT
    have e3 : |∫ ω, Rr ω ∂P| ≤ K * (4 / f0 ^ 2 / m) := by
      have hQi' : Integrable (A.indicator (fun ω => K * (X ω - v) ^ 2)) P :=
        hint _ (K * δ ^ 2) ((measurable_const.mul ((hXm.sub measurable_const).pow_const 2)).indicator hAm)
          (fun ω => by
            simp only [Set.indicator]; split_ifs with h
            · rw [abs_of_nonneg (by positivity)]
              apply mul_le_mul_of_nonneg_left _ hK
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
            · simp; positivity)
      calc |∫ ω, Rr ω ∂P| ≤ ∫ ω, |Rr ω| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ ω, A.indicator (fun ω => K * (X ω - v) ^ 2) ω ∂P :=
            integral_mono hRi.abs hQi' hRb
        _ = K * ∫ ω, A.indicator (fun ω => (X ω - v) ^ 2) ω ∂P := by
            rw [← integral_const_mul]; congr 1; funext ω
            simp only [Set.indicator]; split_ifs <;> simp
        _ ≤ K * (4 / f0 ^ 2 / m) := mul_le_mul_of_nonneg_left hQ hK
    have habs : |f0 * ∫ ω, L ω ∂P| ≤ 1 / m + 1 / η ^ 2 / m + K * (4 / f0 ^ 2 / m) := by
      rw [hint_eq]
      calc |∫ ω, (U ω - α) ∂P - ∫ ω, Tt ω ∂P - ∫ ω, Rr ω ∂P|
          ≤ |∫ ω, (U ω - α) ∂P| + |∫ ω, Tt ω ∂P| + |∫ ω, Rr ω ∂P| := by
            have := abs_sub (∫ ω, (U ω - α) ∂P - ∫ ω, Tt ω ∂P) (∫ ω, Rr ω ∂P)
            have := abs_sub (∫ ω, (U ω - α) ∂P) (∫ ω, Tt ω ∂P)
            linarith
        _ ≤ _ := by linarith
    rw [abs_mul, abs_of_pos hf0] at habs
    rw [le_div_iff₀ hmR0]
    have : |∫ ω, L ω ∂P| ≤ (1 / m + 1 / η ^ 2 / m + K * (4 / f0 ^ 2 / m)) / f0 := by
      rw [le_div_iff₀ hf0]; linarith
    calc |∫ ω, L ω ∂P| * m ≤ (1 / m + 1 / η ^ 2 / m + K * (4 / f0 ^ 2 / m)) / f0 * m :=
          mul_le_mul_of_nonneg_right this hmR0.le
      _ = 1 / f0 * (1 + 1 / η ^ 2 + 4 * K / f0 ^ 2) := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← measureReal_def]
    calc P.real Ac ≤ 1 / η ^ 2 / m := hT
      _ ≤ C / m := div_le_div_of_nonneg_right (by linarith) hmR0.le
  · calc |∫ ω, A.indicator (fun ω => X ω - v) ω ∂P| ≤ 1 / f0 * (1 + 1 / η ^ 2 + 4 * K / f0 ^ 2) / m := hB
      _ ≤ C / m := div_le_div_of_nonneg_right (by linarith) hmR0.le
  · calc ∫ ω, A.indicator (fun ω => (X ω - v) ^ 2) ω ∂P ≤ 4 / f0 ^ 2 / m := hQ
      _ ≤ C / m := div_le_div_of_nonneg_right (by linarith) hmR0.le

end CoVaROSM

open CoVaRMC.Batching in
theorem solution (D : JointDensity) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (v : ℝ) (𝒳 : Set ℝ) (h𝒳 : IsOpen 𝒳) (hv𝒳 : v ∈ 𝒳)
    (hfXc : ContDiffOn ℝ 1 D.fX 𝒳) (hfXpos : ∀ x ∈ 𝒳, 0 < D.fX x) (hv : D.FX v = α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law) :
    ∃ δ > 0, ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      (P {ω | δ < |Xorder S α m 0 ω - v|}).toReal ≤ C / m ∧
      |∫ ω, Set.indicator {ω | |Xorder S α m 0 ω - v| ≤ δ}
          (fun ω => Xorder S α m 0 ω - v) ω ∂P| ≤ C / m ∧
      ∫ ω, Set.indicator {ω | |Xorder S α m 0 ω - v| ≤ δ}
          (fun ω => (Xorder S α m 0 ω - v) ^ 2) ω ∂P ≤ C / m :=
  CoVaROSM.osm_main D α hα v 𝒳 h𝒳 hv𝒳 hfXc hfXpos hv P S hSm hSi hSl
