-- Prove2me | solution 1 for GIGnBounds.Tail.server_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T03:24:43.684072+00:00
-- url     : https://prove2.me/submissions/83fccdbc-5d1f-4152-83ac-190762fb08d2

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory
namespace GIGnBounds.Tail

namespace SCAux

noncomputable def cnt {n : ℕ} (v : Fin n → ℝ) (y : ℝ) : ℕ :=
  (Finset.univ.filter (fun j => v j ≤ y)).card

lemma cnt_sortVec {n : ℕ} (v : Fin n → ℝ) (y : ℝ) : cnt (sortVec v) y = cnt v y := by
  unfold cnt sortVec
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp (Tuple.sort v) (fun j => if v j ≤ y then 1 else 0)

lemma work_mono {n : ℕ} (z : ℝ × (Fin n → ℝ)) (a s : ℕ → ℝ) (k : ℕ) :
    Monotone (work z a s k) := by
  cases k <;> (simp only [work]; exact Tuple.monotone_sort _)

lemma cnt_add {n' m : ℕ} (v : Fin (n' + m) → ℝ) (y : ℝ) :
    cnt v y = cnt (fun i => v (Fin.castAdd m i)) y + cnt (fun j => v (Fin.natAdd n' j)) y := by
  unfold cnt; simp only [Finset.card_filter]; exact Fin.sum_univ_add _

lemma cnt_zero_of_lt {n : ℕ} (v : Fin n → ℝ) (h0 : 0 < n) (hv : Monotone v) (y : ℝ)
    (hy : y < v ⟨0, h0⟩) : cnt v y = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ hj
  have : v ⟨0, h0⟩ ≤ v j := hv (Fin.mk_le_of_le_val (Nat.zero_le _))
  linarith

lemma cnt_pos {n : ℕ} (v : Fin n → ℝ) (h0 : 0 < n) : 1 ≤ cnt v (v ⟨0, h0⟩) := by
  unfold cnt
  exact Finset.card_pos.mpr ⟨⟨0, h0⟩, by simp⟩

lemma min_le {n n' : ℕ} (V : Fin n → ℝ) (W : Fin n' → ℝ) (h0 : 0 < n) (h0' : 0 < n')
    (hV : Monotone V) (H : ∀ y, cnt W y ≤ cnt V y) : V ⟨0, h0⟩ ≤ W ⟨0, h0'⟩ := by
  have h1 := le_trans (cnt_pos W h0') (H _)
  unfold cnt at h1
  obtain ⟨j, hj⟩ := Finset.card_pos.mp h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact le_trans (hV (Fin.mk_le_of_le_val (Nat.zero_le _))) hj

/-- bump identity -/
lemma cnt_bump {n : ℕ} (v : Fin n → ℝ) (h0 : 0 < n) (s y : ℝ) :
    cnt (fun i => v i + (if (i : ℕ) = 0 then s else 0)) y + (if v ⟨0, h0⟩ ≤ y then 1 else 0) =
      cnt v y + (if v ⟨0, h0⟩ + s ≤ y then 1 else 0) := by
  unfold cnt
  simp only [Finset.card_filter]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, h0⟩ : Fin n)),
    ← Finset.add_sum_erase _ (fun j => if v j ≤ y then 1 else 0)
      (Finset.mem_univ (⟨0, h0⟩ : Fin n))]
  have : ∑ x ∈ Finset.univ.erase (⟨0, h0⟩ : Fin n),
      (if v x + (if (x : ℕ) = 0 then s else 0) ≤ y then 1 else 0) =
      ∑ x ∈ Finset.univ.erase (⟨0, h0⟩ : Fin n), (if v x ≤ y then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    have : (x : ℕ) ≠ 0 := by
      intro h; apply (Finset.mem_erase.mp hx).1; exact Fin.ext h
    simp [this]
  rw [this]
  simp only [if_true]
  omega

lemma cnt_step {n : ℕ} (v : Fin n → ℝ) (s a y : ℝ) (hy : 0 ≤ y) :
    cnt (fun i => max (v i + (if (i : ℕ) = 0 then s else 0) - a) 0) y =
      cnt (fun i => v i + (if (i : ℕ) = 0 then s else 0)) (y + a) := by
  unfold cnt
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [max_le_iff]
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; exact ⟨by linarith, hy⟩

lemma cnt_neg {n : ℕ} (v : Fin n → ℝ) (y : ℝ) (hy : y < 0) :
    cnt (fun i => max (v i) 0) y = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ hj
  have := le_max_right (v j) 0
  linarith

lemma step_inv {n n' : ℕ} (V : Fin n → ℝ) (W : Fin n' → ℝ) (h0 : 0 < n) (h0' : 0 < n')
    (hV : Monotone V) (hW : Monotone W) (H : ∀ y, cnt W y ≤ cnt V y) (s a : ℝ) (hs : 0 ≤ s)
    (y : ℝ) :
    cnt (fun i => max (W i + (if (i : ℕ) = 0 then s else 0) - a) 0) y ≤
      cnt (fun i => max (V i + (if (i : ℕ) = 0 then s else 0) - a) 0) y := by
  rcases lt_or_ge y 0 with hy | hy
  · rw [cnt_neg _ y hy]; exact Nat.zero_le _
  rw [cnt_step _ _ _ _ hy, cnt_step _ _ _ _ hy]
  have hVW := min_le V W h0 h0' hV H
  set y' := y + a
  have eV := cnt_bump V h0 s y'
  have eW := cnt_bump W h0' s y'
  have hH := H y'
  have zV : y' < V ⟨0, h0⟩ → cnt V y' = 0 := cnt_zero_of_lt V h0 hV y'
  have zW : y' < W ⟨0, h0'⟩ → cnt W y' = 0 := cnt_zero_of_lt W h0' hW y'
  by_cases c1 : V ⟨0, h0⟩ ≤ y' <;> by_cases c2 : V ⟨0, h0⟩ + s ≤ y' <;>
    by_cases c3 : W ⟨0, h0'⟩ ≤ y' <;> by_cases c4 : W ⟨0, h0'⟩ + s ≤ y' <;>
    simp only [c1, c2, c3, c4, if_true, if_false] at eV eW <;>
    first
    | omega
    | (exfalso; linarith)
    | (have := zV (by linarith); omega)
    | (have := zW (by linarith); omega)
    | (have := zV (by linarith); have := zW (by linarith); omega)

def ext {n' m : ℕ} (w : Fin n' → ℝ) : Fin (n' + m) → ℝ :=
  fun i => if h : (i : ℕ) < n' then w ⟨i, h⟩ else 0

@[simp] lemma ext_castAdd {n' m : ℕ} (w : Fin n' → ℝ) (i : Fin n') :
    ext (m := m) w (Fin.castAdd m i) = w i := by
  simp [ext]

@[simp] lemma ext_natAdd {n' m : ℕ} (w : Fin n' → ℝ) (j : Fin m) :
    ext (m := m) w (Fin.natAdd n' j) = 0 := by
  simp [ext]

lemma inv {n' m : ℕ} (hn' : 0 < n') (T : ℝ) (w : Fin n' → ℝ) (a s : ℕ → ℝ)
    (hs : ∀ k, 0 ≤ s k) (k : ℕ) :
    ∀ y, cnt (work (T, w) a s k) y ≤ cnt (work (T, ext (m := m) w) a s k) y := by
  induction k with
  | zero =>
    intro y
    simp only [work, cnt_sortVec]
    rw [cnt_add (fun i => max (ext (m := m) w i - T) 0)]
    simp only [ext_castAdd]
    exact Nat.le_add_right _ _
  | succ k ih =>
    intro y
    simp only [work, cnt_sortVec]
    exact step_inv _ _ (by omega) hn' (work_mono _ _ _ _) (work_mono _ _ _ _) ih _ _ (hs k) y

lemma delay_le {n' m : ℕ} (hn' : 0 < n') (T : ℝ) (w : Fin n' → ℝ) (a s : ℕ → ℝ)
    (hs : ∀ k, 0 ≤ s k) (k : ℕ) :
    delay (T, ext (m := m) w) a s k ≤ delay (T, w) a s k := by
  unfold delay
  rw [dif_pos (by omega), dif_pos hn']
  exact min_le _ _ _ _ (work_mono _ _ _ _) (inv hn' T w a s hs k)

lemma nis_le {n' m : ℕ} (hn' : 0 < n') (T : ℝ) (w : Fin n' → ℝ) (a s : ℕ → ℝ)
    (hs : ∀ k, 0 ≤ s k) (t : ℝ) (ht : 0 ≤ t)
    (hfin : {k : ℕ | T + ∑ j ∈ Finset.range k, a j ≤ t}.Finite) :
    numInSystem (T, ext (m := m) w) a s t ≤ numInSystem (T, w) a s t := by
  unfold numInSystem
  apply add_le_add
  · apply le_of_eq
    simp only [Finset.card_filter]
    rw [Fin.sum_univ_add]
    simp [not_lt.mpr ht]
  · show Nat.card ↥{k : ℕ | arrTime (T, ext (m := m) w) a k ≤ t ∧
        t < arrTime (T, ext (m := m) w) a k + delay (T, ext (m := m) w) a s k + s k} ≤
      Nat.card ↥{k : ℕ | arrTime (T, w) a k ≤ t ∧ t < arrTime (T, w) a k + delay (T, w) a s k + s k}
    apply Nat.card_mono
    · exact hfin.subset (fun k hk => hk.1)
    · intro k hk
      have := delay_le (m := m) hn' T w a s hs k
      simp only [Set.mem_ofPred_eq, arrTime] at hk ⊢
      exact ⟨hk.1, by linarith [hk.2]⟩


lemma diverge (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (ε : ℝ) (hε : 0 < ε)
    (hinf : ∀ N, ∃ j ≥ N, ε ≤ a j) (T t : ℝ) :
    {k : ℕ | T + ∑ j ∈ Finset.range k, a j ≤ t}.Finite := by
  have mono : ∀ k k', k ≤ k' → ∑ j ∈ Finset.range k, a j ≤ ∑ j ∈ Finset.range k', a j :=
    fun k k' h => Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
      (fun i _ _ => ha i)
  have key : ∀ M : ℕ, ∃ K, ∀ k ≥ K, (M : ℝ) * ε ≤ ∑ j ∈ Finset.range k, a j := by
    intro M
    induction M with
    | zero => exact ⟨0, fun k _ => by simpa using Finset.sum_nonneg (fun i _ => ha i)⟩
    | succ M ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨j, hj, hεj⟩ := hinf K
      refine ⟨j + 1, fun k hk => ?_⟩
      have h1 := hK j hj
      have h2 := mono (j + 1) k hk
      rw [Finset.sum_range_succ] at h2
      push_cast; linarith
  obtain ⟨M, hM⟩ := exists_nat_gt ((t - T) / ε)
  obtain ⟨K, hK⟩ := key M
  apply (Finset.finite_toSet (Finset.range K)).subset
  intro k hk
  simp only [Set.mem_ofPred_eq] at hk
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hcon
  have := hK k (not_lt.mp hcon)
  rw [div_lt_iff₀ hε] at hM
  linarith

lemma exists_eps (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : IsTimeLaw μ) :
    ∃ ε > 0, 0 < μ (Set.Ici ε) := by
  by_contra hc
  push Not at hc
  have hnull : μ {x : ℝ | ¬ x ≤ 0} = 0 := by
    apply measure_mono_null (t := ⋃ n : ℕ, Set.Ici (1 / ((n : ℝ) + 1)))
    · intro x hx
      simp only [Set.mem_ofPred_eq, not_le] at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact Set.mem_iUnion.mpr ⟨n, le_of_lt hn⟩
    · exact measure_iUnion_null (fun n => le_antisymm (hc _ (by positivity)) bot_le)
  have hae : (fun x : ℝ => x) ≤ᵐ[μ] 0 := by
    rw [Filter.EventuallyLE, ae_iff]; simpa using hnull
  have := integral_nonpos_of_ae hae
  linarith [h.mean_pos]

lemma ae_good (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS) :
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μA.prod μS)),
      (∀ k, 0 ≤ (x k).2) ∧ ∀ T t : ℝ, {k : ℕ | T + ∑ j ∈ Finset.range k, (x j).1 ≤ t}.Finite := by
  have single : ∀ (k : ℕ) (U : Set (ℝ × ℝ)), MeasurableSet U →
      Measure.infinitePi (fun _ : ℕ => μA.prod μS) {x | x k ∈ U} = (μA.prod μS) U := by
    intro k U hU
    have : {x : ℕ → ℝ × ℝ | x k ∈ U} = Set.pi (↑({k} : Finset ℕ)) (fun _ => U) := by
      ext x; simp
    rw [this, Measure.infinitePi_pi _ (fun _ _ => hU), Finset.prod_singleton]
  have h1 : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μA.prod μS)), ∀ k, 0 ≤ (x k).1 := by
    rw [ae_all_iff]; intro k
    rw [ae_iff]
    have := single k (Set.Iio 0 ×ˢ Set.univ) (measurableSet_Iio.prod MeasurableSet.univ)
    rw [Measure.prod_prod, hA.nonneg, zero_mul] at this
    refine measure_mono_null (fun x hx => ?_) this
    simp only [Set.mem_ofPred_eq, not_le] at hx
    exact ⟨hx, trivial⟩
  have h2 : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μA.prod μS)), ∀ k, 0 ≤ (x k).2 := by
    rw [ae_all_iff]; intro k
    rw [ae_iff]
    have := single k (Set.univ ×ˢ Set.Iio 0) (MeasurableSet.univ.prod measurableSet_Iio)
    rw [Measure.prod_prod, hS.nonneg, mul_zero] at this
    refine measure_mono_null (fun x hx => ?_) this
    simp only [Set.mem_ofPred_eq, not_le] at hx
    exact ⟨trivial, hx⟩
  obtain ⟨ε, hε, hp⟩ := exists_eps μA hA
  have hq : μA (Set.Iio ε) < 1 := by
    rw [← Set.compl_Ici, prob_compl_eq_one_sub measurableSet_Ici]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp.ne'
  have h3 : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μA.prod μS)), ∀ N, ∃ j ≥ N, ε ≤ (x j).1 := by
    rw [ae_all_iff]; intro N
    rw [ae_iff]
    apply le_antisymm _ bot_le
    apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
    intro M
    have hsub : {x : ℕ → ℝ × ℝ | ¬ ∃ j ≥ N, ε ≤ (x j).1} ⊆
        Set.pi (↑(Finset.Ico N (N + M))) (fun _ => Set.Iio ε ×ˢ Set.univ) := by
      intro x hx i hi
      simp only [Set.mem_ofPred_eq, not_exists, not_and, not_le] at hx
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi
      exact ⟨hx i hi.1, trivial⟩
    refine (measure_mono hsub).trans (le_of_eq ?_)
    rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_Iio.prod MeasurableSet.univ)]
    simp [Measure.prod_prod]
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  exact ⟨hx2, fun T t => diverge _ hx1 ε hε hx3 T t⟩

lemma eqLaw_finite (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : IsTimeLaw μ) :
    IsFiniteMeasure (eqLaw μ) := by
  constructor
  unfold eqLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (rate μ * (μ (Set.Ioi z)).toReal)
      ≤ ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (rate μ) * μ {a | z < a} := by
        apply lintegral_mono
        intro z
        dsimp only
        rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg]
        gcongr
        exact ENNReal.ofReal_toReal_le
    _ = ENNReal.ofReal (rate μ) * ∫⁻ x, ENNReal.ofReal x ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_eq_lintegral_meas_lt μ (f := fun x => x) _ aemeasurable_id]
        rw [Filter.EventuallyLE, ae_iff]
        simpa [Set.Iio] using h.nonneg
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.integrable.lintegral_lt_top

lemma ext_measurable {n' m : ℕ} : Measurable (ext (n' := n') (m := m)) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  simp only [ext]
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

noncomputable def Fm {n' m : ℕ} : QueueSpace n' → QueueSpace (n' + m) :=
  fun ω => ((ω.1.1, ext (m := m) ω.1.2), ω.2)

lemma Fm_emb {n' m : ℕ} : MeasurableEmbedding (Fm (n' := n') (m := m)) := by
  refine MeasurableEmbedding.of_measurable_inverse
    (g := fun ω : QueueSpace (n' + m) => ((ω.1.1, fun i => ω.1.2 (Fin.castAdd m i)), ω.2))
    ?_ ?_ ?_ ?_
  · exact (measurable_fst.fst.prodMk (ext_measurable.comp measurable_fst.snd)).prodMk measurable_snd
  · have : Set.range (Fm (n' := n') (m := m)) =
        ⋂ j : Fin m, {ω : QueueSpace (n' + m) | ω.1.2 (Fin.natAdd n' j) = 0} := by
      ext ω
      simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨ω', rfl⟩ j; simp [Fm]
      · intro h
        refine ⟨((ω.1.1, fun i => ω.1.2 (Fin.castAdd m i)), ω.2), ?_⟩
        obtain ⟨⟨T, v⟩, x⟩ := ω
        simp only [Fm, Prod.mk.injEq, and_true, true_and]
        funext i
        refine Fin.addCases (fun i => ?_) (fun j => ?_) i
        · simp
        · simpa using (h j).symm
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_eq_fun (by fun_prop) measurable_const
  · fun_prop
  · intro ω; simp [Fm]

lemma pi_pad {n' m : ℕ} (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Measure.pi (fun i : Fin (n' + m) => if (i : ℕ) < n' then ν else Measure.dirac 0) =
      (Measure.pi (fun _ : Fin n' => ν)).map (ext (m := m)) := by
  have : ∀ i : Fin (n' + m), SigmaFinite (if (i : ℕ) < n' then ν else Measure.dirac (0 : ℝ)) :=
    fun i => by split_ifs <;> infer_instance
  refine Measure.pi_eq (fun S hS => ?_)
  rw [Measure.map_apply ext_measurable (MeasurableSet.univ_pi hS), Fin.prod_univ_add]
  simp only [Fin.val_castAdd, Fin.is_lt, if_true, Fin.val_natAdd, add_lt_iff_neg_left,
    not_lt_zero, if_false]
  by_cases hz : ∀ j, (0 : ℝ) ∈ S (Fin.natAdd n' j)
  · have : ext (m := m) ⁻¹' Set.univ.pi S = Set.univ.pi (fun i => S (Fin.castAdd m i)) := by
      ext w; simp [Fin.forall_fin_add, hz]
    rw [this, Measure.pi_pi, Finset.prod_eq_one (fun j _ => Measure.dirac_apply_of_mem (hz j)),
      mul_one]
  · push Not at hz
    obtain ⟨j, hj⟩ := hz
    have : ext (m := m) ⁻¹' Set.univ.pi S = ∅ := by
      ext w; simp only [Set.mem_preimage, Set.mem_univ_pi, Fin.forall_fin_add, ext_castAdd,
        ext_natAdd, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ h; exact hj (h j)
    rw [this, measure_empty, Finset.prod_eq_zero (Finset.mem_univ j), mul_zero]
    rw [Measure.dirac_apply' _ (hS _), Set.indicator_of_notMem hj]

lemma meas_eq {n' m : ℕ} (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS) :
    queueMeasure (n' + m) μA μS ((eqLaw μA).prod
        (Measure.pi (fun i : Fin (n' + m) => if (i : ℕ) < n' then eqLaw μS else Measure.dirac 0))) =
      (queueMeasure n' μA μS (resInit n' μA μS)).map (Fm (m := m)) := by
  have := eqLaw_finite μA hA
  have := eqLaw_finite μS hS
  unfold queueMeasure resInit
  rw [pi_pad]
  conv_lhs => rw [← Measure.map_id (μ := eqLaw μA),
    Measure.map_prod_map _ _ measurable_id ext_measurable,
    ← Measure.map_id (μ := Measure.infinitePi (fun _ : ℕ => μA.prod μS)),
    Measure.map_prod_map _ _ (measurable_id.prodMap ext_measurable) measurable_id]
  rfl

end SCAux

end GIGnBounds.Tail

open GIGnBounds.Tail

theorem solution (n n' : ℕ) (hn' : 1 ≤ n') (hnn' : n' ≤ n) (μA μS : Measure ℝ)
    [IsProbabilityMeasure μA] [IsProbabilityMeasure μS] (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (t z : ℝ) (ht : 0 ≤ t) :
    (queueMeasure n μA μS ((eqLaw μA).prod
        (Measure.pi (fun i : Fin n => if (i : ℕ) < n' then eqLaw μS else Measure.dirac 0)))).real
        {ω | z ≤ (queueLength ω t : ℝ)} ≤
      (queueMeasure n' μA μS (resInit n' μA μS)).real {ω | z ≤ (queueLength ω t : ℝ)} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnn'
  have := SCAux.eqLaw_finite μA hA
  have := SCAux.eqLaw_finite μS hS
  rw [SCAux.meas_eq μA μS hA hS]
  simp only [measureReal_def]
  rw [SCAux.Fm_emb.map_apply]
  have : IsFiniteMeasure (queueMeasure n' μA μS (resInit n' μA μS)) := by
    unfold queueMeasure resInit; infer_instance
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  have hg := SCAux.ae_good μA μS hA hS
  have hP : ∀ᵐ ω ∂(queueMeasure n' μA μS (resInit n' μA μS)), (∀ k, 0 ≤ (ω.2 k).2) ∧
      ∀ T t : ℝ, {k : ℕ | T + ∑ j ∈ Finset.range k, (ω.2 j).1 ≤ t}.Finite := by
    unfold queueMeasure
    rw [ae_iff] at hg ⊢
    refine measure_mono_null (t := Set.univ ×ˢ {x : ℕ → ℝ × ℝ | ¬((∀ k, 0 ≤ (x k).2) ∧
      ∀ T t : ℝ, {k : ℕ | T + ∑ j ∈ Finset.range k, (x j).1 ≤ t}.Finite)})
      (fun ω hω => ⟨Set.mem_univ _, hω⟩) ?_
    rw [Measure.prod_prod, hg, mul_zero]
  filter_upwards [hP] with ω hω hmem
  obtain ⟨⟨T, w⟩, x⟩ := ω
  have h1 : z ≤ (queueLength (SCAux.Fm (m := m) ((T, w), x)) t : ℝ) := hmem
  show z ≤ (queueLength ((T, w), x) t : ℝ)
  refine le_trans h1 ?_
  exact_mod_cast SCAux.nis_le (by omega) T w _ _ hω.1 t ht (hω.2 T t)


