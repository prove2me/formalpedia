-- Prove2me | solution 1 for DynDoubleAuction.TwoSided.exit_tails
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T00:49:50.88243+00:00
-- url     : https://prove2.me/submissions/f8ed6538-5638-4115-9062-411584fde082

import Mathlib
import Definitions.Def_DynDoubleAuction_TwoSided_Model

namespace DDAx
open DynDoubleAuction.TwoSided
open MeasureTheory Filter Topology

lemma buyers_nonempty {n : ℕ} (hn : 1 ≤ n) : (Finset.univ.erase (0 : Fin (n + 1))).Nonempty :=
  ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩

lemma maxBuyer_eq {n : ℕ} (hn : 1 ≤ n) (v : Fin (n + 1) → ℝ) :
    maxBuyer v = (Finset.univ.erase (0 : Fin (n + 1))).sup' (buyers_nonempty hn) v := by
  unfold maxBuyer; simp [buyers_nonempty hn]

lemma le_maxBuyer {n : ℕ} (hn : 1 ≤ n) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hi : i ≠ 0) :
    v i ≤ maxBuyer v := by
  rw [maxBuyer_eq hn]; exact Finset.le_sup' v (by simp [hi])

lemma maxBuyer_attained {n : ℕ} (hn : 1 ≤ n) (v : Fin (n + 1) → ℝ) :
    ∃ i, i ≠ 0 ∧ maxBuyer v = v i := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup' (buyers_nonempty hn) v
  exact ⟨i, by simpa using hi, by rw [maxBuyer_eq hn, h]⟩

lemma maxBuyer_le {n : ℕ} (hn : 1 ≤ n) (v : Fin (n + 1) → ℝ) (C : ℝ)
    (h : ∀ i, i ≠ 0 → v i ≤ C) : maxBuyer v ≤ C := by
  obtain ⟨i, hi, he⟩ := maxBuyer_attained hn v; rw [he]; exact h i hi

lemma measurable_maxBuyer {n : ℕ} (hn : 1 ≤ n) :
    Measurable (fun v : Fin (n + 1) → ℝ => maxBuyer v) := by
  have : (fun v : Fin (n + 1) → ℝ => maxBuyer v) =
      (Finset.univ.erase (0 : Fin (n + 1))).sup' (buyers_nonempty hn)
        (fun i (v : Fin (n + 1) → ℝ) => v i) := by
    funext v; rw [maxBuyer_eq hn, Finset.sup'_apply]
  rw [this]
  exact Finset.measurable_sup' _ (fun i _ => measurable_pi_apply i)

section rules
variable {n : ℕ} (M : Market n) (T t : ℕ) (w v : Fin (n + 1) → ℝ)

open Classical in
lemma rq_med (h : Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).q i = if i = 0 then (if v 0 ≤ maxBuyer v then 1 else 0)
      else (if isWinner v i then 1 else 0) := by
  classical
  simp [rule, h]

lemma rz_med (h : Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).z i = v i * (rule M T t w v).q i := by
  simp [rule, h]

lemma ru_med (h : Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).u i = w i + max (maxBuyer v - v 0) 0 - wlow M := by
  simp [rule, h]

lemma rq_nmed (h : ¬ Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).q i = if i = 0 then min 1 (w 0 / mu M) * (if v 0 ≤ M.r then 1 else 0)
      else M.α i * min 1 (w i / mu M) * (if v 0 ≤ M.r then 1 else 0) := by
  simp [rule, h]

lemma rz_nmed (h : ¬ Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).z i = if i = 0 then M.r * (rule M T t w v).q 0 else 0 := by
  simp [rule, h]

lemma ru_nmed (h : ¬ Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).u i = max (w i - mu M) 0 := by
  simp [rule, h]

end rules

lemma winner_unique {n : ℕ} (v : Fin (n + 1) → ℝ) (i j : Fin (n + 1))
    (hi : isWinner v i) (hj : isWinner v j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := hj.2.2.2 i hi.1 h; linarith [hi.2.2.1, hj.2.2.1]
  · exact h
  · have := hi.2.2.2 j hj.1 h; linarith [hi.2.2.1, hj.2.2.1]

open Classical in
lemma winners_sum_le {n : ℕ} (v : Fin (n + 1) → ℝ) :
    (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (if isWinner v i then (1:ℝ) else 0)) ≤
      (if v 0 ≤ maxBuyer v then 1 else 0) := by
  rw [Finset.sum_boole]
  by_cases hw : ∃ i, isWinner v i
  · obtain ⟨i, hi⟩ := hw
    have h0 : v 0 ≤ maxBuyer v := by linarith [hi.2.1, hi.2.2.1]
    rw [if_pos h0]
    have : ((Finset.univ.erase (0 : Fin (n + 1))).filter (fun i => isWinner v i)).card ≤ 1 :=
      Finset.card_le_one.2 (fun a ha b hb =>
        winner_unique v a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2)
    exact_mod_cast this
  · push_neg at hw
    have : ((Finset.univ.erase (0 : Fin (n + 1))).filter (fun i => isWinner v i)) = ∅ :=
      Finset.filter_eq_empty_iff.2 (fun x _ => hw x)
    rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; split_ifs <;> norm_num

end DDAx

namespace DDAx
open DynDoubleAuction.TwoSided
open MeasureTheory

lemma maxBuyer_congr {n : ℕ} (hn : 1 ≤ n) (v v' : Fin (n + 1) → ℝ)
    (h : ∀ i, i ≠ 0 → v i = v' i) : maxBuyer v = maxBuyer v' := by
  rw [maxBuyer_eq hn, maxBuyer_eq hn]
  exact Finset.sup'_congr _ rfl (fun i hi => h i (by simpa using hi))

end DDAx


namespace DDAx
open MeasureTheory Filter

variable {V : Type*} [MeasurableSpace V]

lemma map_update_infinitePi (F : Measure V) [IsProbabilityMeasure F] (k : ℕ) :
    ((Measure.infinitePi (fun _ : ℕ => F)).prod F).map
      (fun p : (ℕ → V) × V => Function.update p.1 k p.2) =
      Measure.infinitePi (fun _ : ℕ => F) := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (measurable_update' (a := k)) (MeasurableSet.pi s.countable_toSet
    (fun i _ => ht i))]
  have hpre : (fun p : (ℕ → V) × V => Function.update p.1 k p.2) ⁻¹' (Set.pi (↑s) t) =
      (Set.pi (↑(s.erase k)) t) ×ˢ (if k ∈ s then t k else Set.univ) := by
    ext ⟨vs, v⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨fun i ⟨hik, his⟩ => ?_, ?_⟩
      · have := h i his; rwa [Function.update_of_ne hik] at this
      · split_ifs with hk
        · have := h k hk; rwa [Function.update_self] at this
        · trivial
    · rintro ⟨h1, h2⟩ i his
      by_cases hik : i = k
      · subst hik; rw [Function.update_self]; rwa [if_pos his] at h2
      · rw [Function.update_of_ne hik]; exact h1 i ⟨hik, his⟩
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi (μ := fun _ : ℕ => F) (mt := fun i _ => ht i)]
  split_ifs with hk
  · rw [← Finset.prod_erase_mul _ _ hk]
  · rw [Finset.erase_eq_of_notMem hk, measure_univ, mul_one]

lemma step_integral (F : Measure V) [IsProbabilityMeasure F] (k : ℕ)
    {A : Type*} [MeasurableSpace A]
    (h : (ℕ → V) → A) (hh : Measurable h)
    (hk : ∀ vs v, h (Function.update vs k v) = h vs)
    (f : A → V → ℝ) (hf : Measurable (Function.uncurry f)) (C : ℝ)
    (hb : ∀ᵐ vs ∂(Measure.infinitePi (fun _ : ℕ => F)), ∀ᵐ v ∂F, |f (h vs) v| ≤ C) :
    ∫ vs, f (h vs) (vs k) ∂(Measure.infinitePi (fun _ : ℕ => F)) =
      ∫ vs, (∫ v, f (h vs) v ∂F) ∂(Measure.infinitePi (fun _ : ℕ => F)) := by
  classical
  have hg : Measurable (fun p : (ℕ → V) × V => f (h p.1) p.2) :=
    hf.comp ((hh.comp measurable_fst).prodMk measurable_snd)
  have hint : Integrable (fun p : (ℕ → V) × V => f (h p.1) p.2) ((Measure.infinitePi (fun _ : ℕ => F)).prod F) := by
    refine Integrable.of_bound hg.aestronglyMeasurable C ?_
    rw [Measure.ae_prod_iff_ae_ae]
    · simpa [Real.norm_eq_abs] using hb
    · exact measurableSet_le (by fun_prop) measurable_const
  have e1 : ∫ vs, f (h vs) (vs k) ∂(Measure.infinitePi (fun _ : ℕ => F)) =
      ∫ p, f (h (Function.update p.1 k p.2)) (Function.update p.1 k p.2 k) ∂((Measure.infinitePi (fun _ : ℕ => F)).prod F) := by
    conv_lhs => rw [← map_update_infinitePi F k]
    rw [integral_map (measurable_update' (a := k)).aemeasurable]
    exact (hf.comp ((hh.comp measurable_id).prodMk (measurable_pi_apply k))).aestronglyMeasurable
  rw [e1]
  simp only [Function.update_self, hk]
  exact integral_prod _ hint
end DDAx


namespace DDAx
open DynDoubleAuction.TwoSided MeasureTheory Filter

section st
variable {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)

noncomputable def Xf (v : Fin (n + 1) → ℝ) : ℝ := max (maxBuyer v - v 0) 0

open Classical in
noncomputable def uf (t : ℕ) (c : ℝ) (v : Fin (n + 1) → ℝ) : ℝ :=
  if Medium M T t c then c + Xf v - wlow M else max (c - mu M) 0

noncomputable def cst (vs : ℕ → Fin (n + 1) → ℝ) (k : ℕ) : ℝ := state M T w1 vs k 0

lemma state_coupled (vs : ℕ → Fin (n + 1) → ℝ) (k : ℕ) :
    state M T w1 vs k = fun _ => cst M T w1 vs k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext j
    show (rule M T (k + 1) (state M T w1 vs k) (vs k)).u j =
      (rule M T (k + 1) (state M T w1 vs k) (vs k)).u 0
    by_cases h : Medium M T (k + 1) (state M T w1 vs k 0)
    · rw [ru_med M T (k + 1) _ _ h, ru_med M T (k + 1) _ _ h, ih]
    · rw [ru_nmed M T (k + 1) _ _ h, ru_nmed M T (k + 1) _ _ h, ih]

lemma cst_zero (vs : ℕ → Fin (n + 1) → ℝ) : cst M T w1 vs 0 = w1 := rfl

lemma cst_succ (vs : ℕ → Fin (n + 1) → ℝ) (k : ℕ) :
    cst M T w1 vs (k + 1) = uf M T (k + 1) (cst M T w1 vs k) (vs k) := by
  show (rule M T (k + 1) (state M T w1 vs k) (vs k)).u 0 = _
  rw [state_coupled M T w1 vs k]
  by_cases h : Medium M T (k + 1) (cst M T w1 vs k)
  · rw [ru_med M T (k + 1) (fun _ => cst M T w1 vs k) (vs k) h, uf, if_pos h]; rfl
  · rw [ru_nmed M T (k + 1) (fun _ => cst M T w1 vs k) (vs k) h, uf, if_neg h]

lemma cst_update (vs : ℕ → Fin (n + 1) → ℝ) (m : ℕ) (v : Fin (n + 1) → ℝ) :
    ∀ k ≤ m, cst M T w1 (Function.update vs m v) k = cst M T w1 vs k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [cst_succ, cst_succ, ih (by omega), Function.update_of_ne (by omega)]

lemma measurableSet_medium (t : ℕ) : MeasurableSet {c : ℝ | Medium M T t c} := by
  unfold Medium
  exact (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_lt measurable_id measurable_const)

lemma measurable_Xf (hn : 1 ≤ n) : Measurable (fun v : Fin (n + 1) → ℝ => Xf v) :=
  ((measurable_maxBuyer hn).sub (measurable_pi_apply 0)).max measurable_const

lemma measurable_uf (hn : 1 ≤ n) (t : ℕ) :
    Measurable (Function.uncurry (uf M T t)) := by
  unfold uf Function.uncurry
  refine Measurable.ite ((measurableSet_medium M T t).preimage measurable_fst) ?_ ?_
  · exact (measurable_fst.add ((measurable_Xf hn).comp measurable_snd)).sub measurable_const
  · exact (measurable_fst.sub measurable_const).max measurable_const

lemma measurable_cst (hn : 1 ≤ n) (k : ℕ) :
    Measurable (fun vs : ℕ → Fin (n + 1) → ℝ => cst M T w1 vs k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simp_rw [cst_succ]
    exact (measurable_uf M T hn (k + 1)).comp (ih.prodMk (measurable_pi_apply k))

lemma Xf_bounds (hn : 1 ≤ n) (v : Fin (n + 1) → ℝ) (hv : ∀ j, v j ∈ Set.Icc 0 M.vbar)
    (hvb : 0 < M.vbar) : 0 ≤ Xf v ∧ Xf v ≤ M.vbar := by
  refine ⟨le_max_right _ _, max_le ?_ hvb.le⟩
  have := maxBuyer_le hn v M.vbar (fun i _ => (hv i).2)
  linarith [(hv 0).1]

lemma cst_range (hM : Standing M) (hw1 : 0 ≤ w1 ∧ w1 ≤ wbar M T 1)
    (vs : ℕ → Fin (n + 1) → ℝ) (hvs : ∀ k j, vs k j ∈ Set.Icc 0 M.vbar) :
    ∀ k ≤ T, 0 ≤ cst M T w1 vs k ∧ cst M T w1 vs k ≤ wbar M T (k + 1) := by
  obtain ⟨hn, -, hvb, -, -, -, -, -, hmw, hmu⟩ := hM
  intro k
  induction k with
  | zero => intro _; rw [cst_zero]; exact ⟨hw1.1, by simpa using hw1.2⟩
  | succ k ih =>
    intro hk
    obtain ⟨a0, a1⟩ := ih (by omega)
    have hwb : wbar M T (k + 1 + 1) = wbar M T (k + 1) - mu M := by
      simp only [wbar]; push_cast; ring
    have hwb0 : 0 ≤ wbar M T (k + 1 + 1) := by
      simp only [wbar]
      apply mul_nonneg _ hmu.le
      have : ((k:ℝ) + 1) ≤ T := by exact_mod_cast hk
      push_cast; linarith
    obtain ⟨hX0, hX1⟩ := Xf_bounds M hn (vs k) (hvs k) hvb
    rw [cst_succ, uf]
    split_ifs with hmed
    · obtain ⟨m1, m2⟩ := hmed
      refine ⟨by linarith, ?_⟩
      rw [hwb]; linarith
    · exact ⟨le_max_right _ _, max_le (by linarith) hwb0⟩

end st

lemma ae_box {n : ℕ} (M : Market n) (hae : ∀ᵐ v ∂M.F, ∀ j, v j ∈ Set.Icc 0 M.vbar)
    [IsProbabilityMeasure M.F] :
    ∀ᵐ vs ∂(valueLaw M), ∀ k j, vs k j ∈ Set.Icc 0 M.vbar := by
  rw [ae_all_iff]
  intro k
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => M.F) k).quasiMeasurePreserving.ae hae

end DDAx


namespace DDAx
open DynDoubleAuction.TwoSided MeasureTheory Filter

section per
variable {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)

noncomputable def ind (v : Fin (n + 1) → ℝ) : ℝ := if v 0 ≤ M.r then 1 else 0
noncomputable def mf (c : ℝ) : ℝ := min 1 (c / mu M)

open Classical in
noncomputable def πf (t : ℕ) (c : ℝ) (v : Fin (n + 1) → ℝ) : ℝ :=
  if Medium M T t c then Xf v else -(M.r * (mf M c * ind M v))

open Classical in
noncomputable def sf (t : ℕ) (c : ℝ) (v : Fin (n + 1) → ℝ) : ℝ :=
  if Medium M T t c then Xf v else
    mf M c * ind M v * ((∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * v i) - v 0)

open Classical in
lemma exists_winner {n : ℕ} (hn : 1 ≤ n) (v : Fin (n + 1) → ℝ) (h0 : v 0 ≤ maxBuyer v) :
    ∃ i, isWinner v i := by
  classical
  set S := (Finset.univ.erase (0 : Fin (n + 1))).filter (fun i => v i = maxBuyer v)
  obtain ⟨i0, hi0, he⟩ := maxBuyer_attained hn v
  have hS : S.Nonempty := ⟨i0, by simp [S, hi0, he]⟩
  refine ⟨S.min' hS, ?_⟩
  have hmem := Finset.min'_mem S hS
  simp only [S, Finset.mem_filter, Finset.mem_erase] at hmem
  refine ⟨hmem.1.1, by rw [hmem.2]; exact h0, hmem.2, ?_⟩
  intro j hj hjlt
  rcases (le_maxBuyer hn v j hj).lt_or_eq with hlt | heq
  · rw [hmem.2]; exact hlt
  · exfalso
    have : j ∈ S := by simp [S, hj, heq]
    exact absurd (Finset.min'_le S j this) (not_le.2 hjlt)

open Classical in
lemma medium_sum (hn : 1 ≤ n) (v : Fin (n + 1) → ℝ) :
    (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), v i * (if isWinner v i then 1 else 0)) -
      v 0 * (if v 0 ≤ maxBuyer v then 1 else 0) = Xf v := by
  unfold Xf
  by_cases h0 : v 0 ≤ maxBuyer v
  · obtain ⟨i, hi⟩ := exists_winner hn v h0
    rw [Finset.sum_eq_single_of_mem i (by simp [hi.1]) (fun j _ hj => by
      rw [if_neg (fun hw => hj (winner_unique v j i hw hi))]; ring), if_pos hi, if_pos h0,
      max_eq_left (by linarith), hi.2.2.1]
    ring
  · rw [if_neg h0, max_eq_right (by linarith)]
    rw [Finset.sum_eq_zero (fun i _ => by
      rw [if_neg (fun hw => h0 (by linarith [hw.2.1, hw.2.2.1]))]; ring)]
    ring

lemma profit_period (hn : 1 ≤ n) (vs : ℕ → Fin (n + 1) → ℝ) (k : ℕ) :
    (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (periodOutcome M T w1 vs k).z i) -
      (periodOutcome M T w1 vs k).z 0 = πf M T (k + 1) (cst M T w1 vs k) (vs k) := by
  unfold periodOutcome
  rw [state_coupled M T w1 vs k]
  set c := cst M T w1 vs k
  by_cases h : Medium M T (k + 1) c
  · have hz := rz_med M T (k + 1) (fun _ => c) (vs k) h
    have hq := rq_med M T (k + 1) (fun _ => c) (vs k) h
    rw [πf, if_pos h, ← medium_sum hn (vs k), hz 0, hq 0, if_pos rfl]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hz i, hq i, if_neg (Finset.ne_of_mem_erase hi)]
  · have hz := rz_nmed M T (k + 1) (fun _ => c) (vs k) h
    have hq := rq_nmed M T (k + 1) (fun _ => c) (vs k) h
    rw [πf, if_neg h, Finset.sum_eq_zero (fun i hi => by rw [hz i, if_neg (Finset.ne_of_mem_erase hi)]),
      hz 0, if_pos rfl, hq 0, if_pos rfl]
    simp [mf, ind]

lemma welfare_period (hn : 1 ≤ n) (vs : ℕ → Fin (n + 1) → ℝ) (k : ℕ) :
    (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), vs k i * (periodOutcome M T w1 vs k).q i) -
      vs k 0 * (periodOutcome M T w1 vs k).q 0 = sf M T (k + 1) (cst M T w1 vs k) (vs k) := by
  unfold periodOutcome
  rw [state_coupled M T w1 vs k]
  set c := cst M T w1 vs k
  by_cases h : Medium M T (k + 1) c
  · have hq := rq_med M T (k + 1) (fun _ => c) (vs k) h
    rw [sf, if_pos h, ← medium_sum hn (vs k), hq 0, if_pos rfl]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hq i, if_neg (Finset.ne_of_mem_erase hi)]
  · have hq := rq_nmed M T (k + 1) (fun _ => c) (vs k) h
    rw [sf, if_neg h, hq 0, if_pos rfl, mul_sub, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i hi => by rw [hq i, if_neg (Finset.ne_of_mem_erase hi)])]
    simp only [mf, ind]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => by ring)
    · ring

lemma profitPath_eq (hn : 1 ≤ n) (vs : ℕ → Fin (n + 1) → ℝ) :
    profitPath M T w1 vs = ∑ k ∈ Finset.range T, πf M T (k + 1) (cst M T w1 vs k) (vs k) := by
  unfold profitPath
  exact Finset.sum_congr rfl (fun k _ => profit_period M T w1 hn vs k)

lemma welfarePath_eq (hn : 1 ≤ n) (vs : ℕ → Fin (n + 1) → ℝ) :
    welfarePath M T w1 vs = ∑ k ∈ Finset.range T, sf M T (k + 1) (cst M T w1 vs k) (vs k) := by
  unfold welfarePath
  exact Finset.sum_congr rfl (fun k _ => welfare_period M T w1 hn vs k)

end per
end DDAx


namespace DDAx
open DynDoubleAuction.TwoSided MeasureTheory Filter

section ident
variable {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)

lemma measurable_ind : Measurable (ind M) :=
  Measurable.ite (measurableSet_le (measurable_pi_apply 0) measurable_const)
    measurable_const measurable_const

lemma measurable_mf : Measurable (mf M) :=
  measurable_const.min (measurable_id.div_const _)

lemma measurable_πf (hn : 1 ≤ n) (t : ℕ) : Measurable (Function.uncurry (πf M T t)) := by
  unfold πf Function.uncurry
  refine Measurable.ite ((measurableSet_medium M T t).preimage measurable_fst) ?_ ?_
  · exact (measurable_Xf hn).comp measurable_snd
  · exact (measurable_const.mul (((measurable_mf M).comp measurable_fst).mul
      ((measurable_ind M).comp measurable_snd))).neg

lemma measurable_sumα : Measurable (fun v : Fin (n + 1) → ℝ =>
    ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * v i) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))

lemma measurable_sf (hn : 1 ≤ n) (t : ℕ) : Measurable (Function.uncurry (sf M T t)) := by
  unfold sf Function.uncurry
  refine Measurable.ite ((measurableSet_medium M T t).preimage measurable_fst) ?_ ?_
  · exact (measurable_Xf hn).comp measurable_snd
  · exact (((measurable_mf M).comp measurable_fst).mul ((measurable_ind M).comp measurable_snd)).mul
      (((measurable_sumα M).comp measurable_snd).sub ((measurable_pi_apply 0).comp measurable_snd))

lemma mf_bounds (hmu : 0 < mu M) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ mf M c ∧ mf M c ≤ 1 :=
  ⟨le_min zero_le_one (div_nonneg hc hmu.le), min_le_left _ _⟩

lemma ind_bounds (v : Fin (n + 1) → ℝ) : 0 ≤ ind M v ∧ ind M v ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma mf_mu (hmu : 0 < mu M) {c : ℝ} (hc : 0 ≤ c) : c - max (c - mu M) 0 = mf M c * mu M := by
  unfold mf
  rw [min_mul_of_nonneg _ _ hmu.le, one_mul, div_mul_cancel₀ _ hmu.ne']
  rcases le_total (mu M) c with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]; ring

lemma sumα_bounds (hM : Standing M) (v : Fin (n + 1) → ℝ) (hv : ∀ j, v j ∈ Set.Icc 0 M.vbar) :
    0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * v i ∧
    ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * v i ≤ M.vbar := by
  obtain ⟨hn, -, hvb, -, -, hα, -, hαsum, -, -⟩ := hM
  constructor
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (hα i (Finset.ne_of_mem_erase hi)).1 (hv i).1)
  · calc _ ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * M.vbar :=
          Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hv i).2
            (hα i (Finset.ne_of_mem_erase hi)).1)
      _ = (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i) * M.vbar := by rw [Finset.sum_mul]
      _ ≤ 1 * M.vbar := mul_le_mul_of_nonneg_right hαsum hvb.le
      _ = M.vbar := one_mul _

lemma wlow_nonneg (hM : Standing M) : 0 ≤ wlow M := by
  obtain ⟨-, -, -, -, -, -, -, -, hmw, hmu⟩ := hM; linarith

lemma πf_abs (hM : Standing M) (t : ℕ) {c : ℝ} (hc : 0 ≤ c) (v : Fin (n + 1) → ℝ)
    (hv : ∀ j, v j ∈ Set.Icc 0 M.vbar) : |πf M T t c v| ≤ M.vbar := by
  have hM' := hM
  obtain ⟨hn, -, hvb, -, hr, -, -, -, -, hmu⟩ := hM
  obtain ⟨x0, x1⟩ := Xf_bounds M hn v hv hvb
  obtain ⟨m0, m1⟩ := mf_bounds M hmu hc
  obtain ⟨i0, i1⟩ := ind_bounds M v
  unfold πf; split_ifs
  · rw [abs_le]; constructor <;> linarith
  · have h1 : 0 ≤ mf M c * ind M v := mul_nonneg m0 i0
    have h2 : mf M c * ind M v ≤ 1 := by nlinarith
    have h3 : 0 ≤ M.r * (mf M c * ind M v) := mul_nonneg hr.1 h1
    have h4 : M.r * (mf M c * ind M v) ≤ M.vbar := by nlinarith [hr.2, hr.1]
    rw [abs_le]; constructor <;> linarith

lemma sf_abs (hM : Standing M) (t : ℕ) {c : ℝ} (hc : 0 ≤ c) (v : Fin (n + 1) → ℝ)
    (hv : ∀ j, v j ∈ Set.Icc 0 M.vbar) : |sf M T t c v| ≤ M.vbar := by
  have hM' := hM
  obtain ⟨hn, -, hvb, -, hr, -, -, -, -, hmu⟩ := hM
  obtain ⟨x0, x1⟩ := Xf_bounds M hn v hv hvb
  obtain ⟨m0, m1⟩ := mf_bounds M hmu hc
  obtain ⟨i0, i1⟩ := ind_bounds M v
  obtain ⟨s0, s1⟩ := sumα_bounds M hM' v hv
  unfold sf; split_ifs
  · rw [abs_le]; constructor <;> linarith
  · have h1 : 0 ≤ mf M c * ind M v := mul_nonneg m0 i0
    have h2 : mf M c * ind M v ≤ 1 := by nlinarith
    rw [abs_mul, abs_of_nonneg h1]
    have : |∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * v i - v 0| ≤ M.vbar := by
      rw [abs_le]; constructor <;> linarith [(hv 0).1, (hv 0).2]
    calc _ ≤ 1 * M.vbar := mul_le_mul h2 this (abs_nonneg _) zero_le_one
      _ = M.vbar := one_mul _

lemma uf_abs (hM : Standing M) (t : ℕ) {c : ℝ} (hc : 0 ≤ c) (v : Fin (n + 1) → ℝ)
    (hv : ∀ j, v j ∈ Set.Icc 0 M.vbar) : |c - uf M T t c v| ≤ wlow M + M.vbar + mu M := by
  have hM' := hM
  obtain ⟨hn, -, hvb, -, hr, -, -, -, hmw, hmu⟩ := hM
  obtain ⟨x0, x1⟩ := Xf_bounds M hn v hv hvb
  unfold uf; split_ifs
  · rw [abs_le]; constructor <;> linarith
  · rw [mf_mu M hmu hc]
    obtain ⟨m0, m1⟩ := mf_bounds M hmu hc
    have : mf M c * mu M ≤ mu M := by nlinarith
    rw [abs_le]; constructor <;> nlinarith

noncomputable def Df (t : ℕ) (c : ℝ) (v : Fin (n + 1) → ℝ) : ℝ :=
  πf M T t c v - sf M T t c v + ((n : ℝ) + 1) * (c - uf M T t c v)

lemma Df_abs (hM : Standing M) (t : ℕ) {c : ℝ} (hc : 0 ≤ c) (v : Fin (n + 1) → ℝ)
    (hv : ∀ j, v j ∈ Set.Icc 0 M.vbar) :
    |Df M T t c v| ≤ M.vbar + M.vbar + ((n : ℝ) + 1) * (wlow M + M.vbar + mu M) := by
  unfold Df
  have h1 := πf_abs M T hM t hc v hv
  have h2 := sf_abs M T hM t hc v hv
  have h3 := uf_abs M T hM t hc v hv
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  calc _ ≤ |πf M T t c v - sf M T t c v| + |((n : ℝ) + 1) * (c - uf M T t c v)| := abs_add_le _ _
    _ ≤ (|πf M T t c v| + |sf M T t c v|) + ((n : ℝ) + 1) * |c - uf M T t c v| := by
        rw [abs_mul, abs_of_nonneg hn1]; gcongr; exact abs_sub _ _
    _ ≤ _ := by gcongr

lemma measurable_Df (hn : 1 ≤ n) (t : ℕ) : Measurable (Function.uncurry (Df M T t)) := by
  unfold Df
  exact ((measurable_πf M T hn t).sub (measurable_sf M T hn t)).add
    (measurable_const.mul (measurable_fst.sub (measurable_uf M T hn t)))

lemma integrable_Xf (hM : Standing M) : Integrable (fun v : Fin (n + 1) → ℝ => Xf v) M.F := by
  obtain ⟨hn, hP, hvb, hae, -, -, -, -, -, -⟩ := hM
  refine Integrable.of_bound (measurable_Xf hn).aestronglyMeasurable M.vbar ?_
  filter_upwards [hae] with v hv
  obtain ⟨a, b⟩ := Xf_bounds M hn v hv hvb
  rw [Real.norm_eq_abs, abs_of_nonneg a]; exact b

lemma integral_Xf (M : Market n) : ∫ v, Xf v ∂M.F = wlow M := rfl

lemma Df_integral (hM : Standing M) (t : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ v, Df M T t c v ∂M.F = 0 := by
  have hM' := hM
  obtain ⟨hn, hP, hvb, hae, hr, hα, hαmu, hαsum, hmw, hmu⟩ := hM
  have hXi := integrable_Xf M hM'
  by_cases hmed : Medium M T t c
  · have : (fun v => Df M T t c v) = fun v => ((n : ℝ) + 1) * (wlow M - Xf v) := by
      funext v; unfold Df πf sf uf; simp only [if_pos hmed]; ring
    rw [this, integral_const_mul, integral_sub (integrable_const _) hXi, integral_const,
      integral_Xf]
    simp
  · have hint1 : Integrable (fun v : Fin (n + 1) → ℝ => max (M.r - v 0) 0) M.F := by
      refine Integrable.of_bound ?_ M.vbar ?_
      · exact ((measurable_const.sub (measurable_pi_apply 0)).max
          measurable_const).aestronglyMeasurable
      · filter_upwards [hae] with v hv
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [(hv 0).1, hr.2]) hvb.le
    have hint2 : ∀ j, Integrable (fun v : Fin (n + 1) → ℝ => v j * ind M v) M.F := by
      intro j
      refine Integrable.of_bound ?_ M.vbar ?_
      · exact ((measurable_pi_apply j).mul (measurable_ind M)).aestronglyMeasurable
      · filter_upwards [hae] with v hv
        rw [Real.norm_eq_abs]
        unfold ind
        split_ifs
        · rw [mul_one, abs_of_nonneg (hv j).1]; exact (hv j).2
        · simp [hvb.le]
    have : (fun v => Df M T t c v) = fun v =>
        ((n : ℝ) + 1) * (mf M c * mu M) - mf M c * (max (M.r - v 0) 0 +
          ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * (v i * ind M v)) := by
      funext v
      unfold Df πf sf uf
      simp only [if_neg hmed]
      rw [mf_mu M hmu hc]
      have e : max (M.r - v 0) 0 = (M.r - v 0) * ind M v := by
        unfold ind; split_ifs with h
        · rw [max_eq_left (by linarith)]; ring
        · rw [max_eq_right (by linarith)]; ring
      have e2 : ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * (v i * ind M v) =
          (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * v i) * ind M v := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [e, e2]; ring
    rw [this, integral_sub (integrable_const _), integral_const, integral_const_mul,
      integral_add hint1 (integrable_finset_sum _ (fun i _ => (hint2 i).const_mul _)),
      integral_finset_sum _ (fun i _ => (hint2 i).const_mul _)]
    · have hsum : ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), ∫ v, M.α i * (v i * ind M v) ∂M.F
          = ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), mu M := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [integral_const_mul]; exact hαmu i (Finset.ne_of_mem_erase hi)
      rw [hsum, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
      simp only [integral_const, probReal_univ, one_smul, nsmul_eq_mul]
      have : ∫ v, max (M.r - v 0) 0 ∂M.F = mu M := rfl
      rw [this]; push_cast; ring
    · exact (hint1.add (integrable_finset_sum _ (fun i _ => (hint2 i).const_mul _))).const_mul _

end ident
end DDAx


namespace DDAx
open DynDoubleAuction.TwoSided MeasureTheory Filter

section pid
variable {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)

lemma ae_cst (hM : Standing M) (hw1 : 0 ≤ w1 ∧ w1 ≤ wbar M T 1) :
    ∀ᵐ vs ∂(valueLaw M), ∀ k ≤ T, 0 ≤ cst M T w1 vs k ∧ cst M T w1 vs k ≤ wbar M T (k + 1) := by
  have hM' := hM
  obtain ⟨-, hP, -, hae, -⟩ := hM
  filter_upwards [ae_box M hae] with vs hvs
  exact cst_range M T w1 hM' hw1 vs hvs

theorem valueLaw_prob (hP : IsProbabilityMeasure M.F) : IsProbabilityMeasure (valueLaw M) := by
  unfold valueLaw; infer_instance

lemma integrable_πk (hM : Standing M) (hw1 : 0 ≤ w1 ∧ w1 ≤ wbar M T 1) (k : ℕ) (hk : k < T) :
    Integrable (fun vs => πf M T (k + 1) (cst M T w1 vs k) (vs k)) (valueLaw M) := by
  have hM' := hM
  obtain ⟨hn, hP, -, hae, -⟩ := hM
  haveI := valueLaw_prob M hP
  refine Integrable.of_bound ?_ M.vbar ?_
  · exact ((measurable_πf M T hn (k + 1)).comp
      ((measurable_cst M T w1 hn k).prodMk (measurable_pi_apply k))).aestronglyMeasurable
  · filter_upwards [ae_box M hae, ae_cst M T w1 hM' hw1] with vs hvs hc
    rw [Real.norm_eq_abs]
    exact πf_abs M T hM' _ (hc k hk.le).1 _ (hvs k)

lemma integrable_sk (hM : Standing M) (hw1 : 0 ≤ w1 ∧ w1 ≤ wbar M T 1) (k : ℕ) (hk : k < T) :
    Integrable (fun vs => sf M T (k + 1) (cst M T w1 vs k) (vs k)) (valueLaw M) := by
  have hM' := hM
  obtain ⟨hn, hP, -, hae, -⟩ := hM
  haveI := valueLaw_prob M hP
  refine Integrable.of_bound ?_ M.vbar ?_
  · exact ((measurable_sf M T hn (k + 1)).comp
      ((measurable_cst M T w1 hn k).prodMk (measurable_pi_apply k))).aestronglyMeasurable
  · filter_upwards [ae_box M hae, ae_cst M T w1 hM' hw1] with vs hvs hc
    rw [Real.norm_eq_abs]
    exact sf_abs M T hM' _ (hc k hk.le).1 _ (hvs k)

lemma integrable_cst (hM : Standing M) (hw1 : 0 ≤ w1 ∧ w1 ≤ wbar M T 1) (k : ℕ) (hk : k ≤ T) :
    Integrable (fun vs => cst M T w1 vs k) (valueLaw M) := by
  have hM' := hM
  obtain ⟨hn, hP, -, hae, -, -, -, -, -, hmu⟩ := hM
  haveI := valueLaw_prob M hP
  refine Integrable.of_bound (measurable_cst M T w1 hn k).aestronglyMeasurable (wbar M T 1) ?_
  filter_upwards [ae_cst M T w1 hM' hw1] with vs hc
  rw [Real.norm_eq_abs, abs_of_nonneg (hc k hk).1]
  refine (hc k hk).2.trans ?_
  unfold wbar; apply mul_le_mul_of_nonneg_right _ hmu.le; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]

lemma Dk_integral (hM : Standing M) (hw1 : 0 ≤ w1 ∧ w1 ≤ wbar M T 1) (k : ℕ) (hk : k < T) :
    ∫ vs, Df M T (k + 1) (cst M T w1 vs k) (vs k) ∂(valueLaw M) = 0 := by
  have hM' := hM
  obtain ⟨hn, hP, -, hae, -⟩ := hM
  haveI := valueLaw_prob M hP
  unfold valueLaw
  rw [step_integral M.F k (fun vs => cst M T w1 vs k) (measurable_cst M T w1 hn k)
    (fun vs v => cst_update M T w1 vs k v k le_rfl) (Df M T (k + 1))
    (measurable_Df M T hn (k + 1)) (M.vbar + M.vbar + ((n : ℝ) + 1) * (wlow M + M.vbar + mu M)) ?_]
  · rw [← integral_zero (ℕ → Fin (n + 1) → ℝ) ℝ]
    apply integral_congr_ae
    filter_upwards [ae_cst M T w1 hM' hw1] with vs hc
    exact Df_integral M T hM' (k + 1) (hc k hk.le).1
  · filter_upwards [ae_cst M T w1 hM' hw1] with vs hc
    filter_upwards [hae] with v hv
    exact Df_abs M T hM' (k + 1) (hc k hk.le).1 v hv

theorem profit_identity (hM : Standing M) (hw1 : 0 ≤ w1 ∧ w1 ≤ wbar M T 1) :
    expectedProfit M T w1 = expectedWelfare M T w1 - ((n : ℝ) + 1) * w1 := by
  have hM' := hM
  obtain ⟨hn, hP, -, hae, -⟩ := hM
  haveI := valueLaw_prob M hP
  have hP1 : expectedProfit M T w1 =
      ∑ k ∈ Finset.range T, ∫ vs, πf M T (k + 1) (cst M T w1 vs k) (vs k) ∂(valueLaw M) := by
    unfold expectedProfit
    simp_rw [profitPath_eq M T w1 hn]
    exact integral_finsetSum _ (fun k hk => integrable_πk M T w1 hM' hw1 k (Finset.mem_range.1 hk))
  have hS1 : expectedWelfare M T w1 =
      ∑ k ∈ Finset.range T, ∫ vs, sf M T (k + 1) (cst M T w1 vs k) (vs k) ∂(valueLaw M) := by
    unfold expectedWelfare
    simp_rw [welfarePath_eq M T w1 hn]
    exact integral_finsetSum _ (fun k hk => integrable_sk M T w1 hM' hw1 k (Finset.mem_range.1 hk))
  have hk : ∀ k ∈ Finset.range T,
      (∫ vs, πf M T (k + 1) (cst M T w1 vs k) (vs k) ∂(valueLaw M)) -
      (∫ vs, sf M T (k + 1) (cst M T w1 vs k) (vs k) ∂(valueLaw M)) =
      -(((n : ℝ) + 1) * ((∫ vs, cst M T w1 vs k ∂(valueLaw M)) -
        (∫ vs, cst M T w1 vs (k + 1) ∂(valueLaw M)))) := by
    intro k hkT
    have hkT := Finset.mem_range.1 hkT
    have h0 := Dk_integral M T w1 hM' hw1 k hkT
    have e : (fun vs => Df M T (k + 1) (cst M T w1 vs k) (vs k)) = fun vs =>
        (πf M T (k + 1) (cst M T w1 vs k) (vs k) - sf M T (k + 1) (cst M T w1 vs k) (vs k)) +
        ((n : ℝ) + 1) * (cst M T w1 vs k - cst M T w1 vs (k + 1)) := by
      funext vs; rw [cst_succ]; rfl
    have hI1 : Integrable (fun vs => πf M T (k + 1) (cst M T w1 vs k) (vs k) -
        sf M T (k + 1) (cst M T w1 vs k) (vs k)) (valueLaw M) :=
      (integrable_πk M T w1 hM' hw1 k hkT).sub (integrable_sk M T w1 hM' hw1 k hkT)
    have hI2 : Integrable (fun vs => ((n : ℝ) + 1) * (cst M T w1 vs k - cst M T w1 vs (k + 1)))
        (valueLaw M) :=
      ((integrable_cst M T w1 hM' hw1 k hkT.le).sub
        (integrable_cst M T w1 hM' hw1 (k + 1) hkT)).const_mul _
    rw [e, integral_add hI1 hI2,
      integral_sub (integrable_πk M T w1 hM' hw1 k hkT) (integrable_sk M T w1 hM' hw1 k hkT),
      integral_const_mul, integral_sub (integrable_cst M T w1 hM' hw1 k hkT.le)
        (integrable_cst M T w1 hM' hw1 (k + 1) hkT)] at h0
    linarith
  have hT : ∫ vs, cst M T w1 vs T ∂(valueLaw M) = 0 := by
    rw [← integral_zero (ℕ → Fin (n + 1) → ℝ) ℝ]
    apply integral_congr_ae
    filter_upwards [ae_cst M T w1 hM' hw1] with vs hc
    have := hc T le_rfl
    have hw : wbar M T (T + 1) = 0 := by unfold wbar; push_cast; ring
    rw [hw] at this
    show cst M T w1 vs T = 0
    linarith [this.1, this.2]
  have h0 : ∫ vs, cst M T w1 vs 0 ∂(valueLaw M) = w1 := by
    simp [cst_zero]
  rw [hP1, hS1]
  have := Finset.sum_congr rfl hk
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    Finset.sum_range_sub' (fun k => ∫ vs, cst M T w1 vs k ∂(valueLaw M)), hT, h0] at this
  linarith

end pid
end DDAx


namespace DDAx
open DynDoubleAuction.TwoSided MeasureTheory Filter

section wfb
variable {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)

lemma sf_le_Xf (hM : Standing M) (t : ℕ) {c : ℝ} (hc : 0 ≤ c) (v : Fin (n + 1) → ℝ)
    (hv : ∀ j, v j ∈ Set.Icc 0 M.vbar) : sf M T t c v ≤ Xf v := by
  have hM' := hM
  obtain ⟨hn, -, hvb, -, hr, hα, -, hαsum, -, hmu⟩ := hM
  unfold sf; split_ifs
  · exact le_rfl
  · obtain ⟨m0, m1⟩ := mf_bounds M hmu hc
    obtain ⟨i0, i1⟩ := ind_bounds M v
    have hS : ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * v i ≤ maxBuyer v := by
      calc _ ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * maxBuyer v :=
            Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
              (le_maxBuyer hn v i (Finset.ne_of_mem_erase hi)) (hα i (Finset.ne_of_mem_erase hi)).1)
        _ = (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i) * maxBuyer v := by
            rw [Finset.sum_mul]
        _ ≤ 1 * maxBuyer v := mul_le_mul_of_nonneg_right hαsum
            ((hv ⟨1, by omega⟩).1.trans (le_maxBuyer hn v _ (by simp [Fin.ext_iff])))
        _ = maxBuyer v := one_mul _
    have h1 : 0 ≤ mf M c * ind M v := mul_nonneg m0 i0
    have h2 : mf M c * ind M v ≤ 1 := by nlinarith
    unfold Xf
    rcases le_total 0 (maxBuyer v - v 0) with h | h
    · rw [max_eq_left h]
      rcases le_total 0 (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i * v i - v 0) with h' | h'
      · nlinarith
      · nlinarith
    · rw [max_eq_right h]; nlinarith

open Classical in
lemma Xf_sub_le_sf (hM : Standing M) (t : ℕ) {c : ℝ} (hc : 0 ≤ c) (v : Fin (n + 1) → ℝ)
    (hv : ∀ j, v j ∈ Set.Icc 0 M.vbar) :
    Xf v - M.vbar * (if Medium M T t c then 0 else 1) ≤ sf M T t c v := by
  have hM' := hM
  obtain ⟨hn, -, hvb, -, hr, hα, -, hαsum, -, hmu⟩ := hM
  unfold sf; split_ifs
  · simp
  · obtain ⟨m0, m1⟩ := mf_bounds M hmu hc
    obtain ⟨s0, s1⟩ := sumα_bounds M hM' v hv
    have hB := maxBuyer_le hn v M.vbar (fun i _ => (hv i).2)
    unfold ind Xf
    split_ifs with h
    · -- v 0 ≤ r : X + v0 ≤ vbar
      have : max (maxBuyer v - v 0) 0 ≤ M.vbar - v 0 :=
        max_le (by linarith) (by linarith [(hv 0).2])
      have hv0 := (hv 0).1
      nlinarith
    · have := (Xf_bounds M hn v hv hvb).2
      unfold Xf at this
      simp only [mul_zero, zero_mul]; linarith

lemma integral_Xk (hM : Standing M) (k : ℕ) :
    ∫ vs, Xf (vs k) ∂(valueLaw M) = wlow M := by
  obtain ⟨hn, hP, -⟩ := hM
  unfold valueLaw
  rw [← integral_Xf M]
  have := (measurePreserving_eval_infinitePi (fun _ : ℕ => M.F) k)
  have h2 := integral_map (μ := Measure.infinitePi (fun _ : ℕ => M.F)) (φ := Function.eval k)
    (measurable_pi_apply k).aemeasurable (f := fun v => Xf v)
    (measurable_Xf hn).aestronglyMeasurable
  rw [this.map_eq] at h2
  exact h2.symm

lemma integrable_Xk (hM : Standing M) (k : ℕ) :
    Integrable (fun vs : ℕ → Fin (n + 1) → ℝ => Xf (vs k)) (valueLaw M) := by
  have hM' := hM
  obtain ⟨hn, hP, hvb, hae, -⟩ := hM
  haveI := valueLaw_prob M hP
  refine Integrable.of_bound ((measurable_Xf hn).comp (measurable_pi_apply k)).aestronglyMeasurable
    M.vbar ?_
  filter_upwards [ae_box M hae] with vs hvs
  obtain ⟨a, b⟩ := Xf_bounds M hn (vs k) (hvs k) hvb
  rw [Real.norm_eq_abs, abs_of_nonneg a]; exact b

theorem welfare_le_firstBest (hM : Standing M) (hw1 : 0 ≤ w1 ∧ w1 ≤ wbar M T 1) :
    expectedWelfare M T w1 ≤ firstBest M T := by
  have hM' := hM
  obtain ⟨hn, hP, -, hae, -⟩ := hM
  unfold expectedWelfare
  simp_rw [welfarePath_eq M T w1 hn]
  rw [integral_finsetSum _ (fun k hk => integrable_sk M T w1 hM' hw1 k (Finset.mem_range.1 hk))]
  calc _ ≤ ∑ k ∈ Finset.range T, ∫ vs, Xf (vs k) ∂(valueLaw M) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        refine integral_mono_ae (integrable_sk M T w1 hM' hw1 k (Finset.mem_range.1 hk))
          (integrable_Xk M hM' k) ?_
        filter_upwards [ae_box M hae, ae_cst M T w1 hM' hw1] with vs hvs hc
        exact sf_le_Xf M T hM' _ (hc k (Finset.mem_range.1 hk).le).1 _ (hvs k)
    _ = firstBest M T := by
        simp_rw [integral_Xk M hM']
        simp [firstBest]

end wfb
end DDAx


namespace DDAx
open DynDoubleAuction.TwoSided MeasureTheory Filter

section exitt
variable {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)

lemma exitTime_le_iff (vs : ℕ → Fin (n + 1) → ℝ) (t : ℕ) (ht : t ≤ T) :
    exitTime M T w1 vs ≤ t ↔
      ∃ s, s ≤ t ∧ (1 ≤ s ∧ s ≤ T) ∧ ¬ Medium M T s (cst M T w1 vs (s - 1)) := by
  classical
  unfold exitTime
  split_ifs with h
  · rw [Nat.find_le_iff]
    constructor
    · rintro ⟨m, hm, hm1, hm2⟩
      exact ⟨m, hm, Finset.mem_Icc.1 hm1, hm2⟩
    · rintro ⟨m, hm, hm1, hm2⟩
      exact ⟨m, hm, Finset.mem_Icc.2 hm1, hm2⟩
  · constructor
    · intro h'; omega
    · rintro ⟨m, -, hm1, hm2⟩
      exact absurd ⟨m, Finset.mem_Icc.2 hm1, hm2⟩ h

lemma one_le_exitTime (vs : ℕ → Fin (n + 1) → ℝ) : 1 ≤ exitTime M T w1 vs := by
  classical
  unfold exitTime
  split_ifs with h
  · have := Nat.find_spec h
    exact (Finset.mem_Icc.1 this.1).1
  · omega

lemma exitTime_le_succ (vs : ℕ → Fin (n + 1) → ℝ) : exitTime M T w1 vs ≤ T + 1 := by
  classical
  unfold exitTime
  split_ifs with h
  · have := Nat.find_spec h
    have := (Finset.mem_Icc.1 this.1).2; omega
  · exact le_rfl

lemma measurableSet_exit_le (hn : 1 ≤ n) (t : ℕ) (ht : t ≤ T) :
    MeasurableSet {vs : ℕ → Fin (n + 1) → ℝ | exitTime M T w1 vs ≤ t} := by
  have : {vs : ℕ → Fin (n + 1) → ℝ | exitTime M T w1 vs ≤ t} =
      ⋃ s ∈ Finset.range (t + 1), {vs | (1 ≤ s ∧ s ≤ T) ∧
        ¬ Medium M T s (cst M T w1 vs (s - 1))} := by
    ext vs
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    rw [exitTime_le_iff M T w1 vs t ht]
    constructor
    · rintro ⟨s, h1, h2⟩; exact ⟨s, by omega, h2⟩
    · rintro ⟨s, h1, h2⟩; exact ⟨s, by omega, h2⟩
  rw [this]
  refine Finset.measurableSet_biUnion _ (fun s _ => ?_)
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  exact ((measurableSet_medium M T s).compl).preimage (measurable_cst M T w1 hn (s - 1))

lemma count_sum (a T : ℕ) (ha : 1 ≤ a) :
    (∑ k ∈ Finset.range T, (if a ≤ k + 1 then (1 : ℝ) else 0)) = ((T + 1 - a : ℕ) : ℝ) := by
  induction T with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; rw [show 0 + 1 - a = 0 by omega]; simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs with h
    · rw [show T + 1 + 1 - a = (T + 1 - a) + 1 by omega]; push_cast; ring
    · rw [show T + 1 - a = 0 by omega, show T + 1 + 1 - a = 0 by omega]; simp

lemma exit_count (vs : ℕ → Fin (n + 1) → ℝ) :
    max ((T : ℝ) - (exitTime M T w1 vs : ℝ) + 1) 0 =
      ∑ k ∈ Finset.range T, (if exitTime M T w1 vs ≤ k + 1 then (1 : ℝ) else 0) := by
  rw [count_sum _ T (one_le_exitTime M T w1 vs)]
  have h := exitTime_le_succ M T w1 vs
  rw [max_eq_left (by have : (exitTime M T w1 vs : ℝ) ≤ T + 1 := by exact_mod_cast h
                      linarith)]
  rw [Nat.cast_sub h]; push_cast; ring

lemma integrable_exitInd (hn : 1 ≤ n) [IsProbabilityMeasure (valueLaw M)] (k : ℕ) (hk : k < T) :
    Integrable (fun vs => if exitTime M T w1 vs ≤ k + 1 then (1 : ℝ) else 0) (valueLaw M) := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact (Measurable.ite (measurableSet_exit_le M T w1 hn (k + 1) hk) measurable_const
      measurable_const).aestronglyMeasurable
  · exact ae_of_all _ (fun vs => by split_ifs <;> simp)

lemma integral_exit_count (hn : 1 ≤ n) [IsProbabilityMeasure (valueLaw M)] :
    ∫ vs, max ((T : ℝ) - (exitTime M T w1 vs : ℝ) + 1) 0 ∂(valueLaw M) =
      ∑ k ∈ Finset.range T, ∫ vs, (if exitTime M T w1 vs ≤ k + 1 then (1 : ℝ) else 0)
        ∂(valueLaw M) := by
  simp_rw [exit_count M T w1]
  exact integral_finsetSum _ (fun k hk => integrable_exitInd M T w1 hn k (Finset.mem_range.1 hk))

end exitt
end DDAx


namespace DDAx
open DynDoubleAuction.TwoSided MeasureTheory Filter ProbabilityTheory

section hoeff
variable {n : ℕ} (M : Market n)

lemma mart_eq (w1 : ℝ) (vs : ℕ → Fin (n + 1) → ℝ) (s : ℕ) :
    mart M w1 vs s = w1 + ∑ k ∈ Finset.range s, (Xf (vs k) - wlow M) := by
  induction s with
  | zero => simp [mart]
  | succ s ih => rw [mart, ih, Finset.sum_range_succ, Xf]; ring

lemma hoeffding_up (hM : Standing M) (s : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (valueLaw M).real {vs | a ≤ ∑ k ∈ Finset.range s, (Xf (vs k) - wlow M)} ≤
      Real.exp (-a ^ 2 / (2 * s * ((‖M.vbar‖₊ / 2) ^ 2 : NNReal))) := by
  have hM' := hM
  obtain ⟨hn, hP, hvb, hae, -⟩ := hM
  haveI := valueLaw_prob M hP
  have hind : iIndepFun (fun k (vs : ℕ → Fin (n + 1) → ℝ) => Xf (vs k) - wlow M) (valueLaw M) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => M.F) (X := fun _ v => Xf v - wlow M)
      (fun _ => (measurable_Xf hn).sub measurable_const)
  refine HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind (fun k _ => ?_) ha
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := valueLaw M)
    (X := fun vs : ℕ → Fin (n + 1) → ℝ => Xf (vs k) - wlow M) (a := -wlow M) (b := M.vbar - wlow M)
    (((measurable_Xf hn).comp (measurable_pi_apply k)).sub measurable_const).aemeasurable ?_ ?_
  · simpa using h
  · filter_upwards [ae_box M hae] with vs hvs
    obtain ⟨x0, x1⟩ := Xf_bounds M hn (vs k) (hvs k) hvb
    constructor <;> linarith
  · rw [integral_sub (integrable_Xk M hM' k) (integrable_const _), integral_Xk M hM' k]
    simp

lemma hoeffding_down (hM : Standing M) (s : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (valueLaw M).real {vs | a ≤ ∑ k ∈ Finset.range s, (wlow M - Xf (vs k))} ≤
      Real.exp (-a ^ 2 / (2 * s * ((‖M.vbar‖₊ / 2) ^ 2 : NNReal))) := by
  have hM' := hM
  obtain ⟨hn, hP, hvb, hae, -⟩ := hM
  haveI := valueLaw_prob M hP
  have hind : iIndepFun (fun k (vs : ℕ → Fin (n + 1) → ℝ) => wlow M - Xf (vs k)) (valueLaw M) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => M.F) (X := fun _ v => wlow M - Xf v)
      (fun _ => measurable_const.sub (measurable_Xf hn))
  refine HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind (fun k _ => ?_) ha
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := valueLaw M)
    (X := fun vs : ℕ → Fin (n + 1) → ℝ => wlow M - Xf (vs k)) (a := wlow M - M.vbar) (b := wlow M)
    (measurable_const.sub ((measurable_Xf hn).comp (measurable_pi_apply k))).aemeasurable ?_ ?_
  · simpa using h
  · filter_upwards [ae_box M hae] with vs hvs
    obtain ⟨x0, x1⟩ := Xf_bounds M hn (vs k) (hvs k) hvb
    constructor <;> linarith
  · rw [integral_sub (integrable_const _) (integrable_Xk M hM' k), integral_Xk M hM' k]
    simp

lemma nn_coe (M : Market n) (hvb : 0 < M.vbar) :
    (((‖M.vbar‖₊ / 2) ^ 2 : NNReal) : ℝ) = M.vbar ^ 2 / 4 := by
  push_cast
  rw [Real.norm_eq_abs, abs_of_pos hvb]; ring

end hoeff
end DDAx


namespace DDAx
open DynDoubleAuction.TwoSided MeasureTheory Filter ProbabilityTheory

section ee
variable {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)

lemma wbar_anti (hmu : 0 < mu M) {a b : ℕ} (h : a ≤ b) : wbar M T b ≤ wbar M T a := by
  unfold wbar
  apply mul_le_mul_of_nonneg_right _ hmu.le
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  linarith

lemma inv_K (vs : ℕ → Fin (n + 1) → ℝ) (s : ℕ) :
    cst M T w1 vs s = mart M w1 vs s ∨
      ∃ s' ≤ s, mart M w1 vs s' ≤ wlow M ∨ wbar M T (s' + 1) - M.vbar ≤ mart M w1 vs s' := by
  induction s with
  | zero => left; rfl
  | succ s ih =>
    rcases ih with h | ⟨s', hs', h'⟩
    · by_cases hm : Medium M T (s + 1) (cst M T w1 vs s)
      · left
        rw [cst_succ, uf, if_pos hm, h, mart, Xf]
      · right
        refine ⟨s, by omega, ?_⟩
        unfold Medium at hm
        rw [← h]
        by_contra hc
        push_neg at hc
        exact hm ⟨hc.1, hc.2⟩
    · right; exact ⟨s', by omega, h'⟩

lemma exit_incl (hmu : 0 < mu M) (vs : ℕ → Fin (n + 1) → ℝ) (t : ℕ) (ht : t ≤ T)
    (h : exitTime M T w1 vs ≤ t) :
    ∃ s < t, mart M w1 vs s ≤ wlow M ∨ wbar M T t - M.vbar ≤ mart M w1 vs s := by
  rw [exitTime_le_iff M T w1 vs t ht] at h
  obtain ⟨s', hs't, ⟨h1, h2⟩, hm⟩ := h
  have hmm : cst M T w1 vs (s' - 1) ≤ wlow M ∨ wbar M T s' - M.vbar ≤ cst M T w1 vs (s' - 1) := by
    unfold Medium at hm
    by_contra hc
    push_neg at hc
    exact hm ⟨hc.1, hc.2⟩
  rcases inv_K M T w1 vs (s' - 1) with he | ⟨s'', hs'', h''⟩
  · refine ⟨s' - 1, by omega, ?_⟩
    rw [← he]
    rcases hmm with h | h
    · left; exact h
    · right; linarith [wbar_anti M T hmu (show s' ≤ t from hs't)]
  · refine ⟨s'', by omega, ?_⟩
    rcases h'' with h | h
    · left; exact h
    · right; linarith [wbar_anti M T hmu (show s'' + 1 ≤ t by omega)]

lemma cnt_le (x : ℝ) : ∀ T : ℕ, x ≤ T + 1 →
    (∑ k ∈ Finset.range T, (if x < (k : ℝ) + 1 then (1 : ℝ) else 0)) ≤ T - x + 1 := by
  intro T
  induction T with
  | zero => intro h; simp at h ⊢; linarith
  | succ T ih =>
    intro h
    push_cast at h
    rw [Finset.sum_range_succ]
    by_cases hx : x ≤ T + 1
    · have := ih hx
      have : (if x < (T : ℝ) + 1 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      push_cast; linarith
    · push_neg at hx
      rw [Finset.sum_eq_zero (fun k hk => by
        have : (k : ℝ) + 1 ≤ T := by
          have := Finset.mem_range.1 hk
          have : (k : ℝ) + 1 ≤ (T : ℝ) := by exact_mod_cast this
          exact this
        rw [if_neg (by linarith)])]
      rw [if_neg (by linarith)]
      push_cast; linarith

end ee
end DDAx


namespace DDAx
open DynDoubleAuction.TwoSided MeasureTheory Filter ProbabilityTheory

section et
variable {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)

lemma wbar_succ (s : ℕ) : wbar M T (s + 1) = wbar M T s - mu M := by
  unfold wbar; push_cast; ring

lemma inv_low (vs : ℕ → Fin (n + 1) → ℝ) (s : ℕ) :
    cst M T w1 vs s = mart M w1 vs s ∨ (∃ s' ≤ s, mart M w1 vs s' ≤ wlow M) ∨
      wbar M T (s + 1) - M.vbar ≤ cst M T w1 vs s := by
  induction s with
  | zero => left; rfl
  | succ s ih =>
    rcases ih with h | ⟨s', hs', h'⟩ | h
    · by_cases hm : Medium M T (s + 1) (cst M T w1 vs s)
      · left; rw [cst_succ, uf, if_pos hm, h, mart, Xf]
      · unfold Medium at hm
        by_cases hl : cst M T w1 vs s ≤ wlow M
        · right; left; exact ⟨s, by omega, by rw [← h]; exact hl⟩
        · right; right
          have hh : wbar M T (s + 1) - M.vbar ≤ cst M T w1 vs s := by
            by_contra hc; push_neg at hc hl; exact hm ⟨hl, hc⟩
          rw [cst_succ, uf, if_neg (by unfold Medium; exact hm), wbar_succ]
          exact le_trans (by linarith) (le_max_left _ _)
    · right; left; exact ⟨s', by omega, h'⟩
    · right; right
      have hm : ¬ Medium M T (s + 1) (cst M T w1 vs s) := by
        unfold Medium; intro hc; linarith [hc.2]
      rw [cst_succ, uf, if_neg hm, wbar_succ]
      exact le_trans (by linarith) (le_max_left _ _)

lemma inv_high (hwl : 0 ≤ wlow M) (hmu : 0 < mu M) (vs : ℕ → Fin (n + 1) → ℝ) (s : ℕ) :
    cst M T w1 vs s = mart M w1 vs s ∨
      (∃ s' ≤ s, wbar M T (s' + 1) - M.vbar ≤ mart M w1 vs s') ∨
      cst M T w1 vs s ≤ wlow M := by
  induction s with
  | zero => left; rfl
  | succ s ih =>
    rcases ih with h | ⟨s', hs', h'⟩ | h
    · by_cases hm : Medium M T (s + 1) (cst M T w1 vs s)
      · left; rw [cst_succ, uf, if_pos hm, h, mart, Xf]
      · by_cases hl : cst M T w1 vs s ≤ wlow M
        · right; right
          rw [cst_succ, uf, if_neg hm]
          exact max_le (by linarith) hwl
        · right; left
          refine ⟨s, by omega, ?_⟩
          unfold Medium at hm
          rw [← h]; by_contra hc; push_neg at hc hl; exact hm ⟨hl, hc⟩
    · right; left; exact ⟨s', by omega, h'⟩
    · right; right
      have hm : ¬ Medium M T (s + 1) (cst M T w1 vs s) := by
        unfold Medium; intro hc; linarith [hc.1]
      rw [cst_succ, uf, if_neg hm]
      exact max_le (by linarith) hwl

lemma tauLow_le (vs : ℕ → Fin (n + 1) → ℝ) (t : ℕ) (ht : t ≤ T)
    (h : tauLow M T w1 vs ≤ t) :
    ∃ t' ≤ t, (1 ≤ t' ∧ t' ≤ T) ∧ cst M T w1 vs (t' - 1) ≤ wlow M := by
  classical
  unfold tauLow at h
  split_ifs at h with hh
  · rw [Nat.find_le_iff] at h
    obtain ⟨m, hm, hm1, hm2⟩ := h
    exact ⟨m, hm, Finset.mem_Icc.1 hm1, hm2⟩
  · omega

lemma tauHigh_le (vs : ℕ → Fin (n + 1) → ℝ) (t : ℕ) (ht : t ≤ T)
    (h : tauHigh M T w1 vs ≤ t) :
    ∃ t' ≤ t, (1 ≤ t' ∧ t' ≤ T) ∧ wbar M T t' - M.vbar ≤ cst M T w1 vs (t' - 1) := by
  classical
  unfold tauHigh at h
  split_ifs at h with hh
  · rw [Nat.find_le_iff] at h
    obtain ⟨m, hm, hm1, hm2⟩ := h
    exact ⟨m, hm, Finset.mem_Icc.1 hm1, hm2⟩
  · omega

lemma low_incl (hmu : 0 < mu M) (vs : ℕ → Fin (n + 1) → ℝ) (t : ℕ) (ht : t ≤ T)
    (hgap : wlow M < wbar M T t - M.vbar) (h : tauLow M T w1 vs ≤ t) :
    ∃ s < t, mart M w1 vs s ≤ wlow M := by
  obtain ⟨t', ht', ⟨h1, h2⟩, hc⟩ := tauLow_le M T w1 vs t ht h
  rcases inv_low M T w1 vs (t' - 1) with he | ⟨s', hs', h'⟩ | hh
  · exact ⟨t' - 1, by omega, by rw [← he]; exact hc⟩
  · exact ⟨s', by omega, h'⟩
  · exfalso
    have := wbar_anti M T hmu (show t' - 1 + 1 ≤ t by omega)
    linarith

lemma high_incl (hwl : 0 ≤ wlow M) (hmu : 0 < mu M) (vs : ℕ → Fin (n + 1) → ℝ) (t : ℕ)
    (ht : t ≤ T) (hgap : wlow M < wbar M T t - M.vbar) (h : tauHigh M T w1 vs ≤ t) :
    ∃ s < t, wbar M T t - M.vbar ≤ mart M w1 vs s := by
  obtain ⟨t', ht', ⟨h1, h2⟩, hc⟩ := tauHigh_le M T w1 vs t ht h
  rcases inv_high M T w1 hwl hmu vs (t' - 1) with he | ⟨s', hs', h'⟩ | hh
  · refine ⟨t' - 1, by omega, ?_⟩
    rw [← he]; linarith [wbar_anti M T hmu (show t' ≤ t from ht')]
  · refine ⟨s', by omega, ?_⟩
    linarith [wbar_anti M T hmu (show s' + 1 ≤ t by omega)]
  · exfalso
    have := wbar_anti M T hmu (show t' ≤ t from ht')
    linarith

end et

lemma final_bound {vbar : ℝ} (hvb : 0 < vbar) {t T : ℕ} (ht1 : 1 ≤ t) (htT : t ≤ T) (hT : 2 ≤ T)
    {a : ℝ} (ha2 : 8 * vbar ^ 2 * ((T : ℝ) * Real.log T) ≤ a ^ 2) :
    (t : ℝ) * Real.exp (-a ^ 2 / ((t : ℝ) * vbar ^ 2 / 2)) ≤
      Real.exp (-a ^ 2 / (8 * (t : ℝ) * vbar ^ 2)) := by
  have ht : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have htT' : (t : ℝ) ≤ T := by exact_mod_cast htT
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  set x := a ^ 2 / ((t : ℝ) * vbar ^ 2) with hx
  have htv : 0 < (t : ℝ) * vbar ^ 2 := by positivity
  have hx0 : 0 ≤ x := div_nonneg (sq_nonneg a) htv.le
  have hlogt : Real.log t ≤ x := by
    have h1 : Real.log t ≤ Real.log T := Real.log_le_log (by linarith) htT'
    have h2 : 8 * Real.log T ≤ x := by
      rw [hx, le_div_iff₀ htv]
      have : (t : ℝ) * Real.log T ≤ T * Real.log T := mul_le_mul_of_nonneg_right htT' hlog
      nlinarith [sq_nonneg vbar]
    linarith
  have e1 : -a ^ 2 / ((t : ℝ) * vbar ^ 2 / 2) = -2 * x := by
    rw [hx]; field_simp
  have e2 : -a ^ 2 / (8 * (t : ℝ) * vbar ^ 2) = -x / 8 := by
    rw [hx]; field_simp
  rw [e1, e2]
  have : (t : ℝ) ≤ Real.exp x := by
    calc (t : ℝ) = Real.exp (Real.log t) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp x := Real.exp_le_exp.2 hlogt
  calc (t : ℝ) * Real.exp (-2 * x) ≤ Real.exp x * Real.exp (-2 * x) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    _ = Real.exp (-x) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-x / 8) := Real.exp_le_exp.2 (by linarith)

end DDAx

namespace DDAx
open DynDoubleAuction.TwoSided MeasureTheory Filter ProbabilityTheory

lemma per_s_bound {vbar a : ℝ} (hvb : 0 < vbar) {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) :
    Real.exp (-a ^ 2 / (2 * s * (vbar ^ 2 / 4))) ≤ Real.exp (-a ^ 2 / ((t : ℝ) * vbar ^ 2 / 2)) := by
  apply Real.exp_le_exp.2
  rw [neg_div, neg_div, neg_le_neg_iff]
  apply div_le_div_of_nonneg_left (sq_nonneg a)
  · have : (1 : ℝ) ≤ s := by exact_mod_cast hs
    positivity
  · have : (s : ℝ) ≤ t := by exact_mod_cast hst
    nlinarith [sq_nonneg vbar]

end DDAx

open DynDoubleAuction.TwoSided MeasureTheory Filter ProbabilityTheory DDAx in
theorem solution {n : ℕ} (M : Market n) (hM : Standing M)
    (T t : ℕ) (hT : 2 ≤ T) (ht : 1 ≤ t ∧ (t : ℝ) ≤ Tstar M T)
    (hside : initialPromise M T ≤ wbar M T 1 -
      M.vbar * (1 + Real.sqrt (8 * (T : ℝ) * Real.log T))) :
    (valueLaw M).real {vs | tauLow M T (initialPromise M T) vs ≤ t} ≤
        Real.exp (-(initialPromise M T - wlow M) ^ 2 /
          (8 * (t : ℝ) * M.vbar ^ 2)) ∧
    (valueLaw M).real {vs | tauHigh M T (initialPromise M T) vs ≤ t} ≤
        Real.exp (-(wbar M T t - M.vbar - initialPromise M T) ^ 2 /
          (8 * (t : ℝ) * M.vbar ^ 2)) := by
  have hM' := hM
  obtain ⟨hn, hP, hvb, hae, hr, hα, hαmu, hαsum, hmw, hmu⟩ := hM
  haveI := valueLaw_prob M hP
  have hwl : 0 ≤ wlow M := wlow_nonneg M hM'
  set w1 := initialPromise M T with hw1def
  set sT := Real.sqrt (8 * (T : ℝ) * Real.log T) with hsTdef
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hsT2 : sT ^ 2 = 8 * (T : ℝ) * Real.log T := Real.sq_sqrt (by positivity)
  have hsTpos : 0 < sT := Real.sqrt_pos.2 (by positivity)
  have hw1 : w1 = wlow M + M.vbar * sT := rfl
  have hTsdef : (T : ℝ) - Tstar M T + 1 = (M.vbar + wlow M + 2 * M.vbar * sT) / mu M := by
    rw [Tstar]; ring
  obtain ⟨ht1, htTs⟩ := ht
  have htT : t ≤ T := by
    have : 0 < (M.vbar + wlow M + 2 * M.vbar * sT) / mu M := by positivity
    have : (t : ℝ) < T + 1 := by linarith
    exact_mod_cast (show (t : ℝ) ≤ T by
      have h := this; exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast h))
  have hwt : M.vbar + wlow M + 2 * M.vbar * sT ≤ wbar M T t := by
    unfold wbar
    rw [← div_le_iff₀ hmu, ← hTsdef]; linarith
  have hgap : wlow M < wbar M T t - M.vbar := by nlinarith
  have hcoe := nn_coe M hvb
  constructor
  · set a := w1 - wlow M with ha
    have ha0 : 0 ≤ a := by rw [ha, hw1]; nlinarith
    have ha2 : 8 * M.vbar ^ 2 * ((T : ℝ) * Real.log T) ≤ a ^ 2 := by
      rw [ha, hw1]; ring_nf; rw [hsT2]; nlinarith [sq_nonneg M.vbar]
    have hs_bound : ∀ s ∈ Finset.range t, (valueLaw M).real {vs | mart M w1 vs s ≤ wlow M} ≤
        Real.exp (-a ^ 2 / ((t : ℝ) * M.vbar ^ 2 / 2)) := by
      intro s hs
      have hs := Finset.mem_range.1 hs
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · subst h0
        have : {vs : ℕ → Fin (n + 1) → ℝ | mart M w1 vs 0 ≤ wlow M} = ∅ := by
          ext vs; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
          show wlow M < w1
          rw [hw1]; nlinarith
        rw [this, measureReal_empty]; positivity
      · calc _ ≤ (valueLaw M).real {vs | a ≤ ∑ k ∈ Finset.range s, (wlow M - Xf (vs k))} := by
                refine measureReal_mono ?_ (measure_ne_top _ _)
                intro vs hvs
                simp only [Set.mem_setOf_eq] at hvs ⊢
                rw [mart_eq] at hvs
                rw [Finset.sum_sub_distrib] at hvs ⊢
                rw [ha]; linarith
          _ ≤ _ := hoeffding_down M hM' s ha0
          _ ≤ _ := by rw [hcoe]; exact per_s_bound hvb h0 hs.le
    calc _ ≤ (valueLaw M).real (⋃ s ∈ Finset.range t, {vs | mart M w1 vs s ≤ wlow M}) := by
          refine measureReal_mono ?_ (measure_ne_top _ _)
          intro vs hvs
          obtain ⟨s, hs, h⟩ := low_incl M T w1 hmu vs t htT hgap hvs
          simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range]
          exact ⟨s, hs, h⟩
      _ ≤ ∑ s ∈ Finset.range t, (valueLaw M).real {vs | mart M w1 vs s ≤ wlow M} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ s ∈ Finset.range t, Real.exp (-a ^ 2 / ((t : ℝ) * M.vbar ^ 2 / 2)) :=
          Finset.sum_le_sum hs_bound
      _ = (t : ℝ) * Real.exp (-a ^ 2 / ((t : ℝ) * M.vbar ^ 2 / 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := final_bound hvb ht1 htT hT ha2
  · set a := wbar M T t - M.vbar - w1 with ha
    have ha1 : M.vbar * sT ≤ a := by rw [ha, hw1]; linarith
    have ha0 : 0 ≤ a := le_trans (by positivity) ha1
    have ha2 : 8 * M.vbar ^ 2 * ((T : ℝ) * Real.log T) ≤ a ^ 2 := by
      have h1 : (M.vbar * sT) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) ha1 2
      rw [mul_pow, hsT2] at h1; nlinarith [sq_nonneg M.vbar]
    have hs_bound : ∀ s ∈ Finset.range t,
        (valueLaw M).real {vs | wbar M T t - M.vbar ≤ mart M w1 vs s} ≤
        Real.exp (-a ^ 2 / ((t : ℝ) * M.vbar ^ 2 / 2)) := by
      intro s hs
      have hs := Finset.mem_range.1 hs
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · subst h0
        have : {vs : ℕ → Fin (n + 1) → ℝ | wbar M T t - M.vbar ≤ mart M w1 vs 0} = ∅ := by
          ext vs; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
          show w1 < wbar M T t - M.vbar
          have : 0 < M.vbar * sT := by positivity
          linarith
        rw [this, measureReal_empty]; positivity
      · calc _ ≤ (valueLaw M).real {vs | a ≤ ∑ k ∈ Finset.range s, (Xf (vs k) - wlow M)} := by
                refine measureReal_mono ?_ (measure_ne_top _ _)
                intro vs hvs
                simp only [Set.mem_setOf_eq] at hvs ⊢
                rw [mart_eq] at hvs
                rw [ha]; linarith
          _ ≤ _ := hoeffding_up M hM' s ha0
          _ ≤ _ := by rw [hcoe]; exact per_s_bound hvb h0 hs.le
    calc _ ≤ (valueLaw M).real (⋃ s ∈ Finset.range t,
            {vs | wbar M T t - M.vbar ≤ mart M w1 vs s}) := by
          refine measureReal_mono ?_ (measure_ne_top _ _)
          intro vs hvs
          obtain ⟨s, hs, h⟩ := high_incl M T w1 hwl hmu vs t htT hgap hvs
          simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range]
          exact ⟨s, hs, h⟩
      _ ≤ ∑ s ∈ Finset.range t, (valueLaw M).real {vs | wbar M T t - M.vbar ≤ mart M w1 vs s} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ s ∈ Finset.range t, Real.exp (-a ^ 2 / ((t : ℝ) * M.vbar ^ 2 / 2)) :=
          Finset.sum_le_sum hs_bound
      _ = (t : ℝ) * Real.exp (-a ^ 2 / ((t : ℝ) * M.vbar ^ 2 / 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := final_bound hvb ht1 htT hT ha2
