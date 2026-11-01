-- Prove2me | solution 1 for DynDoubleAuction.TwoSided.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T00:38:37.379696+00:00
-- url     : https://prove2.me/submissions/556f203c-4b13-43fb-a03e-6a9d78d54b4f

import Mathlib
import Definitions.Def_DynDoubleAuction_TwoSided_Model
import Theorems.Thm_DynDoubleAuction_TwoSided_welfare_loss
import Theorems.Thm_DynDoubleAuction_TwoSided_expected_exit

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
open DynDoubleAuction.TwoSided MeasureTheory Filter Topology

lemma sqrt_logdiv_tendsto :
    Tendsto (fun T : ℕ => Real.sqrt ((T : ℝ) * Real.log T) / T) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h2 : Tendsto (fun T : ℕ => Real.log T / (T : ℝ)) atTop (𝓝 0) :=
    h1.comp tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun T : ℕ => Real.sqrt (Real.log T / (T : ℝ))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at this
    exact this
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  rw [show Real.log T / (T : ℝ) = ((T : ℝ) * Real.log T) / ((T : ℝ) ^ 2) by
    field_simp, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hT'.le]

lemma sqrt8_eq (T : ℕ) : Real.sqrt (8 * (T : ℝ) * Real.log T) =
    Real.sqrt 8 * Real.sqrt ((T : ℝ) * Real.log T) := by
  rw [mul_assoc, Real.sqrt_mul (by norm_num)]

end DDAx

open DynDoubleAuction.TwoSided MeasureTheory Filter Topology DDAx in
theorem solution {n : ℕ} (M : Market n) (hM : Standing M) :
    (∃ C : ℝ, ∀ T : ℕ, 2 ≤ T →
      initialPromise M T ≤ wbar M T 1 -
        M.vbar * (1 + Real.sqrt (8 * (T : ℝ) * Real.log T)) →
      firstBest M T - C * Real.sqrt ((T : ℝ) * Real.log T) ≤
        expectedProfit M T (initialPromise M T)) ∧
    Tendsto (fun T : ℕ =>
      expectedProfit M T (initialPromise M T) / firstBest M T)
      atTop (𝓝 1) := by
  have hM' := hM
  obtain ⟨hn, hP, hvb, hae, hr, hα, hαmu, hαsum, hmw, hmu⟩ := hM
  have hwl0 : 0 < wlow M := lt_of_lt_of_le hmu hmw
  set K0 := M.vbar * (1 + wlow M / mu M + M.vbar / mu M) + ((n : ℝ) + 1) * wlow M with hK0
  set K1 := 2 * M.vbar * M.vbar / mu M + ((n : ℝ) + 1) * M.vbar with hK1
  set L0 := Real.sqrt (2 * Real.log 2) with hL0
  have hL0pos : 0 < L0 := Real.sqrt_pos.2 (by have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith)
  have hK0nn : 0 ≤ K0 := by
    have : 0 ≤ wlow M / mu M := div_nonneg hwl0.le hmu.le
    have : 0 ≤ M.vbar / mu M := div_nonneg hvb.le hmu.le
    positivity
  have hK1nn : 0 ≤ K1 := by
    have : 0 ≤ 2 * M.vbar * M.vbar / mu M := by positivity
    positivity
  set C := K0 / L0 + Real.sqrt 8 * K1 with hC
  -- key lower bound valid whenever the side condition holds
  have key : ∀ T : ℕ, 2 ≤ T →
      initialPromise M T ≤ wbar M T 1 - M.vbar * (1 + Real.sqrt (8 * (T : ℝ) * Real.log T)) →
      firstBest M T - C * Real.sqrt ((T : ℝ) * Real.log T) ≤
        expectedProfit M T (initialPromise M T) ∧
      expectedProfit M T (initialPromise M T) ≤ firstBest M T := by
    intro T hT hside
    set s := Real.sqrt (8 * (T : ℝ) * Real.log T) with hs
    set L := Real.sqrt ((T : ℝ) * Real.log T) with hL
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hsL : s = Real.sqrt 8 * L := sqrt8_eq T
    have hLL0 : L0 ≤ L := by
      apply Real.sqrt_le_sqrt
      have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
      have hlog : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT2
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
    have hw1 : 0 ≤ initialPromise M T ∧ initialPromise M T ≤ wbar M T 1 := by
      constructor
      · unfold initialPromise; positivity
      · have : 0 ≤ M.vbar * (1 + s) := by positivity
        linarith
    have hid := profit_identity M T (initialPromise M T) hM' hw1
    have hwle := welfare_le_firstBest M T (initialPromise M T) hM' hw1
    have hwl := welfare_loss M hM' T (initialPromise M T) hw1
    have hee := expected_exit M hM' T hT hside
    have hw1v : initialPromise M T = wlow M + M.vbar * s := rfl
    refine ⟨?_, by nlinarith [hw1.1]⟩
    have hE := mul_le_mul_of_nonneg_left hee hvb.le
    have expand : M.vbar * (1 + wlow M / mu M + (2 * s + 1) * M.vbar / mu M) +
        ((n : ℝ) + 1) * (wlow M + M.vbar * s) = K0 + K1 * s := by
      rw [hK0, hK1]; field_simp; ring
    have hK0L : K0 ≤ K0 / L0 * L := by
      calc K0 = K0 / L0 * L0 := by field_simp
        _ ≤ K0 / L0 * L := mul_le_mul_of_nonneg_left hLL0 (div_nonneg hK0nn hL0pos.le)
    have hCL : K0 + K1 * s ≤ C * L := by
      rw [hC, hsL, add_mul]; nlinarith
    have : firstBest M T - expectedProfit M T (initialPromise M T) ≤ K0 + K1 * s := by
      rw [← expand, hid, ← hw1v]; linarith
    linarith
  refine ⟨⟨C, fun T hT hside => (key T hT hside).1⟩, ?_⟩
  -- eventually the side condition holds
  have hLT := sqrt_logdiv_tendsto
  have hg : Tendsto (fun T : ℕ => (wlow M + M.vbar) * (1 / (T : ℝ)) +
      2 * M.vbar * Real.sqrt 8 * (Real.sqrt ((T : ℝ) * Real.log T) / T)) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat.const_mul (wlow M + M.vbar)).add
      (hLT.const_mul (2 * M.vbar * Real.sqrt 8))
    simpa using this
  have hev : ∀ᶠ T : ℕ in atTop, 2 ≤ T ∧ initialPromise M T ≤ wbar M T 1 -
      M.vbar * (1 + Real.sqrt (8 * (T : ℝ) * Real.log T)) := by
    filter_upwards [eventually_ge_atTop 2, (hg.eventually (gt_mem_nhds hmu))] with T hT hlt
    refine ⟨hT, ?_⟩
    have hTpos : (0 : ℝ) < T := by have : (2:ℝ) ≤ T := by exact_mod_cast hT
                                   linarith
    have e : (wlow M + M.vbar) * (1 / (T : ℝ)) +
        2 * M.vbar * Real.sqrt 8 * (Real.sqrt ((T : ℝ) * Real.log T) / T) =
        (wlow M + M.vbar + 2 * M.vbar * Real.sqrt (8 * (T : ℝ) * Real.log T)) / T := by
      rw [sqrt8_eq]; field_simp
    rw [e, div_lt_iff₀ hTpos] at hlt
    unfold initialPromise wbar
    have : ((T : ℝ) - ((1 : ℕ) : ℝ) + 1) = T := by push_cast; ring
    rw [this]; nlinarith
  have hlow : Tendsto (fun T : ℕ => 1 - C / wlow M * (Real.sqrt ((T : ℝ) * Real.log T) / T))
      atTop (𝓝 1) := by
    have := (hLT.const_mul (C / wlow M)).const_sub 1
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with T ⟨hT, hside⟩
    have hFB : 0 < firstBest M T := by
      unfold firstBest
      have : (2:ℝ) ≤ T := by exact_mod_cast hT
      positivity
    rw [le_div_iff₀ hFB]
    have h1 := (key T hT hside).1
    have : (1 - C / wlow M * (Real.sqrt ((T : ℝ) * Real.log T) / T)) * firstBest M T =
        firstBest M T - C * Real.sqrt ((T : ℝ) * Real.log T) := by
      unfold firstBest
      have : (2:ℝ) ≤ T := by exact_mod_cast hT
      field_simp
    linarith
  · filter_upwards [hev] with T ⟨hT, hside⟩
    have hFB : 0 < firstBest M T := by
      unfold firstBest
      have : (2:ℝ) ≤ T := by exact_mod_cast hT
      positivity
    rw [div_le_one hFB]
    exact (key T hT hside).2
