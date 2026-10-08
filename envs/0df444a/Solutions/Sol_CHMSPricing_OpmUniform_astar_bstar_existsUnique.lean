-- Prove2me | solution 1 for CHMSPricing.OpmUniform.astar_bstar_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:35:55.039365+00:00
-- url     : https://prove2.me/submissions/22fa0603-99b8-4e9d-a904-98ec9043b0bc

import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Prophet

namespace CHMSPricing.OpmUniform.P6bdc

open MeasureTheory ProbabilityTheory

/-- Fixed point lemma: `a = ∑ i, E (Y i - a/k)^+` has a unique solution. -/
theorem key {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m k : ℕ} (hk : 0 < k) (Y : Fin m → Ω → ℝ) (hY : ∀ i, Integrable (Y i) P) :
    ∃! a : ℝ, a = ∑ i, ∫ ω, max 0 (Y i ω - a / k) ∂P := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set F : ℝ → ℝ := fun a => ∑ i, ∫ ω, max 0 (Y i ω - a / k) ∂P with hFdef
  have hint : ∀ i (a : ℝ), Integrable (fun ω => max 0 (Y i ω - a / k)) P := by
    intro i a
    have := ((hY i).sub (integrable_const (a / k))).pos_part
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [max_comm]
  have hnn : ∀ a, 0 ≤ F a := fun a =>
    Finset.sum_nonneg fun i _ => integral_nonneg fun ω => le_max_left _ _
  have hanti : ∀ a b, a ≤ b → F b ≤ F a := by
    intro a b hab
    refine Finset.sum_le_sum fun i _ => integral_mono (hint i b) (hint i a) fun ω => ?_
    have : a / k ≤ b / k := div_le_div_of_nonneg_right hab hkpos.le
    exact max_le_max le_rfl (by linarith)
  have hlip : ∀ a b, a ≤ b → F a ≤ F b + (m / k) * (b - a) := by
    intro a b hab
    have h1 : ∀ i, ∫ ω, max 0 (Y i ω - a / k) ∂P ≤
        ∫ ω, max 0 (Y i ω - b / k) ∂P + (b - a) / k := by
      intro i
      have : ∫ ω, max 0 (Y i ω - a / k) ∂P ≤ ∫ ω, (max 0 (Y i ω - b / k) + (b - a) / k) ∂P := by
        refine integral_mono (hint i a) ((hint i b).add (integrable_const _)) fun ω => ?_
        have e : (b - a) / k = b / k - a / k := by ring
        simp only [e]
        rcases le_total 0 (Y i ω - a / k) with h | h
        · rw [max_eq_right h]; have := le_max_right 0 (Y i ω - b / k); linarith
        · rw [max_eq_left h]; have := le_max_left 0 (Y i ω - b / k)
          have : a / k ≤ b / k := div_le_div_of_nonneg_right hab hkpos.le
          linarith
      rw [integral_add (hint i b) (integrable_const _)] at this
      simpa using this
    calc F a ≤ ∑ i : Fin m, (∫ ω, max 0 (Y i ω - b / k) ∂P + (b - a) / k) :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = F b + (m / k) * (b - a) := by
          rw [Finset.sum_add_distrib]; simp [hFdef]; ring
  have hcont : Continuous F := by
    have : LipschitzWith (Real.toNNReal (m / k)) F := by
      refine LipschitzWith.of_le_add_mul' _ fun x y => ?_
      rw [Real.dist_eq]
      rcases le_total x y with h | h
      · have := hlip x y h
        rw [abs_of_nonpos (by linarith)]; linarith
      · have := hanti y x h
        have : 0 ≤ (m / k : ℝ) * |x - y| := by positivity
        linarith
    exact this.continuous
  set g : ℝ → ℝ := fun a => a - F a
  have hg : Continuous g := continuous_id.sub hcont
  obtain ⟨a, ha⟩ : (0 : ℝ) ∈ Set.range g := by
    refine intermediate_value_univ 0 (F 0) hg ⟨?_, ?_⟩
    · simp only [g]; linarith [hnn 0]
    · simp only [g]; linarith [hanti 0 (F 0) (hnn 0)]
  refine ⟨a, ?_, ?_⟩
  · show a = F a
    simp only [g] at ha; linarith
  · intro b hb
    have hb' : b = F b := hb
    have ha' : a = F a := by simp only [g] at ha; linarith
    rcases lt_trichotomy a b with h | h | h
    · have := hanti a b h.le; linarith
    · exact h.symm
    · have := hanti b a h.le; linarith

/-- Combinatorial characterization of `orderStat` by counts. -/
theorem le_orderStat_iff {n : ℕ} (x : Fin n → ℝ) (i : ℕ) (hi : i < n) (t : ℝ) :
    t ≤ orderStat x i ↔ i + 1 ≤ (Finset.univ.filter (fun j => t ≤ x j)).card := by
  classical
  set L := (Finset.univ.val.map x).sort (fun a b => b ≤ a) with hL
  have hlen : L.length = n := by simp [hL]
  have hsorted : L.Pairwise (fun a b => b ≤ a) := Multiset.pairwise_sort _ _
  have hiL : i < L.length := by omega
  have hos : orderStat x i = L[i] := by
    show L.getD i 0 = L[i]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL]
    rfl
  have hcount : (Finset.univ.filter (fun j => t ≤ x j)).card = L.countP (fun v => decide (t ≤ v)) := by
    have h1 : (L : Multiset ℝ) = Finset.univ.val.map x := Multiset.sort_eq _ _
    rw [← Multiset.coe_countP, h1, Multiset.countP_map, Finset.card_def, Finset.filter_val]
  rw [hos, hcount]
  have hpw := List.pairwise_iff_getElem.mp hsorted
  constructor
  · intro ht
    have hall : ∀ v ∈ L.take (i + 1), t ≤ v := by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hv
      have hj1 : j ≤ i := by omega
      rcases hj1.lt_or_eq with hlt | heq
      · exact ht.trans (hpw j i (by omega) hiL hlt)
      · subst heq; exact ht
    have e1 : (L.take (i + 1)).countP (fun v => decide (t ≤ v)) = i + 1 := by
      rw [List.countP_eq_length.mpr (by simpa using hall)]
      simp; omega
    calc i + 1 = (L.take (i + 1)).countP (fun v => decide (t ≤ v)) := e1.symm
      _ ≤ L.countP (fun v => decide (t ≤ v)) := (List.take_sublist _ _).countP_le
  · intro hc
    by_contra ht
    push Not at ht
    have hnone : ∀ v ∈ L.drop i, ¬ t ≤ v := by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hv
      have hle : L[i + j] ≤ L[i] := by
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0; simp
        · exact hpw i (i + j) hiL (by omega) (by omega)
      exact not_le.mpr (lt_of_le_of_lt hle ht)
    have e2 : (L.drop i).countP (fun v => decide (t ≤ v)) = 0 :=
      List.countP_eq_zero.mpr (by simpa using hnone)
    have e3 : (L.take i).countP (fun v => decide (t ≤ v)) ≤ i := by
      refine (List.countP_le_length).trans ?_
      simp
    have := List.countP_append (l₁ := L.take i) (l₂ := L.drop i) (p := fun v => decide (t ≤ v))
    rw [List.take_append_drop] at this
    omega

theorem orderStat_mem_or_zero {n : ℕ} (x : Fin n → ℝ) (i : ℕ) :
    orderStat x i = 0 ∨ ∃ j, orderStat x i = x j := by
  unfold orderStat
  rw [List.getD_eq_getElem?_getD]
  cases h : ((Finset.univ.val.map x).sort (fun a b => b ≤ a))[i]? with
  | none => left; simp
  | some v =>
    right
    have hv := List.mem_of_getElem? h
    rw [Multiset.mem_sort, Multiset.mem_map] at hv
    obtain ⟨j, _, hj⟩ := hv
    exact ⟨j, by simp [hj]⟩

theorem orderStat_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (i : ℕ) (hi : i < n) :
    Measurable (fun ω => orderStat (fun j => X j ω) i) := by
  classical
  refine measurable_of_Ici fun t => ?_
  have hset : (fun ω => orderStat (fun j => X j ω) i) ⁻¹' Set.Ici t =
      {ω | i + 1 ≤ ∑ j, (if t ≤ X j ω then 1 else 0 : ℕ)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_ofPred_eq]
    rw [le_orderStat_iff _ i hi t, Finset.card_filter]
  rw [hset]
  have hmeas : Measurable (fun ω => ∑ j, (if t ≤ X j ω then 1 else 0 : ℕ)) := by
    refine Finset.measurable_sum _ fun j _ => ?_
    exact Measurable.ite (measurableSet_le measurable_const (hXm j)) measurable_const
      measurable_const
  exact measurableSet_le measurable_const hmeas

end CHMSPricing.OpmUniform.P6bdc

open MeasureTheory ProbabilityTheory CHMSPricing.OpmUniform in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hXint : ∀ i, Integrable (X i) P) :
    (∃! a : ℝ, a = ∑ i : Fin k, ∫ ω, max 0 (orderStat (fun j => X j ω) i - a / k) ∂P) ∧
    (∃! b : ℝ, b = ∑ i, ∫ ω, max 0 (X i ω - b / k) ∂P) := by
  refine ⟨?_, P6bdc.key P hk X hXint⟩
  have hYint : ∀ i : Fin k, Integrable (fun ω => orderStat (fun j => X j ω) (i : ℕ)) P := by
    intro i
    refine Integrable.mono' (integrable_finsetSum Finset.univ fun j _ => (hXint j).abs)
      (P6bdc.orderStat_measurable X hXm i (by omega)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    rcases P6bdc.orderStat_mem_or_zero (fun j => X j ω) i with h | ⟨j, h⟩
    · rw [h, abs_zero]; exact Finset.sum_nonneg fun j _ => abs_nonneg _
    · rw [h]
      exact Finset.single_le_sum (f := fun j => |X j ω|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ j)
  exact P6bdc.key P hk (fun i ω => orderStat (fun j => X j ω) (i : ℕ)) hYint
