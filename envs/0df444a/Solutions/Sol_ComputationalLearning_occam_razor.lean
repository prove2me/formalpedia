-- Prove2me | solution 1 for ComputationalLearning.occam_razor
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T03:22:15.896583+00:00
-- url     : https://prove2.me/submissions/ca97380e-8d9d-4715-bb2d-e8f6f84420bb

import Mathlib
import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory

namespace ComputationalLearning

section OccamCard

variable {X : Type*} [MeasurableSpace X]

lemma oc_single (c : X → Bool) (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D]
    (h : X → Bool) (hh : Measurable h) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (herr : ε < errorOf D c h) (m : ℕ) :
    sampleLaw D c m {S | IsConsistent h S} ≤ ENNReal.ofReal ((1 - ε) ^ m) := by
  have hφ : Measurable (fun x : X => (x, c x)) := measurable_id.prodMk hc
  haveI : IsProbabilityMeasure (exampleLaw D c) :=
    Measure.isProbabilityMeasure_map hφ.aemeasurable
  have hset : {S : Fin m → X × Bool | IsConsistent h S} =
      Set.univ.pi (fun _ => {q : X × Bool | h q.1 = q.2}) := by
    ext S; simp [IsConsistent, Set.mem_pi]
  rw [hset, sampleLaw, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hA : exampleLaw D c {q : X × Bool | h q.1 = q.2} = 1 - D {x | h x ≠ c x} := by
    rw [exampleLaw, Measure.map_apply hφ (show MeasurableSet {q : X × Bool | h q.1 = q.2} from
      measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd)]
    have : (fun x : X => (x, c x)) ⁻¹' {q : X × Bool | h q.1 = q.2} = {x | h x ≠ c x}ᶜ := by
      ext x; simp
    rw [this, prob_compl_eq_one_sub
      (show MeasurableSet {x | h x ≠ c x} from (measurableSet_eq_fun hh hc).compl)]
  rw [hA]
  have h1 : 1 - D {x | h x ≠ c x} ≤ ENNReal.ofReal (1 - ε) := by
    rw [ENNReal.ofReal_sub 1 hε.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left (ENNReal.ofReal_le_of_le_toReal herr.le) 1
  calc (1 - D {x | h x ≠ c x}) ^ m ≤ ENNReal.ofReal (1 - ε) ^ m := pow_le_pow_left₀ zero_le h1 m
    _ = ENNReal.ofReal ((1 - ε) ^ m) := (ENNReal.ofReal_pow (by linarith) m).symm

theorem oc_bad (c : X → Bool) (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D]
    (H : Finset (X → Bool)) (hH : ∀ h ∈ H, Measurable h) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) :
    sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ≤
      ENNReal.ofReal (H.card * (1 - ε) ^ m) := by
  classical
  set H' := H.filter (fun h => ε < errorOf D c h) with hH'
  have hsub : {S : Fin m → X × Bool | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ⊆
      ⋃ h ∈ H', {S | IsConsistent h S} := by
    rintro S ⟨h, hh, hcons, herr⟩
    exact Set.mem_iUnion₂.mpr ⟨h, Finset.mem_filter.mpr ⟨hh, herr⟩, hcons⟩
  calc sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h}
      ≤ sampleLaw D c m (⋃ h ∈ H', {S | IsConsistent h S}) := measure_mono hsub
    _ ≤ ∑ h ∈ H', sampleLaw D c m {S | IsConsistent h S} := measure_biUnion_finset_le _ _
    _ ≤ ∑ h ∈ H', ENNReal.ofReal ((1 - ε) ^ m) := Finset.sum_le_sum fun h hh =>
          oc_single c hc D h (hH h (Finset.mem_filter.mp hh).1) hε hε1
            (Finset.mem_filter.mp hh).2 m
    _ = ENNReal.ofReal (H'.card * (1 - ε) ^ m) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (H.card * (1 - ε) ^ m) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) m)
          exact_mod_cast Finset.card_filter_le _ _

/-- `K (1 − ε)^m ≤ δ` once `m ≥ (1/ε)(ln K + ln(1/δ))`. -/
lemma oc_real {K ε δ : ℝ} (hK : 0 < K) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (m : ℕ)
    (hm : 1 / ε * (Real.log K + Real.log (1 / δ)) ≤ m) : K * (1 - ε) ^ m ≤ δ := by
  calc K * (1 - ε) ^ m ≤ K * Real.exp (-(ε * m)) := by
        apply mul_le_mul_of_nonneg_left _ hK.le
        calc (1 - ε) ^ m ≤ (Real.exp (-ε)) ^ m :=
              pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-ε)]) m
          _ = Real.exp (-(ε * m)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ K * Real.exp (-(Real.log K + Real.log (1 / δ))) := by
        apply mul_le_mul_of_nonneg_left _ hK.le
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left hm hε.le
        have e : ε * (1 / ε * (Real.log K + Real.log (1 / δ))) =
            Real.log K + Real.log (1 / δ) := by field_simp
        linarith
    _ = δ := by
        rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hK,
          Real.exp_log (by positivity)]
        field_simp

lemma oc_null (c : X → Bool) (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D]
    (m : ℕ) : sampleLaw D c m {S | ¬ IsLabeledBy c S} = 0 := by
  have hφ : Measurable (fun x : X => (x, c x)) := measurable_id.prodMk hc
  haveI : IsProbabilityMeasure (exampleLaw D c) :=
    Measure.isProbabilityMeasure_map hφ.aemeasurable
  have e : {S : Fin m → X × Bool | ¬ IsLabeledBy c S} =
      ⋃ j, (fun S : Fin m → X × Bool => S j) ⁻¹' {p | p.2 ≠ c p.1} := by
    ext S; simp [IsLabeledBy]
  rw [e]
  refine measure_iUnion_null fun j => ?_
  apply Measure.pi_eval_preimage_null
  have hms : MeasurableSet {p : X × Bool | p.2 ≠ c p.1} :=
    (measurableSet_eq_fun measurable_snd (hc.comp measurable_fst)).compl
  rw [exampleLaw, Measure.map_apply hφ hms]
  simp

theorem oc_main (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] (H : Finset (X → Bool)) (hH : ∀ h ∈ H, Measurable h)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (m : ℕ) :
    sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ≤
      ENNReal.ofReal (H.card * (1 - ε) ^ m) ∧
    (1 / ε * (Real.log H.card + Real.log (1 / δ)) ≤ m →
      sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ≤ ENNReal.ofReal δ) ∧
    (∀ L : (Fin m → X × Bool) → X → Bool, (∀ S, L S ∈ H) →
      (∀ S, IsLabeledBy c S → IsConsistent (L S) S) →
      sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal (H.card * (1 - ε) ^ m)) := by
  refine ⟨oc_bad c hc D H hH hε hε1 m, fun hm => ?_, fun L hLH hLcons => ?_⟩
  · refine (oc_bad c hc D H hH hε hε1 m).trans (ENNReal.ofReal_le_ofReal ?_)
    rcases Nat.eq_zero_or_pos H.card with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, zero_mul]; exact hδ.le
    · exact oc_real (by exact_mod_cast hpos) hε hε1 hδ m hm
  · have hsub : {S : Fin m → X × Bool | ε < errorOf D c (L S)} ⊆ {S | ¬ IsLabeledBy c S} ∪
        {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} := by
      intro S hS
      by_cases hlab : IsLabeledBy c S
      · exact Or.inr ⟨L S, hLH S, hLcons S hlab, hS⟩
      · exact Or.inl hlab
    calc sampleLaw D c m {S | ε < errorOf D c (L S)}
        ≤ sampleLaw D c m ({S | ¬ IsLabeledBy c S} ∪
            {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h}) := measure_mono hsub
      _ ≤ sampleLaw D c m {S | ¬ IsLabeledBy c S} +
            sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} :=
          measure_union_le _ _
      _ ≤ 0 + ENNReal.ofReal (H.card * (1 - ε) ^ m) := by
          rw [oc_null c hc D m]
          gcongr
          exact oc_bad c hc D H hH hε hε1 m
      _ = ENNReal.ofReal (H.card * (1 - ε) ^ m) := zero_add _

end OccamCard


section Razor

lemma geom_two (N : ℕ) : ∑ ℓ ∈ Finset.range N, 2 ^ ℓ + 1 = 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, pow_succ]; omega

lemma short_lists (N : ℕ) : ∃ Ls : Finset (List Bool), Ls.card ≤ 2 ^ (N + 1) ∧
    ∀ r : List Bool, r.length ≤ N → r ∈ Ls := by
  classical
  refine ⟨(Finset.range (N + 1)).biUnion
    (fun ℓ => (Finset.univ : Finset (Fin ℓ → Bool)).image List.ofFn), ?_, ?_⟩
  · calc _ ≤ ∑ ℓ ∈ Finset.range (N + 1),
          ((Finset.univ : Finset (Fin ℓ → Bool)).image List.ofFn).card := Finset.card_biUnion_le
      _ ≤ ∑ ℓ ∈ Finset.range (N + 1), 2 ^ ℓ := Finset.sum_le_sum fun ℓ _ => by
          calc _ ≤ (Finset.univ : Finset (Fin ℓ → Bool)).card := Finset.card_image_le
            _ = 2 ^ ℓ := by simp
      _ ≤ 2 ^ (N + 1) := by have := geom_two (N + 1); omega
  · intro r hr
    rw [Finset.mem_biUnion]
    exact ⟨r.length, Finset.mem_range.mpr (Nat.lt_succ_of_le hr),
      Finset.mem_image.mpr ⟨r.get, Finset.mem_univ _, List.ofFn_get r⟩⟩

theorem razor_main {X : Type*} [MeasurableSpace X] (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] (R : List Bool → X → Bool)
    (hR : ∀ r, Measurable (R r)) (n s : ℕ) {α β : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β < 1)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (L : (Fin m → X × Bool) → List Bool)
    (hcons : ∀ S, IsLabeledBy c S → IsConsistent (R (L S)) S)
    (hsize : ∀ S, IsLabeledBy c S →
      ((L S).length : ℝ) ≤ ((n * s : ℕ) : ℝ) ^ α * (m : ℝ) ^ β)
    (hm1 : 2 / ε * Real.log (1 / δ) ≤ m) (hm2 : 4 * Real.log 2 / ε ≤ m)
    (hm3 : 4 * Real.log 2 / ε * ((n * s : ℕ) : ℝ) ^ α ≤ (m : ℝ) ^ (1 - β)) :
    sampleLaw D c m {S | ε < errorOf D c (R (L S))} ≤ ENNReal.ofReal δ := by
  classical
  set K : ℝ := ((n * s : ℕ) : ℝ) ^ α * (m : ℝ) ^ β with hKdef
  have hK0 : 0 ≤ K := by positivity
  set N := ⌊K⌋₊ with hN
  obtain ⟨Ls, hLs, hmem⟩ := short_lists N
  set H := Ls.image R with hH
  have hHm : ∀ h ∈ H, Measurable h := by
    intro h hh
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hh
    exact hR r
  have hsub : {S : Fin m → X × Bool | ε < errorOf D c (R (L S))} ⊆ {S | ¬ IsLabeledBy c S} ∪
      {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} := by
    intro S hS
    by_cases hlab : IsLabeledBy c S
    · refine Or.inr ⟨R (L S), Finset.mem_image.mpr ⟨L S, hmem _ ?_, rfl⟩, hcons S hlab, hS⟩
      exact Nat.le_floor (hsize S hlab)
    · exact Or.inl hlab
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm0 : (0:ℝ) < m := by
    have : 0 < 4 * Real.log 2 / ε := by positivity
    linarith
  have hcardH : (H.card : ℝ) ≤ 2 ^ (N + 1) := by
    have : H.card ≤ 2 ^ (N + 1) := Finset.card_image_le.trans hLs
    exact_mod_cast this
  have hNK : (N : ℝ) ≤ K := Nat.floor_le hK0
  have h2pow : (2:ℝ) ^ (N + 1) ≤ Real.exp (Real.log 2 * (K + 1)) := by
    rw [← Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hKln : K * Real.log 2 ≤ ε / 4 * m := by
    have h3 := mul_le_mul_of_nonneg_left hm3 (show 0 ≤ ε / 4 * (m:ℝ) ^ β by positivity)
    have e1 : ε / 4 * (m:ℝ) ^ β * (4 * Real.log 2 / ε * ((n * s : ℕ) : ℝ) ^ α) =
        K * Real.log 2 := by
      rw [hKdef]; field_simp
    have e2 : ε / 4 * (m:ℝ) ^ β * (m:ℝ) ^ (1 - β) = ε / 4 * m := by
      rw [mul_assoc, ← Real.rpow_add hm0]; simp
    linarith
  have hl1 : Real.log (1 / δ) ≤ ε / 2 * m := by
    have := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ ε / 2 by positivity)
    have e : ε / 2 * (2 / ε * Real.log (1 / δ)) = Real.log (1 / δ) := by field_simp
    linarith
  have hl2 : Real.log 2 ≤ ε / 4 * m := by
    have := mul_le_mul_of_nonneg_left hm2 (show 0 ≤ ε / 4 by positivity)
    have e : ε / 4 * (4 * Real.log 2 / ε) = Real.log 2 := by field_simp
    linarith
  have hexp : (1 - ε) ^ m ≤ Real.exp (-(ε * m)) := by
    calc (1 - ε) ^ m ≤ (Real.exp (-ε)) ^ m :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-ε)]) m
      _ = Real.exp (-(ε * m)) := by rw [← Real.exp_nat_mul]; ring_nf
  have hbound : (H.card : ℝ) * (1 - ε) ^ m ≤ δ := by
    calc (H.card : ℝ) * (1 - ε) ^ m ≤ Real.exp (Real.log 2 * (K + 1)) * Real.exp (-(ε * m)) :=
          mul_le_mul (hcardH.trans h2pow) hexp (pow_nonneg (by linarith) m) (Real.exp_pos _).le
      _ = Real.exp (Real.log 2 * (K + 1) - ε * m) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-Real.log (1 / δ)) := Real.exp_le_exp.mpr (by linarith)
      _ = δ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  calc sampleLaw D c m {S | ε < errorOf D c (R (L S))}
      ≤ sampleLaw D c m ({S | ¬ IsLabeledBy c S} ∪
          {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h}) := measure_mono hsub
    _ ≤ sampleLaw D c m {S | ¬ IsLabeledBy c S} +
          sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} :=
        measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal (H.card * (1 - ε) ^ m) := by
        rw [oc_null c hc D m]
        gcongr
        exact oc_bad c hc D H hHm hε hε1 m
    _ ≤ ENNReal.ofReal δ := by rw [zero_add]; exact ENNReal.ofReal_le_ofReal hbound

end Razor

end ComputationalLearning

open ComputationalLearning

theorem solution {X : Type*} [MeasurableSpace X] (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] (R : List Bool → X → Bool)
    (hR : ∀ r, Measurable (R r)) (n s : ℕ) {α β : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β < 1)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (L : (Fin m → X × Bool) → List Bool)
    (hcons : ∀ S, IsLabeledBy c S → IsConsistent (R (L S)) S)
    (hsize : ∀ S, IsLabeledBy c S →
      ((L S).length : ℝ) ≤ ((n * s : ℕ) : ℝ) ^ α * (m : ℝ) ^ β)
    (hm1 : 2 / ε * Real.log (1 / δ) ≤ m) (hm2 : 4 * Real.log 2 / ε ≤ m)
    (hm3 : 4 * Real.log 2 / ε * ((n * s : ℕ) : ℝ) ^ α ≤ (m : ℝ) ^ (1 - β)) :
    sampleLaw D c m {S | ε < errorOf D c (R (L S))} ≤ ENNReal.ofReal δ := by
  exact razor_main c hc D R hR n s hα hβ0 hβ hε hε1 hδ hδ1 m L hcons hsize hm1 hm2 hm3
