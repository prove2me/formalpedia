-- Prove2me | solution 1 for ComputationalLearning.vc_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:51:41.743019+00:00
-- url     : https://prove2.me/submissions/ef5a04bd-bf5d-4b0b-930f-f67988a4c8d4

import Definitions.Def_ComputationalLearning_VC

open MeasureTheory


namespace ComputationalLearning

open Classical in
theorem vclb_flip {d m : ℕ} (s : Fin m → Fin d) (U : Finset (Fin d))
    (hU : ∀ i ∈ U, ∀ j, s j ≠ i) (H : (Fin d → Bool) → Fin d → Bool)
    (hH : ∀ b b', (∀ j, b (s j) = b' (s j)) → H b = H b') :
    2 ^ d ≤ 2 * (Finset.univ.filter
      (fun b : Fin d → Bool => U.card ≤ 2 * (U.filter (fun i => H b i ≠ b i)).card)).card := by
  set A := Finset.univ.filter
      (fun b : Fin d → Bool => U.card ≤ 2 * (U.filter (fun i => H b i ≠ b i)).card) with hA
  let fl : (Fin d → Bool) → (Fin d → Bool) := fun b i => if i ∈ U then !b i else b i
  have hfl : ∀ b, fl (fl b) = b := by
    intro b; funext i; simp only [fl]; split_ifs <;> simp
  have hHfl : ∀ b, H (fl b) = H b := by
    intro b; apply hH; intro j
    simp only [fl]; rw [if_neg]; intro hj; exact hU _ hj j rfl
  have hsum : ∀ b, (U.filter (fun i => H b i ≠ b i)).card
      + (U.filter (fun i => H (fl b) i ≠ fl b i)).card = U.card := by
    intro b
    have : U.filter (fun i => H (fl b) i ≠ fl b i) = U.filter (fun i => ¬ (H b i ≠ b i)) := by
      apply Finset.filter_congr
      intro i hi
      rw [hHfl]; simp only [fl, if_pos hi]
      cases H b i <;> cases b i <;> simp
    rw [this, Finset.card_filter_add_card_filter_not]
  have hcov : (Finset.univ : Finset (Fin d → Bool)) ⊆ A ∪ A.image fl := by
    intro b _
    by_cases hb : b ∈ A
    · exact Finset.mem_union_left _ hb
    · apply Finset.mem_union_right
      refine Finset.mem_image.2 ⟨fl b, ?_, hfl b⟩
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hb ⊢
      have := hsum b
      omega
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_union_le A (A.image fl)
  have h3 : (A.image fl).card ≤ A.card := Finset.card_image_le
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h1
  omega

open Classical in
theorem vclb_avg {d m : ℕ} (P : (Fin m → Fin d) → ℝ) (hP : ∀ s, 0 ≤ P s)
    (G : Finset (Fin m → Fin d)) (E : (Fin d → Bool) → (Fin m → Fin d) → Prop)
    (hE : ∀ s ∈ G, 2 ^ d ≤ 2 * (Finset.univ.filter (fun b => E b s)).card) :
    ∃ b, (∑ s ∈ G, P s) / 2 ≤ ∑ s ∈ Finset.univ.filter (fun s => E b s), P s := by
  by_contra hcon
  push_neg at hcon
  have h1 : ∑ b : Fin d → Bool, ∑ s ∈ Finset.univ.filter (fun s => E b s), P s
      < ∑ b : Fin d → Bool, (∑ s ∈ G, P s) / 2 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun b _ => hcon b)
  have h2 : ∑ b : Fin d → Bool, ∑ s ∈ Finset.univ.filter (fun s => E b s), P s
      = ∑ s, P s * ((Finset.univ.filter (fun b => E b s)).card : ℝ) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _; split_ifs <;> simp
  have h3 : ∑ s ∈ G, P s * (2 ^ d / 2 : ℝ)
      ≤ ∑ s, P s * ((Finset.univ.filter (fun b => E b s)).card : ℝ) := by
    calc ∑ s ∈ G, P s * (2 ^ d / 2 : ℝ)
        ≤ ∑ s ∈ G, P s * ((Finset.univ.filter (fun b => E b s)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro s hs
          apply mul_le_mul_of_nonneg_left _ (hP s)
          have := hE s hs
          have : ((2 ^ d : ℕ) : ℝ) ≤ ((2 * (Finset.univ.filter (fun b => E b s)).card : ℕ) : ℝ) := by
            exact_mod_cast this
          push_cast at this
          linarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun s _ _ => mul_nonneg (hP s) (Nat.cast_nonneg _))
  rw [h2] at h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at h1
  rw [← Finset.sum_mul] at h3
  push_cast at h1
  nlinarith


noncomputable def vclbD {X : Type*} [MeasurableSpace X] {d : ℕ} (x : Fin d → X) (w : Fin d → ℝ) :
    Measure X := ∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i)

section bridge
variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {d : ℕ}

theorem vclbD_apply (x : Fin d → X) (w : Fin d → ℝ) (A : Set X) :
    vclbD x w A = ∑ i, ENNReal.ofReal (w i) * A.indicator 1 (x i) := by
  simp [vclbD, Measure.coe_finsetSum, Measure.dirac_apply]

theorem vclbD_prob (x : Fin d → X) (w : Fin d → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) : IsProbabilityMeasure (vclbD x w) := by
  constructor
  rw [vclbD_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hw1, ENNReal.ofReal_one]

theorem vclbD_single (x : Fin d → X) (hx : Function.Injective x) (w : Fin d → ℝ) (i : Fin d) :
    vclbD x w {x i} = ENNReal.ofReal (w i) := by
  rw [vclbD_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Set.indicator, hx.ne hk]
  · simp

theorem vclb_err (x : Fin d → X) (w : Fin d → ℝ) (hw0 : ∀ i, 0 ≤ w i) (c h : X → Bool) :
    errorOf (vclbD x w) c h = ∑ i, w i * if h (x i) ≠ c (x i) then 1 else 0 := by
  unfold errorOf
  rw [vclbD_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw0 i)]
    congr 1
    by_cases hh : h (x i) ≠ c (x i) <;> simp [Set.indicator, hh]
  · intro i _
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    by_cases hh : h (x i) ≠ c (x i) <;> simp [Set.indicator, hh]

theorem vclb_aemeas (x : Fin d → X) (w : Fin d → ℝ) (c : X → Bool) :
    AEMeasurable (fun y => (y, c y)) (vclbD x w) := by
  classical
  let T : Finset X := (Finset.univ.image x).filter (fun y => c y = true)
  let g : X → X × Bool := fun y => (y, if y ∈ (T : Set X) then true else false)
  have hg : Measurable g :=
    measurable_id.prodMk (Measurable.ite T.measurableSet measurable_const measurable_const)
  refine ⟨g, hg, ?_⟩
  rw [Filter.EventuallyEq, ae_iff, vclbD_apply]
  apply Finset.sum_eq_zero
  intro i _
  have : x i ∉ {a | ¬ (a, c a) = g a} := by
    simp only [Set.mem_setOf_eq, not_not, g, T, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_image, Finset.mem_univ, true_and]
    by_cases hc : c (x i) = true
    · simp [hc]
    · simp [hc]
  simp [Set.indicator, this]

open Classical in
theorem vclb_bridge {m : ℕ} (x : Fin d → X) (hx : Function.Injective x) (w : Fin d → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (c : X → Bool) (A : Set (Fin m → X × Bool)) :
    ENNReal.ofReal (∑ s ∈ Finset.univ.filter
        (fun s : Fin m → Fin d => (fun j => (x (s j), c (x (s j)))) ∈ A), ∏ j, w (s j))
      ≤ sampleLaw (vclbD x w) c m A := by
  haveI := vclbD_prob x w hw0 hw1
  haveI : IsFiniteMeasure (exampleLaw (vclbD x w) c) := by unfold exampleLaw; infer_instance
  let pt : (Fin m → Fin d) → (Fin m → X × Bool) := fun s j => (x (s j), c (x (s j)))
  have hpt : Function.Injective pt := by
    intro s s' h
    funext j
    have := congrFun h j
    simp only [pt, Prod.mk.injEq] at this
    exact hx this.1
  let F := Finset.univ.filter (fun s : Fin m → Fin d => pt s ∈ A)
  have hsub : ((F.image pt : Finset _) : Set (Fin m → X × Bool)) ⊆ A := by
    intro p hp
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, F, Finset.mem_filter] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    exact hs.2
  have hsingle : ∀ i, exampleLaw (vclbD x w) c {(x i, c (x i))} = ENNReal.ofReal (w i) := by
    intro i
    unfold exampleLaw
    rw [Measure.map_apply_of_aemeasurable (vclb_aemeas x w c) (measurableSet_singleton _)]
    have : (fun y => (y, c y)) ⁻¹' {(x i, c (x i))} = {x i} := by
      ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · exact fun h => h.1
      · rintro rfl; exact ⟨rfl, rfl⟩
    rw [this, vclbD_single x hx]
  calc ENNReal.ofReal (∑ s ∈ F, ∏ j, w (s j))
      = ∑ s ∈ F, ∏ j, ENNReal.ofReal (w (s j)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => Finset.prod_nonneg (fun j _ => hw0 _))]
        apply Finset.sum_congr rfl
        intro s _
        rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => hw0 _)]
    _ = ∑ s ∈ F, sampleLaw (vclbD x w) c m {pt s} := by
        apply Finset.sum_congr rfl
        intro s _
        unfold sampleLaw
        rw [Measure.pi_singleton]
        apply Finset.prod_congr rfl
        intro j _
        rw [hsingle]
    _ = ∑ p ∈ F.image pt, sampleLaw (vclbD x w) c m {p} := by
        rw [Finset.sum_image (fun a _ b _ h => hpt h)]
    _ = sampleLaw (vclbD x w) c m (F.image pt : Set _) := by
        rw [sum_measure_singleton]
    _ ≤ _ := measure_mono hsub

end bridge

open Classical in
theorem vclb_core {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : Set (X → Bool)) {d m : ℕ} (x : Fin d → X) (hx : Function.Injective x)
    (hsh : ∀ b : Fin d → Bool, ∃ c ∈ C, ∀ i, c (x i) = b i)
    (L : (Fin m → X × Bool) → X → Bool) (w : Fin d → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (Q : ℝ → Prop) (hQ : ∀ a b, a ≤ b → Q a → Q b)
    (G : Finset (Fin m → Fin d)) (U : (Fin m → Fin d) → Finset (Fin d))
    (hU : ∀ s, ∀ i ∈ U s, ∀ j, s j ≠ i)
    (hQU : ∀ s ∈ G, ∀ V ⊆ U s, (U s).card ≤ 2 * V.card → Q (∑ i ∈ V, w i)) :
    ∃ c ∈ C, ∃ D : Measure X, IsProbabilityMeasure D ∧
      ENNReal.ofReal ((∑ s ∈ G, ∏ j, w (s j)) / 2) ≤
        sampleLaw D c m {S | Q (errorOf D c (L S))} := by
  choose cf hcfC hcf using hsh
  let D := vclbD x w
  let pt : (Fin d → Bool) → (Fin m → Fin d) → (Fin m → X × Bool) :=
    fun b s j => (x (s j), b (s j))
  let E : (Fin d → Bool) → (Fin m → Fin d) → Prop :=
    fun b s => Q (errorOf D (cf b) (L (pt b s)))
  have hE : ∀ s ∈ G, 2 ^ d ≤ 2 * (Finset.univ.filter (fun b => E b s)).card := by
    intro s hs
    have hfl := vclb_flip s (U s) (hU s) (fun b i => L (pt b s) (x i)) (by
      intro b b' hbb
      funext i
      simp only [pt]
      congr 2
      funext j
      rw [hbb j])
    refine le_trans hfl (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    refine hQ _ _ ?_ (hQU s hs _ (Finset.filter_subset _ _) hb)
    rw [vclb_err x w hw0]
    calc ∑ i ∈ (U s).filter (fun i => L (pt b s) (x i) ≠ b i), w i
        = ∑ i ∈ (U s).filter (fun i => L (pt b s) (x i) ≠ b i),
            w i * (if L (pt b s) (x i) ≠ cf b (x i) then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mem_filter] at hi
          rw [hcf, if_pos hi.2, mul_one]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => mul_nonneg (hw0 i) (by split_ifs <;> norm_num))
  obtain ⟨b, hb⟩ := vclb_avg (fun s => ∏ j, w (s j))
    (fun s => Finset.prod_nonneg (fun j _ => hw0 _)) G E hE
  refine ⟨cf b, hcfC b, D, vclbD_prob x w hw0 hw1, ?_⟩
  refine le_trans (ENNReal.ofReal_le_ofReal hb) (le_trans (le_of_eq ?_)
    (vclb_bridge x hx w hw0 hw1 (cf b) {S | Q (errorOf D (cf b) (L S))}))
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, E, pt, hcf]

theorem vclb_shatter {X : Type*} (C : Set (X → Bool)) (d : ℕ) (hd1 : 1 ≤ d)
    (hd : (d : ℕ∞) ≤ vcDim C) :
    ∃ x : Fin d → X, Function.Injective x ∧ ∀ b : Fin d → Bool, ∃ c ∈ C, ∀ i, c (x i) = b i := by
  classical
  have hlt : ((d - 1 : ℕ) : ℕ∞) < vcDim C := by
    refine lt_of_lt_of_le ?_ hd
    exact_mod_cast (by omega : d - 1 < d)
  unfold vcDim at hlt
  obtain ⟨S, hS⟩ := lt_iSup_iff.1 hlt
  obtain ⟨hSh, hS2⟩ := lt_iSup_iff.1 hS
  have hcard : d ≤ S.card := by
    have : d - 1 < S.card := by exact_mod_cast hS2
    omega
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hcard
  let e := T.equivFin
  let x : Fin d → X := fun i => (e.symm (Fin.cast hT.symm i)).1
  refine ⟨x, ?_, ?_⟩
  · intro i j h
    have := Subtype.ext h
    have := e.symm.injective this
    exact Fin.cast_injective _ this
  · intro b
    let f : S → Bool := fun y => if hy : y.1 ∈ T then b (Fin.cast hT (e ⟨y.1, hy⟩)) else false
    obtain ⟨c, hc, hcf⟩ := hSh f
    refine ⟨c, hc, fun i => ?_⟩
    have hy : (e.symm (Fin.cast hT.symm i)).1 ∈ S := hTS (e.symm (Fin.cast hT.symm i)).2
    have := hcf ⟨_, hy⟩
    simp only [x]
    rw [this]
    simp only [f, Subtype.coe_prop, dite_true, Subtype.coe_eta, Equiv.apply_symm_apply]
    simp

theorem vclb_sumP {d m : ℕ} (w : Fin d → ℝ) :
    ∑ s : Fin m → Fin d, ∏ j, w (s j) = (∑ i, w i) ^ m := by
  rw [← Fintype.prod_sum (fun (_ : Fin m) i => w i)]
  simp

open Classical in
theorem vclb_unseen {d m : ℕ} (s : Fin m → Fin d) :
    d ≤ (Finset.univ.filter (fun i => ∀ j, s j ≠ i)).card + m := by
  have h : (Finset.univ : Finset (Fin d)) ⊆
      Finset.univ.filter (fun i => ∀ j, s j ≠ i) ∪ Finset.univ.image s := by
    intro i _
    by_cases hi : ∀ j, s j ≠ i
    · exact Finset.mem_union_left _ (by simp [hi])
    · push_neg at hi
      obtain ⟨j, rfl⟩ := hi
      exact Finset.mem_union_right _ (by simp)
  have h1 := Finset.card_le_card h
  have h2 := Finset.card_union_le (Finset.univ.filter (fun i => ∀ j, s j ≠ i))
    (Finset.univ.image s)
  have h3 : (Finset.univ.image s).card ≤ m := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := s))
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

open Classical in
theorem vclb_uniform {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : Set (X → Bool)) {d m : ℕ} (hd1 : 1 ≤ d) (x : Fin d → X) (hx : Function.Injective x)
    (hsh : ∀ b : Fin d → Bool, ∃ c ∈ C, ∀ i, c (x i) = b i)
    (L : (Fin m → X × Bool) → X → Bool) (Q : ℝ → Prop) (hQ : ∀ a b, a ≤ b → Q a → Q b)
    (hQ0 : Q (((d : ℝ) - m) / (2 * d))) :
    ∃ c ∈ C, ∃ D : Measure X, IsProbabilityMeasure D ∧
      ENNReal.ofReal (1 / 2) ≤ sampleLaw D c m {S | Q (errorOf D c (L S))} := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hw1 : ∑ _i : Fin d, (1 / (d : ℝ)) = 1 := by
    simp; field_simp
  obtain ⟨c, hc, D, hD, h⟩ := vclb_core C x hx hsh L (fun _ => 1 / (d : ℝ))
    (fun _ => by positivity) hw1 Q hQ Finset.univ
    (fun s => Finset.univ.filter (fun i => ∀ j, s j ≠ i))
    (by intro s i hi j; simp only [Finset.mem_filter] at hi; exact hi.2 j)
    (by
      intro s _ V _ hV
      apply hQ _ _ _ hQ0
      have h1 := vclb_unseen s
      have h2 : ((d : ℕ) : ℝ) ≤ 2 * (V.card : ℝ) + m := by
        have := le_trans h1 (Nat.add_le_add_right hV m)
        exact_mod_cast this
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith)
  refine ⟨c, hc, D, hD, le_trans (le_of_eq ?_) h⟩
  have := vclb_sumP (m := m) (fun _ : Fin d => 1 / (d : ℝ))
  rw [this, hw1]; simp

open Classical in
theorem vclb_rare_exp {k m : ℕ} (w : Fin (k + 1) → ℝ) (hw1 : ∑ i, w i = 1) (a : ℝ)
    (ha : ∑ i, w i * (if i.val ≠ 0 then 1 else 0) = a) (j0 : Fin m) :
    ∑ s : Fin m → Fin (k + 1), (∏ j, w (s j)) * (if (s j0).val ≠ 0 then 1 else 0) = a := by
  have := Fintype.prod_sum (fun (j : Fin m) (i : Fin (k + 1)) =>
    w i * (if j = j0 then (if i.val ≠ 0 then (1 : ℝ) else 0) else 1))
  have hl : ∏ j : Fin m, ∑ i : Fin (k + 1),
      w i * (if j = j0 then (if i.val ≠ 0 then (1 : ℝ) else 0) else 1) = a := by
    rw [Finset.prod_eq_single j0]
    · simpa using ha
    · intro j _ hj; simp [hj, hw1]
    · simp
  rw [hl] at this
  rw [this]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite_eq']
  simp

open Classical in
theorem vclb_rare {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : Set (X → Bool)) {k m : ℕ} (hk : 1 ≤ k) (x : Fin (k + 1) → X)
    (hx : Function.Injective x)
    (hsh : ∀ b : Fin (k + 1) → Bool, ∃ c ∈ C, ∀ i, c (x i) = b i)
    (L : (Fin m → X × Bool) → X → Bool) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 16)
    (hm : 64 * ε * m ≤ k) :
    ∃ c ∈ C, ∃ D : Measure X, IsProbabilityMeasure D ∧
      ENNReal.ofReal (1 / 4) ≤ sampleLaw D c m {S | ε < errorOf D c (L S)} := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  let w : Fin (k + 1) → ℝ := fun i => if i.val = 0 then 1 - 8 * ε else 8 * ε / k
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i; simp only [w]; split_ifs
    · linarith
    · positivity
  have hw1 : ∑ i, w i = 1 := by
    rw [Fin.sum_univ_succ]
    simp only [w, Fin.val_zero, if_true, Fin.val_succ, Nat.succ_ne_zero, if_false,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have ha : ∑ i, w i * (if i.val ≠ 0 then 1 else 0) = 8 * ε := by
    rw [Fin.sum_univ_succ]
    simp only [w, Fin.val_zero, if_true, Fin.val_succ, Nat.succ_ne_zero, if_false,
      ne_eq, not_true_eq_false, not_false_eq_true, mul_zero, mul_one, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  let r : (Fin m → Fin (k + 1)) → ℕ := fun s => (Finset.univ.filter fun j => (s j).val ≠ 0).card
  let U : (Fin m → Fin (k + 1)) → Finset (Fin (k + 1)) :=
    fun s => Finset.univ.filter (fun i => i.val ≠ 0 ∧ ∀ j, s j ≠ i)
  have hUr : ∀ s, k ≤ (U s).card + r s := by
    intro s
    have h : (Finset.univ : Finset (Fin k)).image Fin.succ ⊆
        U s ∪ (Finset.univ.filter fun j => (s j).val ≠ 0).image s := by
      intro i hi
      obtain ⟨i', _, rfl⟩ := Finset.mem_image.1 hi
      by_cases h' : ∀ j, s j ≠ i'.succ
      · exact Finset.mem_union_left _ (by simp [U, h'])
      · push_neg at h'
        obtain ⟨j, hj⟩ := h'
        apply Finset.mem_union_right
        refine Finset.mem_image.2 ⟨j, ?_, hj⟩
        simp [hj]
    have h1 := Finset.card_le_card h
    rw [Finset.card_image_of_injective _ (Fin.succ_injective k)] at h1
    have h2 := Finset.card_union_le (U s) ((Finset.univ.filter fun j => (s j).val ≠ 0).image s)
    have h3 := Finset.card_image_le (s := Finset.univ.filter fun j => (s j).val ≠ 0) (f := s)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    simp only [r]
    omega
  let G := Finset.univ.filter (fun s : Fin m → Fin (k + 1) => 2 * r s ≤ k)
  obtain ⟨c, hc, D, hD, h⟩ := vclb_core C x hx hsh L w hw0 hw1 (fun a => ε < a)
    (fun a b hab ha => lt_of_lt_of_le ha hab) G U
    (by intro s i hi j; simp only [U, Finset.mem_filter] at hi; exact hi.2.2 j)
    (by
      intro s hs V hV hVc
      have hsG : 2 * r s ≤ k := by simpa [G] using hs
      have hsum : ∑ i ∈ V, w i = V.card * (8 * ε / k) := by
        rw [Finset.sum_congr rfl (g := fun _ => 8 * ε / k), Finset.sum_const, nsmul_eq_mul]
        intro i hi
        have := hV hi
        simp only [U, Finset.mem_filter] at this
        simp only [w]; rw [if_neg this.2.1]
      rw [hsum]
      have h1 := hUr s
      have h2 : (k : ℝ) ≤ 4 * V.card := by
        have : k ≤ 4 * V.card := by omega
        exact_mod_cast this
      rw [mul_div_assoc', lt_div_iff₀ hkpos]
      nlinarith)
  refine ⟨c, hc, D, hD, le_trans (ENNReal.ofReal_le_ofReal ?_) h⟩
  -- probability of G is at least 3/4
  have hPtot := vclb_sumP (m := m) w
  rw [hw1, one_pow] at hPtot
  have hP0 : ∀ s : Fin m → Fin (k + 1), 0 ≤ ∏ j, w (s j) :=
    fun s => Finset.prod_nonneg (fun j _ => hw0 _)
  have hexp : ∑ s : Fin m → Fin (k + 1), (∏ j, w (s j)) * (r s : ℝ) = m * (8 * ε) := by
    have : ∀ s : Fin m → Fin (k + 1), (∏ j, w (s j)) * (r s : ℝ)
        = ∑ j0, (∏ j, w (s j)) * (if (s j0).val ≠ 0 then 1 else 0) := by
      intro s
      simp only [r, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; split_ifs <;> simp
    simp_rw [this]
    rw [Finset.sum_comm]
    simp_rw [vclb_rare_exp w hw1 (8 * ε) ha]
    simp
  have hnotG : ∑ s ∈ Finset.univ.filter (fun s => ¬ (2 * r s ≤ k)), ∏ j, w (s j)
      ≤ ∑ s : Fin m → Fin (k + 1), (∏ j, w (s j)) * (2 * (r s : ℝ) / k) := by
    calc _ ≤ ∑ s ∈ Finset.univ.filter (fun s => ¬ (2 * r s ≤ k)),
          (∏ j, w (s j)) * (2 * (r s : ℝ) / k) := by
          apply Finset.sum_le_sum
          intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hs
          have : (1 : ℝ) ≤ 2 * (r s : ℝ) / k := by
            rw [le_div_iff₀ hkpos]
            have : k < 2 * r s := hs
            have : (k : ℝ) < 2 * (r s : ℝ) := by exact_mod_cast this
            linarith
          nlinarith [hP0 s]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun s _ _ => mul_nonneg (hP0 s) (by positivity))
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun s : Fin m → Fin (k + 1) => 2 * r s ≤ k) (fun s => ∏ j, w (s j))
  have hexp2 : ∑ s : Fin m → Fin (k + 1), (∏ j, w (s j)) * (2 * (r s : ℝ) / k)
      = 2 / k * (m * (8 * ε)) := by
    rw [← hexp, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _; ring
  have hmk : 2 / (k : ℝ) * (m * (8 * ε)) ≤ 1 / 4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hkpos]
    nlinarith
  show 1 / 4 ≤ (∑ s ∈ G, ∏ j, w (s j)) / 2
  simp only [G]
  linarith

theorem vc_lower_bound_core {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : Set (X → Bool)) (d : ℕ) (hd1 : 1 ≤ d) (hd : (d : ℕ∞) ≤ vcDim C) (m : ℕ)
    (L : (Fin m → X × Bool) → X → Bool) :
    ((m : ℝ) ≤ d / 2 → ∃ c ∈ C, ∃ D : Measure X, IsProbabilityMeasure D ∧
      ENNReal.ofReal (1 / 2) ≤ sampleLaw D c m {S | 1 / 8 ≤ errorOf D c (L S)}) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 → (m : ℝ) ≤ (d - 1) / (64 * ε) →
      ∃ c ∈ C, ∃ D : Measure X, IsProbabilityMeasure D ∧
        ENNReal.ofReal (1 / 4) ≤ sampleLaw D c m {S | ε < errorOf D c (L S)}) := by
  obtain ⟨x, hx, hsh⟩ := vclb_shatter C d hd1 hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  constructor
  · intro hm
    apply vclb_uniform C hd1 x hx hsh L (fun a => 1 / 8 ≤ a) (fun a b hab h => le_trans h hab)
    show 1 / 8 ≤ ((d : ℝ) - m) / (2 * d)
    rw [le_div_iff₀ (by positivity)]
    linarith
  · intro ε hε hε1 hm
    have hm' : 64 * ε * m ≤ (d : ℝ) - 1 := by
      rw [le_div_iff₀ (by positivity)] at hm; linarith
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hm0 : (m : ℝ) ≤ 0 := by
        push_cast at hm'
        nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      obtain ⟨c, hc, D, hD, h⟩ := vclb_uniform C hd1 x hx hsh L (fun a => ε < a)
        (fun a b hab h => lt_of_lt_of_le h hab) (by
          show ε < (((0 + 1 : ℕ) : ℝ) - m) / (2 * ((0 + 1 : ℕ) : ℝ))
          have : (m : ℝ) = 0 := le_antisymm hm0 (Nat.cast_nonneg m)
          rw [this]; norm_num; linarith)
      exact ⟨c, hc, D, hD, le_trans (ENNReal.ofReal_le_ofReal (by norm_num)) h⟩
    · exact vclb_rare C hk x hx hsh L ε hε hε1 (by push_cast at hm'; linarith)

end ComputationalLearning

open ComputationalLearning


theorem solution {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : Set (X → Bool)) (d : ℕ) (hd1 : 1 ≤ d) (hd : (d : ℕ∞) ≤ vcDim C) (m : ℕ)
    (L : (Fin m → X × Bool) → X → Bool) :
    ((m : ℝ) ≤ d / 2 → ∃ c ∈ C, ∃ D : Measure X, IsProbabilityMeasure D ∧
      ENNReal.ofReal (1 / 2) ≤ sampleLaw D c m {S | 1 / 8 ≤ errorOf D c (L S)}) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 → (m : ℝ) ≤ (d - 1) / (64 * ε) →
      ∃ c ∈ C, ∃ D : Measure X, IsProbabilityMeasure D ∧
        ENNReal.ofReal (1 / 4) ≤ sampleLaw D c m {S | ε < errorOf D c (L S)}) := by
  exact vc_lower_bound_core C d hd1 hd m L
