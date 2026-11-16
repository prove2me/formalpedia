-- Prove2me | solution 1 for ExactLearningSeparation678.Randomized.Supplement.proposition_4_6
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:43:23.960601+00:00
-- url     : https://prove2.me/submissions/c1257704-2b66-44a6-b891-a2e6e06c6b97

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Teaching

open Classical
set_option autoImplicit false

open ExactLearningSeparation678.Randomized.Supplement QAlgorithms.Learning

theorem ELS46_split_nonneg {ι : Type} [Fintype ι] {C : Finset (ι → Bool)}
    (μ : {c // c ∈ C} → ℝ) (hμ : ∀ c, 0 ≤ μ c) : 0 ≤ splitObjective μ := by
  unfold splitObjective
  exact Real.iSup_nonneg (fun i => le_min (Finset.sum_nonneg (fun c _ => hμ c))
    (Finset.sum_nonneg (fun c _ => hμ c)))

theorem ELS46_fGamma_nonneg {ι : Type} [Fintype ι] (C : Finset (ι → Bool)) : 0 ≤ fGamma C := by
  unfold fGamma
  exact Real.iInf_nonneg (fun μ => ELS46_split_nonneg μ.1 μ.2.1.1)

/-- uniform distribution on a subfamily -/
noncomputable def ELS46_unif {ι : Type} [Fintype ι] (C C' : Finset (ι → Bool)) : {c // c ∈ C} → ℝ :=
  fun c => if c.1 ∈ C' then 1 / (C'.card : ℝ) else 0

theorem ELS46_unif_massAt {ι : Type} [Fintype ι] (C C' : Finset (ι → Bool)) (hsub : C' ⊆ C)
    (i : ι) (b : Bool) :
    massAt (ELS46_unif C C') i b = ((C'.filter fun c => c i = b).card : ℝ) / (C'.card : ℝ) := by
  unfold massAt ELS46_unif
  rw [Finset.sum_filter, Finset.univ_eq_attach]
  calc _ = ∑ a ∈ C.attach, (fun c : ι → Bool =>
        if c ∈ C' then (if c i = b then 1 / (C'.card : ℝ) else 0) else 0) a.1 :=
        Finset.sum_congr rfl (fun a _ => by
          dsimp only; by_cases h1 : a.1 i = b <;> by_cases h2 : a.1 ∈ C' <;> simp [h1, h2])
    _ = ∑ c ∈ C, (if c ∈ C' then (if c i = b then 1 / (C'.card : ℝ) else 0) else 0) :=
        Finset.sum_attach C (fun c : ι → Bool =>
          if c ∈ C' then (if c i = b then 1 / (C'.card : ℝ) else 0) else 0)
    _ = _ := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul]
      ring

theorem ELS46_unif_capped {ι : Type} [Fintype ι] (C C' : Finset (ι → Bool)) (hsub : C' ⊆ C)
    (h2 : 2 ≤ C'.card) : IsCappedDist C (ELS46_unif C C') := by
  have hk : (2:ℝ) ≤ C'.card := by exact_mod_cast h2
  refine ⟨⟨fun c => ?_, ?_⟩, fun c => ?_⟩
  · unfold ELS46_unif; split_ifs <;> positivity
  · unfold ELS46_unif
    rw [Finset.univ_eq_attach]
    rw [show (∑ x ∈ C.attach, if x.1 ∈ C' then 1 / (C'.card : ℝ) else 0) =
        ∑ x ∈ C, if x ∈ C' then 1 / (C'.card : ℝ) else 0 from
        Finset.sum_attach C (fun x => if x ∈ C' then 1 / (C'.card : ℝ) else 0),
      Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub, Finset.sum_const, nsmul_eq_mul]
    field_simp
  · unfold ELS46_unif; split_ifs
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    · norm_num

theorem ELS46_fGamma_le {ι : Type} [Fintype ι] (C C' : Finset (ι → Bool)) (hsub : C' ⊆ C)
    (h2 : 2 ≤ C'.card) : fGamma C ≤ gammaPrime C' := by
  unfold fGamma
  have hbdd : BddBelow (Set.range fun μ : {μ : {c // c ∈ C} → ℝ // IsCappedDist C μ} =>
      splitObjective μ.1) := ⟨0, by rintro _ ⟨μ, rfl⟩; exact ELS46_split_nonneg μ.1 μ.2.1.1⟩
  refine (ciInf_le hbdd ⟨ELS46_unif C C', ELS46_unif_capped C C' hsub h2⟩).trans (le_of_eq ?_)
  unfold splitObjective gammaPrime gammaFrac
  simp only [ELS46_unif_massAt C C' hsub]

theorem ELS46_fGamma_pos {ι : Type} [Fintype ι] (C : Finset (ι → Bool)) (h2 : 2 ≤ C.card) :
    0 < fGamma C := by
  have hk : (2:ℝ) ≤ C.card := by exact_mod_cast h2
  set δ : ℝ := 1 / (2 * (C.card : ℝ)) with hδ
  have hδpos : 0 < δ := by positivity
  have hne : Nonempty {μ : {c // c ∈ C} → ℝ // IsCappedDist C μ} :=
    ⟨⟨ELS46_unif C C, ELS46_unif_capped C C (subset_refl _) h2⟩⟩
  refine lt_of_lt_of_le hδpos ?_
  unfold fGamma
  refine le_ciInf (fun μ => ?_)
  obtain ⟨⟨hnn, hsum⟩, hcap⟩ := μ.2
  have hCne : (Finset.univ : Finset {c // c ∈ C}).Nonempty := by
    have : 0 < C.card := by omega
    obtain ⟨c, hc⟩ := Finset.card_pos.1 this
    exact ⟨⟨c, hc⟩, Finset.mem_univ _⟩
  obtain ⟨c1, -, hc1⟩ := Finset.exists_max_image Finset.univ μ.1 hCne
  have hcard_sub : Fintype.card {c // c ∈ C} = C.card := Fintype.card_coe C
  have herase_ne : (Finset.univ.erase c1).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      hcard_sub]; omega
  have hrest : 1 - μ.1 c1 = ∑ c ∈ Finset.univ.erase c1, μ.1 c := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ c1)]; ring
  have hle : ∑ c ∈ Finset.univ.erase c1, δ ≤ ∑ c ∈ Finset.univ.erase c1, μ.1 c := by
    rw [← hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      hcard_sub, nsmul_eq_mul]
    have := hcap c1
    have hc1' : ((C.card - 1 : ℕ) : ℝ) ≤ C.card := by exact_mod_cast Nat.sub_le _ _
    calc ((C.card - 1 : ℕ) : ℝ) * δ ≤ C.card * δ := mul_le_mul_of_nonneg_right hc1' hδpos.le
      _ = 1 / 2 := by rw [hδ]; field_simp
      _ ≤ 1 - μ.1 c1 := by linarith
  obtain ⟨c2, hc2mem, hc2⟩ := Finset.exists_le_of_sum_le herase_ne hle
  have hc12 : c2 ≠ c1 := Finset.ne_of_mem_erase hc2mem
  have hval : c2.1 ≠ c1.1 := fun h => hc12 (Subtype.ext h)
  obtain ⟨i, hi⟩ : ∃ i, c2.1 i ≠ c1.1 i := by
    by_contra hcon; push Not at hcon; exact hval (funext hcon)
  have hμc1 : μ.1 c2 ≤ μ.1 c1 := hc1 c2 (Finset.mem_univ _)
  have hmass : ∀ b, δ ≤ massAt μ.1 i b := by
    intro b
    unfold massAt
    by_cases hb : c1.1 i = b
    · have hm : c1 ∈ Finset.univ.filter (fun c : {c // c ∈ C} => c.1 i = b) := by simp [hb]
      have := Finset.single_le_sum (f := μ.1) (fun c _ => hnn c) hm
      linarith
    · have hb2 : c2.1 i = b := by
        cases h1 : c1.1 i <;> cases h2' : c2.1 i <;> cases b <;> simp_all
      have hm : c2 ∈ Finset.univ.filter (fun c : {c // c ∈ C} => c.1 i = b) := by simp [hb2]
      have := Finset.single_le_sum (f := μ.1) (fun c _ => hnn c) hm
      linarith
  unfold splitObjective
  have hbdd : BddAbove (Set.range fun j : ι => min (massAt μ.1 j false) (massAt μ.1 j true)) :=
    (Set.finite_range _).bddAbove
  exact (le_min (hmass false) (hmass true)).trans (le_ciSup hbdd i)

theorem solution (ι : Type) [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool)) :
    1 / gammaParam C ≤ 1 / fGamma C := by
  by_cases h2 : 2 ≤ C.card
  · have hpos := ELS46_fGamma_pos C h2
    have hne : Nonempty {C' : Finset (ι → Bool) // C' ⊆ C ∧ 2 ≤ C'.card} :=
      ⟨⟨C, subset_refl _, h2⟩⟩
    have hle : fGamma C ≤ gammaParam C := by
      unfold gammaParam
      exact le_ciInf (fun C' => ELS46_fGamma_le C C'.1 C'.2.1 C'.2.2)
    exact one_div_le_one_div_of_le hpos hle
  · have hemp : IsEmpty {C' : Finset (ι → Bool) // C' ⊆ C ∧ 2 ≤ C'.card} :=
      ⟨fun C' => h2 (C'.2.2.trans (Finset.card_le_card C'.2.1))⟩
    have : gammaParam C = 0 := by unfold gammaParam; exact Real.iInf_of_isEmpty _
    rw [this, div_zero]
    exact one_div_nonneg.2 (ELS46_fGamma_nonneg C)
