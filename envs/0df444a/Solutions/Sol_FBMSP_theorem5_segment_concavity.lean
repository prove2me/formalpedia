-- Prove2me | solution 1 for FBMSP.theorem5_segment_concavity
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:36:49.917102+00:00
-- url     : https://prove2.me/submissions/2aacb621-3efd-4914-877c-fe0651fd795b

import Theorems.Thm_FBMSP_singlePrice_attains

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace FBMSP

private lemma rb_menu_nonneg (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) :
    0 ≤ menuAt η x P := by
  classical
  unfold menuAt
  split_ifs <;> simp_all only [le_max_iff, le_refl, true_or]

private lemma rb_menu_le (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (b : ℝ)
    (hb : 0 ≤ b) (h : ∀ p ∈ P, postedRevenue η x p ≤ b) : menuAt η x P ≤ b := by
  classical
  unfold menuAt
  split_ifs with hP
  · exact max_le hb (Finset.sup'_le _ _ h)
  · exact hb

private lemma rb_le_menu (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (p : ℝ)
    (hp : p ∈ P) : postedRevenue η x p ≤ menuAt η x P := by
  classical
  have hP : P.Nonempty := ⟨p, hp⟩
  rw [menuAt, dif_pos hP]
  exact (Finset.le_sup' (fun q => postedRevenue η x q) hp).trans (le_max_right _ _)

private lemma rb_menu_mono (η : Measure ℝ) (x : ℝ) : Monotone (menuAt η x) := by
  intro A B hAB
  exact rb_menu_le η x A _ (rb_menu_nonneg η x B) (fun p hp => rb_le_menu η x B p (hAB hp))

private lemma rb_menu_insert (η : Measure ℝ) (x p : ℝ) (P : Finset ℝ) :
    menuAt η x (insert p P) = max (menuAt η x P) (postedRevenue η x p) := by
  classical
  apply le_antisymm
  · apply rb_menu_le η x _ _ ((rb_menu_nonneg η x P).trans (le_max_left _ _))
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact le_max_right _ _
    · exact (rb_le_menu η x P q hq).trans (le_max_left _ _)
  · exact max_le (rb_menu_mono η x (Finset.subset_insert p P))
      (rb_le_menu η x _ p (Finset.mem_insert_self p P))

private lemma rb_menu_union (η : Measure ℝ) (x : ℝ) (A B : Finset ℝ) :
    menuAt η x (A ∪ B) = max (menuAt η x A) (menuAt η x B) := by
  classical
  apply le_antisymm
  · apply rb_menu_le η x _ _ ((rb_menu_nonneg η x A).trans (le_max_left _ _))
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (rb_le_menu η x A p hp).trans (le_max_left _ _)
    · exact (rb_le_menu η x B p hp).trans (le_max_right _ _)
  · exact max_le (rb_menu_mono η x Finset.subset_union_left)
      (rb_menu_mono η x Finset.subset_union_right)

private lemma rb_posted_integrable (ν η : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] (p : ℝ) :
    Integrable (fun x => postedRevenue η x p) ν := by
  have hs : Antitone (survival η) := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top η (Ici a))
      (measure_mono (Ici_subset_Ici.mpr hab))
  have hm : Measurable (fun x => postedRevenue η x p) :=
    measurable_const.mul (hs.measurable.comp (measurable_const.sub measurable_id))
  apply (integrable_const (|p| : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  have hS : survival η (p - x) ≤ 1 := measureReal_le_one
  have hS0 : 0 ≤ survival η (p - x) := ENNReal.toReal_nonneg
  simp only [postedRevenue, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hS0]
  simpa using mul_le_mul_of_nonneg_left hS (abs_nonneg p)

private lemma rb_menu_integrable (ν η : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] (P : Finset ℝ) :
    Integrable (fun x => menuAt η x P) ν := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa [menuAt] using (integrable_const (0 : ℝ) : Integrable (fun _ : ℝ => 0) ν)
  | @insert p P hp ih =>
    have h := ih.sup (rb_posted_integrable ν η p)
    change Integrable (fun x => max (menuAt η x P) (postedRevenue η x p)) ν at h
    simpa only [rb_menu_insert] using h

private lemma rb_survival_le_one (η : Measure ℝ) [IsProbabilityMeasure η] (t : ℝ) :
    survival η t ≤ 1 := by
  simpa only [survival, Measure.real] using (measureReal_le_one (μ := η) (s := Ici t))

private lemma rb_posted_mono (η : Measure ℝ) [IsProbabilityMeasure η] (p : ℝ)
    (hp : 0 ≤ p) : Monotone (fun x => postedRevenue η x p) := by
  intro x y hxy
  apply mul_le_mul_of_nonneg_left ?_ hp
  exact ENNReal.toReal_mono (measure_ne_top η (Ici (p - y)))
    (measure_mono (Ici_subset_Ici.mpr (sub_le_sub_left hxy p)))

private lemma rb_single_nonneg (η : Measure ℝ) (hη : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ singleRevenue η x := by
  obtain ⟨ha, hr⟩ := singlePrice_attains η hη x hx
  rw [← hr]
  exact mul_nonneg ha.1.1 ENNReal.toReal_nonneg

private lemma rb_single_mono (η : Measure ℝ) (hη : ValidNoise η) :
    Monotone (fun x : ℝ => singleRevenue η (max x 0)) := by
  letI : IsProbabilityMeasure η := hη.1
  intro x y hxy
  change singleRevenue η (max x 0) ≤ singleRevenue η (max y 0)
  obtain ⟨ha, hr⟩ := singlePrice_attains η hη (max x 0) (le_max_right x 0)
  obtain ⟨hb, hs⟩ := singlePrice_attains η hη (max y 0) (le_max_right y 0)
  rw [← hr, ← hs]
  exact (rb_posted_mono η (singlePrice η (max x 0)) ha.1.1
    (max_le_max hxy le_rfl)).trans (hb.1.2 _ ha.1.1)

private lemma rb_margin_value (η : Measure ℝ) (hη : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) :
    singleRevenue η x = (x + margin η x) * survival η (margin η x) := by
  rw [← (singlePrice_attains η hη x hx).2]
  unfold postedRevenue margin
  ring

private lemma rb_affine_le (η : Measure ℝ) (hη : ValidNoise η)
    (x θ : ℝ) (hx : 0 ≤ x) :
    (x + θ) * survival η θ ≤ singleRevenue η x := by
  by_cases hprice : 0 ≤ x + θ
  · have h := (singlePrice_attains η hη x hx).1.1.2 (x + θ) hprice
    rw [(singlePrice_attains η hη x hx).2] at h
    simpa only [postedRevenue, add_sub_cancel_left] using h
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hprice)
      ENNReal.toReal_nonneg).trans (rb_single_nonneg η hη x hx)

private lemma rb_single_difference (η : Measure ℝ) (hη : ValidNoise η)
    (x y : ℝ) (hy : 0 ≤ y) (hxy : y ≤ x) :
    singleRevenue η x - singleRevenue η y ≤ x - y := by
  letI : IsProbabilityMeasure η := hη.1
  have hx : 0 ≤ x := hy.trans hxy
  have hval := rb_margin_value η hη x hx
  have hlow := rb_affine_le η hη y (margin η x) hy
  have hS := mul_le_mul_of_nonneg_right (rb_survival_le_one η (margin η x))
    (sub_nonneg.mpr hxy)
  nlinarith only [hval, hlow, hS]

private lemma rb_single_le_base (η : Measure ℝ) (hη : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) : singleRevenue η x ≤ x + singleRevenue η 0 := by
  have h := rb_single_difference η hη x 0 le_rfl hx
  linarith

private lemma rb_single_integrable (ν η : Measure ℝ) (hν : ValidPredictions ν)
    (hη : ValidNoise η) : Integrable (singleRevenue η) ν := by
  letI : IsProbabilityMeasure ν := hν.1
  have hmeas : AEStronglyMeasurable (singleRevenue η) ν := by
    apply (rb_single_mono η hη).measurable.aestronglyMeasurable.congr
    filter_upwards [hν.2.2] with x hx
    simp only [max_eq_left hx]
  apply (hν.2.1.add (integrable_const (singleRevenue η 0))).mono' hmeas
  filter_upwards [hν.2.2] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (rb_single_nonneg η hη x hx)]
  exact rb_single_le_base η hη x hx

private lemma rb_posted_le_single (η : Measure ℝ) (hη : ValidNoise η)
    (x p : ℝ) (hx : 0 ≤ x) : postedRevenue η x p ≤ singleRevenue η x := by
  have h := rb_affine_le η hη x (p - x) hx
  have heq : x + (p - x) = p := by ring
  simpa only [heq, postedRevenue] using h

private lemma rb_menu_le_single (η : Measure ℝ) (hη : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) (P : Finset ℝ) : menuAt η x P ≤ singleRevenue η x := by
  exact rb_menu_le η x P _ (rb_single_nonneg η hη x hx)
    (fun p _ => rb_posted_le_single η hη x p hx)

private lemma rb_menuRevenue_le_personalized (ν η : Measure ℝ) (hν : ValidPredictions ν)
    (hη : ValidNoise η) (P : Finset ℝ) :
    menuRevenue ν η P ≤ personalizedRevenue ν η := by
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure η := hη.1
  apply integral_mono_ae (rb_menu_integrable ν η P) (rb_single_integrable ν η hν hη)
  filter_upwards [hν.2.2] with x hx
  exact rb_menu_le_single η hη x hx P

private lemma rb_revenue_bddAbove (ν η : Measure ℝ) (hν : ValidPredictions ν)
    (hη : ValidNoise η) (k : ℕ) :
    BddAbove {r : ℝ | ∃ P : Finset ℝ, FeasibleMenu P k ∧ r = menuRevenue ν η P} := by
  refine ⟨personalizedRevenue ν η, ?_⟩
  rintro r ⟨P, _, rfl⟩
  exact rb_menuRevenue_le_personalized ν η hν hη P

private lemma rb_menuRevenue_le_optimal (ν η : Measure ℝ) (hν : ValidPredictions ν)
    (hη : ValidNoise η) {P : Finset ℝ} {k : ℕ} (hP : FeasibleMenu P k) :
    menuRevenue ν η P ≤ optimalRevenue ν η k := by
  exact le_csSup (rb_revenue_bddAbove ν η hν hη k) ⟨P, hP, rfl⟩

end FBMSP



open MeasureTheory Set FBMSP

private lemma menu_nonneg (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) :
    0 ≤ menuAt η x P := by
  classical
  unfold menuAt
  split_ifs <;> simp_all only [le_max_iff, le_refl, true_or]

private lemma menu_le (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (b : ℝ)
    (hb : 0 ≤ b) (h : ∀ p ∈ P, postedRevenue η x p ≤ b) : menuAt η x P ≤ b := by
  classical
  unfold menuAt
  split_ifs with hP
  · exact max_le hb (Finset.sup'_le _ _ h)
  · exact hb

private lemma le_menu (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (p : ℝ)
    (hp : p ∈ P) : postedRevenue η x p ≤ menuAt η x P := by
  classical
  have hP : P.Nonempty := ⟨p, hp⟩
  rw [menuAt, dif_pos hP]
  exact (Finset.le_sup' (fun q => postedRevenue η x q) hp).trans (le_max_right _ _)


private lemma seg_survival_antitone (η : Measure ℝ) [IsProbabilityMeasure η] :
    Antitone (survival η) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top η (Ici a))
    (measure_mono (Ici_subset_Ici.mpr hab))


/-- Log-concave survival makes price revenue quasiconcave, including zero tails. -/
private lemma seg_revenue_three_point (η : Measure ℝ) [IsProbabilityMeasure η]
    (hmhr : HasMHR η) (x a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    min (postedRevenue η x a) (postedRevenue η x c) ≤ postedRevenue η x b := by
  have hs0 (t : ℝ) : 0 ≤ survival η t := ENNReal.toReal_nonneg
  by_cases hm : min (postedRevenue η x a) (postedRevenue η x c) ≤ 0
  · exact hm.trans (mul_nonneg (ha.trans hab) (hs0 _))
  have hmpos := lt_of_not_ge hm
  have hrapos := (lt_min_iff.mp hmpos).1
  have hrcpos := (lt_min_iff.mp hmpos).2
  have hapos : 0 < a := pos_of_mul_pos_left hrapos (hs0 _)
  have hcpos : 0 < c := hapos.trans_le (hab.trans hbc)
  have hbpos : 0 < b := hapos.trans_le hab
  have hsa : 0 < survival η (a - x) := pos_of_mul_pos_right hrapos ha
  have hsc : 0 < survival η (c - x) :=
    pos_of_mul_pos_right hrcpos (le_of_lt hcpos)
  have hsb : 0 < survival η (b - x) :=
    hsc.trans_le (seg_survival_antitone η (sub_le_sub_right hbc x))
  by_cases hac : a = c
  · have hba : b = a := le_antisymm (hbc.trans hac.symm.le) hab
    simp [hac, hba]
  have hac' : a < c := lt_of_le_of_ne (hab.trans hbc) hac
  have hden : 0 < c - a := sub_pos.mpr hac'
  let u := (c - b) / (c - a)
  let v := (b - a) / (c - a)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hbc) hden.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hab) hden.le
  have huv : u + v = 1 := by
    dsimp [u, v]
    field_simp [ne_of_gt hden]
    <;> ring
  have hbary : u * a + v * c = b := by
    dsimp [u, v]
    field_simp [ne_of_gt hden]
    <;> ring
  have hshift : u * (a - x) + v * (c - x) = b - x := by
    calc
      u * (a - x) + v * (c - x) = (u * a + v * c) - (u + v) * x := by ring
      _ = b - x := by rw [hbary, huv, one_mul]
  have hlogP := strictConcaveOn_log_Ioi.concaveOn.2 hapos hcpos hu hv huv
  simp only [smul_eq_mul, hbary] at hlogP
  have hlogS := hmhr.2.2 hsa hsc hu hv huv
  simp only [smul_eq_mul, hshift] at hlogS
  have hlogRa : Real.log (postedRevenue η x a) =
      Real.log a + Real.log (survival η (a - x)) :=
    Real.log_mul (ne_of_gt hapos) (ne_of_gt hsa)
  have hlogRb : Real.log (postedRevenue η x b) =
      Real.log b + Real.log (survival η (b - x)) :=
    Real.log_mul (ne_of_gt hbpos) (ne_of_gt hsb)
  have hlogRc : Real.log (postedRevenue η x c) =
      Real.log c + Real.log (survival η (c - x)) :=
    Real.log_mul (ne_of_gt hcpos) (ne_of_gt hsc)
  have hlogR : u * Real.log (postedRevenue η x a) +
      v * Real.log (postedRevenue η x c) ≤ Real.log (postedRevenue η x b) := by
    rw [hlogRa, hlogRc, hlogRb]
    nlinarith only [hlogP, hlogS]
  have hma := Real.log_le_log hmpos (min_le_left (postedRevenue η x a) (postedRevenue η x c))
  have hmc := Real.log_le_log hmpos (min_le_right (postedRevenue η x a) (postedRevenue η x c))
  apply (Real.log_le_log_iff hmpos (mul_pos hbpos hsb)).mp
  calc
    Real.log (min (postedRevenue η x a) (postedRevenue η x c)) =
        u * Real.log (min (postedRevenue η x a) (postedRevenue η x c)) +
        v * Real.log (min (postedRevenue η x a) (postedRevenue η x c)) := by
          rw [← add_mul, huv, one_mul]
    _ ≤ u * Real.log (postedRevenue η x a) + v * Real.log (postedRevenue η x c) :=
      add_le_add (mul_le_mul_of_nonneg_left hma hu) (mul_le_mul_of_nonneg_left hmc hv)
    _ ≤ Real.log (postedRevenue η x b) := hlogR

private def evenIndex {n m : ℕ} (hn : n = 2 * m) (i : Fin m) : Fin n :=
  ⟨2 * i.val, by omega⟩

private def oddIndex {n m : ℕ} (hn : n = 2 * m) (i : Fin m) : Fin n :=
  ⟨2 * i.val + 1, by omega⟩

private def evenMenu {n m : ℕ} (hn : n = 2 * m) (r : Fin n → ℝ) : Finset ℝ :=
  Finset.univ.image (fun i => r (evenIndex hn i))

private def oddMenu {n m : ℕ} (hn : n = 2 * m) (r : Fin n → ℝ) : Finset ℝ :=
  Finset.univ.image (fun i => r (oddIndex hn i))

private theorem interleaving_pair {n m : ℕ} (hn : n = 2 * m)
    (η : Measure ℝ) [IsProbabilityMeasure η] (hMHR : HasMHR η)
    (r : Fin n → ℝ) (hr : Monotone r) (hr0 : ∀ i, 0 ≤ r i) (x : ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    postedRevenue η x (r i) + postedRevenue η x (r j) ≤
      menuAt η x (evenMenu hn r) + menuAt η x (oddMenu hn r) := by
  classical
  have he (a : Fin n) (ha : a.val % 2 = 0) :
      postedRevenue η x (r a) ≤ menuAt η x (evenMenu hn r) := by
    apply le_menu
    refine Finset.mem_image.mpr ⟨⟨a.val / 2, by omega⟩, Finset.mem_univ _, ?_⟩
    congr 1
    apply Fin.ext
    dsimp [evenIndex]
    omega
  have ho (a : Fin n) (ha : a.val % 2 ≠ 0) :
      postedRevenue η x (r a) ≤ menuAt η x (oddMenu hn r) := by
    apply le_menu
    refine Finset.mem_image.mpr ⟨⟨a.val / 2, by omega⟩, Finset.mem_univ _, ?_⟩
    congr 1
    apply Fin.ext
    dsimp [oddIndex]
    omega
  have hordered (a b : Fin n) (hab : a < b) :
      postedRevenue η x (r a) + postedRevenue η x (r b) ≤
        menuAt η x (evenMenu hn r) + menuAt η x (oddMenu hn r) := by
    by_cases hae : a.val % 2 = 0 <;> by_cases hbe : b.val % 2 = 0
    · let c : Fin n := ⟨a.val + 1, by omega⟩
      have hac : a ≤ c := by change a.val ≤ a.val + 1; omega
      have hcb : c ≤ b := by change a.val + 1 ≤ b.val; omega
      have hco : c.val % 2 ≠ 0 := by dsimp [c]; omega
      have hmid := seg_revenue_three_point η hMHR x (r a) (r c) (r b)
        (hr0 a) (hr hac) (hr hcb)
      have hmin := hmid.trans (ho c hco)
      have hmax := max_le (he a hae) (he b hbe)
      linarith [min_add_max (postedRevenue η x (r a)) (postedRevenue η x (r b))]
    · exact add_le_add (he a hae) (ho b hbe)
    · simpa only [add_comm] using add_le_add (he b hbe) (ho a hae)
    · let c : Fin n := ⟨a.val + 1, by omega⟩
      have hac : a ≤ c := by change a.val ≤ a.val + 1; omega
      have hcb : c ≤ b := by change a.val + 1 ≤ b.val; omega
      have hce : c.val % 2 = 0 := by dsimp [c]; omega
      have hmid := seg_revenue_three_point η hMHR x (r a) (r c) (r b)
        (hr0 a) (hr hac) (hr hcb)
      have hmin := hmid.trans (he c hce)
      have hmax := max_le (ho a hae) (ho b hbe)
      linarith [min_add_max (postedRevenue η x (r a)) (postedRevenue η x (r b))]
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hordered i j hij
  · simpa only [add_comm] using hordered j i hji

private theorem pad_menu {n : ℕ} (hn : 0 < n) (P : Finset ℝ) (hP : FeasibleMenu P n)
    (η : Measure ℝ) :
    ∃ p : Fin n → ℝ, (∀ i, 0 ≤ p i) ∧
      ∀ x : ℝ, ∃ i : Fin n, menuAt η x P = postedRevenue η x (p i) := by
  classical
  let p : Fin n → ℝ := fun i => P.toList.getD i.val 0
  have hmem (i : Fin n) : p i ∈ P ∨ p i = 0 := by
    by_cases hi : i.val < P.toList.length
    · left
      dsimp [p]
      rw [List.getD_eq_getElem _ _ hi]
      exact Finset.mem_toList.mp (List.getElem_mem hi)
    · right
      exact List.getD_eq_default _ _ (Nat.le_of_not_lt hi)
  have hcover (q : ℝ) (hq : q ∈ P) : ∃ i : Fin n, p i = q := by
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hq)
    have hin : i < n := by
      have hlen := Finset.length_toList P
      have hcard := hP.1
      omega
    refine ⟨⟨i, hin⟩, ?_⟩
    simpa only [p, List.getD_eq_getElem _ _ hi] using heq
  have hp0 (i : Fin n) : 0 ≤ p i := by
    rcases hmem i with h | h
    · exact hP.2 _ h
    · simp [h]
  refine ⟨p, hp0, ?_⟩
  intro x
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => postedRevenue η x (p j)) huniv
  refine ⟨i, le_antisymm ?_ ?_⟩
  · apply menu_le η x P _ (mul_nonneg (hp0 i) ENNReal.toReal_nonneg)
    intro q hq
    obtain ⟨j, rfl⟩ := hcover q hq
    exact hmax j (Finset.mem_univ _)
  · rcases hmem i with h | h
    · exact le_menu η x P (p i) h
    · simpa [postedRevenue, h] using menu_nonneg η x P

private theorem balanced_menus {k : ℕ} (hk : 1 ≤ k) (η : Measure ℝ)
    [IsProbabilityMeasure η] (hMHR : HasMHR η)
    (P Q : Finset ℝ) (hP : FeasibleMenu P k) (hQ : FeasibleMenu Q (k + 2)) :
    ∃ A B : Finset ℝ, FeasibleMenu A (k + 1) ∧ FeasibleMenu B (k + 1) ∧
      ∀ x : ℝ, menuAt η x P + menuAt η x Q ≤ menuAt η x A + menuAt η x B := by
  classical
  obtain ⟨p, hp, hpmax⟩ := pad_menu (by omega : 0 < k) P hP η
  obtain ⟨q, hq, hqmax⟩ := pad_menu (by omega : 0 < k + 2) Q hQ η
  let w : Fin (k + (k + 2)) → ℝ := Fin.addCases p q
  let σ : Equiv.Perm (Fin (k + (k + 2))) := Tuple.sort w
  let r : Fin (k + (k + 2)) → ℝ := w ∘ σ
  have hsort : Monotone r := Tuple.monotone_sort w
  have hw (i : Fin (k + (k + 2))) : 0 ≤ w i := by
    exact Fin.addCases (fun j => by simpa [w] using hp j)
      (fun j => by simpa [w] using hq j) i
  have hr0 (i : Fin (k + (k + 2))) : 0 ≤ r i := hw (σ i)
  have hn : k + (k + 2) = 2 * (k + 1) := by omega
  let A := evenMenu hn r
  let B := oddMenu hn r
  have hA : FeasibleMenu A (k + 1) := by
    refine ⟨?_, ?_⟩
    · exact (Finset.card_image_le).trans (by simp)
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hr0 _
  have hB : FeasibleMenu B (k + 1) := by
    refine ⟨?_, ?_⟩
    · exact (Finset.card_image_le).trans (by simp)
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hr0 _
  refine ⟨A, B, hA, hB, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hpmax x
  obtain ⟨j, hj⟩ := hqmax x
  have hne : σ.symm (Fin.castAdd (k + 2) i) ≠ σ.symm (Fin.natAdd k j) := by
    intro heq
    have hv := congrArg Fin.val (σ.symm.injective heq)
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hv
    omega
  have h := interleaving_pair hn η hMHR r hsort hr0 x _ _ hne
  rw [hi, hj]
  simpa [r, w, Function.comp_def, A, B] using h

theorem solution (ν η : MeasureTheory.Measure ℝ)
    (hν : ValidPredictions ν) (hη : ValidNoise η) (hMHR : HasMHR η)
    (k : ℕ) (hk : 1 ≤ k) :
    optimalRevenue ν η (k + 2) - optimalRevenue ν η (k + 1) ≤
      optimalRevenue ν η (k + 1) - optimalRevenue ν η k := by
  classical
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure η := hη.1
  have hnonempty (j : ℕ) :
      ({r : ℝ | ∃ P : Finset ℝ, FeasibleMenu P j ∧ r = menuRevenue ν η P} : Set ℝ).Nonempty := by
    refine ⟨0, ∅, ⟨by simp, by simp⟩, ?_⟩
    simp [menuRevenue, menuAt]
  have hpair (P Q : Finset ℝ) (hP : FeasibleMenu P k) (hQ : FeasibleMenu Q (k + 2)) :
      menuRevenue ν η P + menuRevenue ν η Q ≤ 2 * optimalRevenue ν η (k + 1) := by
    obtain ⟨A, B, hA, hB, hpoint⟩ := balanced_menus hk η hMHR P Q hP hQ
    have hint := integral_mono
      ((rb_menu_integrable ν η P).add (rb_menu_integrable ν η Q))
      ((rb_menu_integrable ν η A).add (rb_menu_integrable ν η B)) hpoint
    simp only [Pi.add_apply] at hint
    rw [integral_add (rb_menu_integrable ν η P) (rb_menu_integrable ν η Q),
      integral_add (rb_menu_integrable ν η A) (rb_menu_integrable ν η B)] at hint
    change menuRevenue ν η P + menuRevenue ν η Q ≤
      menuRevenue ν η A + menuRevenue ν η B at hint
    have hAopt := rb_menuRevenue_le_optimal ν η hν hη hA
    have hBopt := rb_menuRevenue_le_optimal ν η hν hη hB
    linarith
  have hQ (P : Finset ℝ) (hP : FeasibleMenu P k) :
      optimalRevenue ν η (k + 2) ≤ 2 * optimalRevenue ν η (k + 1) - menuRevenue ν η P := by
    refine csSup_le (hnonempty (k + 2)) ?_
    rintro r ⟨Q, hQ, rfl⟩
    linarith [hpair P Q hP hQ]
  have hP : optimalRevenue ν η k ≤
      2 * optimalRevenue ν η (k + 1) - optimalRevenue ν η (k + 2) := by
    refine csSup_le (hnonempty k) ?_
    rintro r ⟨P, hP, rfl⟩
    linarith [hQ P hP]
  linarith


