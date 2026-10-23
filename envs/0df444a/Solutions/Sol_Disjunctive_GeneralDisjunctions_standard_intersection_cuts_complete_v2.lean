-- Prove2me | solution 1 for Disjunctive.GeneralDisjunctions.standard_intersection_cuts_complete_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T10:35:04.050971+00:00
-- url     : https://prove2.me/submissions/3939f876-4258-492a-9211-11a48667deac

import Theorems.Thm_Disjunctive_GeneralDisjunctions_rational_valid_cut_has_dual_feasible_tableau

open Disjunctive.GeneralDisjunctions

private theorem sicCoef_halfspace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (abar : ι → ι → ℝ) (v phi : ι → ℝ) (phi0 : ℝ) (j : ι)
    (hv : dotProduct phi v < phi0) (hs : 0 ≤ dotProduct phi (extremeRay I abar j)) :
    sicCoef {x | dotProduct phi x ≤ phi0} I abar v j =
      dotProduct phi (extremeRay I abar j) / (phi0 - dotProduct phi v) := by
  classical
  let d := phi0 - dotProduct phi v
  let s := dotProduct phi (extremeRay I abar j)
  have hd : 0 < d := sub_pos.mpr hv
  have heq : {t : ℝ | 0 ≤ t ∧ v + t • extremeRay I abar j ∈ {x | dotProduct phi x ≤ phi0}} =
      {t : ℝ | 0 ≤ t ∧ t * s ≤ d} := by
    ext t
    simp only [Set.mem_ofPred_eq, dotProduct_add, dotProduct_smul]
    dsimp [d, s]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> first | exact h1 | linarith
  unfold sicCoef
  rw [heq]
  by_cases hz : s = 0
  · have hset : {t : ℝ | 0 ≤ t ∧ t * s ≤ d} = Set.Ici 0 := by
      ext t
      simp [hz, le_of_lt hd]
    rw [hset, if_neg (not_bddAbove_Ici (a := (0 : ℝ)))]
    change 0 = s / d
    simp [hz]
  · have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    have hg : IsGreatest {t : ℝ | 0 ≤ t ∧ t * s ≤ d} (d / s) := by
      refine ⟨⟨le_of_lt (div_pos hd hs'), ?_⟩, ?_⟩
      · exact le_of_eq (div_mul_cancel₀ d hz)
      · intro t ht
        exact (le_div_iff₀ hs').mpr ht.2
    rw [if_pos hg.bddAbove, hg.csSup_eq]
    change (d / s)⁻¹ = s / d
    exact inv_div d s

private theorem tableau_representation {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (I J : Finset ι) (abar : ι → ι → ℝ)
    (v x : ι → ℝ) (htab : IsTableau A b I J abar v) (hx : A.mulVec x = b) :
    x = v + ∑ j ∈ J, x j • extremeRay I abar j := by
  classical
  rcases htab with ⟨hdisj, hcover, hv, heq⟩
  funext k
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k ∈ J
  · have hki : k ∉ I := fun hi => Finset.disjoint_left.mp hdisj hi hk
    simp [extremeRay, hki, hv k hk, hk]
  · have hki : k ∈ I := by
      have : k ∈ I ∪ J := by rw [hcover]; exact Finset.mem_univ k
      simpa [hk] using this
    have hterm : ∀ j ∈ J, x j * extremeRay I abar j k = -(abar k j * x j) := by
      intro j hj
      have hkj : k ≠ j := by intro h; exact hk (h ▸ hj)
      simp [extremeRay, hkj, hki, mul_comm]
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    exact (heq x).mp hx k hki

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (hrat : IsRationalData A b) (Nprime : Finset ι)
    (phi : ι → ℝ) (phi0 : ℝ)
    (hvalid : ∀ x ∈ MixedIntegerSet A b Nprime, phi0 ≤ dotProduct phi x)
    (hfacet : IsFacet (convexHull ℝ (MixedIntegerSet A b Nprime))
      {x ∈ convexHull ℝ (MixedIntegerSet A b Nprime) | dotProduct phi x = phi0})
    (hcutoff : ∃ v ∈ Set.extremePoints ℝ (LPFeasible A b), dotProduct phi v < phi0) :
    ∃ (I J : Finset ι) (abar : ι → ι → ℝ) (v : ι → ℝ),
      IsBasicFeasibleSolution A b I J abar v ∧ dotProduct phi v < phi0 ∧
      PIFree {x | dotProduct phi x ≤ phi0} (MixedIntegerSet A b Nprime) v ∧
      SICSet {x | dotProduct phi x ≤ phi0} I J abar v ∩ {x | A.mulVec x = b} =
        {x | phi0 ≤ dotProduct phi x} ∩ {x | A.mulVec x = b}  := by
  classical
  have hne : (MixedIntegerSet A b Nprime).Nonempty := by
    by_contra h
    have hempty : MixedIntegerSet A b Nprime = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simpa [hempty] using hfacet.2.1
  obtain ⟨I, J, abar, v, hbfs, hv, hcost⟩ :=
    rational_valid_cut_has_dual_feasible_tableau A b hrat Nprime phi phi0 hne hvalid
      (by obtain ⟨v, hv, hcut⟩ := hcutoff; exact ⟨v, hv.1, hcut⟩)
  refine ⟨I, J, abar, v, hbfs, hv, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact convex_halfSpace_le ⟨dotProduct_add phi,
        fun a x => by simp [dotProduct_smul]⟩ phi0
    · have hopen : IsOpen {x : ι → ℝ | dotProduct phi x < phi0} :=
        isOpen_lt (by fun_prop) continuous_const
      have hsub : {x : ι → ℝ | dotProduct phi x < phi0} ⊆
          {x | dotProduct phi x ≤ phi0} := by
        intro y hy
        exact show dotProduct phi y ≤ phi0 from le_of_lt hy
      exact (interior_maximal hsub hopen) hv
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxPI⟩
      have hphi : phi ≠ 0 := by
        intro hzero
        obtain ⟨z, hz⟩ := hne
        have := hvalid z hz
        simp [hzero] at hv this
        linarith
      let l : (ι → ℝ) →L[ℝ] ℝ := ∑ i, phi i • ContinuousLinearMap.proj i
      have hl (y : ι → ℝ) : l y = dotProduct phi y := by
        simp [l, dotProduct]
      have hsurj : Function.Surjective l := by
        have hi : ∃ i, phi i ≠ 0 := by
          by_contra hi
          push Not at hi
          exact hphi (funext hi)
        obtain ⟨i, hi⟩ := hi
        intro t
        refine ⟨Pi.single i (t / phi i), ?_⟩
        rw [hl]
        simp [dotProduct, Pi.single_apply]
        field_simp
      have hboundary : interior {x | dotProduct phi x ≤ phi0} = {x | dotProduct phi x < phi0} := by
        simpa only [Set.preimage, hl, interior_Iic, Set.mem_Iio, Set.mem_Iic] using
          ((l.isOpenMap hsurj).preimage_interior_eq_interior_preimage l.continuous (Set.Iic phi0)).symm
      rw [hboundary] at hx
      exact (not_lt_of_ge (hvalid x hxPI)) hx
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    by_cases hx : A.mulVec x = b
    · simp only [hx, and_true]
      have hrepr := tableau_representation A b I J abar v x hbfs.1 hx
      have hdot : dotProduct phi x = dotProduct phi v +
          ∑ j ∈ J, x j * dotProduct phi (extremeRay I abar j) := by
        conv_lhs => rw [hrepr]
        simp only [dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]
      have hcoeff : (∑ j ∈ J, sicCoef {x | dotProduct phi x ≤ phi0} I abar v j * x j) =
          (∑ j ∈ J, x j * dotProduct phi (extremeRay I abar j)) /
            (phi0 - dotProduct phi v) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        rw [sicCoef_halfspace I abar v phi phi0 j hv (hcost j hj)]
        ring
      change 1 ≤ (∑ j ∈ J, sicCoef {x | dotProduct phi x ≤ phi0} I abar v j * x j) ↔ _
      rw [hcoeff, le_div_iff₀ (sub_pos.mpr hv)]
      rw [hdot]
      constructor <;> intro h <;> linarith
    · simp [hx]


