-- Prove2me | solution 1 for FairGuarantees.DivideChoose.lemma_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:03:19.738686+00:00
-- url     : https://prove2.me/submissions/648ae869-7c1b-4949-be73-48c436c4a8f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Theorems.Thm_FairGuarantees_DivideChoose_theorem_of_4

open FairGuarantees.DivideChoose MeasureTheory

namespace DCL1

variable {d : ℕ}

theorem hyp_null (i0 : Fin d) (s : ℝ) : volume {x : E d | x i0 = s} = 0 := by
  have h := (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (s := Set.pi Set.univ (fun j => if j = i0 then ({s} : Set ℝ) else Set.univ))
    (MeasurableSet.univ_pi (fun j => by split_ifs <;> simp)).nullMeasurableSet
  have e : {x : E d | x i0 = s} = (WithLp.ofLp) ⁻¹'
      Set.pi Set.univ (fun j => if j = i0 then ({s} : Set ℝ) else Set.univ) := by
    ext x; simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx j; split_ifs with hj
      · subst hj; simpa using hx
      · trivial
    · intro hx; simpa using hx i0
  rw [e, h, volume_pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i0) (by simp)

theorem cont_coord (i0 : Fin d) : Continuous (fun x : E d => x i0) := by
  fun_prop

/-- The moving knife: the part of `S` whose `i0`-coordinate is at most `-R + 2 R t`. -/
def K (S : Set (E d)) (i0 : Fin d) (R t : ℝ) : Set (E d) := S ∩ {x | x i0 ≤ -R + 2 * R * t}

theorem K_mono {S : Set (E d)} {i0 : Fin d} {R : ℝ} (hR : 0 < R) {t t' : ℝ} (h : t ≤ t') :
    K S i0 R t ⊆ K S i0 R t' := by
  intro x ⟨hx1, hx2⟩
  refine ⟨hx1, ?_⟩
  simp only [Set.mem_ofPred_eq] at hx2 ⊢
  nlinarith

theorem K_meas {S : Set (E d)} (hS : MeasurableSet S) (i0 : Fin d) (R t : ℝ) :
    MeasurableSet (K S i0 R t) :=
  hS.inter (measurableSet_le (cont_coord i0).measurable measurable_const)

theorem slab_small {S : Set (E d)} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤) (i0 : Fin d)
    (s : ℝ) (ε : ENNReal) (hε : 0 < ε) :
    ∃ r > 0, volume (S ∩ {x | |x i0 - s| ≤ r}) < ε := by
  let A : ℕ → Set (E d) := fun k => S ∩ {x | |x i0 - s| ≤ 1 / ((k : ℝ) + 1)}
  have hmeas : ∀ k, NullMeasurableSet (A k) volume := fun k =>
    (hS.inter (measurableSet_le ((cont_coord i0).sub continuous_const).abs.measurable
      measurable_const)).nullMeasurableSet
  have hanti : Antitone A := by
    intro k l hkl x ⟨hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    simp only [Set.mem_ofPred_eq] at hx2 ⊢
    refine hx2.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  have hfin' : ∃ k, volume (A k) ≠ ⊤ := ⟨0, ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)⟩
  have ht := tendsto_measure_iInter_atTop hmeas hanti hfin'
  have hI : volume (⋂ k, A k) = 0 := by
    apply measure_mono_null _ (hyp_null i0 s)
    intro x hx
    simp only [Set.mem_iInter] at hx
    simp only [Set.mem_ofPred_eq]
    by_contra hne
    have hpos : 0 < |x i0 - s| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    have := (hx k).2
    simp only [Set.mem_ofPred_eq] at this
    linarith
  rw [hI] at ht
  obtain ⟨k, hk⟩ := ((tendsto_order.1 ht).2 ε hε).exists
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

theorem symmDiff_K_subset {S : Set (E d)} {i0 : Fin d} {R : ℝ} (hR : 0 < R) (t t' : ℝ) :
    symmDiff (K S i0 R t) (K S i0 R t') ⊆
      S ∩ {x | |x i0 - (-R + 2 * R * t)| ≤ 2 * R * |t' - t|} := by
  have h1 : R * (t - t') ≤ R * |t' - t| :=
    mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact le_abs_self _) hR.le
  have h2 : R * (t' - t) ≤ R * |t' - t| := mul_le_mul_of_nonneg_left (le_abs_self _) hR.le
  intro x hx
  rcases hx with ⟨⟨hxS, hx1⟩, hx2⟩ | ⟨⟨hxS, hx1⟩, hx2⟩
  · refine ⟨hxS, ?_⟩
    simp only [K, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and, not_le] at hx1 hx2 ⊢
    have := hx2 hxS
    rw [abs_le]; constructor <;> nlinarith
  · refine ⟨hxS, ?_⟩
    simp only [K, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and, not_le] at hx1 hx2 ⊢
    have := hx2 hxS
    rw [abs_le]; constructor <;> nlinarith

theorem knife_cont {S : Set (E d)} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤) (i0 : Fin d)
    {R : ℝ} (hR : 0 < R) (t : ℝ) (ε : ENNReal) (hε : 0 < ε) :
    ∃ ρ > 0, ∀ t', |t' - t| < ρ → volume (symmDiff (K S i0 R t) (K S i0 R t')) < ε := by
  obtain ⟨r, hr, hsmall⟩ := slab_small hS hfin i0 (-R + 2 * R * t) ε hε
  refine ⟨r / (2 * R), by positivity, fun t' ht' => ?_⟩
  refine lt_of_le_of_lt (measure_mono ((symmDiff_K_subset hR t t').trans ?_)) hsmall
  intro x ⟨hx1, hx2⟩
  refine ⟨hx1, ?_⟩
  simp only [Set.mem_ofPred_eq] at hx2 ⊢
  have : 2 * R * |t' - t| < r := by
    rw [lt_div_iff₀ (by positivity)] at ht'; linarith
  linarith

theorem symmDiff_diff_subset (A B A' B' : Set (E d)) :
    symmDiff (B \ A) (B' \ A') ⊆ symmDiff A A' ∪ symmDiff B B' := by
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_union] at hx ⊢
  tauto

end DCL1

open DCL1

theorem solution {d n : ℕ} (hd : 0 < d) {Ω : Set (E d)} (hΩ : IsManna Ω)
    {u : Set (E d) → ℝ} (hu : IsUtility Ω u) {S : Set (E d)} (hS : IsShare Ω S) (hn : 0 < n) :
    ∃ P : Fin n → Set (E d), IsEquipartition Ω u S n P := by
  let i0 : Fin d := ⟨0, hd⟩
  have hSb : Bornology.IsBounded S := hΩ.2.1.subset hS.2
  have hfin : volume S ≠ ⊤ := (hSb.measure_lt_top).ne
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).mp hSb
  set R : ℝ := |C| + 1 with hRdef
  have hR : 0 < R := by positivity
  have hcoord : ∀ x ∈ S, |x i0| < R := by
    intro x hx
    have h1 : ‖x.ofLp i0‖ ≤ ‖x‖ := PiLp.norm_apply_le x i0
    have h2 := hC x hx
    rw [Real.norm_eq_abs] at h1
    have : C ≤ |C| := le_abs_self C
    change |x.ofLp i0| < R
    linarith
  let Kt : ℝ → Set (E d) := fun t => K S i0 R t
  have hK0 : Kt 0 = ∅ := by
    ext x; simp only [Kt, K, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and, not_le]
    intro hx; have := hcoord x hx; rw [abs_lt] at this; linarith
  have hK1 : Kt 1 = S := by
    ext x; simp only [Kt, K, Set.mem_inter_iff, Set.mem_ofPred_eq, and_iff_left_iff_imp]
    intro hx; have := hcoord x hx; rw [abs_lt] at this; linarith
  have hKs : ∀ t, IsShare Ω (Kt t) := fun t =>
    ⟨K_meas hS.1 i0 R t, Set.inter_subset_left.trans hS.2⟩
  have hDs : ∀ a b, IsShare Ω (Kt b \ Kt a) := fun a b =>
    ⟨(hKs b).1.diff (hKs a).1, Set.sdiff_subset.trans (hKs b).2⟩
  let f : ℝ → ℝ → ℝ := fun a b => u (Kt b \ Kt a)
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} := by
    rw [Metric.continuousOn_iff]
    intro p _ ε hε
    obtain ⟨η, hη, hcont⟩ := hu.2.2 _ (hDs p.1 p.2) ε hε
    have hη2 : (0 : ENNReal) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨ρ1, hρ1, h1⟩ := knife_cont hS.1 hfin i0 hR p.1 _ hη2
    obtain ⟨ρ2, hρ2, h2⟩ := knife_cont hS.1 hfin i0 hR p.2 _ hη2
    refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, fun q _ hq => ?_⟩
    rw [Prod.dist_eq] at hq
    have hq1 : |q.1 - p.1| < ρ1 := by
      have := le_max_left (dist q.1 p.1) (dist q.2 p.2)
      rw [Real.dist_eq] at this
      exact lt_of_le_of_lt this (lt_of_lt_of_le hq (min_le_left _ _))
    have hq2 : |q.2 - p.2| < ρ2 := by
      have := le_max_right (dist q.1 p.1) (dist q.2 p.2)
      rw [Real.dist_eq] at this
      exact lt_of_le_of_lt this (lt_of_lt_of_le hq (min_le_right _ _))
    have hvol : volume (symmDiff (Kt p.2 \ Kt p.1) (Kt q.2 \ Kt q.1)) < ENNReal.ofReal η := by
      calc volume (symmDiff (Kt p.2 \ Kt p.1) (Kt q.2 \ Kt q.1))
          ≤ volume (symmDiff (Kt p.1) (Kt q.1) ∪ symmDiff (Kt p.2) (Kt q.2)) :=
            measure_mono (symmDiff_diff_subset _ _ _ _)
        _ ≤ volume (symmDiff (Kt p.1) (Kt q.1)) + volume (symmDiff (Kt p.2) (Kt q.2)) :=
            measure_union_le _ _
        _ < ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
            ENNReal.add_lt_add (h1 q.1 hq1) (h2 q.2 hq2)
        _ = ENNReal.ofReal η := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    have hδ : δ (Kt p.2 \ Kt p.1) (Kt q.2 \ Kt q.1) < η :=
      ENNReal.toReal_lt_of_lt_ofReal hvol
    have := hcont _ (hDs q.1 q.2) hδ
    rw [Real.dist_eq]
    exact this
  have h0 : ∀ a ∈ Set.Icc (0 : ℝ) 1, f a a = 0 := by
    intro a _
    simp only [f, Set.sdiff_self]
    exact hu.1
  obtain ⟨x, hx0, hxn, hxm, hxeq⟩ :=
    FairGuarantees.DivideChoose.theorem_of_4 f hf h0 n hn
  refine ⟨fun k => Kt (x k.succ) \ Kt (x k.castSucc), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro k
    exact ⟨hDs _ _, Set.sdiff_subset.trans Set.inter_subset_left⟩
  · apply Set.Subset.antisymm
    · intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨k, hk⟩ := hy
      exact hk.1.1
    · classical
      intro y hy
      let J := Finset.univ.filter (fun j : Fin (n+1) => y ∈ Kt (x j))
      have hJ : J.Nonempty := ⟨Fin.last n, by simp [J, hxn, hK1, hy]⟩
      let j := J.min' hJ
      have hjJ : j ∈ J := J.min'_mem hJ
      have hj0 : j ≠ 0 := by
        intro h
        have : y ∈ Kt (x j) := (Finset.mem_filter.mp hjJ).2
        rw [h, hx0, hK0] at this
        exact this
      obtain ⟨k, hk⟩ := Fin.exists_succ_eq.mpr hj0
      simp only [Set.mem_iUnion]
      refine ⟨k, ?_, ?_⟩
      · rw [hk]; exact (Finset.mem_filter.mp hjJ).2
      · intro hmem
        have hcJ : k.castSucc ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
        have := J.min'_le _ hcJ
        have hlt : k.castSucc < k.succ := Fin.castSucc_lt_succ
        rw [hk] at hlt
        exact absurd this (not_le.mpr hlt)
  · have key : ∀ i j : Fin n, i < j →
        (Kt (x i.succ) \ Kt (x i.castSucc)) ∩ (Kt (x j.succ) \ Kt (x j.castSucc)) = ∅ := by
      intro i j hij
      apply Set.eq_empty_of_subset_empty
      intro y ⟨hy1, hy2⟩
      have hle : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hij
      exact hy2.2 (K_mono hR (hxm hle) hy1.1)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · rw [key i j h]; simp
    · rw [Set.inter_comm, key j i h]; simp
  · intro i j
    exact hxeq i j
