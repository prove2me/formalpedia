-- Prove2me | solution 1 for Disjunctive.GeneralDisjunctions.rational_valid_cut_has_dual_feasible_tableau
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:05:26.466417+00:00
-- url     : https://prove2.me/submissions/31f8ea47-5838-47b1-98d0-d18fa7192fea

import Definitions.Def_Disjunctive_GeneralDisjunctions_SIC
import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype


open Matrix Finset

set_option linter.unusedSectionVars false

namespace Disjunctive.GeneralDisjunctions

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- Column `j` of `A`. -/
def x8col (A : Matrix (Fin m) ι ℝ) (j : ι) : Fin m → ℝ := fun r => A r j

/-- Support of a vector. -/
noncomputable def x8supp (x : ι → ℝ) : Finset ι := univ.filter (fun j => x j ≠ 0)

lemma x8_mem_supp {x : ι → ℝ} {j : ι} : j ∈ x8supp x ↔ x j ≠ 0 := by
  simp [x8supp]

lemma x8_mulVec (A : Matrix (Fin m) ι ℝ) (x : ι → ℝ) : A *ᵥ x = ∑ j, x j • x8col A j := by
  ext r
  simp [Matrix.mulVec, dotProduct, x8col, Finset.sum_apply, mul_comm]

lemma x8_sum_supp (x : ι → ℝ) (f : ι → (Fin m → ℝ)) {S : Finset ι} (h : x8supp x ⊆ S) :
    ∑ j, x j • f j = ∑ j ∈ S, x j • f j := by
  refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
  intro j _ hj
  have : x j = 0 := by
    by_contra hne; exact hj (h (x8_mem_supp.mpr hne))
  simp [this]

lemma x8_shrink (x w : ι → ℝ) (hx : ∀ j, 0 ≤ x j) (hw : x8supp w ⊆ x8supp x)
    (hneg : ∃ j, w j < 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ j, 0 ≤ x j + t * w j) ∧ x8supp (x + t • w) ⊂ x8supp x := by
  set N := univ.filter (fun j => w j < 0) with hN
  have hNne : N.Nonempty := by
    obtain ⟨j, hj⟩ := hneg; exact ⟨j, by simp [hN, hj]⟩
  obtain ⟨j0, hj0N, hj0⟩ := Finset.exists_min_image N (fun j => x j / (-w j)) hNne
  have hw0 : w j0 < 0 := by simpa [hN] using hj0N
  have hx0 : 0 < x j0 := by
    have h1 : j0 ∈ x8supp x := hw (x8_mem_supp.mpr hw0.ne)
    exact lt_of_le_of_ne (hx j0) (Ne.symm (x8_mem_supp.mp h1))
  refine ⟨x j0 / (-w j0), div_pos hx0 (by linarith), ?_, ?_⟩
  · intro j
    by_cases hj : w j < 0
    · have := hj0 j (by simp [hN, hj])
      have hpos : 0 < -w j := by linarith
      rw [div_le_div_iff₀ (by linarith) hpos] at this
      have : x j0 / -w j0 * w j = -(x j0 * (-w j)) / (-w j0) := by field_simp
      rw [this, neg_div]
      have h2 : x j0 * -w j / -w j0 ≤ x j := by
        rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    · push_neg at hj
      have : 0 ≤ x j0 / -w j0 * w j :=
        mul_nonneg (div_nonneg hx0.le (by linarith)) hj
      linarith [hx j]
  · rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j0, x8_mem_supp.mpr hx0.ne', ?_⟩
      rw [x8_mem_supp]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, not_not]
      rw [div_neg, neg_mul, div_mul_cancel₀ _ hw0.ne]; ring
    · intro j hj
      rw [x8_mem_supp] at hj ⊢
      intro hxj
      apply hj
      have : w j = 0 := by
        by_contra hne; exact (x8_mem_supp.mp (hw (x8_mem_supp.mpr hne))) hxj
      simp [hxj, this]

lemma x8_dep (A : Matrix (Fin m) ι ℝ) (S : Finset ι)
    (h : ¬ LinearIndepOn ℝ (x8col A) (S : Set ι)) :
    ∃ w : ι → ℝ, w ≠ 0 ∧ x8supp w ⊆ S ∧ A *ᵥ w = 0 := by
  rw [linearIndepOn_finset_iff] at h
  push_neg at h
  obtain ⟨f, hf, i, hi, hfi⟩ := h
  refine ⟨fun j => if j ∈ S then f j else 0, ?_, ?_, ?_⟩
  · intro h0; apply hfi; have := congrFun h0 i; simpa [hi] using this
  · intro j hj; rw [x8_mem_supp] at hj; by_contra hjS; exact hj (by simp [hjS])
  · rw [x8_mulVec, x8_sum_supp _ _ (S := S)]
    · rw [← hf]; refine Finset.sum_congr rfl fun j hj => by simp [hj]
    · intro j hj; rw [x8_mem_supp] at hj; by_contra hjS; exact hj (by simp [hjS])

lemma x8_uniq (A : Matrix (Fin m) ι ℝ) (S : Finset ι) (hS : LinearIndepOn ℝ (x8col A) (S : Set ι))
    (x x' : ι → ℝ) (hx : x8supp x ⊆ S) (hx' : x8supp x' ⊆ S) (h : A *ᵥ x = A *ᵥ x') : x = x' := by
  rw [linearIndepOn_finset_iff] at hS
  have hsum : ∑ i ∈ S, (x - x') i • x8col A i = 0 := by
    rw [x8_mulVec, x8_mulVec, x8_sum_supp _ _ hx, x8_sum_supp _ _ hx'] at h
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have h2 := hS _ hsum
  funext j
  by_cases hj : j ∈ S
  · have := h2 j hj; simp only [Pi.sub_apply] at this; linarith
  · have h1 : x j = 0 := by by_contra hne; exact hj (hx (x8_mem_supp.mpr hne))
    have h1' : x' j = 0 := by by_contra hne; exact hj (hx' (x8_mem_supp.mpr hne))
    rw [h1, h1']

/-- Choice of a descent direction with a negative entry. -/
lemma x8_dir (A : Matrix (Fin m) ι ℝ) (φ : ι → ℝ)
    (hray : ∀ r : ι → ℝ, (∀ j, 0 ≤ r j) → A *ᵥ r = 0 → 0 ≤ φ ⬝ᵥ r)
    (w : ι → ℝ) (hw0 : w ≠ 0) (hAw : A *ᵥ w = 0) :
    ∃ w' : ι → ℝ, A *ᵥ w' = 0 ∧ x8supp w' ⊆ x8supp w ∧ φ ⬝ᵥ w' ≤ 0 ∧ ∃ j, w' j < 0 := by
  have hneg_supp : x8supp (-w) ⊆ x8supp w := by
    intro j hj; rw [x8_mem_supp] at hj ⊢; simpa using hj
  have hAnw : A *ᵥ (-w) = 0 := by rw [Matrix.mulVec_neg, hAw, neg_zero]
  by_cases h1 : φ ⬝ᵥ w ≤ 0
  · by_cases h2 : ∃ j, w j < 0
    · exact ⟨w, hAw, subset_refl _, h1, h2⟩
    · push_neg at h2
      have h3 := hray w h2 hAw
      refine ⟨-w, hAnw, hneg_supp, by rw [dotProduct_neg]; linarith, ?_⟩
      by_contra h4; push_neg at h4
      apply hw0; funext j; have := h4 j; have := h2 j; simp at *; linarith
  · push_neg at h1
    refine ⟨-w, hAnw, hneg_supp, by rw [dotProduct_neg]; linarith, ?_⟩
    by_contra h4; push_neg at h4
    have := hray (-w) h4 hAnw
    rw [dotProduct_neg] at this; linarith

/-- Reduction to a basic feasible solution (linearly independent support). -/
lemma x8_bfs (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (φ : ι → ℝ)
    (hray : ∀ r : ι → ℝ, (∀ j, 0 ≤ r j) → A *ᵥ r = 0 → 0 ≤ φ ⬝ᵥ r) :
    ∀ x ∈ LPFeasible A b, ∃ x' ∈ LPFeasible A b, φ ⬝ᵥ x' ≤ φ ⬝ᵥ x ∧
      x8supp x' ⊆ x8supp x ∧ LinearIndepOn ℝ (x8col A) (x8supp x' : Set ι) := by
  intro x hx
  induction hc : (x8supp x).card using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hind : LinearIndepOn ℝ (x8col A) (x8supp x : Set ι)
    · exact ⟨x, hx, le_refl _, subset_refl _, hind⟩
    obtain ⟨w, hw0, hws, hAw⟩ := x8_dep A _ hind
    obtain ⟨w', hAw', hw's, hφw', hneg⟩ := x8_dir A φ hray w hw0 hAw
    obtain ⟨t, ht, hnn, hss⟩ := x8_shrink x w' hx.2 (hw's.trans hws) hneg
    have hx2 : x + t • w' ∈ LPFeasible A b := by
      refine ⟨?_, fun j => by simpa using hnn j⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAw', smul_zero, add_zero, hx.1]
    obtain ⟨x', hx', h1, h2, h3⟩ :=
      ih _ (hc ▸ Finset.card_lt_card hss) (x + t • w') hx2 rfl
    refine ⟨x', hx', ?_, h2.trans hss.subset, h3⟩
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1
    nlinarith

end Disjunctive.GeneralDisjunctions


open Matrix Finset

set_option linter.unusedSectionVars false

namespace Disjunctive.GeneralDisjunctions

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- A rational matrix with dependent columns on `S` has a rational kernel vector supported on `S`. -/
lemma x8_ratker (A : Matrix (Fin m) ι ℝ) (hA : ∀ r j, ∃ q : ℚ, A r j = q) (S : Finset ι)
    (h : ¬ LinearIndepOn ℝ (x8col A) (S : Set ι)) :
    ∃ w : ι → ℝ, w ≠ 0 ∧ x8supp w ⊆ S ∧ A *ᵥ w = 0 ∧ ∀ j, ∃ q : ℚ, w j = q := by
  choose Aq hAq using hA
  let v : ↥(S : Set ι) → Fin m → ℚ := fun i r => Aq r i
  have hv : (fun i : ↥(S : Set ι) => x8col A i) = fun i => algebraMap ℚ ℝ ∘ v i := by
    funext i r; simp [v, x8col, hAq]
  have h2 : ¬ LinearIndependent ℚ v := by
    intro hli; apply h
    have := (linearIndependent_algebraMap_comp_iff (S := ℝ)).mpr hli
    unfold LinearIndepOn; rw [hv]; exact this
  rw [Fintype.not_linearIndependent_iff] at h2
  obtain ⟨g, hg, i0, hi0⟩ := h2
  refine ⟨fun j => if hj : j ∈ S then ((g ⟨j, by simpa using hj⟩ : ℚ) : ℝ) else 0, ?_, ?_, ?_, ?_⟩
  · intro h0
    have := congrFun h0 i0
    have hi0S : (i0 : ι) ∈ S := by simpa using i0.2
    simp only [hi0S, dite_true, Pi.zero_apply, Rat.cast_eq_zero] at this
    exact hi0 (by simpa using this)
  · intro j hj; rw [x8_mem_supp] at hj; by_contra hjS; exact hj (by simp [hjS])
  · ext r
    have := congrFun hg r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at this
    rw [Matrix.mulVec, dotProduct]
    simp only [Pi.zero_apply]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · have h3 : ∑ x ∈ S, A r x * (if hj : x ∈ S then ((g ⟨x, by simpa using hj⟩ : ℚ) : ℝ) else 0)
          = ∑ x : ↥(S : Set ι), ((g x * Aq r x : ℚ) : ℝ) := by
        rw [← Finset.sum_attach S]
        refine Fintype.sum_equiv (Equiv.subtypeEquivRight (fun x => by simp)) _ _ ?_
        intro x
        simp [hAq, mul_comm]
        left; rfl
      rw [h3, ← Rat.cast_sum, this, Rat.cast_zero]
    · intro j _ hj; simp [hj]
  · intro j
    by_cases hj : j ∈ S
    · exact ⟨g ⟨j, by simpa using hj⟩, by simp [hj]⟩
    · exact ⟨0, by simp [hj]⟩

/-- A rational vector has an integer multiple. -/
lemma x8_denom (g : ι → ℝ) (hg : ∀ j, ∃ q : ℚ, g j = q) :
    ∃ D : ℕ, 0 < D ∧ ∀ j, ∃ z : ℤ, (D : ℝ) * g j = z := by
  choose q hq using hg
  refine ⟨∏ i, (q i).den, Finset.prod_pos fun i _ => (q i).den_pos, fun j => ?_⟩
  refine ⟨(q j).num * ∏ i ∈ Finset.univ.erase j, ((q i).den : ℤ), ?_⟩
  rw [hq j, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have h1 : ((q j).den : ℝ) * (q j : ℝ) = (q j).num := by
    exact_mod_cast Rat.den_mul_eq_num (q j)
  push_cast
  calc ((q j).den : ℝ) * (∏ x ∈ Finset.univ.erase j, ((q x).den : ℝ)) * (q j : ℝ)
      = (((q j).den : ℝ) * (q j : ℝ)) * ∏ x ∈ Finset.univ.erase j, ((q x).den : ℝ) := by ring
    _ = _ := by rw [h1]

/-- Existence of a rational descent ray from a real one. -/
lemma x8_ratray (A : Matrix (Fin m) ι ℝ) (hA : ∀ r j, ∃ q : ℚ, A r j = q) (φ : ι → ℝ) :
    ∀ n, ∀ r : ι → ℝ, (x8supp r).card = n → (∀ j, 0 ≤ r j) → A *ᵥ r = 0 → φ ⬝ᵥ r < 0 →
      ∃ g : ι → ℝ, (∀ j, 0 ≤ g j) ∧ A *ᵥ g = 0 ∧ φ ⬝ᵥ g < 0 ∧ ∀ j, ∃ q : ℚ, g j = q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro r hc hr hAr hφr
  have hdep : ¬ LinearIndepOn ℝ (x8col A) (x8supp r : Set ι) := by
    intro hind
    have := x8_uniq A _ hind r 0 (subset_refl _) (by intro j hj; simp [x8_mem_supp] at hj)
      (by rw [hAr, Matrix.mulVec_zero])
    rw [this, dotProduct_zero] at hφr; exact lt_irrefl _ hφr
  obtain ⟨q, hq0, hqs, hAq, hqr⟩ := x8_ratker A hA _ hdep
  set c := φ ⬝ᵥ q / φ ⬝ᵥ r with hc_def
  set w := q - c • r with hw_def
  have hφw : φ ⬝ᵥ w = 0 := by
    rw [hw_def, dotProduct_sub, dotProduct_smul, smul_eq_mul, hc_def, div_mul_cancel₀ _ hφr.ne]
    ring
  have hAw : A *ᵥ w = 0 := by
    rw [hw_def, Matrix.mulVec_sub, Matrix.mulVec_smul, hAq, hAr, smul_zero, sub_zero]
  have hws : x8supp w ⊆ x8supp r := by
    intro j hj; rw [x8_mem_supp] at hj ⊢
    intro hrj; apply hj
    have : q j = 0 := by by_contra hne; exact (x8_mem_supp.mp (hqs (x8_mem_supp.mpr hne))) hrj
    simp [hw_def, this, hrj]
  by_cases hw0 : w = 0
  · have hqc : q = c • r := by rw [← sub_eq_zero]; exact hw0
    have hc0 : c ≠ 0 := by intro h; apply hq0; rw [hqc, h, zero_smul]
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · refine ⟨-q, fun j => ?_, by rw [Matrix.mulVec_neg, hAq, neg_zero], ?_, fun j => ?_⟩
      · rw [hqc]; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; nlinarith [hr j]
      · rw [dotProduct_neg, hqc, dotProduct_smul, smul_eq_mul]; nlinarith
      · obtain ⟨z, hz⟩ := hqr j; exact ⟨-z, by simp [hz]⟩
    · refine ⟨q, fun j => ?_, hAq, ?_, hqr⟩
      · rw [hqc]; simp only [Pi.smul_apply, smul_eq_mul]; nlinarith [hr j]
      · rw [hqc, dotProduct_smul, smul_eq_mul]; nlinarith
  · have hex : ∃ w' : ι → ℝ, A *ᵥ w' = 0 ∧ x8supp w' ⊆ x8supp r ∧ φ ⬝ᵥ w' = 0 ∧
        ∃ j, w' j < 0 := by
      by_cases hn : ∃ j, w j < 0
      · exact ⟨w, hAw, hws, hφw, hn⟩
      · push_neg at hn
        refine ⟨-w, by rw [Matrix.mulVec_neg, hAw, neg_zero], ?_, by rw [dotProduct_neg, hφw,
          neg_zero], ?_⟩
        · intro j hj; apply hws; rw [x8_mem_supp] at hj ⊢; simpa using hj
        · by_contra h4; push_neg at h4
          apply hw0; funext j; have := h4 j; have := hn j; simp at *; linarith
    obtain ⟨w', hAw', hw's, hφw', hneg⟩ := hex
    obtain ⟨t, ht, hnn, hss⟩ := x8_shrink r w' hr hw's hneg
    refine ih _ (hc ▸ Finset.card_lt_card hss) (r + t • w') rfl (fun j => by simpa using hnn j)
      ?_ ?_
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAw', hAr, smul_zero, add_zero]
    · rw [dotProduct_add, dotProduct_smul, hφw', smul_zero, add_zero]; exact hφr

/-- Validity on a nonempty rational mixed-integer set bounds `φ` on the recession cone. -/
lemma x8_hray (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (hrat : IsRationalData A b)
    (Nprime : Finset ι) (φ : ι → ℝ) (φ0 : ℝ) (hne : (MixedIntegerSet A b Nprime).Nonempty)
    (hvalid : ∀ x ∈ MixedIntegerSet A b Nprime, φ0 ≤ φ ⬝ᵥ x) :
    ∀ r : ι → ℝ, (∀ j, 0 ≤ r j) → A *ᵥ r = 0 → 0 ≤ φ ⬝ᵥ r := by
  intro r hr hAr
  by_contra hlt; push_neg at hlt
  obtain ⟨g, hg, hAg, hφg, hgq⟩ := x8_ratray A hrat.1 φ _ r rfl hr hAr hlt
  obtain ⟨D, hD, hDz⟩ := x8_denom g hgq
  obtain ⟨x0, ⟨hx0A, hx0n⟩, hx0I⟩ := hne
  have hmem : ∀ k : ℕ, x0 + ((k : ℝ) * D) • g ∈ MixedIntegerSet A b Nprime := by
    intro k
    refine ⟨⟨?_, fun j => ?_⟩, fun j hj => ?_⟩
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAg, smul_zero, add_zero, hx0A]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hx0n j; have := hg j; positivity
    · obtain ⟨z0, hz0⟩ := hx0I j hj
      obtain ⟨z, hz⟩ := hDz j
      refine ⟨z0 + k * z, ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [hz0, ← hz]; ring
  obtain ⟨k, hk⟩ := exists_nat_gt ((φ ⬝ᵥ x0 - φ0) / (-(D * (φ ⬝ᵥ g))))
  have h1 := hvalid _ (hmem k)
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hneg : 0 < -(D * (φ ⬝ᵥ g)) := by nlinarith
  rw [div_lt_iff₀ hneg] at hk
  nlinarith

end Disjunctive.GeneralDisjunctions


open Matrix Finset

set_option linter.unusedSectionVars false

namespace Disjunctive.GeneralDisjunctions

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- Reduced cost of column `j` for the dual vector `y`. -/
noncomputable def x8rc (A : Matrix (Fin m) ι ℝ) (φ : ι → ℝ) (y : Fin m → ℝ) (j : ι) : ℝ :=
  φ j - x8col A j ⬝ᵥ y

lemma x8_pair (A : Matrix (Fin m) ι ℝ) (x : ι → ℝ) (y : Fin m → ℝ) :
    ∑ j, x j * (x8col A j ⬝ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  simp only [Matrix.mulVec, dotProduct, x8col, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => by ring

lemma x8_split (A : Matrix (Fin m) ι ℝ) (φ : ι → ℝ) (y : Fin m → ℝ) (x : ι → ℝ) :
    φ ⬝ᵥ x = x8rc A φ y ⬝ᵥ x + (A *ᵥ x) ⬝ᵥ y := by
  rw [← x8_pair]
  simp only [dotProduct, x8rc, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- Strong duality via the affine Farkas lemma. -/
lemma x8_dual (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (φ : ι → ℝ) (xs : ι → ℝ)
    (hxs : xs ∈ LPFeasible A b) (hopt : ∀ x ∈ LPFeasible A b, φ ⬝ᵥ xs ≤ φ ⬝ᵥ x) :
    ∃ y : Fin m → ℝ, (∀ j, 0 ≤ x8rc A φ y j) ∧ φ ⬝ᵥ xs ≤ b ⬝ᵥ y := by
  set n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let M : Matrix (ι ⊕ (Fin m ⊕ Fin m)) (Fin n) ℝ := fun R k =>
    match R with
    | Sum.inl j => -(if e j = k then 1 else 0)
    | Sum.inr (Sum.inl r) => A r (e.symm k)
    | Sum.inr (Sum.inr r) => -A r (e.symm k)
  let bb : ι ⊕ (Fin m ⊕ Fin m) → ℝ := fun R =>
    match R with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl r) => b r
    | Sum.inr (Sum.inr r) => -b r
  let c : Fin n → ℝ := fun k => -φ (e.symm k)
  have hMz : ∀ z : Fin n → ℝ, ∀ R, (M *ᵥ z) R =
      match R with
      | Sum.inl j => -z (e j)
      | Sum.inr (Sum.inl r) => (A *ᵥ (z ∘ e)) r
      | Sum.inr (Sum.inr r) => -(A *ᵥ (z ∘ e)) r := by
    intro z R
    rcases R with j | r | r
    · change ∑ k, -(if e j = k then (1:ℝ) else 0) * z k = -z (e j)
      simp [ite_mul]
    · change ∑ k, A r (e.symm k) * z k = ∑ j, A r j * (z ∘ e) j
      exact Fintype.sum_equiv e.symm _ _ (fun k => by simp)
    · change ∑ k, -A r (e.symm k) * z k = -∑ j, A r j * (z ∘ e) j
      rw [← Finset.sum_neg_distrib]
      exact Fintype.sum_equiv e.symm _ _ (fun k => by simp)
  have hcz : ∀ z : Fin n → ℝ, c ⬝ᵥ z = -(φ ⬝ᵥ (z ∘ e)) := by
    intro z
    simp only [c, dotProduct, neg_mul, Finset.sum_neg_distrib, neg_inj]
    exact Fintype.sum_equiv e.symm _ _ (fun k => by simp)
  have hfeas : ∃ z : Fin n → ℝ, M *ᵥ z ≤ bb := by
    refine ⟨xs ∘ e.symm, fun R => ?_⟩
    have h1 : (xs ∘ e.symm) ∘ e = xs := by funext j; simp
    rw [hMz]
    rcases R with j | r | r
    · simp [bb, hxs.2 j]
    · simp [bb, h1, hxs.1]
    · simp [bb, h1, hxs.1]
  have hall : ∀ z : Fin n → ℝ, M *ᵥ z ≤ bb → c ⬝ᵥ z ≤ -(φ ⬝ᵥ xs) := by
    intro z hz
    have hP : z ∘ e ∈ LPFeasible A b := by
      refine ⟨?_, fun j => ?_⟩
      · funext r
        have h1 := hz (Sum.inr (Sum.inl r)); have h2 := hz (Sum.inr (Sum.inr r))
        rw [hMz] at h1 h2
        simp only [bb] at h1 h2
        linarith
      · have h1 := hz (Sum.inl j); rw [hMz] at h1; simp only [bb] at h1
        simp only [Function.comp_apply]; linarith
    rw [hcz]; linarith [hopt _ hP]
  obtain ⟨p, hp0, hpM, hpb⟩ :=
    (LinearOptimization.farkas_inequality_form_fintype M bb c _ hfeas).mp hall
  refine ⟨fun r => p (Sum.inr (Sum.inr r)) - p (Sum.inr (Sum.inl r)), fun j => ?_, ?_⟩
  · have h1 := congrFun hpM (e j)
    have h2 : (Mᵀ *ᵥ p) (e j) = -p (Sum.inl j) +
        ∑ r, A r j * (p (Sum.inr (Sum.inl r)) - p (Sum.inr (Sum.inr r))) := by
      change ∑ R, M R (e j) * p R = _
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      change ∑ i, -(if e i = e j then (1:ℝ) else 0) * p (Sum.inl i) +
        (∑ r, A r (e.symm (e j)) * p (Sum.inr (Sum.inl r)) +
          ∑ r, -A r (e.symm (e j)) * p (Sum.inr (Sum.inr r))) = _
      simp only [Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq, neg_mul, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib,
        mul_sub, Finset.sum_sub_distrib]
      ring
    rw [h2] at h1
    have h1' : -p (Sum.inl j) + ∑ r, A r j * (p (Sum.inr (Sum.inl r)) - p (Sum.inr (Sum.inr r)))
        = -φ j := by rw [h1]; simp [c]
    have h3 : 0 ≤ p (Sum.inl j) := hp0 _
    have h4 : x8col A j ⬝ᵥ (fun r => p (Sum.inr (Sum.inr r)) - p (Sum.inr (Sum.inl r))) =
        ∑ r, A r j * (p (Sum.inr (Sum.inr r)) - p (Sum.inr (Sum.inl r))) := rfl
    have h5 : ∑ r, A r j * (p (Sum.inr (Sum.inl r)) - p (Sum.inr (Sum.inr r))) =
        -∑ r, A r j * (p (Sum.inr (Sum.inr r)) - p (Sum.inr (Sum.inl r))) := by
      rw [← Finset.sum_neg_distrib]; congr 1; funext r; ring
    unfold x8rc; rw [h4]; rw [h5] at h1'; linarith
  · simp only [dotProduct, Fintype.sum_sum_type, bb, mul_zero, Finset.sum_const_zero,
      zero_add] at hpb
    simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
    simp only [mul_neg, Finset.sum_neg_distrib] at hpb
    have : ∑ r, b r * p (Sum.inr (Sum.inr r)) - ∑ r, b r * p (Sum.inr (Sum.inl r)) =
        -(∑ r, p (Sum.inr (Sum.inl r)) * b r + -∑ r, p (Sum.inr (Sum.inr r)) * b r) := by
      simp only [mul_comm (b _)]; ring
    rw [this]; linarith

/-- Complementary slackness. -/
lemma x8_cs (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (φ : ι → ℝ) (xs : ι → ℝ) (y : Fin m → ℝ)
    (hxs : xs ∈ LPFeasible A b) (hrc : ∀ j, 0 ≤ x8rc A φ y j) (hle : φ ⬝ᵥ xs ≤ b ⬝ᵥ y) :
    ∀ j ∈ x8supp xs, x8rc A φ y j = 0 := by
  have h1 := x8_split A φ y xs
  rw [hxs.1] at h1
  have h2 : x8rc A φ y ⬝ᵥ xs ≤ 0 := by linarith
  have h3 : ∀ j, 0 ≤ x8rc A φ y j * xs j := fun j => mul_nonneg (hrc j) (hxs.2 j)
  have h4 : ∀ j, x8rc A φ y j * xs j = 0 := by
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h3 j)).mp
      (le_antisymm (by simpa [dotProduct] using h2) (Finset.sum_nonneg fun j _ => h3 j)) j
      (Finset.mem_univ j)
    exact this
  intro j hj
  rcases mul_eq_zero.mp (h4 j) with h | h
  · exact h
  · exact absurd h (x8_mem_supp.mp hj)

/-- The set of columns with zero reduced cost. -/
noncomputable def x8Z (A : Matrix (Fin m) ι ℝ) (φ : ι → ℝ) (y : Fin m → ℝ) : Finset ι :=
  univ.filter (fun j => x8rc A φ y j = 0)

lemma x8_rc_add (A : Matrix (Fin m) ι ℝ) (φ : ι → ℝ) (y s : Fin m → ℝ) (t : ℝ) (j : ι) :
    x8rc A φ (y + t • s) j = x8rc A φ y j - t * (x8col A j ⬝ᵥ s) := by
  simp only [x8rc, dotProduct_add, dotProduct_smul, smul_eq_mul]; ring

/-- Enlarging the set of zero reduced costs until its columns span all columns. -/
lemma x8_enlarge (A : Matrix (Fin m) ι ℝ) (φ : ι → ℝ) (S0 : Finset ι) :
    ∀ n, ∀ y : Fin m → ℝ, (univ.filter (fun j => x8rc A φ y j ≠ 0)).card = n →
      (∀ j, 0 ≤ x8rc A φ y j) → (∀ j ∈ S0, x8rc A φ y j = 0) →
      ∃ y' : Fin m → ℝ, (∀ j, 0 ≤ x8rc A φ y' j) ∧ (∀ j ∈ S0, x8rc A φ y' j = 0) ∧
        ∀ k, x8col A k ∈ Submodule.span ℝ (x8col A '' (x8Z A φ y' : Set ι)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hc hrc hS0
  by_cases hall : ∀ k, x8col A k ∈ Submodule.span ℝ (x8col A '' (x8Z A φ y : Set ι))
  · exact ⟨y, hrc, hS0, hall⟩
  push_neg at hall
  obtain ⟨k0, hk0⟩ := hall
  obtain ⟨f, hfk, hfU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hk0 inferInstance
  have hfz : ∀ z ∈ x8Z A φ y, f (x8col A z) = 0 := by
    intro z hz
    have : f (x8col A z) ∈ Submodule.map f (Submodule.span ℝ (x8col A '' (x8Z A φ y : Set ι))) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨z, by simpa using hz, rfl⟩)
    rw [hfU] at this; simpa using this
  set u : Fin m → ℝ := fun r => f (fun j => if r = j then 1 else 0) with hu
  have hfu : ∀ v, f v = v ⬝ᵥ u := by
    intro v; rw [LinearMap.pi_apply_eq_sum_univ f v]; simp [dotProduct, hu]
  set s : Fin m → ℝ := if 0 < f (x8col A k0) then u else -u with hs
  have hsk0 : 0 < x8col A k0 ⬝ᵥ s := by
    rw [hs]; split_ifs with h
    · rw [← hfu]; exact h
    · rw [dotProduct_neg, ← hfu]
      rcases lt_or_gt_of_ne hfk with h' | h'
      · linarith
      · exact absurd h' h
  have hsz : ∀ z ∈ x8Z A φ y, x8col A z ⬝ᵥ s = 0 := by
    intro z hz; rw [hs]; split_ifs
    · rw [← hfu]; exact hfz z hz
    · rw [dotProduct_neg, ← hfu, hfz z hz, neg_zero]
  set K := univ.filter (fun k => 0 < x8col A k ⬝ᵥ s) with hK
  have hKne : K.Nonempty := ⟨k0, by simp [hK, hsk0]⟩
  have hKpos : ∀ k ∈ K, 0 < x8rc A φ y k := by
    intro k hk
    have hks : 0 < x8col A k ⬝ᵥ s := by simpa [hK] using hk
    rcases lt_or_eq_of_le (hrc k) with h | h
    · exact h
    · exact absurd (hsz k (by simp [x8Z, h.symm])) hks.ne'
  obtain ⟨ks, hksK, hks⟩ := Finset.exists_min_image K
    (fun k => x8rc A φ y k / (x8col A k ⬝ᵥ s)) hKne
  have hkss : 0 < x8col A ks ⬝ᵥ s := by simpa [hK] using hksK
  set t := x8rc A φ y ks / (x8col A ks ⬝ᵥ s) with ht
  have htpos : 0 < t := div_pos (hKpos ks hksK) hkss
  have hrc' : ∀ j, 0 ≤ x8rc A φ (y + t • s) j := by
    intro j
    rw [x8_rc_add]
    by_cases hj : 0 < x8col A j ⬝ᵥ s
    · have := hks j (by simp [hK, hj])
      rw [le_div_iff₀ hj] at this; linarith
    · push_neg at hj
      have := hrc j; nlinarith
  have hZsub : ∀ j, x8rc A φ y j = 0 → x8rc A φ (y + t • s) j = 0 := by
    intro j hj
    rw [x8_rc_add, hj, hsz j (by simp [x8Z, hj])]; ring
  have hks0 : x8rc A φ (y + t • s) ks = 0 := by
    rw [x8_rc_add, ht, div_mul_cancel₀ _ hkss.ne']; ring
  have hss : univ.filter (fun j => x8rc A φ (y + t • s) j ≠ 0) ⊂
      univ.filter (fun j => x8rc A φ y j ≠ 0) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨ks, by simp [(hKpos ks hksK).ne'], by simp [hks0]⟩
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      intro h0; exact hj (hZsub j h0)
  exact ih _ (hc ▸ Finset.card_lt_card hss) (y + t • s) rfl hrc'
    (fun j hj => hZsub j (hS0 j hj))

/-- Extending an independent set of columns inside `Z` to a maximal one. -/
lemma x8_extend (A : Matrix (Fin m) ι ℝ) (Z S : Finset ι) (hSZ : S ⊆ Z)
    (hS : LinearIndepOn ℝ (x8col A) (S : Set ι)) :
    ∃ I : Finset ι, S ⊆ I ∧ I ⊆ Z ∧ LinearIndepOn ℝ (x8col A) (I : Set ι) ∧
      ∀ k ∈ Z, x8col A k ∈ Submodule.span ℝ (x8col A '' (I : Set ι)) := by
  classical
  set F := Z.powerset.filter (fun I => S ⊆ I ∧ LinearIndepOn ℝ (x8col A) (I : Set ι)) with hF
  have hFne : F.Nonempty := ⟨S, by simp [hF, hSZ, hS]⟩
  obtain ⟨I, hIF, hImax⟩ := Finset.exists_max_image F Finset.card hFne
  simp only [hF, Finset.mem_filter, Finset.mem_powerset] at hIF
  obtain ⟨hIZ, hSI, hIind⟩ := hIF
  refine ⟨I, hSI, hIZ, hIind, fun k hk => ?_⟩
  by_contra hspan
  have hkI : k ∉ I := by
    intro hkI; exact hspan (Submodule.subset_span ⟨k, by simpa using hkI, rfl⟩)
  have hind' : LinearIndepOn ℝ (x8col A) ((insert k I : Finset ι) : Set ι) := by
    rw [Finset.coe_insert]; exact hIind.insert hspan
  have := hImax (insert k I) (by
    simp only [hF, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset hk hIZ, hSI.trans (Finset.subset_insert _ _), hind'⟩)
  rw [Finset.card_insert_of_notMem hkI] at this
  omega

end Disjunctive.GeneralDisjunctions


open Matrix Finset

set_option linter.unusedSectionVars false

namespace Disjunctive.GeneralDisjunctions

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

lemma x8_span_coef (A : Matrix (Fin m) ι ℝ) (I : Finset ι) (v : Fin m → ℝ)
    (hv : v ∈ Submodule.span ℝ (x8col A '' (I : Set ι))) :
    ∃ c : ι → ℝ, v = ∑ i ∈ I, c i • x8col A i := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨fun k => if k = i then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (by simpa using hi) h
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, rfl⟩ := hx; obtain ⟨c2, rfl⟩ := hy
    exact ⟨c1 + c2, by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    exact ⟨a • c, by simp [Finset.smul_sum, smul_smul]⟩

/-- The tableau of a basis `I`. -/
lemma x8_tableau (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (I : Finset ι)
    (hI : LinearIndepOn ℝ (x8col A) (I : Set ι)) (abar : ι → ι → ℝ)
    (habar : ∀ j, x8col A j = ∑ i ∈ I, abar i j • x8col A i)
    (xh : ι → ℝ) (hxh : xh ∈ LPFeasible A b) (hsupp : x8supp xh ⊆ I) :
    IsBasicFeasibleSolution A b I Iᶜ abar xh := by
  refine ⟨⟨disjoint_compl_right, Finset.union_compl I, fun j hj => ?_, fun x => ?_⟩, hxh⟩
  · by_contra hne; exact (Finset.mem_compl.mp hj) (hsupp (x8_mem_supp.mpr hne))
  have hAx : A *ᵥ x = ∑ i ∈ I, (x i + ∑ j ∈ Iᶜ, abar i j * x j) • x8col A i := by
    rw [x8_mulVec, ← Finset.sum_add_sum_compl I]
    have : ∑ j ∈ Iᶜ, x j • x8col A j = ∑ i ∈ I, (∑ j ∈ Iᶜ, abar i j * x j) • x8col A i := by
      rw [Finset.sum_congr rfl (fun j _ => by rw [habar j])]
      simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
    rw [this, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by rw [add_smul]
  have hb : b = ∑ i ∈ I, xh i • x8col A i := by
    rw [← hxh.1, x8_mulVec, x8_sum_supp _ _ hsupp]
  constructor
  · intro h
    rw [hAx, hb, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h
    simp_rw [← sub_smul] at h
    have := (linearIndepOn_finset_iff.mp hI) _ h
    intro i hi; have := this i hi; linarith
  · intro h
    rw [hAx, hb]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [h i hi]; ring_nf

lemma x8_ray_mul (A : Matrix (Fin m) ι ℝ) (I : Finset ι) (abar : ι → ι → ℝ)
    (habar : ∀ j, x8col A j = ∑ i ∈ I, abar i j • x8col A i) (j : ι) (hj : j ∉ I)
    (w : ι → ℝ) :
    w ⬝ᵥ extremeRay I abar j = w j - ∑ i ∈ I, w i * abar i j := by
  have hr : ∀ k, extremeRay I abar j k =
      (if k = j then 1 else 0) + (if k ∈ I then -abar k j else 0) := by
    intro k
    unfold extremeRay
    by_cases hk : k = j
    · subst hk; simp [hj]
    · simp [hk]
  simp only [dotProduct, hr, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_neg]
  rw [← Finset.sum_filter]
  simp [sub_eq_add_neg, Finset.sum_neg_distrib]

lemma x8_ray_ker (A : Matrix (Fin m) ι ℝ) (I : Finset ι) (abar : ι → ι → ℝ)
    (habar : ∀ j, x8col A j = ∑ i ∈ I, abar i j • x8col A i) (j : ι) (hj : j ∉ I) :
    A *ᵥ extremeRay I abar j = 0 := by
  ext r
  have h1 := congrFun (habar j) r
  simp only [x8col, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
  have := x8_ray_mul A I abar habar j hj (fun k => A r k)
  simp only [Matrix.mulVec, Pi.zero_apply]
  rw [this, h1]
  simp [mul_comm]

theorem x8_main {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (hrat : IsRationalData A b)
    (Nprime : Finset ι) (phi : ι → ℝ) (phi0 : ℝ)
    (hne : (MixedIntegerSet A b Nprime).Nonempty)
    (hvalid : ∀ x ∈ MixedIntegerSet A b Nprime, phi0 ≤ dotProduct phi x)
    (hcutoff : ∃ v ∈ LPFeasible A b, dotProduct phi v < phi0) :
    ∃ (I J : Finset ι) (abar : ι → ι → ℝ) (v : ι → ℝ),
      IsBasicFeasibleSolution A b I J abar v ∧
      dotProduct phi v < phi0 ∧
      ∀ j ∈ J, 0 ≤ dotProduct phi (extremeRay I abar j) := by
  classical
  have hray := x8_hray A b hrat Nprime phi phi0 hne hvalid
  obtain ⟨v, hv, hφv⟩ := hcutoff
  -- the finite set of basic feasible solutions
  set B : Set (ι → ℝ) := {x | x ∈ LPFeasible A b ∧ LinearIndepOn ℝ (x8col A) (x8supp x : Set ι)}
    with hB
  have hBfin : B.Finite := by
    apply Set.Finite.of_finite_image (f := x8supp) (Set.toFinite _)
    intro x hx x' hx' hxx
    exact x8_uniq A _ hx.2 x x' (subset_refl _) (by rw [← hxx]) (by rw [hx.1.1, hx'.1.1])
  obtain ⟨v1, hv1, hφv1, -, hv1i⟩ := x8_bfs A b phi hray v hv
  obtain ⟨xs, hxsB, hxsmin⟩ := Set.exists_min_image B (fun x => phi ⬝ᵥ x) hBfin ⟨v1, hv1, hv1i⟩
  have hopt : ∀ x ∈ LPFeasible A b, phi ⬝ᵥ xs ≤ phi ⬝ᵥ x := by
    intro x hx
    obtain ⟨x', hx', h1, -, h3⟩ := x8_bfs A b phi hray x hx
    exact (hxsmin x' ⟨hx', h3⟩).trans h1
  have hxsv : phi ⬝ᵥ xs < phi0 := lt_of_le_of_lt (hopt v hv) hφv
  obtain ⟨y, hrc, hle⟩ := x8_dual A b phi xs hxsB.1 hopt
  have hcs := x8_cs A b phi xs y hxsB.1 hrc hle
  obtain ⟨y', hrc', hcs', hspan⟩ := x8_enlarge A phi (x8supp xs) _ y rfl hrc hcs
  obtain ⟨I, hSI, hIZ, hIind, hIspan⟩ := x8_extend A (x8Z A phi y') (x8supp xs)
    (fun j hj => by simp [x8Z, hcs' j hj]) hxsB.2
  have hall : ∀ k, x8col A k ∈ Submodule.span ℝ (x8col A '' (I : Set ι)) := by
    intro k
    have hle' : Submodule.span ℝ (x8col A '' (x8Z A phi y' : Set ι)) ≤
        Submodule.span ℝ (x8col A '' (I : Set ι)) := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      exact hIspan z (by simpa using hz)
    exact hle' (hspan k)
  choose abar habar using fun k => x8_span_coef A I _ (hall k)
  let abar' : ι → ι → ℝ := fun i j => abar j i
  have habar' : ∀ j, x8col A j = ∑ i ∈ I, abar' i j • x8col A i := habar
  refine ⟨I, Iᶜ, abar', xs, x8_tableau A b I hIind abar' habar' xs hxsB.1 hSI, hxsv, ?_⟩
  intro j hj
  have hjI : j ∉ I := Finset.mem_compl.mp hj
  rw [x8_split A phi y' (extremeRay I abar' j), x8_ray_ker A I abar' habar' j hjI,
    zero_dotProduct, add_zero, x8_ray_mul A I abar' habar' j hjI]
  have hzero : ∀ i ∈ I, x8rc A phi y' i = 0 := by
    intro i hi; have := hIZ hi; simpa [x8Z] using this
  rw [Finset.sum_eq_zero (fun i hi => by rw [hzero i hi, zero_mul]), sub_zero]
  exact hrc' j

end Disjunctive.GeneralDisjunctions

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (hrat : Disjunctive.GeneralDisjunctions.IsRationalData A b)
    (Nprime : Finset ι) (phi : ι → ℝ) (phi0 : ℝ)
    (hne : (Disjunctive.GeneralDisjunctions.MixedIntegerSet A b Nprime).Nonempty)
    (hvalid : ∀ x ∈ Disjunctive.GeneralDisjunctions.MixedIntegerSet A b Nprime,
      phi0 ≤ dotProduct phi x)
    (hcutoff : ∃ v ∈ Disjunctive.GeneralDisjunctions.LPFeasible A b, dotProduct phi v < phi0) :
    ∃ (I J : Finset ι) (abar : ι → ι → ℝ) (v : ι → ℝ),
      Disjunctive.GeneralDisjunctions.IsBasicFeasibleSolution A b I J abar v ∧
      dotProduct phi v < phi0 ∧
      ∀ j ∈ J, 0 ≤ dotProduct phi (Disjunctive.GeneralDisjunctions.extremeRay I abar j) :=
  Disjunctive.GeneralDisjunctions.x8_main A b hrat Nprime phi phi0 hne hvalid hcutoff

