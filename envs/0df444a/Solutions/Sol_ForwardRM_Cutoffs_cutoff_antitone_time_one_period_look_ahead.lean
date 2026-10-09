-- Prove2me | solution 1 for ForwardRM.Cutoffs.cutoff_antitone_time_one_period_look_ahead
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T23:33:47.823909+00:00
-- url     : https://prove2.me/submissions/2e65079a-7322-4a5f-aa57-83c0d527cdab

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Cutoff

set_option autoImplicit false

/-! 18a2631b library, part 1: sorted-list combinatorics and cohort-expectation infrastructure. -/

namespace FRM18

open ForwardRM.Cutoffs MeasureTheory

theorem sortDesc_cons (a : ℝ) (S : Multiset ℝ) :
    sortDesc (a ::ₘ S) = (sortDesc S).orderedInsert (· ≥ ·) a := by
  unfold sortDesc
  apply List.Perm.eq_of_pairwise' (r := (· ≥ ·))
  · exact Multiset.pairwise_sort _ _
  · exact List.Pairwise.orderedInsert _ _ (Multiset.pairwise_sort _ _)
  · rw [← Multiset.coe_eq_coe, Multiset.sort_eq,
      Multiset.coe_eq_coe.mpr (List.perm_orderedInsert _ _ _), ← Multiset.cons_coe, Multiset.sort_eq]

theorem sortDesc_cons_top (a : ℝ) (S : Multiset ℝ) (h : ∀ s ∈ S, s ≤ a) :
    sortDesc (a ::ₘ S) = a :: sortDesc S := by
  unfold sortDesc
  exact Multiset.sort_cons _ _ _ h

theorem coe_sortDesc (S : Multiset ℝ) : ((sortDesc S : List ℝ) : Multiset ℝ) = S :=
  Multiset.sort_eq _ _

theorem pairwise_sortDesc (S : Multiset ℝ) : (sortDesc S).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _

theorem mem_sortDesc {S : Multiset ℝ} {x : ℝ} : x ∈ sortDesc S ↔ x ∈ S :=
  Multiset.mem_sort _

theorem orderedInsert_of_ge (a : ℝ) (L : List ℝ) (h : ∀ y ∈ L, y ≤ a) :
    L.orderedInsert (· ≥ ·) a = a :: L := by
  cases L with
  | nil => rfl
  | cons y L' => rw [List.orderedInsert_cons, if_pos (h y (by simp))]

theorem coe_orderedInsert (a : ℝ) (L : List ℝ) :
    ((L.orderedInsert (· ≥ ·) a : List ℝ) : Multiset ℝ) = a ::ₘ (L : Multiset ℝ) := by
  rw [Multiset.coe_eq_coe.mpr (List.perm_orderedInsert _ _ _), Multiset.cons_coe]

/-- Replacing one element `a` by a larger `b`: comparison of the top-`j` sums and of what is left. -/
theorem comb (g : ℝ → ℝ) (lo hi : ℝ) (hg : MonotoneOn g (Set.Icc lo hi)) :
    ∀ (L : List ℝ), L.Pairwise (· ≥ ·) → ∀ (a b : ℝ), a ∈ Set.Icc lo hi → b ∈ Set.Icc lo hi →
    a ≤ b → ∀ j : ℕ,
    0 ≤ (((L.orderedInsert (· ≥ ·) b).take j).map g).sum -
        (((L.orderedInsert (· ≥ ·) a).take j).map g).sum ∧
    ((((L.orderedInsert (· ≥ ·) a).drop j : List ℝ) : Multiset ℝ) =
        (((L.orderedInsert (· ≥ ·) b).drop j : List ℝ) : Multiset ℝ) ∧
      (((L.orderedInsert (· ≥ ·) b).take j).map g).sum -
        (((L.orderedInsert (· ≥ ·) a).take j).map g).sum ≤ g b - g a ∨
     ∃ a' b' : ℝ, ∃ R : Multiset ℝ, a ≤ a' ∧ a' ≤ b' ∧ b' ≤ b ∧
      (((L.orderedInsert (· ≥ ·) a).drop j : List ℝ) : Multiset ℝ) = a' ::ₘ R ∧
      (((L.orderedInsert (· ≥ ·) b).drop j : List ℝ) : Multiset ℝ) = b' ::ₘ R ∧
      (((L.orderedInsert (· ≥ ·) b).take j).map g).sum -
        (((L.orderedInsert (· ≥ ·) a).take j).map g).sum + (g b' - g a') ≤ g b - g a) := by
  intro L
  induction L with
  | nil =>
    intro _ a b ha hb hab j
    have hgab : g a ≤ g b := hg ha hb hab
    cases j with
    | zero =>
      refine ⟨by simp, Or.inr ⟨a, b, 0, le_rfl, hab, le_rfl, by simp, by simp, by simp⟩⟩
    | succ j =>
      refine ⟨by simpa using hgab, Or.inl ⟨by simp, by simp⟩⟩
  | cons x L' ih =>
    intro hL a b ha hb hab j
    have hL' : L'.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hL).2
    have hxL : ∀ y ∈ L', y ≤ x := fun y hy => (List.pairwise_cons.mp hL).1 y hy
    have hgab : g a ≤ g b := hg ha hb hab
    by_cases hbx : b ≥ x
    · by_cases hax : a ≥ x
      · -- both inserted in front
        have e1 : (x :: L').orderedInsert (· ≥ ·) a = a :: x :: L' := by
          rw [List.orderedInsert_cons, if_pos hax]
        have e2 : (x :: L').orderedInsert (· ≥ ·) b = b :: x :: L' := by
          rw [List.orderedInsert_cons, if_pos hbx]
        rw [e1, e2]
        cases j with
        | zero =>
          refine ⟨by simp, Or.inr ⟨a, b, ((x :: L' : List ℝ) : Multiset ℝ), le_rfl, hab, le_rfl,
            by simp, by simp, by simp⟩⟩
        | succ j =>
          simp only [List.take_succ_cons, List.drop_succ_cons, List.map_cons, List.sum_cons]
          refine ⟨by linarith, Or.inl ⟨trivial, by linarith⟩⟩
      · push Not at hax
        have hxI : x ∈ Set.Icc lo hi := ⟨le_trans ha.1 hax.le, le_trans hbx hb.2⟩
        have hgxb : g x ≤ g b := hg hxI hb hbx
        have hgax : g a ≤ g x := hg ha hxI hax.le
        have e1 : (x :: L').orderedInsert (· ≥ ·) a = x :: L'.orderedInsert (· ≥ ·) a := by
          rw [List.orderedInsert_cons, if_neg (by push Not; exact hax)]
        have e2 : (x :: L').orderedInsert (· ≥ ·) b = b :: x :: L' := by
          rw [List.orderedInsert_cons, if_pos hbx]
        rw [e1, e2]
        cases j with
        | zero =>
          refine ⟨by simp, Or.inr ⟨a, b, ((x :: L' : List ℝ) : Multiset ℝ), le_rfl, hab, le_rfl,
            ?_, by simp, by simp⟩⟩
          simp only [List.drop_zero]
          rw [← Multiset.cons_coe, coe_orderedInsert, ← Multiset.cons_coe, Multiset.cons_swap]
        | succ j =>
          have hIH := ih hL' a x ha hxI hax.le j
          rw [orderedInsert_of_ge x L' hxL] at hIH
          simp only [List.take_succ_cons, List.drop_succ_cons, List.map_cons, List.sum_cons]
          obtain ⟨h0, h1 | ⟨a', b', R, h1, h2, h3, h4, h5, h6⟩⟩ := hIH
          · refine ⟨by linarith, Or.inl ⟨h1.1, by linarith [h1.2]⟩⟩
          · exact ⟨by linarith, Or.inr ⟨a', b', R, h1, h2, h3.trans hbx, h4, h5, by linarith⟩⟩
    · push Not at hbx
      have hax : a < x := lt_of_le_of_lt hab hbx
      have e1 : (x :: L').orderedInsert (· ≥ ·) a = x :: L'.orderedInsert (· ≥ ·) a := by
        rw [List.orderedInsert_cons, if_neg (by push Not; exact hax)]
      have e2 : (x :: L').orderedInsert (· ≥ ·) b = x :: L'.orderedInsert (· ≥ ·) b := by
        rw [List.orderedInsert_cons, if_neg (by push Not; exact hbx)]
      rw [e1, e2]
      cases j with
      | zero =>
        refine ⟨by simp, Or.inr ⟨a, b, ((x :: L' : List ℝ) : Multiset ℝ), le_rfl, hab, le_rfl,
          ?_, ?_, by simp⟩⟩
        · simp only [List.drop_zero]
          rw [← Multiset.cons_coe, coe_orderedInsert, ← Multiset.cons_coe, Multiset.cons_swap]
        · simp only [List.drop_zero]
          rw [← Multiset.cons_coe, coe_orderedInsert, ← Multiset.cons_coe, Multiset.cons_swap]
      | succ j =>
        simp only [List.take_succ_cons, List.drop_succ_cons, List.map_cons, List.sum_cons]
        obtain ⟨h0, h1⟩ := ih hL' a b ha hb hab j
        refine ⟨by linarith, ?_⟩
        rcases h1 with h1 | ⟨a', b', R, h1, h2, h3, h4, h5, h6⟩
        · exact Or.inl ⟨h1.1, by linarith [h1.2]⟩
        · exact Or.inr ⟨a', b', R, h1, h2, h3, h4, h5, by linarith⟩

/-- Adding a buyer `x` in front of a sorted list whose head is `≤ x`. -/
theorem comb_add_top (g : ℝ → ℝ) (lo hi : ℝ) (hg : MonotoneOn g (Set.Icc lo hi)) :
    ∀ (L : List ℝ), L.Pairwise (· ≥ ·) → (∀ y ∈ L, y ∈ Set.Icc lo hi) →
    ∀ (x : ℝ), x ∈ Set.Icc lo hi → (∀ y ∈ L, y ≤ x) → ∀ j : ℕ, j ≤ L.length →
    0 ≤ (((x :: L).take j).map g).sum - ((L.take j).map g).sum ∧
    ∃ z ∈ Set.Icc lo hi, ((((x :: L).drop j : List ℝ)) : Multiset ℝ) =
      z ::ₘ ((L.drop j : List ℝ) : Multiset ℝ) := by
  intro L
  induction L with
  | nil =>
    intro _ _ x hx _ j hj
    simp at hj; subst hj
    exact ⟨by simp, x, hx, by simp⟩
  | cons y L' ih =>
    intro hL hLI x hx hxL j hj
    have hL' : L'.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hL).2
    have hyL : ∀ z ∈ L', z ≤ y := fun z hz => (List.pairwise_cons.mp hL).1 z hz
    have hyI : y ∈ Set.Icc lo hi := hLI y (by simp)
    cases j with
    | zero => exact ⟨by simp, x, hx, by simp⟩
    | succ j =>
      have hj' : j ≤ L'.length := by simpa using hj
      obtain ⟨h0, z, hz, hzz⟩ := ih hL' (fun z hz => hLI z (by simp [hz])) y hyI hyL j hj'
      have hgxy : g y ≤ g x := hg hyI hx (hxL y (by simp))
      simp only [List.take_succ_cons, List.drop_succ_cons, List.map_cons, List.sum_cons] at h0 hzz ⊢
      refine ⟨by linarith, z, hz, hzz⟩

/-- Adding a buyer `x` anywhere. -/
theorem comb_add (g : ℝ → ℝ) (lo hi : ℝ) (hg : MonotoneOn g (Set.Icc lo hi)) :
    ∀ (L : List ℝ), L.Pairwise (· ≥ ·) → (∀ y ∈ L, y ∈ Set.Icc lo hi) →
    ∀ (x : ℝ), x ∈ Set.Icc lo hi → ∀ j : ℕ, j ≤ L.length →
    0 ≤ (((L.orderedInsert (· ≥ ·) x).take j).map g).sum - ((L.take j).map g).sum ∧
    ∃ z ∈ Set.Icc lo hi, (((L.orderedInsert (· ≥ ·) x).drop j : List ℝ) : Multiset ℝ) =
      z ::ₘ ((L.drop j : List ℝ) : Multiset ℝ) := by
  intro L
  induction L with
  | nil =>
    intro _ _ x hx j hj
    simp at hj; subst hj
    exact ⟨by simp, x, hx, by simp⟩
  | cons y L' ih =>
    intro hL hLI x hx j hj
    have hL' : L'.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hL).2
    by_cases hxy : x ≥ y
    · rw [List.orderedInsert_cons, if_pos hxy]
      refine comb_add_top g lo hi hg (y :: L') hL hLI x hx ?_ j hj
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy
      · exact le_trans ((List.pairwise_cons.mp hL).1 z hz) hxy
    · rw [List.orderedInsert_cons, if_neg hxy]
      cases j with
      | zero =>
        refine ⟨by simp, x, hx, ?_⟩
        simp only [List.drop_zero]
        rw [← Multiset.cons_coe, coe_orderedInsert, ← Multiset.cons_coe, Multiset.cons_swap]
      | succ j =>
        have hj' : j ≤ L'.length := by simpa using hj
        obtain ⟨h0, z, hz, hzz⟩ := ih hL' (fun z hz => hLI z (by simp [hz])) x hx j hj'
        simp only [List.take_succ_cons, List.drop_succ_cons, List.map_cons, List.sum_cons]
        exact ⟨by linarith, z, hz, hzz⟩

/-- Sum of a list of values each `≤ c` with `0 ≤ c`, over the first `j` entries. -/
theorem sum_take_le (g : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    ∀ (L : List ℝ) (j : ℕ), (∀ y ∈ L, g y ≤ c) → ((L.take j).map g).sum ≤ j * c := by
  intro L
  induction L with
  | nil => intro j _; simp; positivity
  | cons y L' ih =>
    intro j h
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      have := ih j (fun z hz => h z (by simp [hz]))
      have := h y (by simp)
      push_cast; linarith

/-! ## Cohort infrastructure -/

/-- All values in the support `[v̲, v̄]`. -/
def InI (M : Model) (S : Multiset ℝ) : Prop := ∀ s ∈ S, s ∈ Set.Icc M.vlo M.vhi

theorem InI_add {M : Model} {A B : Multiset ℝ} (hA : InI M A) (hB : InI M B) : InI M (A + B) := by
  intro s hs
  rcases Multiset.mem_add.mp hs with h | h
  · exact hA s h
  · exact hB s h

theorem InI_cons {M : Model} {a : ℝ} {A : Multiset ℝ} (ha : a ∈ Set.Icc M.vlo M.vhi) (hA : InI M A) :
    InI M (a ::ₘ A) := by
  intro s hs
  rcases Multiset.mem_cons.mp hs with rfl | h
  · exact ha
  · exact hA s h

theorem InI_zero (M : Model) : InI M 0 := by intro s hs; simp at hs

theorem InI_dropTop {M : Model} {S : Multiset ℝ} (hS : InI M S) (j : ℕ) : InI M (dropTop j S) := by
  intro s hs
  unfold dropTop at hs
  rw [Multiset.mem_coe] at hs
  exact hS s (mem_sortDesc.mp (List.mem_of_mem_drop hs))

theorem law_compl_Icc (M : Model) : M.law (Set.Icc M.vlo M.vhi)ᶜ = 0 := by
  rw [Model.law, withDensity_apply _ measurableSet_Icc.compl]
  apply le_antisymm _ zero_le
  calc _ ≤ ∫⁻ v in (Set.Icc M.vlo M.vhi)ᶜ, (0 : ENNReal) :=
        setLIntegral_mono measurable_const (fun v hv => by simp [M.f_eq_zero v hv])
    _ = 0 := by simp

theorem ae_cohort (M : Model) (n : ℕ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin n => M.law), InI M (cohort x) := by
  have h : ∀ i : Fin n, ∀ᵐ x ∂(Measure.pi fun _ : Fin n => M.law),
      x i ∈ Set.Icc M.vlo M.vhi := by
    intro i
    rw [ae_iff]
    exact Measure.pi_eval_preimage_null (μ := fun _ => M.law) (law_compl_Icc M)
  filter_upwards [ae_all_iff.mpr h] with x hx
  intro s hs
  unfold cohort at hs
  rw [Multiset.mem_coe, List.mem_ofFn'] at hs
  obtain ⟨i, rfl⟩ := hs
  exact hx i

theorem CL_mono (M : Model) (s : ℕ) {g h : Multiset ℝ → ℝ} (hgh : ∀ C, InI M C → g C ≤ h C) :
    M.cohortLIntegral s g ≤ M.cohortLIntegral s h := by
  unfold Model.cohortLIntegral
  refine ENNReal.tsum_le_tsum fun n => ?_
  exact mul_le_mul_of_nonneg_left (lintegral_mono_ae ((ae_cohort M n).mono
    fun x hx => ENNReal.ofReal_le_ofReal (hgh _ hx))) zero_le

theorem CL_const (M : Model) (s : ℕ) (B : ℝ) :
    M.cohortLIntegral s (fun _ => B) = ENNReal.ofReal B := by
  unfold Model.cohortLIntegral
  simp [lintegral_const, ENNReal.tsum_mul_right, PMF.tsum_coe]

theorem CL_le_const (M : Model) (s : ℕ) {g : Multiset ℝ → ℝ} (B : ℝ)
    (hg : ∀ C, InI M C → g C ≤ B) : M.cohortLIntegral s g ≤ ENNReal.ofReal B :=
  (CL_mono M s hg).trans (CL_const M s B).le

theorem CL_ne_top (M : Model) (s : ℕ) {g : Multiset ℝ → ℝ} (B : ℝ)
    (hg : ∀ C, InI M C → g C ≤ B) : M.cohortLIntegral s g ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (CL_le_const M s B hg)

theorem CE_nonneg (M : Model) (s : ℕ) (g : Multiset ℝ → ℝ) : 0 ≤ M.cohortExp s g :=
  ENNReal.toReal_nonneg

theorem CE_mono (M : Model) (s : ℕ) {g h : Multiset ℝ → ℝ} (B : ℝ)
    (hgh : ∀ C, InI M C → g C ≤ h C) (hB : ∀ C, InI M C → h C ≤ B) :
    M.cohortExp s g ≤ M.cohortExp s h :=
  ENNReal.toReal_mono (CL_ne_top M s B hB) (CL_mono M s hgh)

theorem CE_le_const (M : Model) (s : ℕ) {g : Multiset ℝ → ℝ} (B : ℝ) (hB0 : 0 ≤ B)
    (hg : ∀ C, InI M C → g C ≤ B) : M.cohortExp s g ≤ B := by
  unfold Model.cohortExp
  calc _ ≤ (ENNReal.ofReal B).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (CL_le_const M s B hg)
    _ = B := ENNReal.toReal_ofReal hB0

theorem CE_const (M : Model) (s : ℕ) (B : ℝ) (hB0 : 0 ≤ B) :
    M.cohortExp s (fun _ => B) = B := by
  unfold Model.cohortExp; rw [CL_const, ENNReal.toReal_ofReal hB0]

theorem CL_add_const_le (M : Model) (s : ℕ) (g : Multiset ℝ → ℝ) (c : ℝ) :
    M.cohortLIntegral s (fun C => g C + c) ≤ M.cohortLIntegral s g + ENNReal.ofReal c := by
  unfold Model.cohortLIntegral
  calc _ ≤ ∑' n : ℕ, ((M.arrivals s n) *
        ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (g (cohort x)) ∂(Measure.pi fun _ : Fin n => M.law) +
        M.arrivals s n * ENNReal.ofReal c) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        calc _ ≤ ∫⁻ x : Fin n → ℝ, (ENNReal.ofReal (g (cohort x)) + ENNReal.ofReal c)
              ∂(Measure.pi fun _ : Fin n => M.law) :=
              lintegral_mono fun x => ENNReal.ofReal_add_le
          _ = _ := by rw [lintegral_add_right _ measurable_const]; simp
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem CE_add_const (M : Model) (s : ℕ) {g : Multiset ℝ → ℝ} (c B : ℝ) (hc : 0 ≤ c)
    (hB : ∀ C, InI M C → g C ≤ B) :
    M.cohortExp s (fun C => g C + c) ≤ M.cohortExp s g + c := by
  unfold Model.cohortExp
  have h1 := CL_ne_top M s B hB
  calc _ ≤ (M.cohortLIntegral s g + ENNReal.ofReal c).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h1, ENNReal.ofReal_ne_top⟩)
          (CL_add_const_le M s g c)
    _ = _ := by rw [ENNReal.toReal_add h1 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc]

/-! ## Value function: basic bounds and monotonicity -/

theorem valueAux_succ (M : Model) (r k : ℕ) (S : Multiset ℝ) :
    M.valueAux (r + 1) k S =
      (Finset.range (min k (Multiset.card S) + 1)).sup' Finset.nonempty_range_add_one
        (fun j => M.sumTop j S + M.δ * M.cohortExp (M.T + 1 - r)
          (fun C => M.valueAux r (k - j) (dropTop j S + C))) := rfl

theorem valueAux_zero (M : Model) (k : ℕ) (S : Multiset ℝ) : M.valueAux 0 k S = 0 := rfl

theorem sumTop_zero (M : Model) (S : Multiset ℝ) : M.sumTop 0 S = 0 := by
  simp [Model.sumTop]

theorem valueAux_nonneg (M : Model) : ∀ r k S, 0 ≤ M.valueAux r k S := by
  intro r k S
  cases r with
  | zero => rw [valueAux_zero]
  | succ r =>
    rw [valueAux_succ]
    refine Finset.le_sup'_of_le _ (b := 0) (by simp) ?_
    simp only [sumTop_zero, zero_add]
    exact mul_nonneg M.δ_pos.le (CE_nonneg _ _ _)

theorem m_le_mvhi (M : Model) {x : ℝ} (hx : x ∈ Set.Icc M.vlo M.vhi) : M.m x ≤ M.m M.vhi :=
  M.m_strictMonoOn.monotoneOn hx ⟨M.vlo_lt_vhi.le, le_rfl⟩ hx.2

theorem mvhi_pos (M : Model) : 0 < M.m M.vhi := M.m_vhi_pos

theorem sumTop_le (M : Model) {S : Multiset ℝ} (hS : InI M S) (j : ℕ) :
    M.sumTop j S ≤ j * M.m M.vhi :=
  sum_take_le M.m _ (mvhi_pos M).le _ j fun y hy => m_le_mvhi M (hS y (mem_sortDesc.mp hy))

theorem valueAux_le (M : Model) : ∀ r k S, InI M S → M.valueAux r k S ≤ k * M.m M.vhi := by
  intro r
  induction r with
  | zero => intro k S _; rw [valueAux_zero]; exact mul_nonneg (Nat.cast_nonneg _) (mvhi_pos M).le
  | succ r ih =>
    intro k S hS
    rw [valueAux_succ]
    refine Finset.sup'_le _ _ fun j hj => ?_
    have hjk : j ≤ k := by simp at hj; omega
    have h1 := sumTop_le M hS j
    have h2 : M.cohortExp (M.T + 1 - r) (fun C => M.valueAux r (k - j) (dropTop j S + C)) ≤
        ((k - j : ℕ) : ℝ) * M.m M.vhi :=
      CE_le_const M _ _ (mul_nonneg (Nat.cast_nonneg _) (mvhi_pos M).le)
        fun C hC => ih _ _ (InI_add (InI_dropTop hS j) hC)
    have h3 : 0 ≤ M.cohortExp (M.T + 1 - r) (fun C => M.valueAux r (k - j) (dropTop j S + C)) :=
      CE_nonneg _ _ _
    have hδ1 := M.δ_lt_one
    have hδ0 := M.δ_pos
    rw [Nat.cast_sub hjk] at h2
    nlinarith

/-- The bound used for every `CE_mono` on value functions. -/
theorem valueAux_le' (M : Model) (r k : ℕ) (X : Multiset ℝ) (hX : InI M X) :
    ∀ C, InI M C → M.valueAux r k (X + C) ≤ k * M.m M.vhi :=
  fun C hC => valueAux_le M r k _ (InI_add hX hC)

theorem valueAux_mono_k (M : Model) : ∀ r k S, InI M S → M.valueAux r k S ≤ M.valueAux r (k + 1) S := by
  intro r
  induction r with
  | zero => intro k S _; rw [valueAux_zero, valueAux_zero]
  | succ r ih =>
    intro k S hS
    rw [valueAux_succ, valueAux_succ]
    refine Finset.sup'_le _ _ fun j hj => ?_
    have hjk : j ≤ k := by simp at hj; omega
    have hj' : j ∈ Finset.range (min (k + 1) (Multiset.card S) + 1) := by simp at hj ⊢; omega
    refine Finset.le_sup'_of_le _ hj' ?_
    have hkj : k + 1 - j = (k - j) + 1 := by omega
    rw [hkj]
    have := CE_mono M (M.T + 1 - r) (((k - j + 1 : ℕ) : ℝ) * M.m M.vhi)
      (g := fun C => M.valueAux r (k - j) (dropTop j S + C))
      (h := fun C => M.valueAux r (k - j + 1) (dropTop j S + C))
      (fun C hC => ih _ _ (InI_add (InI_dropTop hS j) hC))
      (valueAux_le' M r _ _ (InI_dropTop hS j))
    have hδ0 := M.δ_pos
    nlinarith

theorem valueAux_mono_add (M : Model) : ∀ r k S x, InI M S → x ∈ Set.Icc M.vlo M.vhi →
    M.valueAux r k S ≤ M.valueAux r k (x ::ₘ S) := by
  intro r
  induction r with
  | zero => intro k S x _ _; rw [valueAux_zero, valueAux_zero]
  | succ r ih =>
    intro k S x hS hx
    rw [valueAux_succ, valueAux_succ]
    refine Finset.sup'_le _ _ fun j hj => ?_
    have hjS : j ≤ (sortDesc S).length := by
      unfold sortDesc; rw [Multiset.length_sort]; simp at hj; omega
    have hj' : j ∈ Finset.range (min k (Multiset.card (x ::ₘ S)) + 1) := by
      simp at hj ⊢; omega
    refine Finset.le_sup'_of_le _ hj' ?_
    obtain ⟨h0, z, hz, hzz⟩ := comb_add M.m M.vlo M.vhi M.m_strictMonoOn.monotoneOn (sortDesc S)
      (pairwise_sortDesc S) (fun y hy => hS y (mem_sortDesc.mp hy)) x hx j hjS
    have eS : M.sumTop j (x ::ₘ S) = ((((sortDesc S).orderedInsert (· ≥ ·) x).take j).map M.m).sum := by
      unfold Model.sumTop; rw [sortDesc_cons]
    have eS' : M.sumTop j S = (((sortDesc S).take j).map M.m).sum := rfl
    have dS : dropTop j (x ::ₘ S) = z ::ₘ dropTop j S := by
      unfold dropTop; rw [sortDesc_cons, hzz]
    rw [eS, eS', dS]
    have := CE_mono M (M.T + 1 - r) (((k - j : ℕ) : ℝ) * M.m M.vhi)
      (g := fun C => M.valueAux r (k - j) (dropTop j S + C))
      (h := fun C => M.valueAux r (k - j) (z ::ₘ dropTop j S + C))
      (fun C hC => by
        rw [Multiset.cons_add]
        exact ih _ _ _ (InI_add (InI_dropTop hS j) hC) hz)
      (valueAux_le' M r _ _ (InI_cons hz (InI_dropTop hS j)))
    have hδ0 := M.δ_pos
    nlinarith

theorem dropTop_zero (S : Multiset ℝ) : dropTop 0 S = S := by
  simp [dropTop, coe_sortDesc]

/-- Replacing one buyer `a` by a higher `b`: the value rises by at most `m b - m a`. -/
theorem valueAux_lip (M : Model) : ∀ r k (S : Multiset ℝ) (a b : ℝ), InI M S →
    a ∈ Set.Icc M.vlo M.vhi → b ∈ Set.Icc M.vlo M.vhi → a ≤ b →
    M.valueAux r k (a ::ₘ S) ≤ M.valueAux r k (b ::ₘ S) ∧
    M.valueAux r k (b ::ₘ S) ≤ M.valueAux r k (a ::ₘ S) + (M.m b - M.m a) := by
  intro r
  induction r with
  | zero =>
    intro k S a b _ ha hb hab
    simp only [valueAux_zero, le_refl, zero_add, sub_nonneg, true_and]
    exact M.m_strictMonoOn.monotoneOn ha hb hab
  | succ r ih =>
    intro k S a b hS ha hb hab
    have hmono := M.m_strictMonoOn.monotoneOn
    have hδ0 := M.δ_pos
    have hδ1 := M.δ_lt_one
    have key : ∀ j : ℕ,
        M.sumTop j (a ::ₘ S) + M.δ * M.cohortExp (M.T + 1 - r)
            (fun C => M.valueAux r (k - j) (dropTop j (a ::ₘ S) + C)) ≤
          M.sumTop j (b ::ₘ S) + M.δ * M.cohortExp (M.T + 1 - r)
            (fun C => M.valueAux r (k - j) (dropTop j (b ::ₘ S) + C)) ∧
        M.sumTop j (b ::ₘ S) + M.δ * M.cohortExp (M.T + 1 - r)
            (fun C => M.valueAux r (k - j) (dropTop j (b ::ₘ S) + C)) ≤
          M.sumTop j (a ::ₘ S) + M.δ * M.cohortExp (M.T + 1 - r)
            (fun C => M.valueAux r (k - j) (dropTop j (a ::ₘ S) + C)) + (M.m b - M.m a) := by
      intro j
      obtain ⟨h0, h1⟩ := comb M.m M.vlo M.vhi hmono (sortDesc S) (pairwise_sortDesc S) a b ha hb hab j
      have eA : M.sumTop j (a ::ₘ S) =
          ((((sortDesc S).orderedInsert (· ≥ ·) a).take j).map M.m).sum := by
        unfold Model.sumTop; rw [sortDesc_cons]
      have eB : M.sumTop j (b ::ₘ S) =
          ((((sortDesc S).orderedInsert (· ≥ ·) b).take j).map M.m).sum := by
        unfold Model.sumTop; rw [sortDesc_cons]
      have dA : dropTop j (a ::ₘ S) = ((((sortDesc S).orderedInsert (· ≥ ·) a).drop j : List ℝ) : Multiset ℝ) := by
        unfold dropTop; rw [sortDesc_cons]
      have dB : dropTop j (b ::ₘ S) = ((((sortDesc S).orderedInsert (· ≥ ·) b).drop j : List ℝ) : Multiset ℝ) := by
        unfold dropTop; rw [sortDesc_cons]
      rw [eA, eB, dA, dB]
      rcases h1 with ⟨hd, hΔ⟩ | ⟨a', b', R, h1, h2, h3, h4, h5, h6⟩
      · rw [hd]; constructor <;> linarith
      · rw [h4, h5]
        have ha' : a' ∈ Set.Icc M.vlo M.vhi := ⟨ha.1.trans h1, (h2.trans h3).trans hb.2⟩
        have hb' : b' ∈ Set.Icc M.vlo M.vhi := ⟨(ha.1.trans h1).trans h2, h3.trans hb.2⟩
        have hR : InI M R := by
          intro s hs
          have hs' : s ∈ a' ::ₘ R := Multiset.mem_cons_of_mem hs
          rw [← h4, Multiset.mem_coe] at hs'
          have hs'' := List.mem_of_mem_drop hs'
          have : s ∈ a ::ₘ S := by
            have h7 : s ∈ (((sortDesc S).orderedInsert (· ≥ ·) a : List ℝ) : Multiset ℝ) :=
              Multiset.mem_coe.mpr hs''
            rwa [coe_orderedInsert, coe_sortDesc] at h7
          rcases Multiset.mem_cons.mp this with rfl | h
          · exact ha
          · exact hS s h
        have hgb' : M.m a' ≤ M.m b' := hmono ha' hb' h2
        have E1 := CE_mono M (M.T + 1 - r) (((k - j : ℕ) : ℝ) * M.m M.vhi)
          (g := fun C => M.valueAux r (k - j) (a' ::ₘ R + C))
          (h := fun C => M.valueAux r (k - j) (b' ::ₘ R + C))
          (fun C hC => by
            simp only [Multiset.cons_add]
            exact (ih _ _ _ _ (InI_add hR hC) ha' hb' h2).1)
          (valueAux_le' M r _ _ (InI_cons hb' hR))
        have E2 := CE_mono M (M.T + 1 - r) (((k - j : ℕ) : ℝ) * M.m M.vhi + (M.m b' - M.m a'))
          (g := fun C => M.valueAux r (k - j) (b' ::ₘ R + C))
          (h := fun C => M.valueAux r (k - j) (a' ::ₘ R + C) + (M.m b' - M.m a'))
          (fun C hC => by
            simp only [Multiset.cons_add]
            exact (ih _ _ _ _ (InI_add hR hC) ha' hb' h2).2)
          (fun C hC => by
            have := valueAux_le' M r (k - j) _ (InI_cons ha' hR) C hC
            linarith)
        have E3 := CE_add_const M (M.T + 1 - r) (g := fun C => M.valueAux r (k - j) (a' ::ₘ R + C))
          (M.m b' - M.m a') (((k - j : ℕ) : ℝ) * M.m M.vhi) (by linarith)
          (valueAux_le' M r _ _ (InI_cons ha' hR))
        have hd' : 0 ≤ M.m b' - M.m a' := by linarith
        constructor
        · nlinarith
        · nlinarith
    constructor
    · rw [valueAux_succ, valueAux_succ]
      refine Finset.sup'_le _ _ fun j hj => ?_
      have hj' : j ∈ Finset.range (min k (Multiset.card (b ::ₘ S)) + 1) := by simpa using hj
      exact Finset.le_sup'_of_le _ hj' (key j).1
    · rw [valueAux_succ, valueAux_succ]
      refine Finset.sup'_le _ _ fun j hj => ?_
      have hj' : j ∈ Finset.range (min k (Multiset.card (a ::ₘ S)) + 1) := by simpa using hj
      exact (key j).2.trans (by gcongr; exact Finset.le_sup'_of_le _ hj' le_rfl)

/-- With a top buyer at `v̄`, the value is at most `m v̄` plus the value with one unit less. -/
theorem valueAux_top_le (M : Model) : ∀ r k (S : Multiset ℝ), InI M S → 1 ≤ k →
    M.valueAux r k (M.vhi ::ₘ S) ≤ M.m M.vhi + M.valueAux r (k - 1) S := by
  intro r
  induction r with
  | zero => intro k S _ _; simp only [valueAux_zero, add_zero]; exact (mvhi_pos M).le
  | succ r ih =>
    intro k S hS hk
    have hδ0 := M.δ_pos
    have hδ1 := M.δ_lt_one
    have hmv := mvhi_pos M
    have hvhi : M.vhi ∈ Set.Icc M.vlo M.vhi := ⟨M.vlo_lt_vhi.le, le_rfl⟩
    rw [valueAux_succ]
    refine Finset.sup'_le _ _ fun j hj => ?_
    cases j with
    | zero =>
      simp only [sumTop_zero, zero_add, dropTop_zero, Nat.sub_zero]
      have E1 := CE_mono M (M.T + 1 - r) (((k - 1 : ℕ) : ℝ) * M.m M.vhi + M.m M.vhi)
        (g := fun C => M.valueAux r k (M.vhi ::ₘ S + C))
        (h := fun C => M.valueAux r (k - 1) (S + C) + M.m M.vhi)
        (fun C hC => by
          simp only [Multiset.cons_add]
          have := ih k (S + C) (InI_add hS hC) hk
          linarith)
        (fun C hC => by
          have := valueAux_le' M r (k - 1) S hS C hC
          linarith)
      have E2 := CE_add_const M (M.T + 1 - r) (g := fun C => M.valueAux r (k - 1) (S + C))
        (M.m M.vhi) (((k - 1 : ℕ) : ℝ) * M.m M.vhi) hmv.le (valueAux_le' M r _ _ hS)
      have E3 : M.δ * M.cohortExp (M.T + 1 - r) (fun C => M.valueAux r (k - 1) (S + C)) ≤
          M.valueAux (r + 1) (k - 1) S := by
        rw [valueAux_succ]
        refine Finset.le_sup'_of_le _ (b := 0) (by simp) ?_
        simp [sumTop_zero, dropTop_zero]
      nlinarith
    | succ j =>
      have hjk : j + 1 ≤ k := by simp at hj; omega
      have hjS : j ≤ Multiset.card S := by simp at hj; omega
      have htop : sortDesc (M.vhi ::ₘ S) = M.vhi :: sortDesc S :=
        sortDesc_cons_top _ _ fun s hs => (hS s hs).2
      have e1 : M.sumTop (j + 1) (M.vhi ::ₘ S) = M.m M.vhi + M.sumTop j S := by
        unfold Model.sumTop; rw [htop]; simp
      have e2 : dropTop (j + 1) (M.vhi ::ₘ S) = dropTop j S := by
        unfold dropTop; rw [htop]; simp
      have e3 : k - (j + 1) = (k - 1) - j := by omega
      rw [e1, e2, e3, add_assoc]
      gcongr
      rw [valueAux_succ]
      exact Finset.le_sup'_of_le _ (b := j) (by simp; omega) le_rfl

/-! ## The cutoff: root of `ΔΠ^k_t(·, ∅)` (Theorem 1, items on the root) -/

theorem piTilde_eq (M : Model) (s k : ℕ) (X : Multiset ℝ) :
    M.piTilde s k X = M.cohortExp s (fun C => M.valueAux (M.T + 1 - s) k (X + C)) := rfl

theorem deltaPi_eq (M : Model) (t k : ℕ) (y : ℝ) :
    M.deltaPi t k y 0 = M.m y + M.δ * M.piTilde (t + 1) (k - 1) 0 -
      M.δ * M.piTilde (t + 1) k (y ::ₘ 0) := by
  simp only [Model.deltaPi, Model.sellOneToday, Model.sellZeroToday]

theorem piTilde_single_lip (M : Model) (s k : ℕ) {y y' : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hy' : y' ∈ Set.Icc M.vlo M.vhi) (hyy : y ≤ y') :
    M.piTilde s k (y ::ₘ 0) ≤ M.piTilde s k (y' ::ₘ 0) ∧
    M.piTilde s k (y' ::ₘ 0) ≤ M.piTilde s k (y ::ₘ 0) + (M.m y' - M.m y) := by
  rw [piTilde_eq, piTilde_eq]
  have hd : 0 ≤ M.m y' - M.m y := sub_nonneg.mpr (M.m_strictMonoOn.monotoneOn hy hy' hyy)
  have hbd : ∀ z ∈ Set.Icc M.vlo M.vhi, ∀ C, InI M C →
      M.valueAux (M.T + 1 - s) k (z ::ₘ 0 + C) ≤ k * M.m M.vhi :=
    fun z hz => valueAux_le' M _ k _ (InI_cons hz (InI_zero M))
  constructor
  · exact CE_mono M s _ (fun C hC => by
      simp only [Multiset.cons_add, zero_add]
      exact (valueAux_lip M _ k C y y' hC hy hy' hyy).1) (hbd y' hy')
  · refine (CE_mono M s (k * M.m M.vhi + (M.m y' - M.m y))
      (h := fun C => M.valueAux (M.T + 1 - s) k (y ::ₘ 0 + C) + (M.m y' - M.m y))
      (fun C hC => by
        simp only [Multiset.cons_add, zero_add]
        exact (valueAux_lip M _ k C y y' hC hy hy' hyy).2)
      (fun C hC => by have := hbd y hy C hC; linarith)).trans ?_
    exact CE_add_const M s _ _ hd (hbd y hy)

theorem piTilde_single_ge (M : Model) (s k : ℕ) (hk : 1 ≤ k) {y : ℝ}
    (hy : y ∈ Set.Icc M.vlo M.vhi) :
    M.piTilde s (k - 1) 0 ≤ M.piTilde s k (y ::ₘ 0) := by
  rw [piTilde_eq, piTilde_eq]
  refine CE_mono M s _ (fun C hC => ?_) (valueAux_le' M _ k _ (InI_cons hy (InI_zero M)))
  simp only [Multiset.cons_add, zero_add]
  have h1 := valueAux_mono_k M (M.T + 1 - s) (k - 1) C hC
  rw [Nat.sub_add_cancel hk] at h1
  exact h1.trans (valueAux_mono_add M _ k C y hC hy)

theorem piTilde_vhi_le (M : Model) (s k : ℕ) (hk : 1 ≤ k) :
    M.piTilde s k (M.vhi ::ₘ 0) ≤ M.m M.vhi + M.piTilde s (k - 1) 0 := by
  rw [piTilde_eq, piTilde_eq]
  have hmv := mvhi_pos M
  refine (CE_mono M s (((k - 1 : ℕ) : ℝ) * M.m M.vhi + M.m M.vhi)
      (h := fun C => M.valueAux (M.T + 1 - s) (k - 1) (0 + C) + M.m M.vhi)
      (fun C hC => ?_) (fun C hC => ?_)).trans ?_
  · simp only [Multiset.cons_add, zero_add]
    have := valueAux_top_le M (M.T + 1 - s) k C hC hk
    linarith
  · have := valueAux_le' M (M.T + 1 - s) (k - 1) 0 (InI_zero M) C hC
    linarith
  · have := CE_add_const M s (g := fun C => M.valueAux (M.T + 1 - s) (k - 1) (0 + C))
      (M.m M.vhi) _ hmv.le (valueAux_le' M _ _ _ (InI_zero M))
    linarith

theorem deltaPi_lip (M : Model) (t k : ℕ) {y y' : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hy' : y' ∈ Set.Icc M.vlo M.vhi) (hyy : y ≤ y') :
    (1 - M.δ) * (M.m y' - M.m y) ≤ M.deltaPi t k y' 0 - M.deltaPi t k y 0 ∧
    M.deltaPi t k y' 0 - M.deltaPi t k y 0 ≤ M.m y' - M.m y := by
  rw [deltaPi_eq, deltaPi_eq]
  obtain ⟨h1, h2⟩ := piTilde_single_lip M (t + 1) k hy hy' hyy
  have hδ0 := M.δ_pos
  have hδ1 := M.δ_lt_one
  constructor <;> nlinarith

theorem deltaPi_strictMonoOn (M : Model) (t k : ℕ) :
    StrictMonoOn (fun y => M.deltaPi t k y 0) (Set.Icc M.vlo M.vhi) := by
  intro y hy y' hy' hlt
  have h := (deltaPi_lip M t k hy hy' hlt.le).1
  have hm : M.m y < M.m y' := M.m_strictMonoOn hy hy' hlt
  have hδ1 := M.δ_lt_one
  have : 0 < (1 - M.δ) * (M.m y' - M.m y) := mul_pos (by linarith) (by linarith)
  simp only
  linarith

theorem deltaPi_continuousOn (M : Model) (t k : ℕ) :
    ContinuousOn (fun y => M.deltaPi t k y 0) (Set.Icc M.vlo M.vhi) := by
  intro y0 hy0
  have hm : ContinuousWithinAt M.m (Set.Icc M.vlo M.vhi) y0 :=
    M.m_contDiffOn.continuousOn y0 hy0
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero] at hm ⊢
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ hm
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [Real.dist_eq, Real.dist_eq]
  have hδ1 := M.δ_lt_one
  have hδ0 := M.δ_pos
  rcases le_total y y0 with h | h
  · obtain ⟨h1, h2⟩ := deltaPi_lip M t k hy hy0 h
    have hm' : M.m y ≤ M.m y0 := M.m_strictMonoOn.monotoneOn hy hy0 h
    rw [abs_of_nonpos (by nlinarith), abs_of_nonpos (by linarith)]
    linarith
  · obtain ⟨h1, h2⟩ := deltaPi_lip M t k hy0 hy h
    have hm' : M.m y0 ≤ M.m y := M.m_strictMonoOn.monotoneOn hy0 hy h
    rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by linarith)]
    linarith

theorem deltaPi_vlo_neg (M : Model) (t k : ℕ) (hk : 1 ≤ k) : M.deltaPi t k M.vlo 0 < 0 := by
  rw [deltaPi_eq]
  have h := piTilde_single_ge M (t + 1) k hk (y := M.vlo) ⟨le_rfl, M.vlo_lt_vhi.le⟩
  have hδ0 := M.δ_pos
  have hm := M.m_vlo_neg
  have : M.m M.vlo = marginalRevenueOf M.f M.vlo := rfl
  nlinarith

theorem deltaPi_vhi_pos (M : Model) (t k : ℕ) (hk : 1 ≤ k) : 0 < M.deltaPi t k M.vhi 0 := by
  rw [deltaPi_eq]
  have h := piTilde_vhi_le M (t + 1) k hk
  have hδ0 := M.δ_pos
  have hδ1 := M.δ_lt_one
  have hm := mvhi_pos M
  nlinarith

/-- Theorem 1, root part: the cutoff lies in `[v̲, v̄]`, is a root of `ΔΠ^k_t(·, ∅)`, and the only one. -/
theorem cutoff_spec (M : Model) (t k : ℕ) (hk : 1 ≤ k) :
    M.cutoff t k ∈ Set.Icc M.vlo M.vhi ∧ M.deltaPi t k (M.cutoff t k) 0 = 0 ∧
    ∀ y ∈ Set.Icc M.vlo M.vhi, M.deltaPi t k y 0 = 0 → y = M.cutoff t k := by
  have hc := deltaPi_continuousOn M t k
  have hsm := deltaPi_strictMonoOn M t k
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc M.vlo_lt_vhi.le hc
    ⟨(deltaPi_vlo_neg M t k hk).le, (deltaPi_vhi_pos M t k hk).le⟩
  have hset : {y | y ∈ Set.Icc M.vlo M.vhi ∧ 0 ≤ M.deltaPi t k y 0} = Set.Icc x M.vhi := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hy, hy0⟩
      refine ⟨?_, hy.2⟩
      by_contra hlt
      push Not at hlt
      have := hsm hy hx hlt
      simp only at this hx0
      linarith
    · rintro ⟨hxy, hyv⟩
      have hy : y ∈ Set.Icc M.vlo M.vhi := ⟨hx.1.trans hxy, hyv⟩
      refine ⟨⟨hy.1, hy.2⟩, ?_⟩
      have := hsm.monotoneOn hx hy hxy
      simp only at this hx0
      linarith
  have hcut : M.cutoff t k = x := by
    unfold Model.cutoff
    rw [hset, csInf_Icc hx.2]
  rw [hcut]
  refine ⟨hx, hx0, fun y hy hy0 => hsm.injOn hy hx ?_⟩
  simp only [hy0, hx0]

/-- H3: the marginal revenue at the cutoff is nonnegative. -/
theorem m_cutoff_nonneg (M : Model) (t k : ℕ) (hk : 1 ≤ k) : 0 ≤ M.m (M.cutoff t k) := by
  obtain ⟨hx, hx0, -⟩ := cutoff_spec M t k hk
  rw [deltaPi_eq] at hx0
  have h := piTilde_single_ge M (t + 1) k hk hx
  have hδ0 := M.δ_pos
  nlinarith


/-! ## Part A (session 3): sell-top decomposition, zero units, measurability infrastructure. -/

theorem valueAux_k_zero (M : Model) : ∀ r S, M.valueAux r 0 S = 0 := by
  intro r
  induction r with
  | zero => intro S; rfl
  | succ r ih =>
    intro S
    refine le_antisymm ?_ (valueAux_nonneg M _ _ _)
    rw [valueAux_succ]
    refine Finset.sup'_le _ _ fun j hj => ?_
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simp only [sumTop_zero, zero_add, Nat.sub_zero, ih]
    rw [CE_const M _ 0 le_rfl, mul_zero]

theorem sumTop_cons_top (M : Model) (y : ℝ) (S : Multiset ℝ) (h : ∀ s ∈ S, s ≤ y) (j : ℕ) :
    M.sumTop (j + 1) (y ::ₘ S) = M.m y + M.sumTop j S := by
  unfold Model.sumTop; rw [sortDesc_cons_top y S h]; simp

theorem dropTop_cons_top (y : ℝ) (S : Multiset ℝ) (h : ∀ s ∈ S, s ≤ y) (j : ℕ) :
    dropTop (j + 1) (y ::ₘ S) = dropTop j S := by
  unfold dropTop; rw [sortDesc_cons_top y S h]; simp

/-- Bellman equation with the top buyer split off: wait, or sell to the top buyer first. -/
theorem valueAux_succ_top (M : Model) (r k : ℕ) (hk : 1 ≤ k) (y : ℝ) (S : Multiset ℝ)
    (h : ∀ s ∈ S, s ≤ y) :
    M.valueAux (r + 1) k (y ::ₘ S) = max (M.δ * M.cohortExp (M.T + 1 - r)
        (fun C => M.valueAux r k (y ::ₘ S + C))) (M.m y + M.valueAux (r + 1) (k - 1) S) := by
  apply le_antisymm
  · rw [valueAux_succ]
    refine Finset.sup'_le _ _ fun j hj => ?_
    rcases j with _ | j
    · refine le_max_of_le_left (le_of_eq ?_)
      simp [sumTop_zero, dropTop_zero]
    · refine le_max_of_le_right ?_
      rw [sumTop_cons_top M y S h, dropTop_cons_top y S h, add_assoc]
      rw [add_le_add_iff_left, valueAux_succ]
      have hj' : j ∈ Finset.range (min (k - 1) (Multiset.card S) + 1) := by
        simp only [Finset.mem_range, Multiset.card_cons, Nat.lt_succ_iff, le_min_iff] at hj ⊢
        omega
      have hkj : k - (j + 1) = k - 1 - j := by omega
      rw [hkj]
      exact Finset.le_sup' (fun j => M.sumTop j S + M.δ * M.cohortExp (M.T + 1 - r)
          (fun C => M.valueAux r (k - 1 - j) (dropTop j S + C))) hj'
  · refine max_le ?_ ?_
    · rw [valueAux_succ]
      refine Finset.le_sup'_of_le _ (b := 0) (by simp) (le_of_eq ?_)
      simp [sumTop_zero, dropTop_zero]
    · rw [← le_sub_iff_add_le', valueAux_succ (r := r) (k := k - 1)]
      refine Finset.sup'_le _ _ fun j hj => ?_
      rw [le_sub_iff_add_le', valueAux_succ]
      have hj' : j + 1 ∈ Finset.range (min k (Multiset.card (y ::ₘ S)) + 1) := by
        simp only [Finset.mem_range, Multiset.card_cons, Nat.lt_succ_iff, le_min_iff] at hj ⊢
        omega
      refine Finset.le_sup'_of_le _ hj' (le_of_eq ?_)
      rw [sumTop_cons_top M y S h, dropTop_cons_top y S h]
      have hkj : k - (j + 1) = k - 1 - j := by omega
      rw [hkj]; ring

/-! ### Measurability -/

theorem f_measurable (M : Model) : Measurable M.f := by
  classical
  have h : M.f = Set.piecewise (Set.Icc M.vlo M.vhi) M.f (fun _ => 0) := by
    funext v
    by_cases hv : v ∈ Set.Icc M.vlo M.vhi
    · simp [Set.piecewise, hv]
    · simp [Set.piecewise, hv, M.f_eq_zero v hv]
  rw [h]
  exact ContinuousOn.measurable_piecewise M.f_continuousOn continuousOn_const measurableSet_Icc

theorem cdf_monotone (M : Model) : Monotone (cdfOf M.f) := by
  intro v w hvw
  unfold cdfOf
  apply ENNReal.toReal_mono
  · exact ne_top_of_le_ne_top (by rw [M.f_total]; exact ENNReal.one_ne_top)
      (setLIntegral_le_lintegral _ _)
  · exact lintegral_mono_set (Set.Iic_subset_Iic.mpr hvw)

theorem m_measurable (M : Model) : Measurable M.m := by
  have h1 : Measurable (cdfOf M.f) := (cdf_monotone M).measurable
  show Measurable (fun v => v - (1 - cdfOf M.f v) / M.f v)
  exact measurable_id.sub ((measurable_const.sub h1).div (f_measurable M))

theorem measurableSet_sort_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurableSet {x : Fin n → ℝ | Tuple.sort x = σ} := by
  have h : {x : Fin n → ℝ | Tuple.sort x = σ} =
      (⋂ i, ⋂ j, {x : Fin n → ℝ | i ≤ j → x (σ i) ≤ x (σ j)}) ∩
      (⋂ i, ⋂ j, {x : Fin n → ℝ | i < j → x (σ i) = x (σ j) → σ i < σ j}) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [eq_comm, Tuple.eq_sort_iff]
    rfl
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  · by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
    · simp [hij]
  · by_cases hij : i < j
    · by_cases hs : σ i < σ j
      · simp [hs]
      · simp only [hij, hs, true_implies, imp_false]
        exact (measurableSet_eq_fun (f := fun x : Fin n → ℝ => x (σ i)) (g := fun x => x (σ j))
          (measurable_pi_apply _) (measurable_pi_apply _)).compl
    · simp [hij]

/-- The values of `y` sorted in decreasing order. -/
noncomputable def sdesc {n : ℕ} (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => y (Tuple.sort y (Fin.rev i))

theorem measurable_sdesc (n : ℕ) : Measurable (sdesc : (Fin n → ℝ) → Fin n → ℝ) := by
  classical
  refine measurable_pi_lambda _ fun i => ?_
  have h : (fun y : Fin n → ℝ => sdesc y i) = fun y => ∑ σ : Equiv.Perm (Fin n),
      if Tuple.sort y = σ then y (σ (Fin.rev i)) else 0 := by
    funext y
    rw [Finset.sum_ite_eq]
    simp [sdesc]
  rw [h]
  exact Finset.measurable_sum _ fun σ _ =>
    Measurable.ite (measurableSet_sort_eq σ) (measurable_pi_apply _) measurable_const

theorem sortDesc_cohort {n : ℕ} (y : Fin n → ℝ) : sortDesc (cohort y) = List.ofFn (sdesc y) := by
  unfold sortDesc cohort
  apply List.Perm.eq_of_pairwise' (r := (· ≥ ·))
  · exact Multiset.pairwise_sort _ _
  · rw [List.pairwise_ofFn]
    intro i j hij
    have := Tuple.monotone_sort y (Fin.rev_le_rev.mpr hij.le)
    exact this
  · rw [← Multiset.coe_eq_coe, Multiset.sort_eq]
    have : sdesc y = y ∘ (Fin.revPerm.trans (Tuple.sort y)) := by
      funext i; simp [sdesc, Fin.revPerm]
    rw [this, Multiset.coe_eq_coe]
    exact ((Equiv.Perm.ofFn_comp_perm _ y)).symm


/-! ## Part B: measurability of the value function and additivity of cohort expectations. -/

theorem ofFn_take_eq {n : ℕ} (z : Fin n → ℝ) (j : ℕ) :
    (List.ofFn z).take j =
      List.ofFn (fun i : Fin (min j n) => z ⟨i, lt_of_lt_of_le i.isLt (min_le_right _ _)⟩) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp [List.getElem_take, List.getElem_ofFn]

theorem ofFn_drop_eq {n : ℕ} (z : Fin n → ℝ) (j : ℕ) :
    (List.ofFn z).drop j =
      List.ofFn (fun i : Fin (n - j) => z ⟨i + j, by have := i.isLt; omega⟩) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp [List.getElem_drop, List.getElem_ofFn, Nat.add_comm]

theorem sumTop_cohort (M : Model) {n : ℕ} (y : Fin n → ℝ) (j : ℕ) :
    M.sumTop j (cohort y) =
      ∑ i : Fin (min j n), M.m (sdesc y ⟨i, lt_of_lt_of_le i.isLt (min_le_right _ _)⟩) := by
  unfold Model.sumTop
  rw [sortDesc_cohort, ofFn_take_eq, List.map_ofFn, List.sum_ofFn]
  rfl

theorem dropTop_cohort {n : ℕ} (y : Fin n → ℝ) (j : ℕ) :
    dropTop j (cohort y) =
      cohort (fun i : Fin (n - j) => sdesc y ⟨i + j, by have := i.isLt; omega⟩) := by
  unfold dropTop
  rw [sortDesc_cohort, ofFn_drop_eq]
  rfl

theorem cohort_append {a b : ℕ} (x : Fin a → ℝ) (y : Fin b → ℝ) :
    cohort x + cohort y = cohort (Fin.append x y) := by
  unfold cohort
  rw [List.ofFn_fin_append, Multiset.coe_add]

theorem cohort_toList (B : Multiset ℝ) : cohort (fun i : Fin B.toList.length => B.toList.get i) = B := by
  unfold cohort
  rw [List.ofFn_get, Multiset.coe_toList]

theorem measurable_append (a b : ℕ) :
    Measurable (fun p : (Fin a → ℝ) × (Fin b → ℝ) => Fin.append p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  induction i using Fin.addCases with
  | left i => simp only [Fin.append_left]; exact (measurable_pi_apply i).comp measurable_fst
  | right i => simp only [Fin.append_right]; exact (measurable_pi_apply i).comp measurable_snd

/-- Parametric cohort expectation of a measurable symmetric function is measurable. -/
theorem measurable_CE (M : Model) (s : ℕ) {g : Multiset ℝ → ℝ}
    (hg : ∀ n, Measurable (fun x : Fin n → ℝ => g (cohort x)))
    {a b : ℕ} {h : (Fin a → ℝ) → (Fin b → ℝ)} (hh : Measurable h) :
    Measurable (fun y => M.cohortExp s (fun C => g (cohort (h y) + C))) := by
  unfold Model.cohortExp Model.cohortLIntegral
  refine ENNReal.measurable_toReal.comp (Measurable.ennreal_tsum fun n => measurable_const.mul ?_)
  simp_rw [cohort_append]
  have hF : Measurable (fun p : (Fin a → ℝ) × (Fin n → ℝ) =>
      ENNReal.ofReal (g (cohort (Fin.append (h p.1) p.2)))) :=
    ((hg _).comp ((measurable_append b n).comp ((hh.comp measurable_fst).prodMk measurable_snd))).ennreal_ofReal
  exact hF.lintegral_prod_right'

/-- Every value function is a measurable function of the buyers' values. -/
theorem vgood (M : Model) : ∀ r k n, Measurable (fun y : Fin n → ℝ => M.valueAux r k (cohort y)) := by
  intro r
  induction r with
  | zero => intro k n; simp only [valueAux_zero]; exact measurable_const
  | succ r ih =>
    intro k n
    have hcard : ∀ y : Fin n → ℝ, Multiset.card (cohort y) = n := by intro y; simp [cohort]
    have e : ∀ y : Fin n → ℝ, M.valueAux (r + 1) k (cohort y) =
        (Finset.range (min k n + 1)).sup' Finset.nonempty_range_add_one (fun j =>
          M.sumTop j (cohort y) + M.δ * M.cohortExp (M.T + 1 - r)
            (fun C => M.valueAux r (k - j) (dropTop j (cohort y) + C))) := by
      intro y; rw [valueAux_succ, hcard]
    simp_rw [e]
    refine Finset.measurable_range_sup'' (f := fun j y => M.sumTop j (cohort y) + M.δ *
      M.cohortExp (M.T + 1 - r) (fun C => M.valueAux r (k - j) (dropTop j (cohort y) + C)))
      fun j _ => ?_
    refine Measurable.add ?_ (measurable_const.mul ?_)
    · simp_rw [sumTop_cohort]
      exact Finset.measurable_sum _ fun i _ =>
        (m_measurable M).comp ((measurable_pi_apply _).comp (measurable_sdesc n))
    · simp_rw [dropTop_cohort]
      refine measurable_CE M _ (ih (k - j)) (h := fun y : Fin n → ℝ =>
        fun i : Fin (n - j) => sdesc y ⟨i + j, by have := i.isLt; omega⟩) ?_
      exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp (measurable_sdesc n)

theorem vgood_add (M : Model) (r k : ℕ) (B : Multiset ℝ) (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => M.valueAux r k (B + cohort x)) := by
  have e : ∀ x : Fin n → ℝ, M.valueAux r k (B + cohort x) =
      M.valueAux r k (cohort (Fin.append (fun i : Fin B.toList.length => B.toList.get i) x)) := by
    intro x; rw [← cohort_append, cohort_toList]
  simp_rw [e]
  exact (vgood M r k _).comp ((measurable_append _ n).comp (measurable_const.prodMk measurable_id))

/-- Additivity of the cohort expectation when one summand is measurable. -/
theorem CE_add (M : Model) (s : ℕ) {f g : Multiset ℝ → ℝ}
    (hf : ∀ n, Measurable (fun x : Fin n → ℝ => f (cohort x)))
    (hf0 : ∀ C, InI M C → 0 ≤ f C) (hg0 : ∀ C, InI M C → 0 ≤ g C)
    (Bf Bg : ℝ) (hfB : ∀ C, InI M C → f C ≤ Bf) (hgB : ∀ C, InI M C → g C ≤ Bg) :
    M.cohortExp s (fun C => f C + g C) = M.cohortExp s f + M.cohortExp s g := by
  unfold Model.cohortExp
  rw [← ENNReal.toReal_add (CL_ne_top M s Bf hfB) (CL_ne_top M s Bg hgB)]
  congr 1
  unfold Model.cohortLIntegral
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun n => ?_
  rw [← mul_add]
  congr 1
  rw [← lintegral_add_left ((hf n).ennreal_ofReal)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_cohort M n] with x hx
  exact ENNReal.ofReal_add (hf0 _ hx) (hg0 _ hx)


/-! ## Part C: algebra of one level of the value function under the invariants R1, Gdec, Gsup. -/

theorem exists_top (Z : Multiset ℝ) (hZ : Z ≠ 0) : ∃ z A, Z = z ::ₘ A ∧ ∀ a ∈ A, a ≤ z := by
  have h := coe_sortDesc Z
  have hp := pairwise_sortDesc Z
  cases hL : sortDesc Z with
  | nil => rw [hL] at h; exact absurd (by simpa using h.symm) hZ
  | cons z L =>
    refine ⟨z, L, ?_, ?_⟩
    · rw [← h, hL, ← Multiset.cons_coe]
    · rw [hL, List.pairwise_cons] at hp
      intro a ha; exact hp.1 a (Multiset.mem_coe.mp ha)

section Alg

variable (V : ℕ → Multiset ℝ → ℝ)

/-- `G(k,y) = V(k,{y}) - V(k-1,∅)`. -/
def GG (k : ℕ) (y : ℝ) : ℝ := V k (y ::ₘ 0) - V (k - 1) 0
/-- `D(k,y,Z) = V(k, y::Z) - V(k-1, Z)`. -/
def DD (k : ℕ) (y : ℝ) (Z : Multiset ℝ) : ℝ := V k (y ::ₘ Z) - V (k - 1) Z
/-- `ΔG(k,y) = G(k,y) - G(k-1,y)`. -/
def dG (k : ℕ) (y : ℝ) : ℝ := GG V k y - GG V (k - 1) y

/-- The three invariants of one level. -/
structure Inv (M : Model) : Prop where
  R1 : ∀ k y S, y ∈ Set.Icc M.vlo M.vhi → InI M S → (∀ s ∈ S, s ≤ y) →
    V k (y ::ₘ S) = GG V k y + V (k - 1) S
  Gdec : ∀ k y, 2 ≤ k → y ∈ Set.Icc M.vlo M.vhi → GG V k y ≤ GG V (k - 1) y
  Gsup : ∀ k y y', y ∈ Set.Icc M.vlo M.vhi → y' ∈ Set.Icc M.vlo M.vhi → y ≤ y' →
    dG V k y ≤ dG V k y'

variable {V} {M : Model}

theorem DD_eq_GG (I : Inv V M) (k : ℕ) {y : ℝ} {Z : Multiset ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hZ : InI M Z) (h : ∀ z ∈ Z, z ≤ y) : DD V k y Z = GG V k y := by
  unfold DD; rw [I.R1 k y Z hy hZ h]; ring

theorem DD_cons (I : Inv V M) (k : ℕ) {y z : ℝ} {A : Multiset ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hz : z ∈ Set.Icc M.vlo M.vhi) (hA : InI M A) (hyz : y ≤ z) (hAz : ∀ a ∈ A, a ≤ z) :
    DD V k y (z ::ₘ A) = dG V k z + DD V (k - 1) y A := by
  unfold DD dG
  have hs : ∀ s ∈ y ::ₘ A, s ≤ z := by
    intro s hs
    rcases Multiset.mem_cons.mp hs with rfl | h
    · exact hyz
    · exact hAz s h
  rw [Multiset.cons_swap y z A, I.R1 k z (y ::ₘ A) hz (InI_cons hy hA) hs, I.R1 (k - 1) z A hz hA hAz]
  ring

/-- Decomposition used by all inductions: either every buyer of `Z` is `≤ y`, or the top buyer `z > y`. -/
theorem top_or_le (Z : Multiset ℝ) (y : ℝ) (hZ : ¬ ∀ z ∈ Z, z ≤ y) :
    ∃ z A, Z = z ::ₘ A ∧ (∀ a ∈ A, a ≤ z) ∧ y < z := by
  have hZ0 : Z ≠ 0 := by rintro rfl; exact hZ (by simp)
  obtain ⟨z, A, rfl, hA⟩ := exists_top Z hZ0
  refine ⟨z, A, rfl, hA, ?_⟩
  by_contra hzy
  push Not at hzy
  apply hZ
  intro x hx
  rcases Multiset.mem_cons.mp hx with rfl | h
  · exact hzy
  · exact (hA x h).trans hzy

/-- I1: buyers below `y` do not affect `D(k,y,·)`. -/
theorem DD_add_low (I : Inv V M) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) {S : Multiset ℝ}
    (hS : InI M S) (hSy : ∀ s ∈ S, s ≤ y) :
    ∀ n (A : Multiset ℝ) k, Multiset.card A = n → InI M A → DD V k y (A + S) = DD V k y A := by
  intro n
  induction n with
  | zero =>
    intro A k hA _
    rw [Multiset.card_eq_zero.mp hA, zero_add, DD_eq_GG I k hy hS hSy,
      DD_eq_GG I k hy (InI_zero M) (by simp)]
  | succ n ih =>
    intro A k hA hAI
    by_cases hle : ∀ a ∈ A, a ≤ y
    · have hAS : ∀ x ∈ A + S, x ≤ y := by
        intro x hx
        rcases Multiset.mem_add.mp hx with h | h
        · exact hle x h
        · exact hSy x h
      rw [DD_eq_GG I k hy (InI_add hAI hS) hAS, DD_eq_GG I k hy hAI hle]
    · obtain ⟨z, A', rfl, hA', hyz⟩ := top_or_le A y hle
      have hz : z ∈ Set.Icc M.vlo M.vhi := hAI z (Multiset.mem_cons_self _ _)
      have hA'I : InI M A' := fun a ha => hAI a (Multiset.mem_cons_of_mem ha)
      have hzS : ∀ x ∈ A' + S, x ≤ z := by
        intro x hx
        rcases Multiset.mem_add.mp hx with h | h
        · exact hA' x h
        · exact (hSy x h).trans hyz.le
      rw [Multiset.cons_add, DD_cons I k hy hz (InI_add hA'I hS) hyz.le hzS,
        DD_cons I k hy hz hA'I hyz.le hA', ih A' (k - 1) (by simpa using hA) hA'I]

/-- P: `D(k,y,Z) - D(k-1,y,Z) ≤ ΔG(k,w)` for any `w` above `y` and `Z`. -/
theorem DD_diff_le (I : Inv V M) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) :
    ∀ n (Z : Multiset ℝ) k w, Multiset.card Z = n → InI M Z → w ∈ Set.Icc M.vlo M.vhi → y ≤ w →
      (∀ z ∈ Z, z ≤ w) → DD V k y Z - DD V (k - 1) y Z ≤ dG V k w := by
  intro n
  induction n with
  | zero =>
    intro Z k w hZ hZI hw hyw _
    have h0 : ∀ z ∈ Z, z ≤ y := by rw [Multiset.card_eq_zero.mp hZ]; simp
    rw [DD_eq_GG I k hy hZI h0, DD_eq_GG I (k - 1) hy hZI h0]
    exact I.Gsup k y w hy hw hyw
  | succ n ih =>
    intro Z k w hZ hZI hw hyw hZw
    by_cases hle : ∀ z ∈ Z, z ≤ y
    · rw [DD_eq_GG I k hy hZI hle, DD_eq_GG I (k - 1) hy hZI hle]
      exact I.Gsup k y w hy hw hyw
    · obtain ⟨z, A, rfl, hA, hyz⟩ := top_or_le Z y hle
      have hz : z ∈ Set.Icc M.vlo M.vhi := hZI z (Multiset.mem_cons_self _ _)
      have hAI : InI M A := fun a ha => hZI a (Multiset.mem_cons_of_mem ha)
      rw [DD_cons I k hy hz hAI hyz.le hA, DD_cons I (k - 1) hy hz hAI hyz.le hA]
      have h1 := ih A (k - 1) z (by simpa using hZ) hAI hz hyz.le hA
      have h2 := I.Gsup k z w hz hw (hZw z (Multiset.mem_cons_self _ _))
      linarith

/-- K: `D(k,y,Z) ≤ D(k-1,y,Z)` for `k ≥ 2` (concavity in the number of units). -/
theorem DD_anti_k (I : Inv V M) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) (Z : Multiset ℝ)
    (hZI : InI M Z) (k : ℕ) (hk : 2 ≤ k) : DD V k y Z ≤ DD V (k - 1) y Z := by
  have hv : M.vhi ∈ Set.Icc M.vlo M.vhi := ⟨M.vlo_lt_vhi.le, le_rfl⟩
  have h := DD_diff_le I hy _ Z k M.vhi rfl hZI hv hy.2 (fun z hz => (hZI z hz).2)
  have h2 := I.Gdec k M.vhi hk hv
  unfold dG at h
  linarith

/-- Q: `D(k,y,Z) - D(k-1,y,Z)` is nondecreasing in `y`. -/
theorem DD_diff_mono (I : Inv V M) {y y' : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hy' : y' ∈ Set.Icc M.vlo M.vhi) (hyy : y ≤ y') :
    ∀ n (Z : Multiset ℝ) k, Multiset.card Z = n → InI M Z →
      DD V k y Z - DD V (k - 1) y Z ≤ DD V k y' Z - DD V (k - 1) y' Z := by
  intro n
  induction n with
  | zero =>
    intro Z k hZ hZI
    have h0 : ∀ z ∈ Z, z ≤ y' := by rw [Multiset.card_eq_zero.mp hZ]; simp
    rw [DD_eq_GG I k hy' hZI h0, DD_eq_GG I (k - 1) hy' hZI h0]
    exact DD_diff_le I hy _ Z k y' rfl hZI hy' hyy h0
  | succ n ih =>
    intro Z k hZ hZI
    by_cases hle : ∀ z ∈ Z, z ≤ y'
    · rw [DD_eq_GG I k hy' hZI hle, DD_eq_GG I (k - 1) hy' hZI hle]
      exact DD_diff_le I hy _ Z k y' rfl hZI hy' hyy hle
    · obtain ⟨z, A, rfl, hA, hyz⟩ := top_or_le Z y' hle
      have hz : z ∈ Set.Icc M.vlo M.vhi := hZI z (Multiset.mem_cons_self _ _)
      have hAI : InI M A := fun a ha => hZI a (Multiset.mem_cons_of_mem ha)
      rw [DD_cons I k hy hz hAI (hyy.trans hyz.le) hA, DD_cons I (k - 1) hy hz hAI (hyy.trans hyz.le) hA,
        DD_cons I k hy' hz hAI hyz.le hA, DD_cons I (k - 1) hy' hz hAI hyz.le hA]
      have h1 := ih A (k - 1) (by simpa using hZ) hAI
      linarith

end Alg


/-! ## Part D: the invariants hold at every level (Theorem 1 core, no assumption on demand). -/

theorem CE_congr (M : Model) (s : ℕ) {f g : Multiset ℝ → ℝ} (h : ∀ C, InI M C → f C = g C) :
    M.cohortExp s f = M.cohortExp s g := by
  unfold Model.cohortExp
  rw [le_antisymm (CL_mono M s fun C hC => (h C hC).le) (CL_mono M s fun C hC => (h C hC).ge)]

theorem CE_VV (M : Model) (s r a b : ℕ) {A B : Multiset ℝ} (hA : InI M A) (hB : InI M B) :
    M.cohortExp s (fun C => M.valueAux r a (A + C) + M.valueAux r b (B + C)) =
      M.cohortExp s (fun C => M.valueAux r a (A + C)) +
        M.cohortExp s (fun C => M.valueAux r b (B + C)) :=
  CE_add M s (vgood_add M r a A) (fun C _ => valueAux_nonneg M _ _ _)
    (fun C _ => valueAux_nonneg M _ _ _) ((a : ℝ) * M.m M.vhi) ((b : ℝ) * M.m M.vhi)
    (valueAux_le' M r a A hA) (valueAux_le' M r b B hB)

theorem CE_four_le (M : Model) (s r a b c d : ℕ) {A B P Q : Multiset ℝ} (hA : InI M A)
    (hB : InI M B) (hP : InI M P) (hQ : InI M Q)
    (h : ∀ C, InI M C → M.valueAux r a (A + C) + M.valueAux r b (B + C) ≤
      M.valueAux r c (P + C) + M.valueAux r d (Q + C)) :
    M.cohortExp s (fun C => M.valueAux r a (A + C)) + M.cohortExp s (fun C => M.valueAux r b (B + C)) ≤
      M.cohortExp s (fun C => M.valueAux r c (P + C)) +
        M.cohortExp s (fun C => M.valueAux r d (Q + C)) := by
  rw [← CE_VV M s r a b hA hB, ← CE_VV M s r c d hP hQ]
  exact CE_mono M s ((c : ℝ) * M.m M.vhi + (d : ℝ) * M.m M.vhi) h
    (fun C hC => add_le_add (valueAux_le' M r c P hP C hC) (valueAux_le' M r d Q hQ C hC))

/-- The wait bracket at level `r + 1`. -/
noncomputable def WW (M : Model) (r k : ℕ) (Z : Multiset ℝ) : ℝ :=
  M.δ * M.cohortExp (M.T + 1 - r) (fun C => M.valueAux r k (Z + C))

/-- `Φ(k,y) = W(k,{y}) - W(k-1,∅)`. -/
noncomputable def Phi (M : Model) (r k : ℕ) (y : ℝ) : ℝ := WW M r k (y ::ₘ 0) - WW M r (k - 1) 0

theorem WW_zero_k (M : Model) (r : ℕ) (Z : Multiset ℝ) : WW M r 0 Z = 0 := by
  unfold WW; simp only [valueAux_k_zero]; rw [CE_const M _ 0 le_rfl, mul_zero]

theorem WW_le_V (M : Model) (r k : ℕ) (S : Multiset ℝ) : WW M r k S ≤ M.valueAux (r + 1) k S := by
  rw [valueAux_succ]
  refine Finset.le_sup'_of_le _ (b := 0) (by simp) (le_of_eq ?_)
  simp [WW, sumTop_zero, dropTop_zero]

theorem V_empty (M : Model) (r k : ℕ) : M.valueAux (r + 1) k 0 = WW M r k 0 := by
  refine le_antisymm ?_ (WW_le_V M r k 0)
  rw [valueAux_succ]
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hj0 : j = 0 := by simp at hj; omega
  subst hj0
  simp [WW, sumTop_zero, dropTop_zero]

theorem V_succ_top' (M : Model) (r k : ℕ) (y : ℝ) (S : Multiset ℝ) (h : ∀ s ∈ S, s ≤ y) :
    M.valueAux (r + 1) (k + 1) (y ::ₘ S) = max (WW M r (k + 1) (y ::ₘ S)) (M.m y + M.valueAux (r + 1) k S) :=
  valueAux_succ_top M r (k + 1) (by omega) y S h

theorem Phi_lip (M : Model) (r k : ℕ) {y y' : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hy' : y' ∈ Set.Icc M.vlo M.vhi) (hyy : y ≤ y') :
    Phi M r k y ≤ Phi M r k y' ∧ Phi M r k y' - Phi M r k y ≤ M.δ * (M.m y' - M.m y) := by
  unfold Phi WW
  set s := M.T + 1 - r
  have hd : 0 ≤ M.m y' - M.m y := sub_nonneg.mpr (M.m_strictMonoOn.monotoneOn hy hy' hyy)
  have hbd : ∀ z ∈ Set.Icc M.vlo M.vhi, ∀ C, InI M C →
      M.valueAux r k (z ::ₘ 0 + C) ≤ k * M.m M.vhi :=
    fun z hz => valueAux_le' M _ k _ (InI_cons hz (InI_zero M))
  have h1 : M.cohortExp s (fun C => M.valueAux r k (y ::ₘ 0 + C)) ≤
      M.cohortExp s (fun C => M.valueAux r k (y' ::ₘ 0 + C)) :=
    CE_mono M s _ (fun C hC => by
      simp only [Multiset.cons_add, zero_add]
      exact (valueAux_lip M _ k C y y' hC hy hy' hyy).1) (hbd y' hy')
  have h2 : M.cohortExp s (fun C => M.valueAux r k (y' ::ₘ 0 + C)) ≤
      M.cohortExp s (fun C => M.valueAux r k (y ::ₘ 0 + C)) + (M.m y' - M.m y) := by
    refine (CE_mono M s (k * M.m M.vhi + (M.m y' - M.m y))
      (h := fun C => M.valueAux r k (y ::ₘ 0 + C) + (M.m y' - M.m y))
      (fun C hC => by
        simp only [Multiset.cons_add, zero_add]
        exact (valueAux_lip M _ k C y y' hC hy hy' hyy).2)
      (fun C hC => by have := hbd y hy C hC; linarith)).trans ?_
    exact CE_add_const M s _ _ hd (hbd y hy)
  have hδ := M.δ_pos
  constructor
  · nlinarith
  · nlinarith

section Step

variable {M : Model} {r : ℕ}


theorem W_split (I : Inv (fun k S => M.valueAux r k S) M) (k : ℕ) {y : ℝ} {S : Multiset ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hS : InI M S) (hSy : ∀ s ∈ S, s ≤ y) :
    WW M r k (y ::ₘ S) = Phi M r k y + WW M r (k - 1) S := by
  have hyS : InI M (y ::ₘ S) := InI_cons hy hS
  have hy0 : InI M (y ::ₘ 0) := InI_cons hy (InI_zero M)
  have h1 := CE_four_le M (M.T + 1 - r) r k (k - 1) k (k - 1) hyS (InI_zero M) hy0 hS
    (fun C hC => by
      have := DD_add_low I hy hS hSy _ C k rfl hC
      simp only [DD] at this
      simp only [Multiset.cons_add, zero_add]
      rw [add_comm C S] at this
      linarith)
  have h2 := CE_four_le M (M.T + 1 - r) r k (k - 1) k (k - 1) hy0 hS hyS (InI_zero M)
    (fun C hC => by
      have := DD_add_low I hy hS hSy _ C k rfl hC
      simp only [DD] at this
      simp only [Multiset.cons_add, zero_add]
      rw [add_comm C S] at this
      linarith)
  unfold Phi WW
  have hδ := M.δ_pos
  nlinarith

theorem Phi_anti (I : Inv (fun k S => M.valueAux r k S) M) (k : ℕ) (hk : 2 ≤ k) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) :
    Phi M r k y ≤ Phi M r (k - 1) y := by
  have hy0 : InI M (y ::ₘ 0) := InI_cons hy (InI_zero M)
  have h := CE_four_le M (M.T + 1 - r) r k (k - 1 - 1) (k - 1) (k - 1) hy0 (InI_zero M) hy0 (InI_zero M)
    (fun C hC => by
      have := DD_anti_k I hy C hC k hk
      simp only [DD] at this
      simp only [Multiset.cons_add, zero_add]
      linarith)
  unfold Phi WW
  have hδ := M.δ_pos
  nlinarith

theorem Phi_Q (I : Inv (fun k S => M.valueAux r k S) M) (k : ℕ) {y y' : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hy' : y' ∈ Set.Icc M.vlo M.vhi) (hyy : y ≤ y') :
    Phi M r k y - Phi M r (k - 1) y ≤ Phi M r k y' - Phi M r (k - 1) y' := by
  have hy0 : InI M (y ::ₘ 0) := InI_cons hy (InI_zero M)
  have hy0' : InI M (y' ::ₘ 0) := InI_cons hy' (InI_zero M)
  have h := CE_four_le M (M.T + 1 - r) r k (k - 1) k (k - 1) hy0 hy0' hy0' hy0
    (fun C hC => by
      have := DD_diff_mono I hy hy' hyy _ C k rfl hC
      simp only [DD] at this
      simp only [Multiset.cons_add, zero_add]
      linarith)
  unfold Phi WW
  have hδ := M.δ_pos
  nlinarith

/-- C(k): if selling is strictly better with `k` units and buyers `S ≤ y`, then selling `y` is optimal
with `k + 1` units. -/
theorem gain_imp (I : Inv (fun k S => M.valueAux r k S) M) : ∀ k (y : ℝ) (S : Multiset ℝ), y ∈ Set.Icc M.vlo M.vhi → InI M S →
    (∀ s ∈ S, s ≤ y) → WW M r k S < M.valueAux (r + 1) k S → Phi M r (k + 1) y ≤ M.m y := by
  intro k
  induction k with
  | zero =>
    intro y S _ _ _ h
    rw [WW_zero_k, valueAux_k_zero] at h
    exact absurd h (lt_irrefl _)
  | succ k ih =>
    intro y S hy hS hSy h
    have hS0 : S ≠ 0 := by
      rintro rfl
      rw [V_empty] at h
      exact lt_irrefl _ h
    obtain ⟨s1, S', rfl, hS'⟩ := exists_top S hS0
    have hs1 : s1 ∈ Set.Icc M.vlo M.vhi := hS s1 (Multiset.mem_cons_self _ _)
    have hS'I : InI M S' := fun a ha => hS a (Multiset.mem_cons_of_mem ha)
    have hs1y : s1 ≤ y := hSy s1 (Multiset.mem_cons_self _ _)
    rw [V_succ_top' M r k s1 S' hS'] at h
    have h2 : WW M r (k + 1) (s1 ::ₘ S') < M.m s1 + M.valueAux (r + 1) k S' := by
      rcases lt_max_iff.mp h with h | h
      · exact absurd h (lt_irrefl _)
      · exact h
    rw [W_split I (k + 1) hs1 hS'I hS'] at h2
    have h2' : Phi M r (k + 1) s1 + WW M r k S' < M.m s1 + M.valueAux (r + 1) k S' := h2
    have hm1 : Phi M r (k + 1) s1 ≤ M.m s1 := by
      by_cases hg : WW M r k S' < M.valueAux (r + 1) k S'
      · exact ih s1 S' hs1 hS'I hS' hg
      · push Not at hg; linarith [h2']
    have ha : Phi M r (k + 2) s1 ≤ Phi M r (k + 1) s1 := Phi_anti I (k + 2) (by omega) hs1
    have hl := (Phi_lip M r (k + 2) hs1 hy hs1y).2
    have hmy : M.m s1 ≤ M.m y := M.m_strictMonoOn.monotoneOn hs1 hy hs1y
    have hδ := M.δ_lt_one
    have hδ0 := M.δ_pos
    nlinarith

theorem GG_succ (k : ℕ) (y : ℝ) :
    GG (fun k S => M.valueAux (r + 1) k S) (k + 1) y = max (Phi M r (k + 1) y) (M.m y) := by
  unfold GG
  simp only [Nat.add_sub_cancel]
  rw [V_succ_top' M r k y 0 (by simp), V_empty]
  unfold Phi
  simp only [Nat.add_sub_cancel]
  rw [← max_sub_sub_right]
  congr 1 <;> ring

theorem step_R1 (I : Inv (fun k S => M.valueAux r k S) M) : ∀ k y S, y ∈ Set.Icc M.vlo M.vhi → InI M S → (∀ s ∈ S, s ≤ y) →
    M.valueAux (r + 1) k (y ::ₘ S) = GG (fun k S => M.valueAux (r + 1) k S) k y + M.valueAux (r + 1) (k - 1) S := by
  intro k y S hy hS hSy
  rcases k with _ | k
  · simp [GG, valueAux_k_zero]
  · rw [GG_succ, V_succ_top' M r k y S hSy, W_split I (k + 1) hy hS hSy]
    simp only [Nat.add_sub_cancel]
    have hW := WW_le_V M r k S
    by_cases hg : WW M r k S < M.valueAux (r + 1) k S
    · have hp := gain_imp I k y S hy hS hSy hg
      rw [max_eq_right (by linarith), max_eq_right hp]
    · push Not at hg
      have he : M.valueAux (r + 1) k S = WW M r k S := le_antisymm hg hW
      rw [he, ← max_add_add_right]

theorem max_diff_mono {a b c a' b' c' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b')
    (h1 : a - b ≤ a' - b') (h2 : c - b ≤ c' - b') :
    max a c - max b c ≤ max a' c' - max b' c' := by
  rw [max_def, max_def, max_def, max_def]
  split_ifs <;> linarith

theorem step_inv (I : Inv (fun k S => M.valueAux r k S) M) : Inv (fun k S => M.valueAux (r + 1) k S) M where
  R1 := step_R1 I
  Gdec := by
    intro k y hk hy
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    show GG (fun k S => M.valueAux (r + 1) k S) (k + 1 + 1) y ≤ GG (fun k S => M.valueAux (r + 1) k S) (k + 1 + 1 - 1) y
    rw [Nat.add_sub_cancel, GG_succ, GG_succ]
    have : Phi M r (k + 2) y ≤ Phi M r (k + 1) y := Phi_anti I (k + 2) (by omega) hy
    exact max_le_max this le_rfl
  Gsup := by
    intro k y y' hy hy' hyy
    have hmy : M.m y ≤ M.m y' := M.m_strictMonoOn.monotoneOn hy hy' hyy
    rcases k with _ | _ | k
    · simp [dG]
    · unfold dG
      have h0 : ∀ z, GG (fun k S => M.valueAux (r + 1) k S) 0 z = 0 := fun z => by simp [GG, valueAux_k_zero]
      show GG (fun k S => M.valueAux (r + 1) k S) (0 + 1) y - GG (fun k S => M.valueAux (r + 1) k S) 0 y ≤ GG (fun k S => M.valueAux (r + 1) k S) (0 + 1) y' - GG (fun k S => M.valueAux (r + 1) k S) 0 y'
      rw [h0, h0, GG_succ, GG_succ]
      have := (Phi_lip M r 1 hy hy' hyy).1
      linarith [max_le_max this hmy]
    · unfold dG
      show GG (fun k S => M.valueAux (r + 1) k S) (k + 1 + 1) y - GG (fun k S => M.valueAux (r + 1) k S) (k + 1 + 1 - 1) y ≤ GG (fun k S => M.valueAux (r + 1) k S) (k + 1 + 1) y' - GG (fun k S => M.valueAux (r + 1) k S) (k + 1 + 1 - 1) y'
      rw [Nat.add_sub_cancel, GG_succ, GG_succ, GG_succ, GG_succ]
      have ha : Phi M r (k + 2) y ≤ Phi M r (k + 1) y := Phi_anti I (k + 2) (by omega) hy
      have ha' : Phi M r (k + 2) y' ≤ Phi M r (k + 1) y' := Phi_anti I (k + 2) (by omega) hy'
      have hq : Phi M r (k + 2) y - Phi M r (k + 1) y ≤ Phi M r (k + 2) y' - Phi M r (k + 1) y' :=
        Phi_Q I (k + 2) hy hy' hyy
      have hl := (Phi_lip M r (k + 1) hy hy' hyy).2
      have hδ := M.δ_lt_one
      have hδ0 := M.δ_pos
      have hdm : M.δ * (M.m y' - M.m y) ≤ M.m y' - M.m y := by nlinarith
      exact max_diff_mono ha ha' hq (by linarith)

end Step

theorem inv_zero (M : Model) : Inv (fun k S => M.valueAux 0 k S) M where
  R1 := by intro k y S _ _ _; simp [GG, valueAux_zero]
  Gdec := by intro k y _ _; simp [GG, valueAux_zero]
  Gsup := by intro k y y' _ _ _; simp [dG, GG, valueAux_zero]

theorem inv_all (M : Model) : ∀ r, Inv (fun k S => M.valueAux r k S) M := by
  intro r
  induction r with
  | zero => exact inv_zero M
  | succ r ih => exact step_inv ih


/-! ## Part E: truncation, the one-period-look-ahead quantities, N1, N2, strict monotonicity of DPi. -/

theorem R1v (M : Model) (r k : ℕ) {y : ℝ} {S : Multiset ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hS : InI M S) (hSy : ∀ s ∈ S, s ≤ y) :
    M.valueAux r k (y ::ₘ S) = GG (fun k S => M.valueAux r k S) k y + M.valueAux r (k - 1) S :=
  (inv_all M r).R1 k y S hy hS hSy

theorem sortDesc_coe_sorted (L : List ℝ) (h : L.Pairwise (· ≥ ·)) : sortDesc (L : Multiset ℝ) = L := by
  unfold sortDesc
  apply List.Perm.eq_of_pairwise' (r := (· ≥ ·))
  · exact Multiset.pairwise_sort _ _
  · exact h
  · rw [← Multiset.coe_eq_coe, Multiset.sort_eq]

theorem mem_take_sortDesc {S : Multiset ℝ} {j : ℕ} {a : ℝ}
    (ha : a ∈ ((((sortDesc S).take j : List ℝ)) : Multiset ℝ)) : a ∈ S :=
  mem_sortDesc.mp (List.mem_of_mem_take (Multiset.mem_coe.mp ha))

/-- Only the `j` highest buyers matter with `j` units. -/
theorem valueAux_trunc (M : Model) (r : ℕ) : ∀ j (S : Multiset ℝ), InI M S →
    M.valueAux r j S = M.valueAux r j (((sortDesc S).take j : List ℝ) : Multiset ℝ) := by
  intro j
  induction j with
  | zero => intro S _; rw [valueAux_k_zero, valueAux_k_zero]
  | succ j ih =>
    intro S hS
    by_cases hS0 : S = 0
    · subst hS0
      have : sortDesc (0 : Multiset ℝ) = [] := by
        unfold sortDesc; simp
      rw [this]; rfl
    obtain ⟨s1, S', rfl, hS'⟩ := exists_top S hS0
    have hs1 := hS s1 (Multiset.mem_cons_self _ _)
    have hS'I : InI M S' := fun a ha => hS a (Multiset.mem_cons_of_mem ha)
    rw [sortDesc_cons_top s1 S' hS', List.take_succ_cons, ← Multiset.cons_coe]
    have hT : InI M (((sortDesc S').take j : List ℝ) : Multiset ℝ) :=
      fun a ha => hS'I a (mem_take_sortDesc ha)
    have hTle : ∀ a ∈ (((sortDesc S').take j : List ℝ) : Multiset ℝ), a ≤ s1 :=
      fun a ha => hS' a (mem_take_sortDesc ha)
    rw [R1v M r (j + 1) hs1 hS'I hS', R1v M r (j + 1) hs1 hT hTle]
    simp only [Nat.add_sub_cancel]
    rw [ih S' hS'I]

theorem V_secondToKth (M : Model) (r k : ℕ) (U : Multiset ℝ) (hU : InI M U) :
    M.valueAux r (k - 1) (secondToKth k U) = M.valueAux r (k - 1) (dropTop 1 U) := by
  have hs : sortDesc (dropTop 1 U) = (sortDesc U).drop 1 := by
    unfold dropTop
    exact sortDesc_coe_sorted _ ((pairwise_sortDesc U).sublist (List.drop_sublist _ _))
  rw [valueAux_trunc M r (k - 1) (dropTop 1 U) (InI_dropTop hU 1), hs]
  rfl

/-- `(m(v¹) - m(y))⁺`, the first summand of `sellTomorrow`. -/
noncomputable def mpart (M : Model) (y : ℝ) (C : Multiset ℝ) : ℝ :=
  max (M.m ((sortDesc C).headD y) - M.m y) 0

theorem mpart_nonneg (M : Model) (y : ℝ) (C : Multiset ℝ) : 0 ≤ mpart M y C := le_max_right _ _

theorem mpart_le (M : Model) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) {C : Multiset ℝ} (hC : InI M C) :
    mpart M y C ≤ max (M.m M.vhi - M.m y) 0 := by
  unfold mpart
  refine max_le_max ?_ le_rfl
  have : (sortDesc C).headD y ∈ Set.Icc M.vlo M.vhi := by
    cases hL : sortDesc C with
    | nil => simpa using hy
    | cons a L => simpa using hC a (mem_sortDesc.mp (by rw [hL]; simp))
  linarith [m_le_mvhi M this]

theorem measurable_mpart (M : Model) (y : ℝ) (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => mpart M y (cohort x)) := by
  unfold mpart
  simp_rw [sortDesc_cohort]
  cases n with
  | zero => simp only [List.ofFn_zero, List.headD_nil]; exact measurable_const
  | succ n =>
    simp only [List.ofFn_succ, List.headD_cons]
    exact (((m_measurable M).comp ((measurable_pi_apply 0).comp (measurable_sdesc _))).sub
      measurable_const).max measurable_const

/-- Case "no entrant above `y`". -/
theorem low_case (M : Model) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) {C : Multiset ℝ} (hC : InI M C)
    (h : ∀ c ∈ C, c ≤ y) : mpart M y C = 0 ∧ dropTop 1 (y ::ₘ C) = C := by
  constructor
  · unfold mpart
    apply max_eq_right
    have : (sortDesc C).headD y ∈ Set.Icc M.vlo M.vhi ∧ (sortDesc C).headD y ≤ y := by
      cases hL : sortDesc C with
      | nil => simpa using hy
      | cons a L =>
        have ha : a ∈ C := mem_sortDesc.mp (by rw [hL]; simp)
        simpa using ⟨hC a ha, h a ha⟩
    have hmm : M.m ((sortDesc C).headD y) ≤ M.m y := M.m_strictMonoOn.monotoneOn this.1 hy this.2
    linarith
  · rw [show (1 : ℕ) = 0 + 1 from rfl, dropTop_cons_top y C h 0, dropTop_zero]

/-- Case "top entrant `c1 > y`". -/
theorem high_case (M : Model) {y c1 : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hc1 : c1 ∈ Set.Icc M.vlo M.vhi) {C' : Multiset ℝ} (hC' : ∀ c ∈ C', c ≤ c1) (hyc : y < c1) :
    mpart M y (c1 ::ₘ C') = M.m c1 - M.m y ∧ dropTop 1 (y ::ₘ c1 ::ₘ C') = y ::ₘ C' := by
  constructor
  · unfold mpart
    rw [sortDesc_cons_top c1 C' hC']
    simp only [List.headD_cons]
    exact max_eq_left (sub_nonneg.mpr (M.m_strictMonoOn.monotoneOn hy hc1 hyc.le))
  · have hs : ∀ s ∈ y ::ₘ C', s ≤ c1 := by
      intro s hs
      rcases Multiset.mem_cons.mp hs with rfl | h
      · exact hyc.le
      · exact hC' s h
    rw [Multiset.cons_swap, show (1 : ℕ) = 0 + 1 from rfl, dropTop_cons_top c1 _ hs 0, dropTop_zero]

/-- `Ψ(y,C) = (m(v¹)-m(y))⁺ + Π^{k-1}(y^{-1} of {y} ∪ C)`, nonincreasing in `y`. -/
noncomputable def Psi (M : Model) (r k : ℕ) (y : ℝ) (C : Multiset ℝ) : ℝ :=
  mpart M y C + M.valueAux r (k - 1) (dropTop 1 (y ::ₘ C))

theorem Psi_anti (M : Model) (r k : ℕ) {y y' : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hy' : y' ∈ Set.Icc M.vlo M.vhi) (hyy : y ≤ y') {C : Multiset ℝ} (hC : InI M C) :
    Psi M r k y' C ≤ Psi M r k y C := by
  unfold Psi
  by_cases hl : ∀ c ∈ C, c ≤ y'
  · obtain ⟨h1, h2⟩ := low_case M hy' hC hl
    rw [h1, h2, zero_add]
    by_cases hl2 : ∀ c ∈ C, c ≤ y
    · obtain ⟨h3, h4⟩ := low_case M hy hC hl2
      rw [h3, h4, zero_add]
    · obtain ⟨c1, C', rfl, hC', hyc⟩ := top_or_le C y hl2
      have hc1 := hC c1 (Multiset.mem_cons_self _ _)
      have hC'I : InI M C' := fun a ha => hC a (Multiset.mem_cons_of_mem ha)
      obtain ⟨h3, h4⟩ := high_case M hy hc1 hC' hyc
      rw [h3, h4]
      have := (valueAux_lip M r (k - 1) C' y c1 hC'I hy hc1 hyc.le).2
      linarith
  · obtain ⟨c1, C', rfl, hC', hyc⟩ := top_or_le C y' hl
    have hc1 := hC c1 (Multiset.mem_cons_self _ _)
    have hC'I : InI M C' := fun a ha => hC a (Multiset.mem_cons_of_mem ha)
    obtain ⟨h1, h2⟩ := high_case M hy' hc1 hC' hyc
    obtain ⟨h3, h4⟩ := high_case M hy hc1 hC' (lt_of_le_of_lt hyy hyc)
    rw [h1, h2, h3, h4]
    have := (valueAux_lip M r (k - 1) C' y y' hC'I hy hy' hyy).2
    linarith

theorem Psi_nonneg (M : Model) (r k : ℕ) (y : ℝ) (C : Multiset ℝ) : 0 ≤ Psi M r k y C :=
  add_nonneg (mpart_nonneg M y C) (valueAux_nonneg M _ _ _)

theorem Psi_le (M : Model) (r k : ℕ) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) {C : Multiset ℝ}
    (hC : InI M C) : Psi M r k y C ≤ max (M.m M.vhi - M.m y) 0 + ((k - 1 : ℕ) : ℝ) * M.m M.vhi :=
  add_le_add (mpart_le M hy hC) (valueAux_le M r (k - 1) _ (InI_dropTop (InI_cons hy hC) 1))

/-- The expectation in `sellTomorrow` as one expectation of `Ψ`. -/
theorem CE_Psi (M : Model) (t k : ℕ) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) :
    M.cohortExp (t + 1) (fun C => mpart M y C) +
      M.cohortExp (t + 1) (fun C => M.piVal (t + 1) (k - 1) (secondToKth k (y ::ₘ C))) =
    M.cohortExp (t + 1) (fun C => Psi M (M.T + 1 - (t + 1)) k y C) := by
  have e : M.cohortExp (t + 1) (fun C => M.piVal (t + 1) (k - 1) (secondToKth k (y ::ₘ C))) =
      M.cohortExp (t + 1) (fun C => M.valueAux (M.T + 1 - (t + 1)) (k - 1) (dropTop 1 (y ::ₘ C))) :=
    CE_congr M _ fun C hC => V_secondToKth M _ k _ (InI_cons hy hC)
  rw [e]
  unfold Psi
  rw [CE_add M (t + 1) (measurable_mpart M y) (fun C _ => mpart_nonneg M y C)
    (fun C _ => valueAux_nonneg M _ _ _) (max (M.m M.vhi - M.m y) 0) (((k - 1 : ℕ) : ℝ) * M.m M.vhi)
    (fun C hC => mpart_le M hy hC)
    (fun C hC => valueAux_le M _ (k - 1) _ (InI_dropTop (InI_cons hy hC) 1))]

theorem DPi_eq_Psi (M : Model) (t k : ℕ) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) :
    M.DPi t k y = (1 - M.δ) * M.m y + M.δ * M.piTilde (t + 1) (k - 1) 0 -
      M.δ * M.cohortExp (t + 1) (fun C => Psi M (M.T + 1 - (t + 1)) k y C) := by
  rw [← CE_Psi M t k hy]
  simp only [Model.DPi, Model.sellOneToday, Model.sellTomorrow, Model.expMaxWith, mpart]
  ring

/-- Sibling 8f17f278 (without the demand assumption): `DΠ^k_t` is strictly increasing. -/
theorem DPi_strictMonoOn' (M : Model) (t k : ℕ) :
    StrictMonoOn (M.DPi t k) (Set.Icc M.vlo M.vhi) := by
  intro y hy y' hy' hlt
  rw [DPi_eq_Psi M t k hy, DPi_eq_Psi M t k hy']
  have hm : M.m y < M.m y' := M.m_strictMonoOn hy hy' hlt
  have hE : M.cohortExp (t + 1) (fun C => Psi M (M.T + 1 - (t + 1)) k y' C) ≤
      M.cohortExp (t + 1) (fun C => Psi M (M.T + 1 - (t + 1)) k y C) :=
    CE_mono M _ _ (fun C hC => Psi_anti M _ k hy hy' hlt.le hC) (fun C hC => Psi_le M _ k hy hC)
  have hδ := M.δ_lt_one
  have hδ0 := M.δ_pos
  nlinarith

theorem deltaPi_Phi (M : Model) (s k : ℕ) (y : ℝ) (hs : s ≤ M.T) :
    M.deltaPi s k y 0 = M.m y - Phi M (M.T - s) k y := by
  rw [deltaPi_eq]
  unfold Phi WW Model.piTilde Model.piVal
  have h1 : M.T + 1 - (M.T - s) = s + 1 := by omega
  have h2 : M.T + 1 - (s + 1) = M.T - s := by omega
  rw [h1, h2]
  ring

theorem CE_const_add (M : Model) (s : ℕ) {f : Multiset ℝ → ℝ} (c B : ℝ)
    (hf0 : ∀ C, InI M C → 0 ≤ f C) (hcf : ∀ C, InI M C → 0 ≤ c + f C)
    (hfB : ∀ C, InI M C → f C ≤ B) :
    M.cohortExp s (fun C => c + f C) = c + M.cohortExp s f := by
  by_cases hc : 0 ≤ c
  · rw [CE_add M s (f := fun _ => c) (fun n => measurable_const) (fun _ _ => hc) hf0 c B
      (fun _ _ => le_rfl) hfB, CE_const M s c hc]
  · push Not at hc
    have h := CE_add M s (f := fun _ => -c) (g := fun C => c + f C) (fun n => measurable_const)
      (fun _ _ => by linarith) hcf (-c) (c + B) (fun _ _ => le_rfl)
      (fun C hC => by linarith [hfB C hC])
    rw [CE_const M s (-c) (by linarith)] at h
    have e : M.cohortExp s (fun C => -c + (c + f C)) = M.cohortExp s f :=
      CE_congr M s fun C _ => by ring
    rw [e] at h
    linarith

/-- Pointwise: selling the top buyer first is feasible (`≥`), and optimal (`=`) above the cutoff. -/
theorem V_ge_sell_top (M : Model) (r k : ℕ) (hk : 1 ≤ k) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    {C : Multiset ℝ} (hC : InI M C) :
    M.m y + Psi M (r + 1) k y C ≤ M.valueAux (r + 1) k (y ::ₘ C) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold Psi
  simp only [Nat.add_sub_cancel]
  by_cases hl : ∀ c ∈ C, c ≤ y
  · obtain ⟨h1, h2⟩ := low_case M hy hC hl
    rw [h1, h2, V_succ_top' M r k y C hl]
    linarith [le_max_right (WW M r (k + 1) (y ::ₘ C)) (M.m y + M.valueAux (r + 1) k C)]
  · obtain ⟨c1, C', rfl, hC', hyc⟩ := top_or_le C y hl
    obtain ⟨h1, h2⟩ := high_case M hy (hC c1 (Multiset.mem_cons_self _ _)) hC' hyc
    have hs : ∀ s ∈ y ::ₘ C', s ≤ c1 := by
      intro s hs
      rcases Multiset.mem_cons.mp hs with rfl | h
      · exact hyc.le
      · exact hC' s h
    rw [h1, h2, Multiset.cons_swap y c1 C', V_succ_top' M r k c1 _ hs]
    linarith [le_max_right (WW M r (k + 1) (c1 ::ₘ y ::ₘ C')) (M.m c1 + M.valueAux (r + 1) k (y ::ₘ C'))]

theorem V_eq_sell_top (M : Model) (r k : ℕ) (hk : 1 ≤ k) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hPhi : Phi M r k y ≤ M.m y) {C : Multiset ℝ} (hC : InI M C) :
    M.valueAux (r + 1) k (y ::ₘ C) = M.m y + Psi M (r + 1) k y C := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold Psi
  simp only [Nat.add_sub_cancel]
  by_cases hl : ∀ c ∈ C, c ≤ y
  · obtain ⟨h1, h2⟩ := low_case M hy hC hl
    rw [h1, h2, R1v M (r + 1) (k + 1) hy hC hl, GG_succ, max_eq_right hPhi]
    simp
  · obtain ⟨c1, C', rfl, hC', hyc⟩ := top_or_le C y hl
    have hc1 := hC c1 (Multiset.mem_cons_self _ _)
    have hC'I : InI M C' := fun a ha => hC a (Multiset.mem_cons_of_mem ha)
    obtain ⟨h1, h2⟩ := high_case M hy hc1 hC' hyc
    have hs : ∀ s ∈ y ::ₘ C', s ≤ c1 := by
      intro s hs
      rcases Multiset.mem_cons.mp hs with rfl | h
      · exact hyc.le
      · exact hC' s h
    have hP1 : Phi M r (k + 1) c1 ≤ M.m c1 := by
      have hl := (Phi_lip M r (k + 1) hy hc1 hyc.le).2
      have hmy : M.m y ≤ M.m c1 := M.m_strictMonoOn.monotoneOn hy hc1 hyc.le
      have hδ := M.δ_lt_one
      have hδ0 := M.δ_pos
      nlinarith
    rw [h1, h2, Multiset.cons_swap y c1 C', R1v M (r + 1) (k + 1) hc1 (InI_cons hy hC'I) hs,
      GG_succ, max_eq_right hP1]
    simp only [Nat.add_sub_cancel]
    ring

/-- New child N1. -/
theorem deltaPi_le_DPi (M : Model) (t k : ℕ) (htT : t + 1 ≤ M.T) (hk : 1 ≤ k)
    (y : ℝ) (hy : y ∈ Set.Icc M.vlo M.vhi) (hmy : 0 ≤ M.m y) :
    M.deltaPi t k y 0 ≤ M.DPi t k y := by
  rw [DPi_eq_Psi M t k hy, deltaPi_eq]
  obtain ⟨r, hr⟩ : ∃ r, M.T + 1 - (t + 1) = r + 1 := ⟨M.T - t - 1, by omega⟩
  have hE : M.cohortExp (t + 1) (fun C => M.m y + Psi M (r + 1) k y C) ≤
      M.piTilde (t + 1) k (y ::ₘ 0) := by
    unfold Model.piTilde Model.piVal
    rw [hr]
    refine CE_mono M _ (k * M.m M.vhi) (fun C hC => ?_)
      (fun C hC => valueAux_le M _ k _ (InI_add (InI_cons hy (InI_zero M)) hC))
    simp only [Multiset.cons_add, zero_add]
    exact V_ge_sell_top M r k hk hy hC
  rw [CE_const_add M (t + 1) (M.m y) _ (fun C _ => Psi_nonneg M _ k y C)
    (fun C _ => add_nonneg hmy (Psi_nonneg M _ k y C)) (fun C hC => Psi_le M _ k hy hC)] at hE
  rw [hr]
  have hδ0 := M.δ_pos
  have := mul_le_mul_of_nonneg_left hE hδ0.le
  nlinarith


/-! ## Part F: N2 and the assembly of the parent from the time comparison `hInc`. -/

/-- New child N2 (no sign condition needed). -/
theorem DPi_eq_deltaPi (M : Model) (t k : ℕ) (htT : t + 1 ≤ M.T) (hk : 1 ≤ k)
    (y : ℝ) (hy : y ∈ Set.Icc M.vlo M.vhi) (hxy : M.cutoff (t + 1) k ≤ y) :
    M.DPi t k y = M.deltaPi t k y 0 := by
  obtain ⟨hc, hc0, -⟩ := cutoff_spec M (t + 1) k hk
  have hd : 0 ≤ M.deltaPi (t + 1) k y 0 := by
    rw [← hc0]; exact (deltaPi_strictMonoOn M (t + 1) k).monotoneOn hc hy hxy
  rw [deltaPi_Phi M (t + 1) k y htT] at hd
  have hPhi : Phi M (M.T - (t + 1)) k y ≤ M.m y := by linarith
  have hr : M.T + 1 - (t + 1) = (M.T - (t + 1)) + 1 := by omega
  have hV : ∀ C, InI M C → M.valueAux (M.T - (t + 1) + 1) k (y ::ₘ C) =
      M.m y + Psi M (M.T - (t + 1) + 1) k y C :=
    fun C hC => V_eq_sell_top M _ k hk hy hPhi hC
  have hE : M.piTilde (t + 1) k (y ::ₘ 0) =
      M.m y + M.cohortExp (t + 1) (fun C => Psi M (M.T - (t + 1) + 1) k y C) := by
    unfold Model.piTilde Model.piVal
    rw [hr]
    rw [← CE_const_add M (t + 1) (M.m y) _ (fun C _ => Psi_nonneg M _ k y C)
      (fun C hC => by rw [← hV C hC]; exact valueAux_nonneg M _ _ _) (fun C hC => Psi_le M _ k hy hC)]
    refine CE_congr M _ fun C hC => ?_
    simp only [Multiset.cons_add, zero_add]
    exact hV C hC
  rw [DPi_eq_Psi M t k hy, deltaPi_eq, hE, hr]
  ring

theorem deltaPi_last' (M : Model) (k : ℕ) (y : ℝ) : M.deltaPi M.T k y 0 = M.m y := by
  have h : ∀ k' (S : Multiset ℝ), M.piTilde (M.T + 1) k' S = 0 := by
    intro k' S
    simp [Model.piTilde, Model.cohortExp, Model.cohortLIntegral, Model.piVal, Model.valueAux]
  simp [Model.deltaPi, Model.sellOneToday, Model.sellZeroToday, h]

/-- The parent, assuming the time comparison of `DΠ` (sibling da7d7c54's content). -/
theorem parent_of_inc (M : Model)
    (hInc : ∀ t k, 1 ≤ t → t + 2 ≤ M.T → 1 ≤ k →
      (∀ s j, t + 1 ≤ s → s + 1 ≤ M.T → 1 ≤ j → j ≤ k → M.cutoff (s + 1) j ≤ M.cutoff s j) →
      ∀ y1 ∈ Set.Icc M.vlo M.vhi, M.DPi t k y1 ≤ M.DPi (t + 1) k y1)
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ t, 1 ≤ t → t + 1 ≤ M.T → M.cutoff (t + 1) k ≤ M.cutoff t k) ∧
    (∀ t, 1 ≤ t → t + 1 ≤ M.T →
      M.DPi t k (M.cutoff t k) = 0 ∧
      ∀ y ∈ Set.Icc M.vlo M.vhi, M.DPi t k y = 0 → y = M.cutoff t k) := by
  have hIcc : ∀ t j, 1 ≤ j → M.cutoff t j ∈ Set.Icc M.vlo M.vhi :=
    fun t j h3 => (cutoff_spec M t j h3).1
  have hroot : ∀ t j, 1 ≤ j → M.deltaPi t j (M.cutoff t j) 0 = 0 :=
    fun t j h3 => (cutoff_spec M t j h3).2.1
  have key : ∀ n t, 1 ≤ t → t + 1 ≤ M.T → M.T - (t + 1) ≤ n →
      ∀ j, 1 ≤ j → M.cutoff (t + 1) j ≤ M.cutoff t j := by
    intro n
    induction n with
    | zero =>
      intro t ht htT hn j hj
      have hT : t + 1 = M.T := by omega
      have h0 : M.m (M.cutoff M.T j) = 0 := by
        have := hroot M.T j hj
        rwa [deltaPi_last'] at this
      have hmx : 0 ≤ M.m (M.cutoff t j) := m_cutoff_nonneg M t j hj
      rw [hT]
      have hx := hIcc t j hj
      have hy := hIcc M.T j hj
      have : M.m (M.cutoff M.T j) ≤ M.m (M.cutoff t j) := by rw [h0]; exact hmx
      exact (M.m_strictMonoOn.le_iff_le hy hx).1 this
    | succ n ih =>
      intro t ht htT hn j hj
      by_cases hlast : t + 1 = M.T
      · exact ih t ht htT (by omega) j hj
      have ht2 : t + 2 ≤ M.T := by omega
      have hfut : ∀ s j', t + 1 ≤ s → s + 1 ≤ M.T → 1 ≤ j' → j' ≤ j →
          M.cutoff (s + 1) j' ≤ M.cutoff s j' :=
        fun s j' h1 h2 h3 _ => ih s (by omega) h2 (by omega) j' h3
      set y' := M.cutoff (t + 1) j with hy'
      set x := M.cutoff t j with hx
      have hy'I : y' ∈ Set.Icc M.vlo M.vhi := hIcc (t + 1) j hj
      have hxI : x ∈ Set.Icc M.vlo M.vhi := hIcc t j hj
      have h1 : M.DPi (t + 1) j y' = 0 := by
        rw [DPi_eq_deltaPi M (t + 1) j (by omega) hj y' hy'I
          (ih (t + 1) (by omega) (by omega) (by omega) j hj)]
        exact hroot (t + 1) j hj
      have h2 : M.DPi t j y' ≤ 0 := by
        have := hInc t j ht ht2 hj hfut y' hy'I
        linarith
      have h3 : 0 ≤ M.DPi t j x := by
        have := deltaPi_le_DPi M t j htT hj x hxI (m_cutoff_nonneg M t j hj)
        rw [hroot t j hj] at this
        exact this
      exact ((DPi_strictMonoOn' M t j).le_iff_le hy'I hxI).1 (by linarith)
  have part1 : ∀ t, 1 ≤ t → t + 1 ≤ M.T → M.cutoff (t + 1) k ≤ M.cutoff t k :=
    fun t ht htT => key (M.T - (t + 1)) t ht htT le_rfl k hk
  refine ⟨part1, ?_⟩
  intro t ht htT
  have hxI := hIcc t k hk
  have hD0 : M.DPi t k (M.cutoff t k) = 0 := by
    rw [DPi_eq_deltaPi M t k htT hk _ hxI (part1 t ht htT)]
    exact hroot t k hk
  refine ⟨hD0, fun y hy hy0 => ?_⟩
  exact (DPi_strictMonoOn' M t k).injOn hy hxI (by rw [hy0, hD0])


/-! ## Part G: the look-ahead loss `LL`, its monotonicity in the entrants, and the two-level comparison. -/

section LAlg

variable {M : Model} {V : ℕ → Multiset ℝ → ℝ}

/-- `Λ(k,y,C) = (m(v¹)-m(y))⁺ + V(k-1, y^{-1} of {y} ∪ C) - V(k-1, C)`. -/
noncomputable def LL (M : Model) (V : ℕ → Multiset ℝ → ℝ) (k : ℕ) (y : ℝ) (C : Multiset ℝ) : ℝ :=
  mpart M y C + V (k - 1) (dropTop 1 (y ::ₘ C)) - V (k - 1) C

theorem LL_low (k : ℕ) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) {C : Multiset ℝ} (hC : InI M C)
    (h : ∀ c ∈ C, c ≤ y) : LL M V k y C = 0 := by
  obtain ⟨h1, h2⟩ := low_case M hy hC h
  unfold LL; rw [h1, h2]; ring

theorem LL_high (k : ℕ) {y c1 : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) (hc1 : c1 ∈ Set.Icc M.vlo M.vhi)
    {C' : Multiset ℝ} (hC' : ∀ c ∈ C', c ≤ c1) (hyc : y < c1) :
    LL M V k y (c1 ::ₘ C') = (M.m c1 - M.m y) - (DD V (k - 1) c1 C' - DD V (k - 1) y C') := by
  obtain ⟨h1, h2⟩ := high_case M hy hc1 hC' hyc
  unfold LL DD; rw [h1, h2]; ring

/-- (M): adding a buyer raises `D`. -/
theorem DD_mono_add (I : Inv V M) {y w : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hw : w ∈ Set.Icc M.vlo M.vhi) :
    ∀ n (Z : Multiset ℝ) j, Multiset.card Z = n → InI M Z → DD V j y Z ≤ DD V j y (w ::ₘ Z) := by
  intro n
  induction n with
  | zero =>
    intro Z j hZ hZI
    rw [Multiset.card_eq_zero.mp hZ]
    by_cases hwy : w ≤ y
    · rw [DD_eq_GG I j hy (InI_zero M) (by simp), DD_eq_GG I j hy (InI_cons hw (InI_zero M)) (by simpa using hwy)]
    · push Not at hwy
      rw [DD_cons I j hy hw (InI_zero M) hwy.le (by simp)]
      have := DD_diff_le I hy 0 0 j w rfl (InI_zero M) hw hwy.le (by simp)
      linarith
  | succ n ih =>
    intro Z j hZ hZI
    by_cases hwy : w ≤ y
    · have h := DD_add_low I hy (S := w ::ₘ 0) (InI_cons hw (InI_zero M)) (by simpa using hwy) _ Z j rfl hZI
      rw [Multiset.add_comm, Multiset.cons_add, zero_add] at h
      exact le_of_eq h.symm
    · push Not at hwy
      by_cases hZw : ∀ z ∈ Z, z ≤ w
      · rw [DD_cons I j hy hw hZI hwy.le hZw]
        have := DD_diff_le I hy _ Z j w rfl hZI hw hwy.le hZw
        linarith
      · obtain ⟨z1, Z', rfl, hZ', hwz⟩ := top_or_le Z w hZw
        have hz1 := hZI z1 (Multiset.mem_cons_self _ _)
        have hZ'I : InI M Z' := fun a ha => hZI a (Multiset.mem_cons_of_mem ha)
        have hs : ∀ s ∈ w ::ₘ Z', s ≤ z1 := by
          intro s hs
          rcases Multiset.mem_cons.mp hs with rfl | h
          · exact hwz.le
          · exact hZ' s h
        rw [Multiset.cons_swap w z1 Z', DD_cons I j hy hz1 (InI_cons hw hZ'I) (hwy.trans hwz).le hs,
          DD_cons I j hy hz1 hZ'I (hwy.trans hwz).le hZ']
        have := ih Z' (j - 1) (by simpa using hZ) hZ'I
        linarith

/-- (S): the upgrade value `D(c) - D(y)` falls when a buyer is added. -/
theorem DD_sub (I : Inv V M) {y c w : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hc : c ∈ Set.Icc M.vlo M.vhi) (hyc : y ≤ c) (hw : w ∈ Set.Icc M.vlo M.vhi) :
    ∀ n (Z : Multiset ℝ) j, Multiset.card Z = n → InI M Z →
      DD V j c (w ::ₘ Z) - DD V j y (w ::ₘ Z) ≤ DD V j c Z - DD V j y Z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Z j hZ hZI
    have hM := DD_mono_add I hy hw _ Z j rfl hZI
    by_cases hZw : ∀ z ∈ Z, z ≤ w
    · by_cases hwc : c ≤ w
      · rw [DD_cons I j hc hw hZI hwc hZw, DD_cons I j hy hw hZI (hyc.trans hwc) hZw]
        have := DD_diff_mono I hy hc hyc _ Z j rfl hZI
        linarith
      · push Not at hwc
        have hs : ∀ s ∈ w ::ₘ Z, s ≤ c := by
          intro s hs
          rcases Multiset.mem_cons.mp hs with rfl | h
          · exact hwc.le
          · exact (hZw s h).trans hwc.le
        rw [DD_eq_GG I j hc (InI_cons hw hZI) hs,
          DD_eq_GG I j hc hZI (fun z hz => (hZw z hz).trans hwc.le)]
        linarith
    · obtain ⟨z1, Z', rfl, hZ', hwz⟩ := top_or_le Z w hZw
      have hz1 := hZI z1 (Multiset.mem_cons_self _ _)
      have hZ'I : InI M Z' := fun a ha => hZI a (Multiset.mem_cons_of_mem ha)
      by_cases hcz : c ≤ z1
      · have hs : ∀ s ∈ w ::ₘ Z', s ≤ z1 := by
          intro s hs
          rcases Multiset.mem_cons.mp hs with rfl | h
          · exact hwz.le
          · exact hZ' s h
        rw [Multiset.cons_swap w z1 Z', DD_cons I j hc hz1 (InI_cons hw hZ'I) hcz hs,
          DD_cons I j hy hz1 (InI_cons hw hZ'I) (hyc.trans hcz) hs,
          DD_cons I j hc hz1 hZ'I hcz hZ', DD_cons I j hy hz1 hZ'I (hyc.trans hcz) hZ']
        have := ih Z'.card (by simp at hZ; omega) Z' (j - 1) rfl hZ'I
        linarith
      · push Not at hcz
        have hs1 : ∀ s ∈ w ::ₘ z1 ::ₘ Z', s ≤ c := by
          intro s hs
          rcases Multiset.mem_cons.mp hs with rfl | h
          · exact (hwz.trans hcz).le
          · rcases Multiset.mem_cons.mp h with rfl | h
            · exact hcz.le
            · exact ((hZ' s h).trans hcz.le)
        have hs2 : ∀ s ∈ z1 ::ₘ Z', s ≤ c := fun s hs => hs1 s (Multiset.mem_cons_of_mem hs)
        rw [DD_eq_GG I j hc (InI_cons hw hZI) hs1, DD_eq_GG I j hc hZI hs2]
        linarith

/-- (b): `Λ` rises when an entrant is added. -/
theorem LL_mono_add (I : Inv V M)
    (hrho : ∀ j z z', z ∈ Set.Icc M.vlo M.vhi → z' ∈ Set.Icc M.vlo M.vhi → z ≤ z' →
      M.m z - GG V j z ≤ M.m z' - GG V j z')
    (k : ℕ) {y w : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) (hw : w ∈ Set.Icc M.vlo M.vhi)
    {C : Multiset ℝ} (hC : InI M C) : LL M V k y C ≤ LL M V k y (w ::ₘ C) := by
  by_cases hCy : ∀ c ∈ C, c ≤ y
  · rw [LL_low k hy hC hCy]
    by_cases hwy : w ≤ y
    · rw [LL_low k hy (InI_cons hw hC)]
      intro s hs
      rcases Multiset.mem_cons.mp hs with rfl | h
      · exact hwy
      · exact hCy s h
    · push Not at hwy
      rw [LL_high k hy hw (fun c hc => (hCy c hc).trans hwy.le) hwy,
        DD_eq_GG I (k - 1) hw hC (fun c hc => (hCy c hc).trans hwy.le), DD_eq_GG I (k - 1) hy hC hCy]
      have := hrho (k - 1) y w hy hw hwy.le
      linarith
  · obtain ⟨c1, C', rfl, hC', hyc⟩ := top_or_le C y hCy
    have hc1 := hC c1 (Multiset.mem_cons_self _ _)
    have hC'I : InI M C' := fun a ha => hC a (Multiset.mem_cons_of_mem ha)
    rw [LL_high k hy hc1 hC' hyc]
    by_cases hwc : w ≤ c1
    · have hs : ∀ s ∈ w ::ₘ C', s ≤ c1 := by
        intro s hs
        rcases Multiset.mem_cons.mp hs with rfl | h
        · exact hwc
        · exact hC' s h
      rw [Multiset.cons_swap w c1 C', LL_high k hy hc1 hs hyc]
      have := DD_sub I hy hc1 hyc.le hw _ C' (k - 1) rfl hC'I
      linarith
    · push Not at hwc
      have hs : ∀ s ∈ c1 ::ₘ C', s ≤ w := by
        intro s hs
        rcases Multiset.mem_cons.mp hs with rfl | h
        · exact hwc.le
        · exact (hC' s h).trans hwc.le
      rw [LL_high k hy hw hs (hyc.trans hwc), DD_eq_GG I (k - 1) hw hC hs,
        DD_cons I (k - 1) hy hc1 hC'I hyc.le hC', DD_eq_GG I (k - 1) hc1 hC'I hC']
      have hP := DD_diff_le I hy _ C' (k - 1) c1 rfl hC'I hc1 hyc.le hC'
      have hr := hrho (k - 1) c1 w hc1 hw hwc.le
      unfold dG at hP ⊢
      linarith

end LAlg

section Pair

variable {M : Model} {V V' : ℕ → Multiset ℝ → ℝ}

/-- `H(j,z) = G_V(j,z) - G_{V'}(j,z)`. -/
def HH (V V' : ℕ → Multiset ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ := GG V j z - GG V' j z

theorem pair_P2 (I : Inv V M) (I' : Inv V' M)
    (hH : ∀ j z z', z ∈ Set.Icc M.vlo M.vhi → z' ∈ Set.Icc M.vlo M.vhi → z ≤ z' → HH V V' j z' ≤ HH V V' j z)
    {x : ℝ} (hx : x ∈ Set.Icc M.vlo M.vhi) :
    ∀ n (Z : Multiset ℝ) j w, Multiset.card Z = n → InI M Z → w ∈ Set.Icc M.vlo M.vhi → x ≤ w →
      (∀ z ∈ Z, z ≤ w) → HH V V' j w ≤ DD V j x Z - DD V' j x Z := by
  intro n
  induction n with
  | zero =>
    intro Z j w hZ hZI hw hxw _
    have h0 : ∀ z ∈ Z, z ≤ x := by rw [Multiset.card_eq_zero.mp hZ]; simp
    rw [DD_eq_GG I j hx hZI h0, DD_eq_GG I' j hx hZI h0]
    exact hH j x w hx hw hxw
  | succ n ih =>
    intro Z j w hZ hZI hw hxw hZw
    by_cases hle : ∀ z ∈ Z, z ≤ x
    · rw [DD_eq_GG I j hx hZI hle, DD_eq_GG I' j hx hZI hle]
      exact hH j x w hx hw hxw
    · obtain ⟨z, A, rfl, hA, hxz⟩ := top_or_le Z x hle
      have hz : z ∈ Set.Icc M.vlo M.vhi := hZI z (Multiset.mem_cons_self _ _)
      have hAI : InI M A := fun a ha => hZI a (Multiset.mem_cons_of_mem ha)
      rw [DD_cons I j hx hz hAI hxz.le hA, DD_cons I' j hx hz hAI hxz.le hA]
      have h1 := ih A (j - 1) z (by simpa using hZ) hAI hz hxz.le hA
      have h2 := hH j z w hz hw (hZw z (Multiset.mem_cons_self _ _))
      unfold HH at h1 h2 ⊢
      unfold dG
      linarith

/-- (B1): `D_V - D_{V'}` is nonincreasing in the buyer's value. -/
theorem pair_B1 (I : Inv V M) (I' : Inv V' M)
    (hH : ∀ j z z', z ∈ Set.Icc M.vlo M.vhi → z' ∈ Set.Icc M.vlo M.vhi → z ≤ z' → HH V V' j z' ≤ HH V V' j z)
    {x x' : ℝ} (hx : x ∈ Set.Icc M.vlo M.vhi) (hx' : x' ∈ Set.Icc M.vlo M.vhi) (hxx : x ≤ x') :
    ∀ n (Z : Multiset ℝ) j, Multiset.card Z = n → InI M Z →
      DD V j x' Z - DD V' j x' Z ≤ DD V j x Z - DD V' j x Z := by
  intro n
  induction n with
  | zero =>
    intro Z j hZ hZI
    have h0 : ∀ z ∈ Z, z ≤ x' := by rw [Multiset.card_eq_zero.mp hZ]; simp
    rw [DD_eq_GG I j hx' hZI h0, DD_eq_GG I' j hx' hZI h0]
    exact pair_P2 I I' hH hx _ Z j x' rfl hZI hx' hxx h0
  | succ n ih =>
    intro Z j hZ hZI
    by_cases hle : ∀ z ∈ Z, z ≤ x'
    · rw [DD_eq_GG I j hx' hZI hle, DD_eq_GG I' j hx' hZI hle]
      exact pair_P2 I I' hH hx _ Z j x' rfl hZI hx' hxx hle
    · obtain ⟨z, A, rfl, hA, hxz⟩ := top_or_le Z x' hle
      have hz : z ∈ Set.Icc M.vlo M.vhi := hZI z (Multiset.mem_cons_self _ _)
      have hAI : InI M A := fun a ha => hZI a (Multiset.mem_cons_of_mem ha)
      rw [DD_cons I j hx hz hAI (hxx.trans hxz.le) hA, DD_cons I' j hx hz hAI (hxx.trans hxz.le) hA,
        DD_cons I j hx' hz hAI hxz.le hA, DD_cons I' j hx' hz hAI hxz.le hA]
      have h1 := ih A (j - 1) (by simpa using hZ) hAI
      linarith

theorem pair_A (I : Inv V M) (I' : Inv V' M)
    (hH : ∀ j z z', z ∈ Set.Icc M.vlo M.vhi → z' ∈ Set.Icc M.vlo M.vhi → z ≤ z' → HH V V' j z' ≤ HH V V' j z)
    (hH0 : ∀ j z, z ∈ Set.Icc M.vlo M.vhi → 0 ≤ HH V V' j z)
    {x : ℝ} (hx : x ∈ Set.Icc M.vlo M.vhi) (Z : Multiset ℝ) (hZI : InI M Z) (j : ℕ) :
    DD V' j x Z ≤ DD V j x Z := by
  have hv : M.vhi ∈ Set.Icc M.vlo M.vhi := ⟨M.vlo_lt_vhi.le, le_rfl⟩
  have := pair_P2 I I' hH hx _ Z j M.vhi rfl hZI hv hx.2 (fun z hz => (hZI z hz).2)
  have h0 := hH0 j M.vhi hv
  linarith

/-- (a): more demand raises the look-ahead loss. -/
theorem pair_LL (I : Inv V M) (I' : Inv V' M)
    (hH : ∀ j z z', z ∈ Set.Icc M.vlo M.vhi → z' ∈ Set.Icc M.vlo M.vhi → z ≤ z' → HH V V' j z' ≤ HH V V' j z)
    (k : ℕ) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) {C : Multiset ℝ} (hC : InI M C) :
    LL M V' k y C ≤ LL M V k y C := by
  by_cases hCy : ∀ c ∈ C, c ≤ y
  · rw [LL_low k hy hC hCy, LL_low k hy hC hCy]
  · obtain ⟨c1, C', rfl, hC', hyc⟩ := top_or_le C y hCy
    have hc1 := hC c1 (Multiset.mem_cons_self _ _)
    have hC'I : InI M C' := fun a ha => hC a (Multiset.mem_cons_of_mem ha)
    rw [LL_high k hy hc1 hC' hyc, LL_high k hy hc1 hC' hyc]
    have := pair_B1 I I' hH hy hc1 hyc.le _ C' (k - 1) rfl hC'I
    linarith

end Pair


/-! ## Part H: stochastic order of the number of entrants. -/

theorem st_tsum_le (P Q : PMF ℕ) (hPQ : ∀ m : ℕ, P.toMeasure {n | m < n} ≤ Q.toMeasure {n | m < n})
    (h : ℕ → ENNReal) (hh : Monotone h) : ∑' n, P n * h n ≤ ∑' n, Q n * h n := by
  have hfin : ∀ n, h n = h 0 + ∑ m ∈ Finset.range n, (h (m + 1) - h m) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih, add_tsub_cancel_of_le (hh (Nat.le_succ n))]
  have hn : ∀ n, h n = h 0 + ∑' m, (if m < n then h (m + 1) - h m else 0) := by
    intro n
    rw [tsum_eq_sum (s := Finset.range n) (fun m hm => by
      simp only [Finset.mem_range, not_lt] at hm; simp [not_lt.mpr hm])]
    rw [Finset.sum_congr rfl (g := fun m => h (m + 1) - h m)
      (fun m hm => by simp only [Finset.mem_range] at hm; simp [hm])]
    exact hfin n
  have key : ∀ R : PMF ℕ, ∑' n, R n * h n = h 0 + ∑' m, (h (m + 1) - h m) * R.toMeasure {n | m < n} := by
    intro R
    have hR : ∀ m : ℕ, R.toMeasure {n | m < n} = ∑' n, (if m < n then R n else 0) := by
      intro m; rw [PMF.toMeasure_apply_eq_tsum]; congr 1; funext n; simp [Set.indicator]
    calc ∑' n, R n * h n
        = ∑' n, (R n * h 0 + ∑' m, (if m < n then R n * (h (m + 1) - h m) else 0)) := by
          congr 1; funext n
          rw [hn n, mul_add, ← ENNReal.tsum_mul_left]
          congr 1; congr 1; funext m; split_ifs <;> simp
      _ = h 0 + ∑' m, (h (m + 1) - h m) * R.toMeasure {n | m < n} := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, ENNReal.tsum_comm]
          congr 1; congr 1; funext m
          rw [hR m, ← ENNReal.tsum_mul_left]
          congr 1; funext n; split_ifs <;> simp [mul_comm]
  rw [key P, key Q]
  exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun m => mul_le_mul' le_rfl (hPQ m))

theorem cohort_succ {n : ℕ} (x : Fin (n + 1) → ℝ) : cohort x = x 0 ::ₘ cohort (fun j => x j.succ) := by
  unfold cohort; rw [List.ofFn_succ, ← Multiset.cons_coe]

theorem lint_succ_ge (M : Model) {f : Multiset ℝ → ℝ}
    (hf : ∀ n, Measurable (fun x : Fin n → ℝ => f (cohort x)))
    (hmono : ∀ C w, InI M C → w ∈ Set.Icc M.vlo M.vhi → f C ≤ f (w ::ₘ C)) (n : ℕ) :
    ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (f (cohort x)) ∂(Measure.pi fun _ => M.law) ≤
      ∫⁻ x : Fin (n + 1) → ℝ, ENNReal.ofReal (f (cohort x)) ∂(Measure.pi fun _ => M.law) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => M.law) 0
  have h2 : ∀ x : Fin (n + 1) → ℝ,
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 x).2 = fun j => x j.succ := by
    intro x; funext j
    first
    | rfl
    | simp [MeasurableEquiv.piFinSuccAbove, Fin.removeNth]
  have h1 : ∫⁻ x : Fin (n + 1) → ℝ, ENNReal.ofReal (f (cohort (fun j => x j.succ)))
      ∂(Measure.pi fun _ => M.law) =
      ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (f (cohort x)) ∂(Measure.pi fun _ => M.law) := by
    have e1 := hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun p : ℝ × (Fin n → ℝ) => ENNReal.ofReal (f (cohort p.2)))
    simp only [h2] at e1
    rw [e1, lintegral_prod (fun p : ℝ × (Fin n → ℝ) => ENNReal.ofReal (f (cohort p.2)))
      ((hf n).ennreal_ofReal.comp measurable_snd).aemeasurable]
    simp [lintegral_const, measure_univ]
  rw [← h1]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_cohort M (n + 1)] with x hx
  rw [cohort_succ x] at hx ⊢
  exact ENNReal.ofReal_le_ofReal (hmono _ _ (fun s hs => hx s (Multiset.mem_cons_of_mem hs))
    (hx _ (Multiset.mem_cons_self _ _)))

/-- Fewer entrants (usual stochastic order) give a smaller expectation of a quantity that rises
when an entrant is added. -/
theorem CE_st_le (M : Model) {s s' : ℕ}
    (hss : StochasticOrders.Usual.UsualOrder (M.arrivals s).toMeasure (M.arrivals s').toMeasure
      (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (n : ℝ)))
    {f : Multiset ℝ → ℝ} (hf : ∀ n, Measurable (fun x : Fin n → ℝ => f (cohort x)))
    (B : ℝ) (hB : ∀ C, InI M C → f C ≤ B)
    (hmono : ∀ C w, InI M C → w ∈ Set.Icc M.vlo M.vhi → f C ≤ f (w ::ₘ C)) :
    M.cohortExp s f ≤ M.cohortExp s' f := by
  unfold Model.cohortExp
  apply ENNReal.toReal_mono (CL_ne_top M s' B hB)
  unfold Model.cohortLIntegral
  apply st_tsum_le
  · intro m
    have := hss m
    simpa using this
  · exact monotone_nat_of_le_succ (lint_succ_ge M hf hmono)


/-! ## Part I: decreasing demand ⇒ `DΠ^k_t ≤ DΠ^k_{t+1}` (sibling da7d7c54's content) and the parent. -/

theorem GG0 (M : Model) (r : ℕ) (z : ℝ) : GG (fun k S => M.valueAux r k S) 0 z = 0 := by
  unfold GG; simp [valueAux_k_zero]

theorem WW0 (M : Model) (k : ℕ) (Z : Multiset ℝ) : WW M 0 k Z = 0 := by
  unfold WW; simp only [valueAux_zero]; rw [CE_const M _ 0 le_rfl, mul_zero]

theorem Phi0 (M : Model) (k : ℕ) (y : ℝ) : Phi M 0 k y = 0 := by
  unfold Phi; rw [WW0, WW0, sub_zero]

theorem DD_nonneg (M : Model) (r k : ℕ) {y : ℝ} {C : Multiset ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hC : InI M C) : 0 ≤ DD (fun k S => M.valueAux r k S) k y C := by
  unfold DD
  rcases k with _ | k
  · simp [valueAux_k_zero]
  · simp only [Nat.add_sub_cancel]
    have h1 := valueAux_mono_k M r k (y ::ₘ C) (InI_cons hy hC)
    have h2 := valueAux_mono_add M r k C y hC hy
    linarith

theorem DD_le (M : Model) (r k : ℕ) {y : ℝ} {C : Multiset ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hC : InI M C) : DD (fun k S => M.valueAux r k S) k y C ≤ k * M.m M.vhi := by
  unfold DD
  have h1 := valueAux_le M r k _ (InI_cons hy hC)
  have h2 := valueAux_nonneg M r (k - 1) C
  linarith

theorem DD_meas (M : Model) (r k : ℕ) (y : ℝ) (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => DD (fun k S => M.valueAux r k S) k y (cohort x)) := by
  have h1 := vgood_add M r k (y ::ₘ 0) n
  have h2 := vgood_add M r (k - 1) 0 n
  simp only [Multiset.cons_add, zero_add] at h1 h2
  exact h1.sub h2

theorem DD_mono_y (M : Model) (r k : ℕ) {y y' : ℝ} {C : Multiset ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hy' : y' ∈ Set.Icc M.vlo M.vhi) (hyy : y ≤ y') (hC : InI M C) :
    DD (fun k S => M.valueAux r k S) k y C ≤ DD (fun k S => M.valueAux r k S) k y' C := by
  unfold DD
  have := (valueAux_lip M r k C y y' hC hy hy' hyy).1
  linarith

theorem Phi_DD (M : Model) (r k : ℕ) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) :
    Phi M r k y = M.δ * M.cohortExp (M.T + 1 - r) (fun C => DD (fun k S => M.valueAux r k S) k y C) := by
  unfold Phi WW
  have h := CE_add M (M.T + 1 - r) (f := fun C => M.valueAux r (k - 1) (0 + C))
    (g := fun C => DD (fun k S => M.valueAux r k S) k y C) (vgood_add M r (k - 1) 0)
    (fun _ _ => valueAux_nonneg M _ _ _) (fun C hC => DD_nonneg M r k hy hC)
    (((k - 1 : ℕ) : ℝ) * M.m M.vhi) (k * M.m M.vhi) (valueAux_le' M r (k - 1) 0 (InI_zero M))
    (fun C hC => DD_le M r k hy hC)
  have e : M.cohortExp (M.T + 1 - r) (fun C => M.valueAux r (k - 1) (0 + C) +
      DD (fun k S => M.valueAux r k S) k y C) =
      M.cohortExp (M.T + 1 - r) (fun C => M.valueAux r k (y ::ₘ 0 + C)) :=
    CE_congr M _ fun C _ => by simp [DD, Multiset.cons_add]
  rw [← e, h]
  ring

theorem CE_st_le_anti (M : Model) {s s' : ℕ}
    (hss : StochasticOrders.Usual.UsualOrder (M.arrivals s).toMeasure (M.arrivals s').toMeasure
      (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (n : ℝ)))
    {g : Multiset ℝ → ℝ} (hg : ∀ n, Measurable (fun x : Fin n → ℝ => g (cohort x)))
    (hg0 : ∀ C, InI M C → 0 ≤ g C) (K : ℝ) (hK0 : 0 ≤ K) (hgK : ∀ C, InI M C → g C ≤ K)
    (hanti : ∀ C w, InI M C → w ∈ Set.Icc M.vlo M.vhi → g (w ::ₘ C) ≤ g C) :
    M.cohortExp s' g ≤ M.cohortExp s g := by
  have h1 := CE_st_le M hss (f := fun C => K - g C) (fun n => measurable_const.sub (hg n)) K
    (fun C hC => by linarith [hg0 C hC]) (fun C w hC hw => by linarith [hanti C w hC hw])
  have hsum : ∀ s0, M.cohortExp s0 (fun C => K - g C) + M.cohortExp s0 g = K := by
    intro s0
    have h2 := CE_add M s0 (f := g) (g := fun C => K - g C) hg hg0 (fun C hC => by linarith [hgK C hC])
      K K hgK (fun C hC => by linarith [hg0 C hC])
    have e : M.cohortExp s0 (fun C => g C + (K - g C)) = K := by
      rw [CE_congr M s0 (f := fun C => g C + (K - g C)) (g := fun _ => K) (fun C _ => by ring),
        CE_const M s0 K hK0]
    linarith
  linarith [hsum s, hsum s']

theorem max_diff_anti {a b c a' b' c' : ℝ} (hab : b ≤ a) (hab' : b' ≤ a')
    (h1 : a' - b' ≤ a - b) (h2 : a' - c' ≤ a - c) :
    max a' c' - max b' c' ≤ max a c - max b c := by
  rw [max_def, max_def, max_def, max_def]
  split_ifs <;> linarith

theorem rho_mono (M : Model) (r j : ℕ) {z z' : ℝ} (hz : z ∈ Set.Icc M.vlo M.vhi)
    (hz' : z' ∈ Set.Icc M.vlo M.vhi) (hzz : z ≤ z') :
    M.m z - GG (fun k S => M.valueAux r k S) j z ≤ M.m z' - GG (fun k S => M.valueAux r k S) j z' := by
  have hm : M.m z ≤ M.m z' := M.m_strictMonoOn.monotoneOn hz hz' hzz
  rcases r with _ | r
  · have h0 : ∀ w, GG (fun k S => M.valueAux 0 k S) j w = 0 := fun w => by simp [GG, valueAux_zero]
    rw [h0, h0]; linarith
  · rcases j with _ | j
    · rw [GG0, GG0]; linarith
    · rw [GG_succ, GG_succ]
      have hl := (Phi_lip M r (j + 1) hz hz' hzz).2
      have hδ := M.δ_lt_one
      have hδ0 := M.δ_pos
      have hd : M.δ * (M.m z' - M.m z) ≤ M.m z' - M.m z := by nlinarith
      rw [max_def, max_def]
      split_ifs <;> linarith

theorem LL_nonneg (M : Model) (r k : ℕ) {y : ℝ} {C : Multiset ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hC : InI M C) : 0 ≤ LL M (fun k S => M.valueAux r k S) k y C := by
  by_cases hCy : ∀ c ∈ C, c ≤ y
  · rw [LL_low k hy hC hCy]
  · obtain ⟨c1, C', rfl, hC', hyc⟩ := top_or_le C y hCy
    have hc1 := hC c1 (Multiset.mem_cons_self _ _)
    have hC'I : InI M C' := fun a ha => hC a (Multiset.mem_cons_of_mem ha)
    rw [LL_high k hy hc1 hC' hyc]
    unfold DD
    have := (valueAux_lip M r (k - 1) C' y c1 hC'I hy hc1 hyc.le).2
    linarith

theorem LL_le (M : Model) (r k : ℕ) {y : ℝ} {C : Multiset ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi)
    (hC : InI M C) : LL M (fun k S => M.valueAux r k S) k y C ≤
      max (M.m M.vhi - M.m y) 0 + ((k - 1 : ℕ) : ℝ) * M.m M.vhi := by
  unfold LL
  have h1 := mpart_le M hy hC
  have h2 := valueAux_le M r (k - 1) _ (InI_dropTop (InI_cons hy hC) 1)
  have h3 := valueAux_nonneg M r (k - 1) C
  linarith

theorem measurable_cons {n : ℕ} (y : ℝ) :
    Measurable (fun x : Fin n → ℝ => (Fin.cons y x : Fin (n + 1) → ℝ)) := by
  refine measurable_pi_lambda _ fun j => ?_
  induction j using Fin.cases with
  | zero => simpa using measurable_const
  | succ i => simpa using measurable_pi_apply i

theorem LL_meas (M : Model) (r k : ℕ) (y : ℝ) (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => LL M (fun k S => M.valueAux r k S) k y (cohort x)) := by
  unfold LL
  have hc : ∀ x : Fin n → ℝ, y ::ₘ cohort x = cohort (Fin.cons y x : Fin (n + 1) → ℝ) := by
    intro x; rw [cohort_succ]; simp
  simp_rw [hc, dropTop_cohort]
  refine ((measurable_mpart M y n).add ?_).sub (vgood M r (k - 1) n)
  exact (vgood M r (k - 1) _).comp (measurable_pi_lambda _ fun i =>
    (measurable_pi_apply _).comp ((measurable_sdesc _).comp (measurable_cons y)))

theorem DPi_LL (M : Model) (t k : ℕ) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) :
    M.DPi t k y = (1 - M.δ) * M.m y -
      M.δ * M.cohortExp (t + 1) (fun C => LL M (fun k S => M.valueAux (M.T + 1 - (t + 1)) k S) k y C) := by
  rw [DPi_eq_Psi M t k hy]
  have h := CE_add M (t + 1) (f := fun C => M.valueAux (M.T + 1 - (t + 1)) (k - 1) (0 + C))
    (g := fun C => LL M (fun k S => M.valueAux (M.T + 1 - (t + 1)) k S) k y C)
    (vgood_add M _ (k - 1) 0) (fun _ _ => valueAux_nonneg M _ _ _) (fun C hC => LL_nonneg M _ k hy hC)
    (((k - 1 : ℕ) : ℝ) * M.m M.vhi) (max (M.m M.vhi - M.m y) 0 + ((k - 1 : ℕ) : ℝ) * M.m M.vhi)
    (valueAux_le' M _ (k - 1) 0 (InI_zero M)) (fun C hC => LL_le M _ k hy hC)
  have e : M.cohortExp (t + 1) (fun C => M.valueAux (M.T + 1 - (t + 1)) (k - 1) (0 + C) +
      LL M (fun k S => M.valueAux (M.T + 1 - (t + 1)) k S) k y C) =
      M.cohortExp (t + 1) (fun C => Psi M (M.T + 1 - (t + 1)) k y C) :=
    CE_congr M _ fun C _ => by simp only [LL, Psi, zero_add]; ring
  rw [← e, h]
  unfold Model.piTilde Model.piVal
  ring

/-! ### The two-level invariant -/

/-- Pair `(r+1, r)`: `H = G_{r+1} - G_r` is nonincreasing and nonnegative. -/
def TMp (M : Model) (r : ℕ) : Prop :=
  (∀ j z z', z ∈ Set.Icc M.vlo M.vhi → z' ∈ Set.Icc M.vlo M.vhi → z ≤ z' →
    HH (fun k S => M.valueAux (r + 1) k S) (fun k S => M.valueAux r k S) j z' ≤
      HH (fun k S => M.valueAux (r + 1) k S) (fun k S => M.valueAux r k S) j z) ∧
  (∀ j z, z ∈ Set.Icc M.vlo M.vhi →
    0 ≤ HH (fun k S => M.valueAux (r + 1) k S) (fun k S => M.valueAux r k S) j z)

theorem HH_succ (M : Model) (r j : ℕ) (z : ℝ) :
    HH (fun k S => M.valueAux (r + 2) k S) (fun k S => M.valueAux (r + 1) k S) (j + 1) z =
      max (Phi M (r + 1) (j + 1) z) (M.m z) - max (Phi M r (j + 1) z) (M.m z) := by
  unfold HH
  rw [GG_succ (M := M) (r := r + 1), GG_succ (M := M) (r := r)]

theorem HH_zero (M : Model) (r : ℕ) (z : ℝ) :
    HH (fun k S => M.valueAux (r + 1) k S) (fun k S => M.valueAux r k S) 0 z = 0 := by
  unfold HH; rw [GG0, GG0, sub_zero]

theorem V1_zero_low (M : Model) : ∀ n (Z : Multiset ℝ) j, Multiset.card Z = n → InI M Z →
    (∀ z ∈ Z, M.m z ≤ 0) → M.valueAux 1 j Z = 0 := by
  intro n
  induction n with
  | zero =>
    intro Z j hZ _ _
    rw [Multiset.card_eq_zero.mp hZ, V_empty, WW0]
  | succ n ih =>
    intro Z j hZ hZI hm
    have hZ0 : Z ≠ 0 := by rintro rfl; simp at hZ
    obtain ⟨z1, Z', rfl, hZ'⟩ := exists_top Z hZ0
    have hz1 := hZI z1 (Multiset.mem_cons_self _ _)
    have hZ'I : InI M Z' := fun a ha => hZI a (Multiset.mem_cons_of_mem ha)
    rw [R1v M 1 j hz1 hZ'I hZ', ih Z' (j - 1) (by simpa using hZ) hZ'I
      (fun z hz => hm z (Multiset.mem_cons_of_mem hz))]
    rcases j with _ | j
    · rw [GG0]; ring
    · rw [GG_succ (M := M) (r := 0), Phi0]
      have := hm z1 (Multiset.mem_cons_self _ _)
      rw [max_eq_left this]; ring

theorem DD1_low (M : Model) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) (hmy : M.m y ≤ 0) :
    ∀ n (Z : Multiset ℝ) j, Multiset.card Z = n → InI M Z →
      DD (fun k S => M.valueAux 1 k S) j y Z = M.valueAux 1 j Z - M.valueAux 1 (j - 1) Z := by
  have I := inv_all M 1
  intro n
  induction n with
  | zero =>
    intro Z j hZ hZI
    rw [Multiset.card_eq_zero.mp hZ] at hZI ⊢
    rw [DD_eq_GG I j hy hZI (by simp), V_empty, V_empty, WW0, WW0]
    rcases j with _ | j
    · rw [GG0]; ring
    · rw [GG_succ (M := M) (r := 0), Phi0, max_eq_left hmy]; ring
  | succ n ih =>
    intro Z j hZ hZI
    by_cases hle : ∀ z ∈ Z, z ≤ y
    · have hmZ : ∀ z ∈ Z, M.m z ≤ 0 := fun z hz =>
        (M.m_strictMonoOn.monotoneOn (hZI z hz) hy (hle z hz) : M.m z ≤ M.m y).trans hmy
      rw [DD_eq_GG I j hy hZI hle, V1_zero_low M _ Z j rfl hZI hmZ,
        V1_zero_low M _ Z (j - 1) rfl hZI hmZ]
      rcases j with _ | j
      · rw [GG0]; ring
      · rw [GG_succ (M := M) (r := 0), Phi0, max_eq_left hmy]; ring
    · obtain ⟨z1, Z', rfl, hZ', hyz⟩ := top_or_le Z y hle
      have hz1 := hZI z1 (Multiset.mem_cons_self _ _)
      have hZ'I : InI M Z' := fun a ha => hZI a (Multiset.mem_cons_of_mem ha)
      rw [DD_cons I j hy hz1 hZ'I hyz.le hZ', ih Z' (j - 1) (by simpa using hZ) hZ'I,
        R1v M 1 j hz1 hZ'I hZ', R1v M 1 (j - 1) hz1 hZ'I hZ']
      unfold dG
      ring

theorem Phi1_const (M : Model) (j : ℕ) {z z' : ℝ} (hz : z ∈ Set.Icc M.vlo M.vhi)
    (hz' : z' ∈ Set.Icc M.vlo M.vhi) (hmz : M.m z ≤ 0) (hmz' : M.m z' ≤ 0) :
    Phi M 1 j z = Phi M 1 j z' := by
  rw [Phi_DD M 1 j hz, Phi_DD M 1 j hz']
  congr 1
  exact CE_congr M _ fun C hC => by
    rw [DD1_low M hz hmz _ C j rfl hC, DD1_low M hz' hmz' _ C j rfl hC]

theorem Phi_nonneg (M : Model) (r k : ℕ) {y : ℝ} (hy : y ∈ Set.Icc M.vlo M.vhi) : 0 ≤ Phi M r k y := by
  rw [Phi_DD M r k hy]
  exact mul_nonneg M.δ_pos.le (CE_nonneg _ _ _)

theorem tm_base (M : Model) : TMp M 1 := by
  refine ⟨fun j z z' hz hz' hzz => ?_, fun j z hz => ?_⟩
  · rcases j with _ | j
    · rw [HH_zero, HH_zero]
    · rw [HH_succ M 0 j z, HH_succ M 0 j z', Phi0, Phi0]
      have hm : M.m z ≤ M.m z' := M.m_strictMonoOn.monotoneOn hz hz' hzz
      have hP0 := Phi_nonneg M 1 (j + 1) hz
      have hP0' := Phi_nonneg M 1 (j + 1) hz'
      have hl := (Phi_lip M 1 (j + 1) hz hz' hzz).2
      have hδ := M.δ_lt_one
      have hδ0 := M.δ_pos
      have hd : M.δ * (M.m z' - M.m z) ≤ M.m z' - M.m z := by nlinarith
      simp only [Nat.zero_add] at *
      by_cases h1 : M.m z' ≤ 0
      · have h2 : M.m z ≤ 0 := hm.trans h1
        have hc := Phi1_const M (j + 1) hz hz' h2 h1
        rw [max_def, max_def, max_def, max_def]
        split_ifs <;> linarith
      · push Not at h1
        by_cases h2 : 0 < M.m z
        · rw [max_def, max_def, max_def, max_def]
          split_ifs <;> linarith
        · push Not at h2
          have hcont : ContinuousOn M.m (Set.Icc z z') :=
            M.m_contDiffOn.continuousOn.mono (Set.Icc_subset_Icc hz.1 hz'.2)
          obtain ⟨z0, hz0, hmz0⟩ := intermediate_value_Icc hzz hcont ⟨h2, h1.le⟩
          have hz0I : z0 ∈ Set.Icc M.vlo M.vhi := ⟨hz.1.trans hz0.1, hz0.2.trans hz'.2⟩
          have hc := Phi1_const M (j + 1) hz hz0I h2 hmz0.le
          have hl0 := (Phi_lip M 1 (j + 1) hz0I hz' hz0.2).2
          rw [hmz0] at hl0
          have hdm : M.δ * (M.m z' - 0) ≤ M.m z' := by nlinarith
          rw [max_def, max_def, max_def, max_def]
          split_ifs <;> linarith
  · rcases j with _ | j
    · rw [HH_zero]
    · rw [HH_succ M 0 j z, Phi0]
      exact sub_nonneg.mpr (max_le_max (Phi_nonneg M 1 (j + 1) hz) le_rfl)

theorem CE_four_le' (M : Model) (s : ℕ) {f1 f2 f3 f4 : Multiset ℝ → ℝ}
    (h1 : ∀ n, Measurable (fun x : Fin n → ℝ => f1 (cohort x)))
    (h3 : ∀ n, Measurable (fun x : Fin n → ℝ => f3 (cohort x)))
    (p1 : ∀ C, InI M C → 0 ≤ f1 C) (p2 : ∀ C, InI M C → 0 ≤ f2 C)
    (p3 : ∀ C, InI M C → 0 ≤ f3 C) (p4 : ∀ C, InI M C → 0 ≤ f4 C) (B : ℝ)
    (b1 : ∀ C, InI M C → f1 C ≤ B) (b2 : ∀ C, InI M C → f2 C ≤ B)
    (b3 : ∀ C, InI M C → f3 C ≤ B) (b4 : ∀ C, InI M C → f4 C ≤ B)
    (h : ∀ C, InI M C → f1 C + f2 C ≤ f3 C + f4 C) :
    M.cohortExp s f1 + M.cohortExp s f2 ≤ M.cohortExp s f3 + M.cohortExp s f4 := by
  rw [← CE_add M s h1 p1 p2 B B b1 b2, ← CE_add M s h3 p3 p4 B B b3 b4]
  exact CE_mono M s (B + B) h (fun C hC => add_le_add (b3 C hC) (b4 C hC))

theorem tm_step (M : Model) (hD : M.DecreasingDemand) (r : ℕ) (hr : 1 ≤ r) (hrT : r + 1 ≤ M.T)
    (ih : TMp M r) : TMp M (r + 1) := by
  have I := inv_all M r
  have I1 := inv_all M (r + 1)
  have hst := hD (M.T - r) (by omega) (by omega)
  have e1 : M.T - r + 1 = M.T + 1 - r := by omega
  have e2 : M.T - r = M.T + 1 - (r + 1) := by omega
  rw [e1, e2] at hst
  -- A(z) ≥ B(z)
  have hAB : ∀ j z, z ∈ Set.Icc M.vlo M.vhi → Phi M r j z ≤ Phi M (r + 1) j z := by
    intro j z hz
    rw [Phi_DD M r j hz, Phi_DD M (r + 1) j hz]
    have hδ0 := M.δ_pos
    have h1 : M.cohortExp (M.T + 1 - r) (fun C => DD (fun k S => M.valueAux r k S) j z C) ≤
        M.cohortExp (M.T + 1 - (r + 1)) (fun C => DD (fun k S => M.valueAux r k S) j z C) :=
      CE_st_le M hst (DD_meas M r j z) (j * M.m M.vhi) (fun C hC => DD_le M r j hz hC)
        (fun C w hC hw => DD_mono_add I hz hw _ C j rfl hC)
    have h2 : M.cohortExp (M.T + 1 - (r + 1)) (fun C => DD (fun k S => M.valueAux r k S) j z C) ≤
        M.cohortExp (M.T + 1 - (r + 1)) (fun C => DD (fun k S => M.valueAux (r + 1) k S) j z C) :=
      CE_mono M _ (j * M.m M.vhi) (fun C hC => pair_A I1 I ih.1 ih.2 hz C hC j)
        (fun C hC => DD_le M (r + 1) j hz hC)
    nlinarith
  -- A - B nonincreasing
  have hAB2 : ∀ j z z', z ∈ Set.Icc M.vlo M.vhi → z' ∈ Set.Icc M.vlo M.vhi → z ≤ z' →
      Phi M (r + 1) j z' - Phi M r j z' ≤ Phi M (r + 1) j z - Phi M r j z := by
    intro j z z' hz hz' hzz
    rw [Phi_DD M r j hz, Phi_DD M (r + 1) j hz, Phi_DD M r j hz', Phi_DD M (r + 1) j hz']
    set s1 := M.T + 1 - (r + 1)
    set s0 := M.T + 1 - r
    have B : ℝ := j * M.m M.vhi
    -- level r+1 vs level r at the same entrants (pair_B1)
    have k1 := CE_four_le' M s1 (f1 := fun C => DD (fun k S => M.valueAux (r + 1) k S) j z' C)
      (f2 := fun C => DD (fun k S => M.valueAux r k S) j z C)
      (f3 := fun C => DD (fun k S => M.valueAux (r + 1) k S) j z C)
      (f4 := fun C => DD (fun k S => M.valueAux r k S) j z' C)
      (DD_meas M (r + 1) j z') (DD_meas M (r + 1) j z)
      (fun C hC => DD_nonneg M _ j hz' hC) (fun C hC => DD_nonneg M _ j hz hC)
      (fun C hC => DD_nonneg M _ j hz hC) (fun C hC => DD_nonneg M _ j hz' hC) (j * M.m M.vhi)
      (fun C hC => DD_le M _ j hz' hC) (fun C hC => DD_le M _ j hz hC)
      (fun C hC => DD_le M _ j hz hC) (fun C hC => DD_le M _ j hz' hC)
      (fun C hC => by
        have := pair_B1 I1 I ih.1 hz hz' hzz _ C j rfl hC
        linarith)
    -- fewer entrants raise the upgrade value of level r
    have hg : ∀ s0', M.cohortExp s0' (fun C => DD (fun k S => M.valueAux r k S) j z' C) =
        M.cohortExp s0' (fun C => DD (fun k S => M.valueAux r k S) j z C) +
        M.cohortExp s0' (fun C => DD (fun k S => M.valueAux r k S) j z' C -
          DD (fun k S => M.valueAux r k S) j z C) := by
      intro s0'
      rw [← CE_add M s0' (DD_meas M r j z) (fun C hC => DD_nonneg M _ j hz hC)
        (fun C hC => sub_nonneg.mpr (DD_mono_y M r j hz hz' hzz hC)) (j * M.m M.vhi) (j * M.m M.vhi)
        (fun C hC => DD_le M _ j hz hC)
        (fun C hC => by linarith [DD_le M r j hz' hC, DD_nonneg M r j hz hC])]
      exact CE_congr M _ fun C _ => by ring
    have k2 := CE_st_le_anti M hst (g := fun C => DD (fun k S => M.valueAux r k S) j z' C -
        DD (fun k S => M.valueAux r k S) j z C)
      (fun n => (DD_meas M r j z' n).sub (DD_meas M r j z n))
      (fun C hC => sub_nonneg.mpr (DD_mono_y M r j hz hz' hzz hC)) (j * M.m M.vhi)
      (mul_nonneg (Nat.cast_nonneg _) (mvhi_pos M).le)
      (fun C hC => by linarith [DD_le M r j hz' hC, DD_nonneg M r j hz hC])
      (fun C w hC hw => by
        have := DD_sub I hz hz' hzz hw _ C j rfl hC
        linarith)
    have hδ0 := M.δ_pos
    rw [hg s1, hg s0] at *
    nlinarith
  refine ⟨fun j z z' hz hz' hzz => ?_, fun j z hz => ?_⟩
  · rcases j with _ | j
    · rw [HH_zero, HH_zero]
    · rw [show r + 1 + 1 = r + 2 from rfl, HH_succ M r j z, HH_succ M r j z']
      have hl := (Phi_lip M (r + 1) (j + 1) hz hz' hzz).2
      have hm : M.m z ≤ M.m z' := M.m_strictMonoOn.monotoneOn hz hz' hzz
      have hδ := M.δ_lt_one
      have hδ0 := M.δ_pos
      have hd : M.δ * (M.m z' - M.m z) ≤ M.m z' - M.m z := by nlinarith
      exact max_diff_anti (hAB (j + 1) z hz) (hAB (j + 1) z' hz') (hAB2 (j + 1) z z' hz hz' hzz)
        (by linarith)
  · rcases j with _ | j
    · rw [HH_zero]
    · rw [show r + 1 + 1 = r + 2 from rfl, HH_succ M r j z]
      exact sub_nonneg.mpr (max_le_max (hAB (j + 1) z hz) le_rfl)

theorem tm_all (M : Model) (hD : M.DecreasingDemand) : ∀ r, 1 ≤ r → r ≤ M.T → TMp M r := by
  intro r hr hrT
  induction r with
  | zero => omega
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; exact tm_base M
    · exact tm_step M hD r h0 hrT (ih h0 (by omega))

/-- Sibling da7d7c54's content (without its cutoff hypothesis): `DΠ^k_t ≤ DΠ^k_{t+1}`. -/
theorem DPi_le_succ (M : Model) (hD : M.DecreasingDemand) (t k : ℕ) (ht : 1 ≤ t) (ht2 : t + 2 ≤ M.T)
    (y : ℝ) (hy : y ∈ Set.Icc M.vlo M.vhi) : M.DPi t k y ≤ M.DPi (t + 1) k y := by
  rw [DPi_LL M t k hy, DPi_LL M (t + 1) k hy]
  set r := M.T - t - 1 with hr
  have e1 : M.T + 1 - (t + 1) = r + 1 := by omega
  have e2 : M.T + 1 - (t + 1 + 1) = r := by omega
  rw [e1, e2]
  have hTM := tm_all M hD r (by omega) (by omega)
  have I := inv_all M r
  have I1 := inv_all M (r + 1)
  have hst := hD (t + 1) (by omega) ht2
  have h1 : M.cohortExp (t + 1 + 1) (fun C => LL M (fun k S => M.valueAux r k S) k y C) ≤
      M.cohortExp (t + 1 + 1) (fun C => LL M (fun k S => M.valueAux (r + 1) k S) k y C) :=
    CE_mono M _ _ (fun C hC => pair_LL I1 I hTM.1 k hy hC) (fun C hC => LL_le M _ k hy hC)
  have h2 : M.cohortExp (t + 1 + 1) (fun C => LL M (fun k S => M.valueAux (r + 1) k S) k y C) ≤
      M.cohortExp (t + 1) (fun C => LL M (fun k S => M.valueAux (r + 1) k S) k y C) :=
    CE_st_le M hst (LL_meas M (r + 1) k y) _ (fun C hC => LL_le M _ k hy hC)
      (fun C w hC hw => LL_mono_add I1 (fun j z z' hz hz' hzz => rho_mono M (r + 1) j hz hz' hzz)
        k hy hw hC)
  have hδ0 := M.δ_pos
  nlinarith

end FRM18

open ForwardRM.Cutoffs in
theorem solution (M : Model) (hD : M.DecreasingDemand)
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ t, 1 ≤ t → t + 1 ≤ M.T → M.cutoff (t + 1) k ≤ M.cutoff t k) ∧
    (∀ t, 1 ≤ t → t + 1 ≤ M.T →
      M.DPi t k (M.cutoff t k) = 0 ∧
      ∀ y ∈ Set.Icc M.vlo M.vhi, M.DPi t k y = 0 → y = M.cutoff t k) := by
  exact FRM18.parent_of_inc M
    (fun t k' ht ht2 _ _ y1 hy1 => FRM18.DPi_le_succ M hD t k' ht ht2 y1 hy1) k hk
