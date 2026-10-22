-- Prove2me | solution 1 for FairProxy.ClosedFormDD.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T13:40:33.898504+00:00
-- url     : https://prove2.me/submissions/6173c84d-fe20-4741-af2f-0ef157784460

import Mathlib
import Definitions.Def_FairProxy_ClosedFormDD_Model

set_option autoImplicit false

namespace FairProxy.ClosedFormDD.P7Aux
open MeasureTheory FairProxy.ClosedFormDD

variable {Z : Type*} [MeasurableSpace Z]

lemma sum_cls (f : Cls → ℝ) : ∑ α, f α = f .a + f .b := by
  rw [show (Finset.univ : Finset Cls) = {.a, .b} from rfl]
  simp

lemma aux_nonneg {M : Marginals Z} (hM : M.Valid) (α : Cls) (z : Z) :
    0 ≤ M.etaAux α z := hM.2.2.2.1 α z

lemma aux_b {M : Marginals Z} (hM : M.Valid) (z : Z) :
    M.etaAux .b z = 1 - M.etaAux .a z := by
  have h := hM.2.2.2.2.1 z
  rw [sum_cls] at h
  linarith

lemma aux_le {M : Marginals Z} (hM : M.Valid) (α : Cls) (z : Z) :
    M.etaAux α z ≤ 1 := by
  have h1 := aux_b hM z
  have h2 := aux_nonneg hM .a z
  have h3 := aux_nonneg hM .b z
  cases α <;> linarith

lemma priT_nonneg {M : Marginals Z} (hM : M.Valid) (ŷ y : Fin 2) (z : Z) :
    0 ≤ M.etaPriT ŷ y z := hM.2.2.2.2.2.1 ŷ y z

lemma pri_sum {M : Marginals Z} (hM : M.Valid) (z : Z) :
    etaPri M 0 z + etaPri M 1 z = 1 := by
  have h := hM.2.2.2.2.2.2 z
  rw [Fin.sum_univ_two] at h
  exact h

lemma pri_nonneg {M : Marginals Z} (hM : M.Valid) (ŷ : Fin 2) (z : Z) :
    0 ≤ etaPri M ŷ z :=
  Finset.sum_nonneg (fun y _ => priT_nonneg hM ŷ y z)

lemma pri1_le {M : Marginals Z} (hM : M.Valid) (z : Z) : etaPri M 1 z ≤ 1 := by
  have := pri_sum hM z
  have := pri_nonneg hM 0 z
  linarith

lemma priT_le_one {M : Marginals Z} (hM : M.Valid) (ŷ y : Fin 2) (z : Z) :
    M.etaPriT ŷ y z ≤ 1 := by
  have h := hM.2.2.2.2.2.2 z
  calc M.etaPriT ŷ y z ≤ ∑ y', M.etaPriT ŷ y' z :=
        Finset.single_le_sum (fun y' _ => priT_nonneg hM ŷ y' z) (Finset.mem_univ y)
    _ ≤ ∑ ŷ', ∑ y', M.etaPriT ŷ' y' z :=
        Finset.single_le_sum (f := fun ŷ' => ∑ y', M.etaPriT ŷ' y' z)
          (fun ŷ' _ => Finset.sum_nonneg (fun y' _ => priT_nonneg hM ŷ' y' z))
          (Finset.mem_univ ŷ)
    _ = 1 := h

lemma meas_pri {M : Marginals Z} (hM : M.Valid) (ŷ : Fin 2) :
    Measurable (etaPri M ŷ) := by
  show Measurable (fun z => ∑ y, M.etaPriT ŷ y z)
  exact Finset.measurable_sum _ (fun y _ => hM.2.2.1 ŷ y)

lemma integ_bdd {M : Marginals Z} (hM : M.Valid) {f : Z → ℝ} (hf : Measurable f)
    (hb : ∀ z, |f z| ≤ 1) : Integrable f M.PZ := by
  have := hM.1
  exact Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hb z))

/-- Fréchet lower envelope for the group-`a` positive mass. -/
noncomputable def Lo (M : Marginals Z) (z : Z) : ℝ :=
  max 0 (etaPri M 1 z + M.etaAux .a z - 1)

/-- Fréchet upper envelope for the group-`a` positive mass. -/
noncomputable def Up (M : Marginals Z) (z : Z) : ℝ :=
  min (etaPri M 1 z) (M.etaAux .a z)

lemma meas_Lo {M : Marginals Z} (hM : M.Valid) : Measurable (Lo M) := by
  unfold Lo
  exact measurable_const.max (((meas_pri hM 1).add (hM.2.1 .a)).sub measurable_const)

lemma meas_Up {M : Marginals Z} (hM : M.Valid) : Measurable (Up M) := by
  unfold Up
  exact (meas_pri hM 1).min (hM.2.1 .a)

lemma Lo_nonneg (M : Marginals Z) (z : Z) : 0 ≤ Lo M z := le_max_left _ _

lemma Lo_le_Up {M : Marginals Z} (hM : M.Valid) (z : Z) : Lo M z ≤ Up M z := by
  unfold Lo Up
  have := pri_nonneg hM 1 z
  have := pri1_le hM z
  have := aux_nonneg hM .a z
  have := aux_le hM .a z
  exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith))

lemma Up_le_p1 (M : Marginals Z) (z : Z) : Up M z ≤ etaPri M 1 z := min_le_left _ _
lemma Up_le_e (M : Marginals Z) (z : Z) : Up M z ≤ M.etaAux .a z := min_le_right _ _
lemma Lo_ge (M : Marginals Z) (z : Z) : etaPri M 1 z + M.etaAux .a z - 1 ≤ Lo M z :=
  le_max_right _ _

lemma integ_Lo {M : Marginals Z} (hM : M.Valid) : Integrable (Lo M) M.PZ :=
  integ_bdd hM (meas_Lo hM) (fun z => by
    have h1 := Lo_nonneg M z
    have h2 := Lo_le_Up hM z
    have h3 := Up_le_p1 M z
    have h4 := pri1_le hM z
    rw [abs_le]; constructor <;> linarith)

lemma integ_Up {M : Marginals Z} (hM : M.Valid) : Integrable (Up M) M.PZ :=
  integ_bdd hM (meas_Up hM) (fun z => by
    have h1 := Lo_nonneg M z
    have h2 := Lo_le_Up hM z
    have h3 := Up_le_p1 M z
    have h4 := pri1_le hM z
    rw [abs_le]; constructor <;> linarith)

lemma integ_p1 {M : Marginals Z} (hM : M.Valid) : Integrable (etaPri M 1) M.PZ :=
  integ_bdd hM (meas_pri hM 1) (fun z => by
    have h1 := pri_nonneg hM 1 z
    have h4 := pri1_le hM z
    rw [abs_le]; constructor <;> linarith)

/-! ### The closed forms of `mu`. -/

lemma mu_sum (M : Marginals Z) (w : Cls → Fin 2 → Z → ℝ) (α : Cls) (z : Z) :
    ∑ ŷ : Fin 2, w α ŷ z * ((ŷ : ℕ) : ℝ) * etaPri M ŷ z = w α 1 z * etaPri M 1 z := by
  simp [Fin.sum_univ_two]

lemma wL_mul {M : Marginals Z} (hM : M.Valid) (α : Cls) (z : Z) :
    wL M α 1 z * etaPri M 1 z = max 0 (etaPri M 1 z + M.etaAux α z - 1) := by
  unfold wL
  have he := aux_le hM α z
  rcases (pri_nonneg hM 1 z).eq_or_lt with h | h
  · rw [← h]
    simp only [mul_zero, zero_add]
    exact (max_eq_left (by linarith)).symm
  · rw [max_mul_of_nonneg _ _ h.le, zero_mul, add_mul, div_mul_cancel₀ _ h.ne']
    congr 1
    ring

lemma wU_mul {M : Marginals Z} (hM : M.Valid) (α : Cls) (z : Z) :
    wU M α 1 z * etaPri M 1 z = min (etaPri M 1 z) (M.etaAux α z) := by
  unfold wU
  have he := aux_nonneg hM α z
  rcases (pri_nonneg hM 1 z).eq_or_lt with h | h
  · rw [← h]
    simp only [mul_zero]
    exact (min_eq_left he).symm
  · rw [min_mul_of_nonneg _ _ h.le, one_mul, div_mul_cancel₀ _ h.ne']

lemma mu_a_wL {M : Marginals Z} (hM : M.Valid) :
    mu M .a (wL M) = (∫ z, Lo M z ∂M.PZ) / probA M .a := by
  unfold mu Lo
  simp only [mu_sum, wL_mul hM]

lemma mu_a_wU {M : Marginals Z} (hM : M.Valid) :
    mu M .a (wU M) = (∫ z, Up M z ∂M.PZ) / probA M .a := by
  unfold mu Up
  simp only [mu_sum, wU_mul hM]

lemma mu_b_wU {M : Marginals Z} (hM : M.Valid) :
    mu M .b (wU M) = (∫ z, (etaPri M 1 z - Lo M z) ∂M.PZ) / probA M .b := by
  unfold mu
  simp only [mu_sum, wU_mul hM]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [aux_b hM z, Lo]
  rcases le_total (etaPri M 1 z + M.etaAux .a z - 1) 0 with h | h
  · rw [max_eq_left h, min_eq_left (by linarith)]; ring
  · rw [max_eq_right h, min_eq_right (by linarith)]; ring

lemma mu_b_wL {M : Marginals Z} (hM : M.Valid) :
    mu M .b (wL M) = (∫ z, (etaPri M 1 z - Up M z) ∂M.PZ) / probA M .b := by
  unfold mu
  simp only [mu_sum, wL_mul hM]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [aux_b hM z, Up]
  rcases le_total (etaPri M 1 z) (M.etaAux .a z) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]; ring

/-! ### Facts about consistent joints. -/

/-- Group-`a` positive-decision mass of a candidate joint. -/
noncomputable def qa (π : Cls → Fin 2 → Fin 2 → Z → ℝ) (z : Z) : ℝ := ∑ y, π .a 1 y z

lemma pd_unfold {M : Marginals Z} {π : Cls → Fin 2 → Fin 2 → Z → ℝ} (hπ : IsInPD M π) (z : Z) :
    (∀ ŷ y, ∑ α, π α ŷ y z = M.etaPriT ŷ y z) ∧
    (∀ α, ∑ ŷ, ∑ y, π α ŷ y z = M.etaAux α z) ∧
    (∀ α ŷ y, 0 ≤ π α ŷ y z ∧ π α ŷ y z ≤ 1) := by
  have h := hπ.2 z
  simp only [couplingSet, Set.mem_ofPred_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun ŷ y => h1 (ŷ, y), fun α => ?_, fun α ŷ y => h3 (ŷ, y) α⟩
  have := h2 α
  rw [Fintype.sum_prod_type] at this
  exact this

lemma pd_qb {M : Marginals Z} {π : Cls → Fin 2 → Fin 2 → Z → ℝ} (hπ : IsInPD M π) (z : Z) :
    ∑ y, π .b 1 y z = etaPri M 1 z - qa π z := by
  have hc := (pd_unfold hπ z).1
  have h2 : ∑ y, M.etaPriT 1 y z = ∑ y, (π .a 1 y z + π .b 1 y z) :=
    Finset.sum_congr rfl (fun y _ => by rw [← hc 1 y, sum_cls])
  show _ = ∑ y, M.etaPriT 1 y z - qa π z
  rw [h2, Finset.sum_add_distrib, qa]
  ring

lemma pd_bounds {M : Marginals Z} (hM : M.Valid) {π : Cls → Fin 2 → Fin 2 → Z → ℝ}
    (hπ : IsInPD M π) (z : Z) : Lo M z ≤ qa π z ∧ qa π z ≤ Up M z := by
  obtain ⟨_, hr, hb⟩ := pd_unfold hπ z
  have hqb := pd_qb hπ z
  have nn : ∀ α ŷ, 0 ≤ ∑ y, π α ŷ y z := fun α ŷ => Finset.sum_nonneg (fun y _ => (hb α ŷ y).1)
  have ra := hr .a
  have rb := hr .b
  rw [Fin.sum_univ_two] at ra rb
  have h0a := nn .a 0
  have h0b := nn .b 0
  have h1a := nn .a 1
  have h1b := nn .b 1
  have hbe := aux_b hM z
  unfold qa at hqb ⊢
  unfold Lo Up
  exact ⟨max_le h1a (by linarith), le_min (by linarith) (by linarith)⟩

lemma meas_qa {M : Marginals Z} {π : Cls → Fin 2 → Fin 2 → Z → ℝ} (hπ : IsInPD M π) :
    Measurable (qa π) := by
  show Measurable (fun z => ∑ y, π .a 1 y z)
  exact Finset.measurable_sum _ (fun y _ => hπ.1 .a 1 y)

lemma integ_qa {M : Marginals Z} (hM : M.Valid) {π : Cls → Fin 2 → Fin 2 → Z → ℝ}
    (hπ : IsInPD M π) : Integrable (qa π) M.PZ :=
  integ_bdd hM (meas_qa hπ) (fun z => by
    have h := pd_bounds hM hπ z
    have h1 := Lo_nonneg M z
    have h3 := Up_le_p1 M z
    have h4 := pri1_le hM z
    rw [abs_le]; constructor <;> linarith)

lemma condPos_eq {M : Marginals Z} {π : Cls → Fin 2 → Fin 2 → Z → ℝ} (hπ : IsInPD M π)
    (α : Cls) : condPosRate M π α = (∫ z, ∑ y, π α 1 y z ∂M.PZ) / probA M α := by
  unfold condPosRate probA
  simp only [(pd_unfold hπ _).2.1]

lemma dd_eq {M : Marginals Z} {π : Cls → Fin 2 → Fin 2 → Z → ℝ} (hπ : IsInPD M π) :
    deltaDD M π = (∫ z, qa π z ∂M.PZ) / probA M .a
      - (∫ z, (etaPri M 1 z - qa π z) ∂M.PZ) / probA M .b := by
  unfold deltaDD
  rw [condPos_eq hπ, condPos_eq hπ]
  simp only [pd_qb hπ]
  rfl

/-! ### The interpolating joints. -/

/-- Interpolated group-`a` positive mass. -/
noncomputable def qt (M : Marginals Z) (t : ℝ) (z : Z) : ℝ := Lo M z + t * (Up M z - Lo M z)

/-- Numerator of the within-cell share of group `a`. -/
noncomputable def num (M : Marginals Z) (t : ℝ) (ŷ : Fin 2) (z : Z) : ℝ :=
  if ŷ = 1 then qt M t z else M.etaAux .a z - qt M t z

/-- Within-cell share of group `a`. -/
noncomputable def lam (M : Marginals Z) (t : ℝ) (ŷ : Fin 2) (z : Z) : ℝ :=
  num M t ŷ z / etaPri M ŷ z

/-- The interpolating joint. -/
noncomputable def piT (M : Marginals Z) (t : ℝ) (α : Cls) (ŷ y : Fin 2) (z : Z) : ℝ :=
  (if α = .a then lam M t ŷ z else 1 - lam M t ŷ z) * M.etaPriT ŷ y z

lemma div_facts {x c : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ c) :
    0 ≤ x / c ∧ x / c ≤ 1 ∧ x / c * c = x := by
  rcases (h0.trans h1).eq_or_lt with hc | hc
  · have hx : x = 0 := by linarith
    subst hx
    simp
  · exact ⟨div_nonneg h0 hc.le, (div_le_one hc).2 h1, div_mul_cancel₀ x hc.ne'⟩

lemma qt_bounds {M : Marginals Z} (hM : M.Valid) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : Z) :
    Lo M z ≤ qt M t z ∧ qt M t z ≤ Up M z := by
  have h := Lo_le_Up hM z
  unfold qt
  have h2 : 0 ≤ t * (Up M z - Lo M z) := mul_nonneg ht0 (by linarith)
  have h3 : t * (Up M z - Lo M z) ≤ Up M z - Lo M z :=
    mul_le_of_le_one_left (by linarith) ht1
  constructor <;> linarith

lemma fin2_cases (ŷ : Fin 2) : ŷ = 0 ∨ ŷ = 1 := by
  fin_cases ŷ <;> simp

lemma num_bounds {M : Marginals Z} (hM : M.Valid) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ŷ : Fin 2) (z : Z) : 0 ≤ num M t ŷ z ∧ num M t ŷ z ≤ etaPri M ŷ z := by
  obtain ⟨hl, hu⟩ := qt_bounds hM ht0 ht1 z
  have h1 := Lo_nonneg M z
  have h2 := Up_le_p1 M z
  have h3 := Up_le_e M z
  have h4 := Lo_ge M z
  have h5 := pri_sum hM z
  rcases fin2_cases ŷ with rfl | rfl
  · simp only [num, show ((0 : Fin 2) = 1) = False from by decide, if_false]
    constructor <;> linarith
  · simp only [num, if_true]
    constructor <;> linarith

lemma lam_facts {M : Marginals Z} (hM : M.Valid) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ŷ : Fin 2) (z : Z) :
    0 ≤ lam M t ŷ z ∧ lam M t ŷ z ≤ 1 ∧ lam M t ŷ z * etaPri M ŷ z = num M t ŷ z := by
  obtain ⟨h0, h1⟩ := num_bounds hM ht0 ht1 ŷ z
  exact div_facts h0 h1

lemma meas_qt {M : Marginals Z} (hM : M.Valid) (t : ℝ) : Measurable (qt M t) := by
  unfold qt
  exact (meas_Lo hM).add (measurable_const.mul ((meas_Up hM).sub (meas_Lo hM)))

lemma meas_lam {M : Marginals Z} (hM : M.Valid) (t : ℝ) (ŷ : Fin 2) :
    Measurable (lam M t ŷ) := by
  unfold lam num
  by_cases h : ŷ = 1
  · simp only [h, if_true]
    exact (meas_qt hM t).div (meas_pri hM 1)
  · simp only [h, if_false]
    exact ((hM.2.1 .a).sub (meas_qt hM t)).div (meas_pri hM ŷ)

lemma piT_mem {M : Marginals Z} (hM : M.Valid) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsInPD M (piT M t) := by
  refine ⟨fun α ŷ y => ?_, fun z => ?_⟩
  · unfold piT
    by_cases h : α = .a
    · simp only [h, if_true]
      exact (meas_lam hM t ŷ).mul (hM.2.2.1 ŷ y)
    · simp only [h, if_false]
      exact (measurable_const.sub (meas_lam hM t ŷ)).mul (hM.2.2.1 ŷ y)
  · simp only [couplingSet, Set.mem_ofPred_eq]
    refine ⟨fun s => ?_, fun α => ?_, fun s α => ?_⟩
    · rw [sum_cls]
      simp only [piT, if_true, reduceCtorEq, if_false]
      ring
    · rw [Fintype.sum_prod_type]
      have hl0 := (lam_facts hM ht0 ht1 0 z).2.2
      have hl1 := (lam_facts hM ht0 ht1 1 z).2.2
      have hs := pri_sum hM z
      have hn0 : num M t 0 z = M.etaAux .a z - qt M t z := by
        simp only [num, show ((0 : Fin 2) = 1) = False from by decide, if_false]
      have hn1 : num M t 1 z = qt M t z := by simp only [num, if_true]
      have hp : ∀ ŷ : Fin 2, ∑ y, M.etaPriT ŷ y z = etaPri M ŷ z := fun ŷ => rfl
      cases α
      · simp only [piT, if_true]
        simp only [← Finset.mul_sum, hp, Fin.sum_univ_two]
        rw [hl0, hl1, hn0, hn1]
        ring
      · simp only [piT, reduceCtorEq, if_false]
        simp only [← Finset.mul_sum, hp, Fin.sum_univ_two]
        rw [sub_mul, sub_mul, one_mul, one_mul, hl0, hl1, hn0, hn1, aux_b hM z]
        linarith
    · obtain ⟨l0, l1, -⟩ := lam_facts hM ht0 ht1 s.1 z
      have e0 := priT_nonneg hM s.1 s.2 z
      have e1 := priT_le_one hM s.1 s.2 z
      unfold piT
      by_cases h : α = .a
      · simp only [h, if_true]
        exact ⟨mul_nonneg l0 e0, mul_le_one₀ l1 e0 e1⟩
      · simp only [h, if_false]
        exact ⟨mul_nonneg (by linarith) e0, mul_le_one₀ (by linarith) e0 e1⟩

lemma qa_piT {M : Marginals Z} (hM : M.Valid) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : Z) :
    qa (piT M t) z = qt M t z := by
  have hl1 := (lam_facts hM ht0 ht1 1 z).2.2
  have hn1 : num M t 1 z = qt M t z := by simp only [num, if_true]
  unfold qa
  simp only [piT, if_true]
  rw [← Finset.mul_sum]
  show lam M t 1 z * etaPri M 1 z = _
  rw [hl1, hn1]

lemma exists_t {lo hi d : ℝ} (h1 : lo ≤ d) (h2 : d ≤ hi) :
    ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ lo + t * (hi - lo) = d := by
  rcases (h1.trans h2).eq_or_lt with h | h
  · exact ⟨0, le_rfl, zero_le_one, by rw [zero_mul, add_zero]; linarith⟩
  · have hk : 0 < hi - lo := by linarith
    refine ⟨(d - lo) / (hi - lo), div_nonneg (by linarith) hk.le,
      (div_le_one hk).2 (by linarith), ?_⟩
    rw [div_mul_cancel₀ _ hk.ne']
    ring

theorem main {M : Marginals Z} (hM : M.Valid)
    (ha : 0 < probA M .a) (hb : 0 < probA M .b) :
    PIsetDD M = Set.Icc
      (mu M .a (wL M) - mu M .b (wU M))
      (mu M .a (wU M) - mu M .b (wL M)) := by
  have := hM.1
  have iL := integ_Lo hM
  have iU := integ_Up hM
  have iP := integ_p1 hM
  rw [mu_a_wL hM, mu_a_wU hM, mu_b_wU hM, mu_b_wL hM,
    integral_sub iP iL, integral_sub iP iU]
  ext d
  constructor
  · rintro ⟨π, hπ, rfl⟩
    have iq := integ_qa hM hπ
    rw [dd_eq hπ, integral_sub iP iq]
    have hA : ∫ z, Lo M z ∂M.PZ ≤ ∫ z, qa π z ∂M.PZ :=
      integral_mono iL iq (fun z => (pd_bounds hM hπ z).1)
    have hB : ∫ z, qa π z ∂M.PZ ≤ ∫ z, Up M z ∂M.PZ :=
      integral_mono iq iU (fun z => (pd_bounds hM hπ z).2)
    constructor
    · have e1 := div_le_div_of_nonneg_right hA ha.le
      have e2 : (∫ z, etaPri M 1 z ∂M.PZ - ∫ z, qa π z ∂M.PZ) / probA M .b ≤
          (∫ z, etaPri M 1 z ∂M.PZ - ∫ z, Lo M z ∂M.PZ) / probA M .b :=
        div_le_div_of_nonneg_right (by linarith) hb.le
      linarith
    · have e1 := div_le_div_of_nonneg_right hB ha.le
      have e2 : (∫ z, etaPri M 1 z ∂M.PZ - ∫ z, Up M z ∂M.PZ) / probA M .b ≤
          (∫ z, etaPri M 1 z ∂M.PZ - ∫ z, qa π z ∂M.PZ) / probA M .b :=
        div_le_div_of_nonneg_right (by linarith) hb.le
      linarith
  · rintro ⟨h1, h2⟩
    obtain ⟨t, ht0, ht1, hd⟩ := exists_t h1 h2
    refine ⟨piT M t, piT_mem hM ht0 ht1, ?_⟩
    have hq : ∫ z, qa (piT M t) z ∂M.PZ =
        ∫ z, Lo M z ∂M.PZ + t * (∫ z, Up M z ∂M.PZ - ∫ z, Lo M z ∂M.PZ) := by
      have hc : ∫ z, qa (piT M t) z ∂M.PZ = ∫ z, (Lo M z + t * (Up M z - Lo M z)) ∂M.PZ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun z => by
          rw [qa_piT hM ht0 ht1 z]; rfl))
      have i2 : Integrable (fun z => t * (Up M z - Lo M z)) M.PZ := (iU.sub iL).const_mul t
      rw [hc, integral_add iL i2, integral_const_mul, integral_sub iU iL]
    have iq := integ_qa hM (piT_mem hM ht0 ht1)
    rw [dd_eq (piT_mem hM ht0 ht1), integral_sub iP iq, hq, ← hd]
    ring

end FairProxy.ClosedFormDD.P7Aux

open FairProxy.ClosedFormDD in
theorem solution {Z : Type*} [MeasurableSpace Z]
    (M : Marginals Z) (hM : M.Valid)
    (ha : 0 < probA M .a) (hb : 0 < probA M .b) :
    PIsetDD M = Set.Icc
      (mu M .a (wL M) - mu M .b (wU M))
      (mu M .a (wU M) - mu M .b (wL M)) := by
  exact FairProxy.ClosedFormDD.P7Aux.main hM ha hb
