-- Prove2me | solution 1 for CalibratedCE.Generic.ae_limitSet_eq_CESet
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T18:14:45.805775+00:00
-- url     : https://prove2.me/submissions/92473a42-250c-4958-ab1b-019460fe107c

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_LimitSet
import Definitions.Def_CalibratedCE_Generic_Forecasts

set_option autoImplicit false

/- Complete checked body: AttributedGeneric -/
section

set_option autoImplicit false

section
-- Prove2me | solution 1 for CalibratedCE.Generic.CE_condForecast_best_response
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:16:14.860447+00:00
-- url     : https://prove2.me/submissions/46341283-0d48-45ac-8948-1943fb247d30


namespace CalibratedCE.Generic

theorem aux_cecf_row {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ)
    (D : Fin m → Fin n → ℝ) (hCE : IsCE u₁ u₂ D) (a a' : Fin m) :
    ∑ b, D a b * u₁ a' b ≤ ∑ b, D a b * u₁ a b := by
  have h := hCE.2.1 (Function.update id a a')
  have key : ∑ x, ∑ b, D x b * u₁ (Function.update id a a' x) b
      - ∑ x, ∑ b, D x b * u₁ x b = ∑ b, D a b * u₁ a' b - ∑ b, D a b * u₁ a b := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
    · simp
    · intro x _ hx
      rw [Function.update_of_ne hx]
      simp
    · intro h; exact absurd (Finset.mem_univ a) h
  linarith

theorem aux_cecf_col {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ)
    (D : Fin m → Fin n → ℝ) (hCE : IsCE u₁ u₂ D) (b b' : Fin n) :
    ∑ a, D a b * u₂ a b' ≤ ∑ a, D a b * u₂ a b := by
  have h := hCE.2.2 (Function.update id b b')
  rw [Finset.sum_comm (f := fun a b_1 => D a b_1 * u₂ a (Function.update id b b' b_1)),
    Finset.sum_comm (f := fun a b_1 => D a b_1 * u₂ a b_1)] at h
  have key : ∑ y, ∑ x, D x y * u₂ x (Function.update id b b' y)
      - ∑ y, ∑ x, D x y * u₂ x y = ∑ a, D a b * u₂ a b' - ∑ a, D a b * u₂ a b := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      rw [Function.update_of_ne hy]
      simp
    · intro h; exact absurd (Finset.mem_univ b) h
  linarith

end CalibratedCE.Generic

open CalibratedCE.Generic

theorem checked_CE_condForecast_best_response {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ)
    (D : Fin m → Fin n → ℝ) (hCE : IsCE u₁ u₂ D) :
    (∀ a, 0 < ∑ c, D a c → condForecast₁ D a ∈ Mb u₁ a) ∧
      (∀ b, 0 < ∑ c, D c b → ∀ b',
        ∑ a, condForecast₂ D b a * u₂ a b' ≤ ∑ a, condForecast₂ D b a * u₂ a b) := by
  refine ⟨fun a ha => ?_, fun b hb b' => ?_⟩
  · refine ⟨⟨fun c => ?_, ?_⟩, fun a' => ?_⟩
    · exact div_nonneg (hCE.1.1 a c) ha.le
    · simp only [condForecast₁]
      rw [← Finset.sum_div, div_self ha.ne']
    · simp only [condForecast₁, div_mul_eq_mul_div]
      rw [← Finset.sum_div, ← Finset.sum_div]
      exact div_le_div_of_nonneg_right (aux_cecf_row u₁ u₂ D hCE a a') ha.le
  · simp only [condForecast₂, div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right (aux_cecf_col u₁ u₂ D hCE b b') hb.le
end

section
-- Prove2me | solution 1 for CalibratedCE.Generic.ae_Mb_strict_interior
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:54:05.484423+00:00
-- url     : https://prove2.me/submissions/5b4126a0-44ab-4700-8ca5-07ea900ddb09


namespace CalibratedCE.Generic

open MeasureTheory Set

/-- Strict-interior property for action `a`. -/
def aux_msi_S {m n : ℕ} (u : Fin m → Fin n → ℝ) (a : Fin m) : Prop :=
  ∃ p : Fin n → ℝ, (∀ b, 0 < p b) ∧ ∑ b, p b = 1 ∧
    ∀ a', a' ≠ a → ∑ b, p b * u a' b < ∑ b, p b * u a b

theorem aux_msi_key {m n : ℕ} (u : Fin m → Fin n → ℝ) (a : Fin m) (hN : (Mb u a).Nonempty)
    (ε : ℝ) (hε : 0 < ε) (w : Fin m → Fin n → ℝ)
    (hw : ∀ a' b, w a' b = u a' b + if a' = a then ε else 0) : aux_msi_S w a := by
  obtain ⟨p, ⟨hp0, hp1⟩, hpa⟩ := hN
  set K : ℝ := ∑ a', ∑ b, |u a b - u a' b| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set δ : ℝ := ε / (K + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  have hδK : δ * K < ε := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  set D : ℝ := 1 + (n : ℝ) * δ with hD
  have hD0 : 0 < D := by
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  refine ⟨fun b => (p b + δ) / D, fun b => div_pos (by linarith [hp0 b]) hD0, ?_, ?_⟩
  · rw [← Finset.sum_div, Finset.sum_add_distrib, hp1, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, div_self hD0.ne']
  · intro a' ha'
    have hsum : ∀ c : Fin n → ℝ, ∑ b, (p b + δ) / D * c b
        = (∑ b, p b * c b + δ * ∑ b, c b) / D := by
      intro c
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have hwa' : ∀ b, w a' b = u a' b := fun b => by rw [hw, if_neg ha', add_zero]
    have hwa : ∀ b, w a b = u a b + ε := fun b => by rw [hw, if_pos rfl]
    simp only [hwa', hwa]
    rw [hsum, hsum, div_lt_div_iff_of_pos_right hD0]
    have h1 := hpa a'
    have h2 : ∑ b, p b * (u a b + ε) = ∑ b, p b * u a b + ε := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul]
    have h3 : ∑ b, (u a b + ε) = ∑ b, u a b + n * ε := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have h4 : ∑ b, u a' b - ∑ b, u a b ≤ K := by
      calc ∑ b, u a' b - ∑ b, u a b = ∑ b, (u a' b - u a b) := by
            rw [Finset.sum_sub_distrib]
        _ ≤ ∑ b, |u a b - u a' b| := Finset.sum_le_sum fun b _ => by
            rw [abs_sub_comm]; exact le_abs_self _
        _ ≤ K := Finset.single_le_sum (f := fun a' => ∑ b, |u a b - u a' b|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a')
    have h5 : δ * (∑ b, u a' b - ∑ b, u a b) ≤ δ * K := mul_le_mul_of_nonneg_left h4 hδ0.le
    have h6 : 0 ≤ δ * (n * ε) := by positivity
    rw [h2, h3]
    nlinarith

theorem aux_msi_open {m n : ℕ} (a : Fin m) : IsOpen {u : Fin m → Fin n → ℝ | aux_msi_S u a} := by
  have : {u : Fin m → Fin n → ℝ | aux_msi_S u a} =
      ⋃ p : {p : Fin n → ℝ // (∀ b, 0 < p b) ∧ ∑ b, p b = 1}, ⋂ a' : Fin m, ⋂ (_ : a' ≠ a),
        {u : Fin m → Fin n → ℝ | ∑ b, p.1 b * u a' b < ∑ b, p.1 b * u a b} := by
    ext u
    simp only [aux_msi_S, mem_ofPred_eq, mem_iUnion, mem_iInter, Subtype.exists, exists_prop]
    constructor
    · rintro ⟨p, h1, h2, h3⟩; exact ⟨p, ⟨h1, h2⟩, h3⟩
    · rintro ⟨p, ⟨h1, h2⟩, h3⟩; exact ⟨p, h1, h2, h3⟩
  rw [this]
  refine isOpen_iUnion fun p => isOpen_iInter_of_finite fun a' => isOpen_iInter_of_finite
    fun _ => isOpen_lt (by fun_prop) (by fun_prop)

theorem aux_msi_closed {m n : ℕ} (a : Fin m) :
    IsClosed {u : Fin m → Fin n → ℝ | (Mb u a).Nonempty} := by
  have : {u : Fin m → Fin n → ℝ | (Mb u a).Nonempty} =
      Prod.fst '' {x : (Fin m → Fin n → ℝ) × stdSimplex ℝ (Fin n) |
        ∀ a', ∑ b, (x.2 : Fin n → ℝ) b * x.1 a' b ≤ ∑ b, (x.2 : Fin n → ℝ) b * x.1 a b} := by
    ext u
    simp only [mem_ofPred_eq, mem_image, Prod.exists, exists_and_right, exists_eq_right,
      Subtype.exists]
    constructor
    · rintro ⟨p, hp, hpa⟩; exact ⟨p, hp, hpa⟩
    · rintro ⟨p, hp, hpa⟩; exact ⟨p, hp, hpa⟩
  rw [this]
  refine isClosedMap_fst_of_compactSpace _ ?_
  simp only [ofPred_forall]
  refine isClosed_iInter fun a' => isClosed_le ?_ ?_
  · exact continuous_finsetSum _ fun b _ =>
      ((continuous_apply b).comp (continuous_subtype_val.comp continuous_snd)).mul
        ((continuous_apply b).comp ((continuous_apply a').comp continuous_fst))
  · exact continuous_finsetSum _ fun b _ =>
      ((continuous_apply b).comp (continuous_subtype_val.comp continuous_snd)).mul
        ((continuous_apply b).comp ((continuous_apply a).comp continuous_fst))

theorem aux_msi_null {m n : ℕ} (a : Fin m) :
    volume ({u : Fin m → Fin n → ℝ | (Mb u a).Nonempty} \ {u | aux_msi_S u a}) = 0 := by
  set V : Fin m → Fin n → ℝ := fun a' _ => if a' = a then 1 else 0 with hV
  set c : ℕ → Fin m → Fin n → ℝ := fun j => ((1 : ℝ) / (j + 1)) • V with hc
  refine Measure.addHaar_eq_zero_of_disjoint_translates volume c ?_ ?_
    ((aux_msi_closed a).measurableSet.diff (aux_msi_open a).measurableSet)
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨‖V‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    rw [hc, norm_smul]
    have : ‖(1 : ℝ) / (j + 1)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [div_le_one (by positivity)]
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    calc ‖(1 : ℝ) / (j + 1)‖ * ‖V‖ ≤ 1 * ‖V‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖V‖ := one_mul _
  · -- key step: two translates in direction `V` of a bad point cannot both be bad
    have step : ∀ (y₁ y₂ : Fin m → Fin n → ℝ) (ε : ℝ), 0 < ε →
        (∀ a' b, y₁ a' b = y₂ a' b + if a' = a then ε else 0) →
        y₂ ∈ {u : Fin m → Fin n → ℝ | (Mb u a).Nonempty} \ {u | aux_msi_S u a} →
        y₁ ∈ {u : Fin m → Fin n → ℝ | (Mb u a).Nonempty} \ {u | aux_msi_S u a} → False := by
      intro y₁ y₂ ε hε h h₂ h₁
      exact h₁.2 (aux_msi_key y₂ a h₂.1 ε hε y₁ h)
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro x hx₁ hx₂
    rw [Set.singleton_add] at hx₁ hx₂
    obtain ⟨y₁, hy₁, rfl⟩ := hx₁
    obtain ⟨y₂, hy₂, hxy⟩ := hx₂
    have hcoord : ∀ a' b, c j a' b + y₂ a' b = c i a' b + y₁ a' b := fun a' b => by
      have := congrFun (congrFun hxy a') b
      simpa using this
    have hti : ((1 : ℝ) / (i + 1)) ≠ 1 / (j + 1) := by
      intro h
      rw [div_eq_div_iff (by positivity) (by positivity), one_mul, one_mul] at h
      exact hij (by exact_mod_cast (add_right_cancel h).symm)
    rcases lt_or_gt_of_ne hti with hlt | hlt
    · refine step y₁ y₂ (1 / (j + 1) - 1 / (i + 1)) (by linarith) (fun a' b => ?_) hy₂ hy₁
      have := hcoord a' b
      simp only [hc, hV, Pi.smul_apply, smul_eq_mul] at this
      split_ifs at this ⊢ <;> linarith
    · refine step y₂ y₁ (1 / (i + 1) - 1 / (j + 1)) (by linarith) (fun a' b => ?_) hy₁ hy₂
      have := hcoord a' b
      simp only [hc, hV, Pi.smul_apply, smul_eq_mul] at this
      split_ifs at this ⊢ <;> linarith

end CalibratedCE.Generic

open CalibratedCE.Generic

theorem checked_ae_Mb_strict_interior (m n : ℕ) :
    ∀ᵐ u₁ : Fin m → Fin n → ℝ ∂MeasureTheory.volume, ∀ a, (Mb u₁ a).Nonempty →
      ∃ p : Fin n → ℝ, (∀ b, 0 < p b) ∧ ∑ b, p b = 1 ∧
        ∀ a', a' ≠ a → ∑ b, p b * u₁ a' b < ∑ b, p b * u₁ a b := by
  refine MeasureTheory.ae_all_iff.2 fun a => ?_
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (fun u hu => ?_) (aux_msi_null (n := n) a)
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hu
  exact ⟨hu.1, hu.2⟩
end

section
-- Prove2me | solution 1 for CalibratedCE.Generic.condForecast_calibrated
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:40:12.152992+00:00
-- url     : https://prove2.me/submissions/e0a2397d-2371-4f6a-9616-b7ef43c1c3b9


open Filter Topology

namespace CalibratedCE.Generic

/-- Fiberwise counting: rounds whose forecast `F (x s)` equals `p` split according to `x s`. -/
theorem aux_ccf_count {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (x : ℕ → α) (F : α → β) (P : ℕ → Prop) [DecidablePred P] (p : β) (t : ℕ) :
    ((Finset.range t).filter (fun s => F (x s) = p ∧ P s)).card =
      ∑ a ∈ Finset.univ.filter (fun a => F a = p),
        ((Finset.range t).filter (fun s => x s = a ∧ P s)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := x) (t := Finset.univ.filter (fun a => F a = p))]
  · apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    congr 1
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _, h3⟩, h4⟩
      exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h4, h3⟩
      exact ⟨⟨h1, h4 ▸ ha, h3⟩, h4⟩
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hs ⊢
    exact hs.2.1

/-- Calibration of the conditional forecasts of player 1. -/
theorem aux_ccf_cal {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD0 : ∀ a b, 0 ≤ D a b)
    (x : ℕ → Fin m) (y : ℕ → Fin n)
    (hlim : ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b))) :
    Shared.Calibrated (fun t => condForecast₁ D (x t)) y := by
  intro j
  set f : ℕ → Fin n → ℝ := fun t => condForecast₁ D (x t) with hf
  set S : Finset (Fin n → ℝ) := Finset.univ.image (condForecast₁ D) with hS
  have key : ∀ t, Shared.calibScore f y j t =
      ∑ p ∈ S, |∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
        (empDist x y t a j - p j * ∑ b, empDist x y t a b)| := by
    intro t
    unfold Shared.calibScore
    rw [Finset.sum_subset (s₁ := (Finset.range t).image f) (s₂ := S)]
    · apply Finset.sum_congr rfl
      intro p _
      have hC : ((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card =
          ∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
            ((Finset.range t).filter (fun s => x s = a ∧ y s = j)).card :=
        aux_ccf_count x (condForecast₁ D) (fun s => y s = j) p t
      have hN : Shared.N f p t = ∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
          ∑ b, ((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card := by
        unfold Shared.N
        rw [Finset.card_eq_sum_card_fiberwise (f := y) (t := Finset.univ) (by simp)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.filter_filter]
        exact aux_ccf_count x (condForecast₁ D) (fun s => y s = b) p t
      have hCN : ((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card ≤ Shared.N f p t := by
        unfold Shared.N
        apply Finset.card_le_card
        intro s hs
        simp only [Finset.mem_filter] at hs ⊢
        exact ⟨hs.1, hs.2.1⟩
      have hR : ∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
          (empDist x y t a j - p j * ∑ b, empDist x y t a b) =
          ((((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card : ℝ)
            - p j * (Shared.N f p t : ℝ)) / (t : ℝ) := by
        rw [hC, hN]
        push_cast
        unfold empDist
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_div]
        ring
      rw [hR, abs_div, Nat.abs_cast]
      congr 1
      by_cases h0 : Shared.N f p t = 0
      · have hr : Shared.rho f y p j t = 0 := by simp [Shared.rho, h0]
        have hc : ((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card = 0 := by omega
        rw [hr, h0, hc]
        simp
      · have hr : Shared.rho f y p j t =
            (((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card : ℝ) /
              (Shared.N f p t : ℝ) := by
          simp [Shared.rho, h0]
        have hNpos : (0 : ℝ) < (Shared.N f p t : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero h0
        rw [hr]
        rw [← abs_of_pos hNpos, ← abs_mul, abs_of_pos hNpos]
        congr 1
        field_simp
    · intro p hp
      simp only [Finset.mem_image, Finset.mem_range, hS, Finset.mem_univ, true_and] at hp ⊢
      obtain ⟨s, _, rfl⟩ := hp
      exact ⟨x s, rfl⟩
    · intro p _ hp
      have : Shared.N f p t = 0 := by
        unfold Shared.N
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro s hs hfs
        exact hp (Finset.mem_image.mpr ⟨s, hs, hfs⟩)
      rw [this]
      simp
  have hT : Tendsto (fun t => ∑ p ∈ S, |∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
        (empDist x y t a j - p j * ∑ b, empDist x y t a b)|) atTop
      (𝓝 (∑ p ∈ S, |∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
        (D a j - p j * ∑ b, D a b)|)) := by
    apply tendsto_finsetSum
    intro p _
    apply Filter.Tendsto.abs
    apply tendsto_finsetSum
    intro a _
    exact (hlim a j).sub ((tendsto_finsetSum _ (fun b _ => hlim a b)).const_mul _)
  have hzero : ∑ p ∈ S, |∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
        (D a j - p j * ∑ b, D a b)| = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    rw [abs_eq_zero]
    apply Finset.sum_eq_zero
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    subst ha
    simp only [condForecast₁]
    by_cases hs : ∑ c, D a c = 0
    · have h1 : D a j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hD0 a c)).mp hs j (Finset.mem_univ _)
      rw [h1, hs]
      simp
    · rw [div_mul_cancel₀ _ hs, sub_self]
  rw [hzero] at hT
  exact hT.congr (fun t => (key t).symm)

theorem aux_ccf_isDist {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD0 : ∀ a b, 0 ≤ D a b)
    (a : Fin m) (b : Fin n) (hpos : 0 < D a b) : IsDist (condForecast₁ D a) := by
  have hs : 0 < ∑ c, D a c :=
    lt_of_lt_of_le hpos (Finset.single_le_sum (fun c _ => hD0 a c) (Finset.mem_univ b))
  refine ⟨fun c => div_nonneg (hD0 a c) hs.le, ?_⟩
  simp only [condForecast₁]
  rw [← Finset.sum_div, div_self hs.ne']

end CalibratedCE.Generic

open CalibratedCE CalibratedCE.Generic
open Filter Topology

theorem checked_condForecast_calibrated {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD : IsJointDist D)
    (x : ℕ → Fin m) (y : ℕ → Fin n) (hsupp : ∀ t, 0 < D (x t) (y t))
    (hlim : ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b))) :
    (∀ t, IsDist (condForecast₁ D (x t))) ∧ (∀ t, IsDist (condForecast₂ D (y t))) ∧
      Shared.Calibrated (fun t => condForecast₁ D (x t)) y ∧
      Shared.Calibrated (fun t => condForecast₂ D (y t)) x := by
  refine ⟨fun t => aux_ccf_isDist D hD.1 (x t) (y t) (hsupp t),
    fun t => aux_ccf_isDist (fun b a => D a b) (fun b a => hD.1 a b) (y t) (x t) (hsupp t),
    aux_ccf_cal D hD.1 x y hlim, ?_⟩
  have hlim' : ∀ b a, Tendsto (fun t => empDist y x t b a) atTop (𝓝 (D a b)) := by
    intro b a
    refine (hlim a b).congr (fun t => ?_)
    unfold empDist
    congr 3
    ext s
    simp only [Finset.mem_filter]
    tauto
  exact aux_ccf_cal (fun b a => D a b) (fun b a => hD.1 a b) y x hlim'
end

section
-- Prove2me | solution 1 for CalibratedCE.Generic.exists_play_with_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:12:45.453029+00:00
-- url     : https://prove2.me/submissions/5a4586da-9343-4115-9805-a1daf840a0cd


open Filter Topology

namespace CalibratedCE.Generic

/-- Greedy selection: a maximizer of `v s + p s`. -/
noncomputable def aux_epl_sel {α : Type} [Fintype α] [Nonempty α] (p : α → ℝ) (v : α → ℝ) : α :=
  Classical.choose (Finite.exists_max (fun s => v s + p s))

lemma aux_epl_sel_spec {α : Type} [Fintype α] [Nonempty α] (p : α → ℝ) (v : α → ℝ) (s : α) :
    v s + p s ≤ v (aux_epl_sel p v) + p (aux_epl_sel p v) :=
  Classical.choose_spec (Finite.exists_max (fun s => v s + p s)) s

/-- The deficit vector `t * p s - count_t s` of the greedy sequence. -/
noncomputable def aux_epl_err {α : Type} [Fintype α] [Nonempty α] [DecidableEq α]
    (p : α → ℝ) : ℕ → α → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun s =>
      aux_epl_err p t s + p s - if s = aux_epl_sel p (aux_epl_err p t) then 1 else 0

lemma aux_epl_err_sum {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (hp1 : ∑ a, p a = 1) (t : ℕ) : ∑ s, aux_epl_err p t s = 0 := by
  induction t with
  | zero => simp [aux_epl_err]
  | succ t ih =>
    simp only [aux_epl_err]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ih, hp1, Finset.sum_ite_eq']
    simp

lemma aux_epl_sel_pos {α : Type} [Fintype α] [Nonempty α] (p : α → ℝ)
    (hp1 : ∑ a, p a = 1) (v : α → ℝ) (hv : ∑ s, v s = 0) :
    0 < v (aux_epl_sel p v) + p (aux_epl_sel p v) := by
  have h1 : ∑ s, (v s + p s) = 1 := by rw [Finset.sum_add_distrib, hv, hp1]; ring
  have h2 : ∑ s, (v s + p s) ≤ ∑ _s : α, (v (aux_epl_sel p v) + p (aux_epl_sel p v)) :=
    Finset.sum_le_sum (fun s _ => aux_epl_sel_spec p v s)
  rw [h1, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h2
  by_contra h
  rw [not_lt] at h
  have : (0:ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  nlinarith

lemma aux_epl_err_lower {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (t : ℕ) (s : α) : -1 < aux_epl_err p t s := by
  induction t generalizing s with
  | zero => simp [aux_epl_err]
  | succ t ih =>
    simp only [aux_epl_err]
    have hpos := aux_epl_sel_pos p hp1 (aux_epl_err p t) (aux_epl_err_sum p hp1 t)
    split_ifs with h
    · subst h; linarith
    · have := ih s; have := hp0 s; linarith

lemma aux_epl_err_zero {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (t : ℕ) (s : α) (hs : p s = 0) : aux_epl_err p t s ≤ 0 := by
  induction t with
  | zero => simp [aux_epl_err]
  | succ t ih =>
    simp only [aux_epl_err]
    split_ifs <;> linarith

lemma aux_epl_err_upper {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (t : ℕ) (s : α) :
    aux_epl_err p t s ≤ Fintype.card α := by
  have hsum : ∑ s, (aux_epl_err p t s + 1) = Fintype.card α := by
    rw [Finset.sum_add_distrib, aux_epl_err_sum p hp1 t]; simp
  have := Finset.single_le_sum (f := fun s => aux_epl_err p t s + 1)
    (fun i _ => by have := aux_epl_err_lower p hp0 hp1 t i; linarith) (Finset.mem_univ s)
  linarith

lemma aux_epl_count {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (t : ℕ) (a : α) :
    ((((Finset.range t).filter (fun i => aux_epl_sel p (aux_epl_err p i) = a)).card : ℕ) : ℝ)
      = t * p a - aux_epl_err p t a := by
  induction t with
  | zero => simp [aux_epl_err]
  | succ t ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [aux_epl_err]
    by_cases h : aux_epl_sel p (aux_epl_err p t) = a
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), Nat.cast_add, ih, if_pos h.symm]
      push_cast; ring
    · rw [if_neg h, ih, if_neg (Ne.symm h)]
      push_cast; ring

lemma aux_epl_main {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    ∃ z : ℕ → α, (∀ t, 0 < p (z t)) ∧ ∀ a,
      Tendsto (fun t : ℕ => (((Finset.range t).filter (fun i => z i = a)).card : ℝ) / t)
        atTop (𝓝 (p a)) := by
  refine ⟨fun i => aux_epl_sel p (aux_epl_err p i), ?_, ?_⟩
  · intro t
    have hpos := aux_epl_sel_pos p hp1 (aux_epl_err p t) (aux_epl_err_sum p hp1 t)
    rcases (hp0 (aux_epl_sel p (aux_epl_err p t))).lt_or_eq with h | h
    · exact h
    · have := aux_epl_err_zero p t _ h.symm
      linarith
  · intro a
    have hlim : Tendsto (fun t : ℕ => p a - aux_epl_err p t a / t) atTop (𝓝 (p a)) := by
      have h0 : Tendsto (fun t : ℕ => aux_epl_err p t a / t) atTop (𝓝 0) := by
        apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (Fintype.card α : ℝ))
        filter_upwards with t
        rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        rw [abs_le]
        constructor
        · have := aux_epl_err_lower p hp0 hp1 t a
          have : (1:ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
          linarith
        · exact aux_epl_err_upper p hp0 hp1 t a
      simpa using (tendsto_const_nhds (x := p a)).sub h0
    refine Tendsto.congr' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with t ht
    show p a - aux_epl_err p t a / t =
      ((((Finset.range t).filter (fun i => aux_epl_sel p (aux_epl_err p i) = a)).card : ℕ) : ℝ) / t
    rw [aux_epl_count]
    have : (t:ℝ) ≠ 0 := by
      have : (1:ℝ) ≤ t := by exact_mod_cast ht
      linarith
    field_simp

end CalibratedCE.Generic

open CalibratedCE.Generic

theorem checked_exists_play_with_limit {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD : IsJointDist D) :
    ∃ (x : ℕ → Fin m) (y : ℕ → Fin n), (∀ t, 0 < D (x t) (y t)) ∧
      ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b)) := by
  obtain ⟨h0, h1⟩ := hD
  have hsum : ∑ s : Fin m × Fin n, D s.1 s.2 = 1 := by
    rw [Fintype.sum_prod_type']; exact h1
  have hne : Nonempty (Fin m × Fin n) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    simp at hsum
  obtain ⟨z, hz, hlim⟩ :=
    aux_epl_main (fun s : Fin m × Fin n => D s.1 s.2) (fun s => h0 _ _) hsum
  refine ⟨fun t => (z t).1, fun t => (z t).2, hz, fun a b => ?_⟩
  have := hlim (a, b)
  simp only [Prod.ext_iff] at this
  exact this
end

section
-- Prove2me | solution 1 for CalibratedCE.Generic.limitSet_subset_CESet
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:17:44.888312+00:00
-- url     : https://prove2.me/submissions/bbb300a9-6ec9-4542-b5de-c09230bec7e5


namespace CalibratedCE.Generic

open Filter Topology

lemma aux_lsc_emp_sum {m n : ℕ} (x : ℕ → Fin m) (y : ℕ → Fin n) (t : ℕ)
    (G : Fin m → Fin n → ℝ) :
    ∑ a, ∑ b, empDist x y t a b * G a b = (∑ s ∈ Finset.range t, G (x s) (y s)) / t := by
  classical
  simp only [empDist, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  have key : ∀ a b, (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ) * G a b
      = ∑ s ∈ Finset.range t, if x s = a ∧ y s = b then G a b else 0 := by
    intro a b
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  simp_rw [key]
  rw [show (∑ a, ∑ b, ∑ s ∈ Finset.range t, if x s = a ∧ y s = b then G a b else 0)
      = ∑ a, ∑ s ∈ Finset.range t, ∑ b, (if x s = a ∧ y s = b then G a b else 0) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [ite_and]

lemma aux_lsc_main {k l : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (R : (Fin k → ℝ) → Fin l)
    (h : Fin l → Fin k → ℝ) (K : ℝ) (hK : ∀ r j, |h r j| ≤ K)
    (hbr : ∀ s, ∑ j, f s j * h (R (f s)) j ≤ 0) (t : ℕ) :
    ∑ s ∈ Finset.range t, h (R (f s)) (z s) ≤
      K * ∑ j, ∑ p ∈ (Finset.range t).image f,
        |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range t) (t := (Finset.range t).image f)
    (g := f) (fun s hs => Finset.mem_image_of_mem f hs)]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨s₀, hs₀, hfs₀⟩ := Finset.mem_image.mp hp
  have hbr' : ∑ j, p j * h (R p) j ≤ 0 := hfs₀ ▸ hbr s₀
  set F := (Finset.range t).filter (fun s => f s = p) with hF
  have hN : (Shared.N f p t : ℝ) = F.card := rfl
  have hNpos : Shared.N f p t ≠ 0 := by
    unfold Shared.N
    rw [← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨s₀, Finset.mem_filter.mpr ⟨hs₀, hfs₀⟩⟩
  set M : Fin k → ℝ := fun j =>
    (((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ) with hM
  have h1 : ∑ s ∈ F, h (R (f s)) (z s) = ∑ j, M j * h (R p) j := by
    rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2])]
    rw [← Finset.sum_fiberwise (s := F) (g := z)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2]),
      Finset.sum_const, nsmul_eq_mul, hF, Finset.filter_filter]
  have h2 : ∀ j, |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ)
      = |M j - (Shared.N f p t : ℝ) * p j| := by
    intro j
    have hNr : (Shared.N f p t : ℝ) ≠ 0 := by exact_mod_cast hNpos
    have hNnn : (0:ℝ) ≤ Shared.N f p t := Nat.cast_nonneg _
    rw [Shared.rho, if_neg hNpos, ← abs_of_nonneg hNnn, ← abs_mul, abs_of_nonneg hNnn]
    congr 1
    field_simp
    ring
  rw [h1, Finset.mul_sum]
  simp_rw [h2]
  have h3 : ∑ j, M j * h (R p) j
      = ∑ j, (M j - (Shared.N f p t : ℝ) * p j) * h (R p) j
        + (Shared.N f p t : ℝ) * ∑ j, p j * h (R p) j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h3]
  have h4 : (Shared.N f p t : ℝ) * ∑ j, p j * h (R p) j ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hbr'
  have h5 : ∑ j, (M j - (Shared.N f p t : ℝ) * p j) * h (R p) j
      ≤ ∑ j, K * |M j - (Shared.N f p t : ℝ) * p j| := by
    apply Finset.sum_le_sum
    intro j _
    calc (M j - (Shared.N f p t : ℝ) * p j) * h (R p) j
        ≤ |(M j - (Shared.N f p t : ℝ) * p j) * h (R p) j| := le_abs_self _
      _ = |M j - (Shared.N f p t : ℝ) * p j| * |h (R p) j| := abs_mul _ _
      _ ≤ |M j - (Shared.N f p t : ℝ) * p j| * K :=
          mul_le_mul_of_nonneg_left (hK _ _) (abs_nonneg _)
      _ = K * |M j - (Shared.N f p t : ℝ) * p j| := mul_comm _ _
  linarith

lemma aux_lsc_limit {k l : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (R : (Fin k → ℝ) → Fin l)
    (h : Fin l → Fin k → ℝ) (hbr : ∀ s, ∑ j, f s j * h (R (f s)) j ≤ 0)
    (hcal : Shared.Calibrated f z) (w : ℕ → ℝ) (L : ℝ) (hw : Tendsto w atTop (𝓝 L))
    (hweq : ∀ t : ℕ, 0 < t → w t = (∑ s ∈ Finset.range t, h (R (f s)) (z s)) / t) :
    L ≤ 0 := by
  set K : ℝ := ∑ r, ∑ j, |h r j| with hKdef
  have hK : ∀ r j, |h r j| ≤ K := by
    intro r j
    calc |h r j| ≤ ∑ j', |h r j'| :=
          Finset.single_le_sum (f := fun j' => |h r j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ K := Finset.single_le_sum (f := fun r' => ∑ j', |h r' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ r)
  have hlim : Tendsto (fun t => K * ∑ j, Shared.calibScore f z j t) atTop (𝓝 0) := by
    have := (tendsto_finsetSum (Finset.univ : Finset (Fin k))
      fun j _ => hcal j).const_mul K
    simpa using this
  refine le_of_tendsto_of_tendsto hw hlim ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  rw [hweq t ht]
  have hcs : K * ∑ j, Shared.calibScore f z j t
      = (K * ∑ j, ∑ p ∈ (Finset.range t).image f,
        |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ)) / t := by
    simp only [Shared.calibScore, Finset.sum_div, mul_div_assoc]
  rw [hcs]
  exact div_le_div_of_nonneg_right (aux_lsc_main f z R h K hK hbr t) htpos.le

end CalibratedCE.Generic

open CalibratedCE.Generic Filter Topology

theorem checked_limitSet_subset_CESet {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) :
    LimitSet u₁ u₂ ⊆ CESet u₁ u₂ := by
  rintro D ⟨R₁, R₂, π₁, π₂, hR₁, hR₂, hπ₁, hπ₂, hc₁, hc₂, hD⟩
  have hconv : ∀ G : Fin m → Fin n → ℝ,
      Tendsto (fun t => ∑ a, ∑ b,
        empDist (play₁ R₁ R₂ π₁ π₂) (play₂ R₁ R₂ π₁ π₂) t a b * G a b) atTop
        (𝓝 (∑ a, ∑ b, D a b * G a b)) := fun G =>
    tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => (hD a b).mul_const _
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b
    exact ge_of_tendsto' (hD a b) fun t => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have h1 := hconv (fun _ _ => 1)
    simp only [mul_one] at h1
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with t ht
    have htpos : (t : ℝ) ≠ 0 := by
      have : (0 : ℝ) < t := by exact_mod_cast ht
      exact this.ne'
    have := aux_lsc_emp_sum (play₁ R₁ R₂ π₁ π₂) (play₂ R₁ R₂ π₁ π₂) t (fun _ _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    rw [this, div_self htpos]
  · intro Φ
    have key := aux_lsc_limit (forecast₁ R₁ R₂ π₁ π₂) (play₂ R₁ R₂ π₁ π₂) R₁
      (fun r j => u₁ (Φ r) j - u₁ r j) ?_ hc₁ _ _ (hconv fun a b => u₁ (Φ a) b - u₁ a b)
      (fun t _ => by rw [aux_lsc_emp_sum]; rfl)
    · simp only [mul_sub, Finset.sum_sub_distrib] at key
      linarith
    · intro s
      have := hR₁ (forecast₁ R₁ R₂ π₁ π₂ s) (hπ₁ _) (Φ (R₁ (forecast₁ R₁ R₂ π₁ π₂ s)))
      simp only [mul_sub, Finset.sum_sub_distrib]
      unfold forecast₁ at this ⊢
      linarith
  · intro Φ
    have key := aux_lsc_limit (forecast₂ R₁ R₂ π₁ π₂) (play₁ R₁ R₂ π₁ π₂) R₂
      (fun r a => u₂ a (Φ r) - u₂ a r) ?_ hc₂ _ _ (hconv fun a b => u₂ a (Φ b) - u₂ a b)
      (fun t _ => by rw [aux_lsc_emp_sum]; rfl)
    · simp only [mul_sub, Finset.sum_sub_distrib] at key
      linarith
    · intro s
      have := hR₂ (forecast₂ R₁ R₂ π₁ π₂ s) (hπ₂ _) (Φ (R₂ (forecast₂ R₁ R₂ π₁ π₂ s)))
      simp only [mul_sub, Finset.sum_sub_distrib]
      unfold forecast₂ at this ⊢
      linarith
end

section
-- Prove2me | solution 1 for CalibratedCE.Generic.pert_strict_best_reply
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:31:53.726638+00:00
-- url     : https://prove2.me/submissions/049089fc-9b93-42e2-96ea-80ac820e02d3


open Filter Topology

namespace CalibratedCE.Generic

theorem aux_psbr_sum_expand {n : ℕ} (pstar q v : Fin n → ℝ) (i : ℕ) :
    ∑ b, pert pstar q i b * v b
      = (1 - 1 / (i : ℝ)) * ∑ b, pstar b * v b + (1 / (i : ℝ)) * ∑ b, q b * v b := by
  simp only [pert, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

end CalibratedCE.Generic

open CalibratedCE.Generic

theorem checked_pert_strict_best_reply {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (a : Fin m)
    (pstar q : Fin n → ℝ) (hpstar : pstar ∈ Mb u₁ a) (hq : IsDist q)
    (hqa : ∀ a', a' ≠ a → ∑ b, q b * u₁ a' b < ∑ b, q b * u₁ a b) :
    (∀ i : ℕ, 1 ≤ i → IsDist (pert pstar q i) ∧
        ∀ a', a' ≠ a → ∑ b, pert pstar q i b * u₁ a' b < ∑ b, pert pstar q i b * u₁ a b) ∧
      Tendsto (pert pstar q) atTop (𝓝 pstar) := by
  obtain ⟨⟨hp0, hp1⟩, hpbr⟩ := hpstar
  obtain ⟨hq0, hq1⟩ := hq
  refine ⟨fun i hi => ?_, ?_⟩
  · have hipos : (0 : ℝ) < i := by exact_mod_cast hi
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have ht0 : (0 : ℝ) < 1 / (i : ℝ) := by positivity
    have ht1 : 1 / (i : ℝ) ≤ 1 := by
      rw [div_le_one hipos]; exact hi1
    have hs0 : (0 : ℝ) ≤ 1 - 1 / (i : ℝ) := by linarith
    refine ⟨⟨fun b => ?_, ?_⟩, fun a' ha' => ?_⟩
    · simp only [pert]
      have := hp0 b
      have := hq0 b
      positivity
    · have := aux_psbr_sum_expand pstar q (fun _ => (1 : ℝ)) i
      simp only [mul_one] at this
      rw [this, hp1, hq1]
      ring
    · rw [aux_psbr_sum_expand, aux_psbr_sum_expand]
      have h1 := mul_le_mul_of_nonneg_left (hpbr a') hs0
      have h2 := mul_lt_mul_of_pos_left (hqa a' ha') ht0
      linarith
  · rw [tendsto_pi_nhds]
    intro b
    have ht := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h : Tendsto (fun i : ℕ => (1 - 1 / (i : ℝ)) * pstar b + (1 / (i : ℝ)) * q b)
        atTop (𝓝 ((1 - 0) * pstar b + 0 * q b)) :=
      ((tendsto_const_nhds.sub ht).mul tendsto_const_nhds).add (ht.mul tendsto_const_nhds)
    simp only [sub_zero, one_mul, zero_mul, add_zero] at h
    exact h
end






end

/- Complete checked body: Genericity -/
section

open MeasureTheory Filter Topology
open CalibratedCE.Generic

namespace CalibratedCE.GenericProof

def StrictWitnesses {m n : ℕ} (u : Fin m → Fin n → ℝ) : Prop :=
  ∀ a, (Mb u a).Nonempty → ∃ q, IsDist q ∧
    ∀ a', a' ≠ a → ∑ b, q b * u a' b < ∑ b, q b * u a b

theorem ae_strictWitnesses (m n : ℕ) :
    ∀ᵐ u : Fin m → Fin n → ℝ ∂volume, StrictWitnesses u := by
  filter_upwards [checked_ae_Mb_strict_interior m n] with u hu
  intro a ha
  obtain ⟨q, hq0, hq1, hqa⟩ := hu a ha
  exact ⟨q, ⟨fun b => (hq0 b).le, hq1⟩, hqa⟩

def transposeEquiv (m n : ℕ) :
    (Fin m → Fin n → ℝ) ≃L[ℝ] (Fin n → Fin m → ℝ) where
  toFun u b a := u a b
  invFun u a b := u b a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem ae_transpose_strictWitnesses (m n : ℕ) :
    ∀ᵐ u : Fin m → Fin n → ℝ ∂volume, StrictWitnesses (fun b a => u a b) := by
  let e := transposeEquiv m n
  have : Measure.IsAddHaarMeasure (volume : Measure (Fin m → Fin n → ℝ)) := {}
  have : Measure.IsAddHaarMeasure (volume : Measure (Fin n → Fin m → ℝ)) := {}
  have : Measure.IsAddHaarMeasure ((volume : Measure (Fin m → Fin n → ℝ)).map e) :=
    e.isAddHaarMeasure_map volume
  have : SigmaFinite ((volume : Measure (Fin m → Fin n → ℝ)).map e) :=
    e.toHomeomorph.toMeasurableEquiv.sigmaFinite_map
  have hac : (volume : Measure (Fin m → Fin n → ℝ)).map e ≪
      (volume : Measure (Fin n → Fin m → ℝ)) :=
    Measure.absolutelyContinuous_isAddHaarMeasure
      ((volume : Measure (Fin m → Fin n → ℝ)).map e)
      (volume : Measure (Fin n → Fin m → ℝ))
  exact ae_of_ae_map e.continuous.measurable.aemeasurable
    (hac.ae_le (ae_strictWitnesses n m))

theorem ae_game_strictWitnesses (m n : ℕ) :
    ∀ᵐ G : (Fin m → Fin n → ℝ) × (Fin m → Fin n → ℝ) ∂volume,
      StrictWitnesses G.1 ∧ StrictWitnesses (fun b a => G.2 a b) := by
  have h₁ := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Fin m → Fin n → ℝ)))
    (ν := (volume : Measure (Fin m → Fin n → ℝ)))).ae (ae_strictWitnesses m n)
  have h₂ := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Fin m → Fin n → ℝ)))
    (ν := (volume : Measure (Fin m → Fin n → ℝ)))).ae
      (ae_transpose_strictWitnesses m n)
  filter_upwards [h₁, h₂] with G h₁ h₂
  exact ⟨h₁, h₂⟩

end CalibratedCE.GenericProof

end

/- Complete checked body: StrictForecasts -/
section

open CalibratedCE.Generic

namespace CalibratedCE.GenericProof

noncomputable def defaultForecast (n : ℕ) [Nonempty (Fin n)] : Fin n → ℝ :=
  fun b => if b = Classical.choice (inferInstance : Nonempty (Fin n)) then 1 else 0

theorem defaultForecast_isDist (n : ℕ) [Nonempty (Fin n)] :
    IsDist (defaultForecast n) := by
  constructor
  · intro b
    unfold defaultForecast
    split_ifs <;> norm_num
  · simp [defaultForecast]

theorem dist_coordinate_le_one {n : ℕ} {p : Fin n → ℝ} (hp : IsDist p) (b : Fin n) :
    p b ≤ 1 := by
  calc p b ≤ ∑ c, p c := Finset.single_le_sum (fun c _ => hp.1 c) (Finset.mem_univ b)
    _ = 1 := hp.2

theorem pert_coordinate_close {n : ℕ} {p q : Fin n → ℝ}
    (hp : IsDist p) (hq : IsDist q) (r : ℕ) (b : Fin n) :
    |pert p q (r + 1) b - p b| ≤ 1 / ((r : ℝ) + 1) := by
  have hb : |q b - p b| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hp.1 b, hq.1 b, dist_coordinate_le_one hp b]
    · linarith [hp.1 b, hq.1 b, dist_coordinate_le_one hq b]
  have hd : 0 ≤ 1 / ((r : ℝ) + 1) := by positivity
  calc |pert p q (r + 1) b - p b|
      = (1 / ((r : ℝ) + 1)) * |q b - p b| := by
          rw [pert]
          push_cast
          rw [show (1 - 1 / ((r : ℝ) + 1)) * p b +
            1 / ((r : ℝ) + 1) * q b - p b =
            (1 / ((r : ℝ) + 1)) * (q b - p b) by ring,
            abs_mul, abs_of_nonneg hd]
    _ ≤ (1 / ((r : ℝ) + 1)) * 1 := mul_le_mul_of_nonneg_left hb hd
    _ = 1 / ((r : ℝ) + 1) := mul_one _

theorem exists_strict_forecasts {m n : ℕ} [Nonempty (Fin n)]
    (u : Fin m → Fin n → ℝ) (D : Fin m → Fin n → ℝ)
    (hweak : ∀ a, 0 < ∑ b, D a b → condForecast₁ D a ∈ Mb u a)
    (hgen : StrictWitnesses u) :
    ∃ F : ℕ → Fin m → Fin n → ℝ,
      (∀ r a, IsDist (F r a)) ∧
      (∀ r a, 0 < ∑ b, D a b → ∀ a', a' ≠ a →
        ∑ b, F r a b * u a' b < ∑ b, F r a b * u a b) ∧
      (∀ r a, 0 < ∑ b, D a b → ∀ b,
        |F r a b - condForecast₁ D a b| ≤ 1 / ((r : ℝ) + 1)) := by
  classical
  have hq : ∀ a : Fin m, ∃ q : Fin n → ℝ, IsDist q ∧
      (0 < ∑ b, D a b → ∀ a', a' ≠ a →
        ∑ b, q b * u a' b < ∑ b, q b * u a b) := by
    intro a
    by_cases ha : 0 < ∑ b, D a b
    · obtain ⟨q, hq, hqa⟩ := hgen a ⟨condForecast₁ D a, hweak a ha⟩
      exact ⟨q, hq, fun _ => hqa⟩
    · exact ⟨defaultForecast n, defaultForecast_isDist n, fun h => (ha h).elim⟩
  choose q hqd hqa using hq
  let F : ℕ → Fin m → Fin n → ℝ := fun r a =>
    if 0 < ∑ b, D a b then pert (condForecast₁ D a) (q a) (r + 1)
    else defaultForecast n
  refine ⟨F, ?_, ?_, ?_⟩
  · intro r a
    by_cases ha : 0 < ∑ b, D a b
    · have h := ((checked_pert_strict_best_reply u a (condForecast₁ D a) (q a)
        (hweak a ha) (hqd a) (hqa a ha)).1 (r + 1) (by omega)).1
      simpa only [F, if_pos ha] using h
    · simpa only [F, if_neg ha] using defaultForecast_isDist n
  · intro r a ha
    simpa only [F, if_pos ha] using
      ((checked_pert_strict_best_reply u a (condForecast₁ D a) (q a)
        (hweak a ha) (hqd a) (hqa a ha)).1 (r + 1) (by omega)).2
  · intro r a ha b
    simpa only [F, if_pos ha] using pert_coordinate_close (hweak a ha).1 (hqd a) r b

noncomputable def bestReply {m n : ℕ} [Nonempty (Fin m)]
    (u : Fin m → Fin n → ℝ) (p : Fin n → ℝ) : Fin m :=
  Classical.choose (Finite.exists_max (fun a => ∑ b, p b * u a b))

theorem bestReply_spec {m n : ℕ} [Nonempty (Fin m)]
    (u : Fin m → Fin n → ℝ) (p : Fin n → ℝ) (a : Fin m) :
    ∑ b, p b * u a b ≤ ∑ b, p b * u (bestReply u p) b :=
  Classical.choose_spec (Finite.exists_max (fun a => ∑ b, p b * u a b)) a

theorem bestReply_isBestReply {m n : ℕ} [Nonempty (Fin m)]
    (u : Fin m → Fin n → ℝ) : IsBestReply₁ u (bestReply u) :=
  fun p _ a => bestReply_spec u p a

theorem bestReply_eq_of_strict {m n : ℕ} [Nonempty (Fin m)]
    (u : Fin m → Fin n → ℝ) (p : Fin n → ℝ) (a : Fin m)
    (ha : ∀ a', a' ≠ a → ∑ b, p b * u a' b < ∑ b, p b * u a b) :
    bestReply u p = a := by
  by_contra h
  exact (not_lt_of_ge (bestReply_spec u p a)) (ha _ h)

end CalibratedCE.GenericProof

end

/- Complete checked body: HistoryRealization -/
section

open Filter Topology
open CalibratedCE.Generic

namespace CalibratedCE.GenericProof

theorem hist_length {m n : ℕ}
    (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (π₁ : List (Fin m × Fin n) → Fin n → ℝ)
    (π₂ : List (Fin m × Fin n) → Fin m → ℝ) (t : ℕ) :
    (hist R₁ R₂ π₁ π₂ t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [hist, List.length_append, List.length_singleton, ih]

theorem limitSet_of_sequences {m n : ℕ}
    (u₁ u₂ D : Fin m → Fin n → ℝ)
    (x : ℕ → Fin m) (y : ℕ → Fin n)
    (f₁ : ℕ → Fin n → ℝ) (f₂ : ℕ → Fin m → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (hR₁ : IsBestReply₁ u₁ R₁) (hR₂ : IsBestReply₂ u₂ R₂)
    (hf₁ : ∀ t, IsDist (f₁ t)) (hf₂ : ∀ t, IsDist (f₂ t))
    (hx : ∀ t, R₁ (f₁ t) = x t) (hy : ∀ t, R₂ (f₂ t) = y t)
    (hc₁ : CalibratedCE.Shared.Calibrated f₁ y)
    (hc₂ : CalibratedCE.Shared.Calibrated f₂ x)
    (hlim : ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b))) :
    D ∈ LimitSet u₁ u₂ := by
  let π₁ : List (Fin m × Fin n) → Fin n → ℝ := fun h => f₁ h.length
  let π₂ : List (Fin m × Fin n) → Fin m → ℝ := fun h => f₂ h.length
  have he₁ : forecast₁ R₁ R₂ π₁ π₂ = f₁ := by
    funext t
    exact congrArg f₁ (hist_length R₁ R₂ π₁ π₂ t)
  have he₂ : forecast₂ R₁ R₂ π₁ π₂ = f₂ := by
    funext t
    exact congrArg f₂ (hist_length R₁ R₂ π₁ π₂ t)
  have hp₁ : play₁ R₁ R₂ π₁ π₂ = x := by
    funext t
    simp only [play₁, he₁, hx]
  have hp₂ : play₂ R₁ R₂ π₁ π₂ = y := by
    funext t
    simp only [play₂, he₂, hy]
  refine ⟨R₁, R₂, π₁, π₂, hR₁, hR₂, fun h => hf₁ h.length,
    fun h => hf₂ h.length, ?_, ?_, ?_⟩
  · simpa only [he₁, hp₂] using hc₁
  · simpa only [he₂, hp₁] using hc₂
  · simpa only [hp₁, hp₂] using hlim

end CalibratedCE.GenericProof

end

/- Complete checked body: GreedyIntervals -/
section

open scoped BigOperators Topology
open Filter CalibratedCE.Generic

namespace CalibratedCE.GenericProof

noncomputable def jointCount {m n : ℕ} (I : Finset ℕ) (x : ℕ → Fin m) (y : ℕ → Fin n)
    (a : Fin m) (b : Fin n) : ℝ :=
  ((I.filter (fun s => x s = a ∧ y s = b)).card : ℝ)

theorem jointCount_eq_sum {m n : ℕ} (I : Finset ℕ) (x : ℕ → Fin m) (y : ℕ → Fin n)
    (a : Fin m) (b : Fin n) :
    jointCount I x y a b = ∑ s ∈ I, if x s = a ∧ y s = b then (1 : ℝ) else 0 := by
  simp only [jointCount, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem jointCount_Ico {m n : ℕ} (x : ℕ → Fin m) (y : ℕ → Fin n)
    (s t : ℕ) (hst : s ≤ t) (a : Fin m) (b : Fin n) :
    jointCount (Finset.Ico s t) x y a b =
      jointCount (Finset.range t) x y a b - jointCount (Finset.range s) x y a b := by
  simp only [jointCount_eq_sum]
  exact Finset.sum_Ico_eq_sub _ hst

theorem interval_count_bound {m n : ℕ} (D : Fin m → Fin n → ℝ)
    (x : ℕ → Fin m) (y : ℕ → Fin n) (C : ℝ)
    (hc : ∀ t a b, |jointCount (Finset.range t) x y a b - (t : ℝ) * D a b| ≤ C)
    (s t : ℕ) (hst : s ≤ t) (a : Fin m) (b : Fin n) :
    |jointCount (Finset.Ico s t) x y a b - ((t - s : ℕ) : ℝ) * D a b| ≤ 2 * C := by
  rw [jointCount_Ico x y s t hst, Nat.cast_sub hst]
  have h := (abs_sub (jointCount (Finset.range t) x y a b - (t : ℝ) * D a b)
    (jointCount (Finset.range s) x y a b - (s : ℝ) * D a b)).trans
      (add_le_add (hc t a b) (hc s a b))
  calc
    _ = |(jointCount (Finset.range t) x y a b - (t : ℝ)*D a b) -
        (jointCount (Finset.range s) x y a b - (s : ℝ)*D a b)| := by congr 1; ring
    _ ≤ C+C := h
    _ = 2*C := by ring

theorem count_bound_tendsto {m n : ℕ} (D : Fin m → Fin n → ℝ)
    (x : ℕ → Fin m) (y : ℕ → Fin n) (C : ℝ)
    (hc : ∀ t a b, |jointCount (Finset.range t) x y a b - (t : ℝ) * D a b| ≤ C)
    (a : Fin m) (b : Fin n) :
    Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b)) := by
  have hz : Tendsto (fun t : ℕ =>
      (jointCount (Finset.range t) x y a b - (t : ℝ) * D a b) / t) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat C)
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (hc t a b) (Nat.cast_nonneg t)
  have hh : Tendsto (fun t : ℕ =>
      (jointCount (Finset.range t) x y a b - (t : ℝ) * D a b) / t + D a b)
      atTop (𝓝 (D a b)) := by simpa using hz.add_const (D a b)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  change (jointCount (Finset.range t) x y a b - (t : ℝ) * D a b) / t + D a b =
    jointCount (Finset.range t) x y a b / t
  field_simp
  ring

theorem exists_bounded_play {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD : IsJointDist D) :
    ∃ (x : ℕ → Fin m) (y : ℕ → Fin n), (∀ t, 0 < D (x t) (y t)) ∧
      (∀ t a b, |jointCount (Finset.range t) x y a b - (t : ℝ) * D a b| ≤ (m * n : ℕ)) ∧
      ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b)) := by
  classical
  let p : Fin m × Fin n → ℝ := fun s => D s.1 s.2
  have hp0 : ∀ s, 0 ≤ p s := fun s => hD.1 _ _
  have hp1 : ∑ s, p s = 1 := by
    dsimp [p]
    rw [Fintype.sum_prod_type']
    exact hD.2
  have hne : Nonempty (Fin m × Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hp1
  let : Nonempty (Fin m × Fin n) := hne
  let z : ℕ → Fin m × Fin n := fun t => aux_epl_sel p (aux_epl_err p t)
  let x : ℕ → Fin m := fun t => (z t).1
  let y : ℕ → Fin n := fun t => (z t).2
  have hsupp : ∀ t, 0 < D (x t) (y t) := by
    intro t
    have hpos := aux_epl_sel_pos p hp1 (aux_epl_err p t) (aux_epl_err_sum p hp1 t)
    change 0 < p (z t)
    by_contra h
    have hz : p (z t) = 0 := le_antisymm (le_of_not_gt h) (hp0 _)
    have he := aux_epl_err_zero p t (z t) hz
    change 0 < aux_epl_err p t (z t) + p (z t) at hpos
    linarith
  have hc : ∀ t a b, |jointCount (Finset.range t) x y a b - (t : ℝ) * D a b| ≤ (m * n : ℕ) := by
    intro t a b
    have he : jointCount (Finset.range t) x y a b =
        (t : ℝ) * D a b - aux_epl_err p t (a,b) := by
      simpa only [jointCount, x, y, z, p, Prod.ext_iff] using aux_epl_count p t (a,b)
    rw [he]
    have hlo := aux_epl_err_lower p hp0 hp1 t (a,b)
    have hup := aux_epl_err_upper p hp0 hp1 t (a,b)
    have hcard : (1 : ℝ) ≤ Fintype.card (Fin m × Fin n) := by
      exact_mod_cast Fintype.card_pos
    simp only [Fintype.card_prod, Fintype.card_fin] at hup hcard
    apply abs_le.mpr
    constructor <;> linarith
  exact ⟨x, y, hsupp, hc, fun a b => count_bound_tendsto D x y (m*n : ℕ) hc a b⟩


end CalibratedCE.GenericProof
end

/- Complete checked body: FiniteBins -/
section

open scoped BigOperators Classical
open CalibratedCE.Generic

namespace CalibratedCE.GenericProof

noncomputable def countWhere (I : Finset ℕ) (P : ℕ → Prop) : ℝ :=
  ((I.filter P).card : ℝ)

theorem countWhere_eq_sum (I : Finset ℕ) (P : ℕ → Prop) :
    countWhere I P = ∑ s ∈ I, if P s then (1 : ℝ) else 0 := by
  simp only [countWhere, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem countWhere_factor {α β : Type*} (I : Finset ℕ) (S : Finset α)
    (a : ℕ → α) (F : α → β) (P : ℕ → Prop) (p : β)
    (hS : ∀ s ∈ I, a s ∈ S) :
    countWhere I (fun s => F (a s) = p ∧ P s) =
      ∑ b ∈ S.filter (fun b => F b = p), countWhere I (fun s => a s = b ∧ P s) := by
  have h : (I.filter (fun s => F (a s) = p ∧ P s)).card =
      ∑ b ∈ S.filter (fun b => F b = p), (I.filter (fun s => a s = b ∧ P s)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := a) (t := S.filter (fun b => F b = p))]
    · apply Finset.sum_congr rfl
      intro b hb
      have hFb := (Finset.mem_filter.mp hb).2
      congr 1
      ext s
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _, h3⟩, h4⟩
        exact ⟨h1, h4, h3⟩
      · rintro ⟨h1, h4, h3⟩
        exact ⟨⟨h1, h4 ▸ hFb, h3⟩, h4⟩
    · intro s hs
      exact Finset.mem_filter.mpr ⟨hS s (Finset.mem_filter.mp hs).1,
        (Finset.mem_filter.mp hs).2.1⟩
  dsimp only [countWhere]
  have hr := congrArg (fun k : ℕ => (k : ℝ)) h
  push_cast at hr
  convert hr using 1 <;> congr!

noncomputable def forecastDeviation {n : ℕ} (I : Finset ℕ) (f : ℕ → Fin n → ℝ)
    (y : ℕ → Fin n) (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  countWhere I (fun s => f s = p ∧ y s = j) - p j * countWhere I (fun s => f s = p)

noncomputable def labelDeviation {α : Type*} {n : ℕ} (I : Finset ℕ) (a : ℕ → α)
    (y : ℕ → Fin n) (b : α) (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  countWhere I (fun s => a s = b ∧ y s = j) - p j * countWhere I (fun s => a s = b)

theorem forecastDeviation_factor {α : Type*} {n : ℕ} (I : Finset ℕ) (S : Finset α)
    (a : ℕ → α) (F : α → Fin n → ℝ) (y : ℕ → Fin n) (p : Fin n → ℝ) (j : Fin n)
    (hS : ∀ s ∈ I, a s ∈ S) :
    forecastDeviation I (fun s => F (a s)) y p j =
      ∑ b ∈ S.filter (fun b => F b = p), labelDeviation I a y b (F b) j := by
  have hn : countWhere I (fun s => F (a s) = p) =
      ∑ b ∈ S.filter (fun b => F b = p), countWhere I (fun s => a s = b) := by
    have ht := countWhere_factor I S a F (fun _ => True) p hS
    simp only [countWhere, and_true] at ht ⊢
    convert ht using 1 <;> congr!
  unfold forecastDeviation
  rw [countWhere_factor I S a F (fun s => y s = j) p hS, hn]
  have he : (∑ b ∈ S.filter (fun b => F b=p), countWhere I (fun s => a s=b ∧ y s=j)) -
      p j * (∑ b ∈ S.filter (fun b => F b=p), countWhere I (fun s => a s=b)) =
      ∑ b ∈ S.filter (fun b => F b=p),
        (countWhere I (fun s => a s=b ∧ y s=j)-p j*countWhere I (fun s => a s=b)) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  trans (∑ b ∈ S.filter (fun b => F b=p),
    (countWhere I (fun s => a s=b ∧ y s=j)-p j*countWhere I (fun s => a s=b)))
  · convert he using 1
    congr!
  apply Finset.sum_congr rfl
  intro b hb
  unfold labelDeviation
  rw [(Finset.mem_filter.mp hb).2]

theorem calibScore_eq_mass {n : ℕ} (f : ℕ → Fin n → ℝ) (y : ℕ → Fin n)
    (j : Fin n) (t : ℕ) :
    Shared.calibScore f y j t =
      (∑ p ∈ (Finset.range t).image f, |forecastDeviation (Finset.range t) f y p j|) / (t : ℝ) := by
  unfold Shared.calibScore
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  have hc : ((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card ≤ Shared.N f p t := by
    apply Finset.card_le_card
    intro s hs
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, (Finset.mem_filter.mp hs).2.1⟩
  have hn : countWhere (Finset.range t) (fun s => f s = p) = (Shared.N f p t : ℝ) := by
    unfold countWhere Shared.N
    congr
  unfold forecastDeviation
  rw [hn]
  by_cases h0 : Shared.N f p t = 0
  · have hct : ((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card = 0 := by omega
    have hcz : countWhere (Finset.range t) (fun s => f s = p ∧ y s = j)=0 := by
      have hz : (((Finset.range t).filter (fun s => f s=p ∧ y s=j)).card : ℝ)=0 := by
        exact_mod_cast hct
      unfold countWhere
      convert hz using 1
      congr!
    rw [h0,hcz]
    simp
  · have hp : 0 < (Shared.N f p t : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hr : Shared.rho f y p j t =
        countWhere (Finset.range t) (fun s => f s=p ∧ y s=j)/(Shared.N f p t:ℝ) := by
      rw [Shared.rho,if_neg h0]
      unfold countWhere
      congr
    rw [hr, ← abs_of_pos hp, ← abs_mul, abs_of_pos hp]
    congr 1
    field_simp

theorem calibScore_nonneg {n : ℕ} (f : ℕ → Fin n → ℝ) (y : ℕ → Fin n)
    (j : Fin n) (t : ℕ) : 0 ≤ Shared.calibScore f y j t := by
  rw [calibScore_eq_mass]
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Nat.cast_nonneg t)

theorem calibScore_le_bins {α : Type*} {n : ℕ} (S : Finset α) (a : ℕ → α)
    (F : α → Fin n → ℝ) (y : ℕ → Fin n) (j : Fin n) (t : ℕ)
    (hS : ∀ s ∈ Finset.range t, a s ∈ S) :
    Shared.calibScore (fun s => F (a s)) y j t ≤
      (∑ b ∈ S, |labelDeviation (Finset.range t) a y b (F b) j|) / (t : ℝ) := by
  rw [calibScore_eq_mass]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg t)
  have hsub : (Finset.range t).image (fun s => F (a s)) ⊆ S.image F := by
    intro p hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨a s, hS s hs, rfl⟩
  calc
    _ ≤ ∑ p ∈ S.image F, |forecastDeviation (Finset.range t) (fun s => F (a s)) y p j| :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ p ∈ S.image F, ∑ b ∈ S.filter (fun b => F b = p),
        |labelDeviation (Finset.range t) a y b (F b) j| := by
      apply Finset.sum_le_sum
      intro p _
      rw [forecastDeviation_factor (Finset.range t) S a F y p j hS]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun b hb => Finset.mem_image.mpr ⟨b,hb,rfl⟩) _


end CalibratedCE.GenericProof
end

/- Complete checked body: EpochCounts -/
section

open scoped BigOperators Classical
open CalibratedCE.Generic

namespace CalibratedCE.GenericProof

def epochEnd (r t : ℕ) : ℕ := min t ((r+1)^2)

theorem epoch_mem_iff (r s t : ℕ) :
    s < t ∧ Nat.sqrt s = r ↔ r^2 ≤ s ∧ s < epochEnd r t := by
  unfold epochEnd
  rw [lt_min_iff]
  constructor
  · rintro ⟨hst, hr⟩
    have h := Nat.eq_sqrt'.mp hr.symm
    exact ⟨h.1, hst, h.2⟩
  · rintro ⟨hrs, hst, hsr⟩
    exact ⟨hst, (Nat.eq_sqrt'.mpr ⟨hrs,hsr⟩).symm⟩

theorem rowCount_eq_sum {m n : ℕ} (I : Finset ℕ) (x : ℕ → Fin m) (y : ℕ → Fin n)
    (a : Fin m) : countWhere I (fun s => x s = a) = ∑ b, jointCount I x y a b := by
  simp only [countWhere_eq_sum, jointCount_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : x s = a <;> simp [h]

theorem epoch_label_deviation {m n : ℕ} (x : ℕ → Fin m) (y : ℕ → Fin n)
    (r t : ℕ) (a : Fin m) (q : Fin n → ℝ) (j : Fin n) :
    labelDeviation (Finset.range t) (fun s => (Nat.sqrt s, x s)) y (r,a) q j =
      jointCount (Finset.Ico (r^2) (epochEnd r t)) x y a j -
        q j * ∑ b, jointCount (Finset.Ico (r^2) (epochEnd r t)) x y a b := by
  have hc : countWhere (Finset.range t) (fun s => (Nat.sqrt s,x s) = (r,a) ∧ y s = j) =
      jointCount (Finset.Ico (r^2) (epochEnd r t)) x y a j := by
    unfold countWhere jointCount
    congr 2
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Prod.mk.injEq, Finset.mem_Ico]
    constructor
    · rintro ⟨hst, ⟨hr,ha⟩,hj⟩
      exact ⟨(epoch_mem_iff r s t).mp ⟨hst,hr⟩,ha,hj⟩
    · rintro ⟨hrst,ha,hj⟩
      have h := (epoch_mem_iff r s t).mpr hrst
      exact ⟨h.1,⟨h.2,ha⟩,hj⟩
  have hn : countWhere (Finset.range t) (fun s => (Nat.sqrt s,x s) = (r,a)) =
      countWhere (Finset.Ico (r^2) (epochEnd r t)) (fun s => x s = a) := by
    unfold countWhere
    congr 2
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Prod.mk.injEq, Finset.mem_Ico]
    constructor
    · rintro ⟨hst,hr,ha⟩
      exact ⟨(epoch_mem_iff r s t).mp ⟨hst,hr⟩,ha⟩
    · rintro ⟨hrst,ha⟩
      have h := (epoch_mem_iff r s t).mpr hrst
      exact ⟨h.1,h.2,ha⟩
  unfold labelDeviation
  rw [hc,hn,rowCount_eq_sum _ x y a]

theorem epoch_length_le (r t : ℕ) (hr : r ≤ Nat.sqrt t) :
    r^2 ≤ epochEnd r t ∧ ((epochEnd r t - r^2 : ℕ) : ℝ) ≤ 2*(r:ℝ)+1 := by
  have h1 : r^2 ≤ t := Nat.le_sqrt'.mp hr
  have h2 : r^2 ≤ (r+1)^2 := by nlinarith
  have hstart : r^2 ≤ epochEnd r t := le_min h1 h2
  refine ⟨hstart, ?_⟩
  have hend : (epochEnd r t : ℝ) ≤ ((r : ℝ)+1)^2 := by
    exact_mod_cast (min_le_right t ((r+1)^2))
  rw [Nat.cast_sub hstart, Nat.cast_pow]
  nlinarith

theorem row_mass_bounds {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD : IsJointDist D)
    (a : Fin m) : 0 ≤ ∑ b, D a b ∧ ∑ b, D a b ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun b _ => hD.1 a b), ?_⟩
  rw [← hD.2]
  exact Finset.single_le_sum (fun c _ => Finset.sum_nonneg (fun b _ => hD.1 c b))
    (Finset.mem_univ a)

theorem dist_coordinate_bounds {n : ℕ} (q : Fin n → ℝ) (hq : IsDist q) (j : Fin n) :
    0 ≤ q j ∧ q j ≤ 1 := by
  refine ⟨hq.1 j, ?_⟩
  rw [← hq.2]
  exact Finset.single_le_sum (fun b _ => hq.1 b) (Finset.mem_univ j)

theorem epoch_bin_bound {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD : IsJointDist D)
    (x : ℕ → Fin m) (y : ℕ → Fin n) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ t a b, |jointCount (Finset.range t) x y a b - (t : ℝ)*D a b| ≤ C)
    (F : ℕ → Fin m → Fin n → ℝ) (hF : ∀ r a, IsDist (F r a))
    (hclose : ∀ r a, 0 < ∑ b, D a b → ∀ b,
      |F r a b - condForecast₁ D a b| ≤ 1/((r:ℝ)+1))
    (r t : ℕ) (hr : r ≤ Nat.sqrt t) (a : Fin m) (j : Fin n) :
    |labelDeviation (Finset.range t) (fun s => (Nat.sqrt s,x s)) y (r,a) (F r a) j| ≤
      2*C*((n:ℝ)+1)+2 := by
  let I := Finset.Ico (r^2) (epochEnd r t)
  let L : ℝ := (epochEnd r t-r^2 : ℕ)
  let A : ℝ := ∑ b, D a b
  have hlen := epoch_length_le r t hr
  have hab : ∀ b, |jointCount I x y a b-L*D a b| ≤ 2*C := fun b =>
    interval_count_bound D x y C hcount (r^2) (epochEnd r t) hlen.1 a b
  have ha : |(∑ b, jointCount I x y a b)-L*A| ≤ (n:ℝ)*(2*C) := by
    dsimp [A]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ b, |jointCount I x y a b-L*D a b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b : Fin n, 2*C := Finset.sum_le_sum (fun b _ => hab b)
      _ = _ := by simp
  have hA := row_mass_bounds D hD a
  have hq := dist_coordinate_bounds (F r a) (hF r a) j
  have herr : |D a j-F r a j*A| ≤ 1/((r:ℝ)+1) := by
    by_cases hpos : 0 < A
    · have hc := hclose r a hpos j
      have he : D a j-F r a j*A = A*(condForecast₁ D a j-F r a j) := by
        unfold condForecast₁
        change D a j-F r a j*A = A*(D a j/A-F r a j)
        field_simp
      rw [he,abs_mul,abs_of_nonneg hA.1,abs_sub_comm]
      calc
        _ ≤ A*(1/((r:ℝ)+1)) := mul_le_mul_of_nonneg_left hc hA.1
        _ ≤ _ := by
          exact mul_le_of_le_one_left (by positivity) hA.2
    · have hAz : A=0 := le_antisymm (le_of_not_gt hpos) hA.1
      have hz : D a j=0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hD.1 a b)).mp hAz j (Finset.mem_univ j)
      rw [hAz,hz]
      simp only [mul_zero,sub_self,abs_zero]
      positivity
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hLd : L*(1/((r:ℝ)+1)) ≤ 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    change ((epochEnd r t-r^2 : ℕ) : ℝ) ≤ 2*((r:ℝ)+1)
    linarith [hlen.2]
  rw [epoch_label_deviation]
  change |jointCount I x y a j-F r a j*(∑ b, jointCount I x y a b)| ≤ _
  have he : jointCount I x y a j-F r a j*(∑ b, jointCount I x y a b) =
      (jointCount I x y a j-L*D a j)-F r a j*((∑ b, jointCount I x y a b)-L*A)+
        L*(D a j-F r a j*A) := by ring
  rw [he]
  calc
    _ ≤ |jointCount I x y a j-L*D a j| +
        |F r a j*((∑ b, jointCount I x y a b)-L*A)|+|L*(D a j-F r a j*A)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 2*C+(n:ℝ)*(2*C)+L*(1/((r:ℝ)+1)) := by
      rw [abs_mul,abs_mul,abs_of_nonneg hq.1,abs_of_nonneg hL]
      apply add_le_add
      · apply add_le_add (hab j)
        exact (mul_le_mul_of_nonneg_left ha hq.1).trans
          (mul_le_of_le_one_left (by positivity) hq.2)
      · exact mul_le_mul_of_nonneg_left herr hL
    _ ≤ _ := by nlinarith


end CalibratedCE.GenericProof
end

/- Complete checked body: EpochCalibration -/
section

open scoped BigOperators Topology Classical
open Filter CalibratedCE.Generic

namespace CalibratedCE.GenericProof

theorem sqrt_nat_tendsto : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (N^2)] with t ht
  exact Nat.le_sqrt'.mpr ht

theorem sqrt_epoch_ratio_tendsto :
    Tendsto (fun t : ℕ => ((Nat.sqrt t : ℝ)+1)/(t:ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℕ => 2/(Nat.sqrt t : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 2).comp sqrt_nat_tendsto
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < (t:ℝ) := by exact_mod_cast (show 0<t by omega)
  have hr : (1:ℝ) ≤ Nat.sqrt t := by
    exact_mod_cast (Nat.sqrt_pos.mpr (show 0<t by omega))
  have hr0 : 0 < (Nat.sqrt t : ℝ) := by linarith
  have hs : (Nat.sqrt t : ℝ)^2 ≤ (t:ℝ) := by exact_mod_cast Nat.sqrt_le' t
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply (div_le_div_iff₀ ht0 hr0).2
  nlinarith

theorem square_forecast_score_bound {m n : ℕ} (D : Fin m → Fin n → ℝ)
    (hD : IsJointDist D) (x : ℕ → Fin m) (y : ℕ → Fin n) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ t a b, |jointCount (Finset.range t) x y a b-(t:ℝ)*D a b| ≤ C)
    (F : ℕ → Fin m → Fin n → ℝ) (hF : ∀ r a, IsDist (F r a))
    (hclose : ∀ r a, 0 < ∑ b, D a b → ∀ b,
      |F r a b-condForecast₁ D a b| ≤ 1/((r:ℝ)+1))
    (j : Fin n) (t : ℕ) :
    Shared.calibScore (fun s => F (Nat.sqrt s) (x s)) y j t ≤
      ((m:ℝ)*(2*C*((n:ℝ)+1)+2))*((Nat.sqrt t:ℝ)+1)/(t:ℝ) := by
  let S : Finset (ℕ × Fin m) := (Finset.range (Nat.sqrt t+1)).product Finset.univ
  have hcard : S.card = (Nat.sqrt t+1)*m := by
    change ((Finset.range (Nat.sqrt t+1)) ×ˢ (Finset.univ : Finset (Fin m))).card = _
    simp only [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin]
  have hS : ∀ s ∈ Finset.range t, (Nat.sqrt s,x s) ∈ S := by
    intro s hs
    refine Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.sqrt_le_sqrt (Nat.le_of_lt (Finset.mem_range.mp hs)))
  have hs : (∑ b ∈ S, |labelDeviation (Finset.range t) (fun s => (Nat.sqrt s,x s))
      y b (F b.1 b.2) j|) ≤ ((Nat.sqrt t:ℝ)+1)*(m:ℝ)*(2*C*((n:ℝ)+1)+2) := by
    calc
      _ ≤ ∑ _b ∈ S, (2*C*((n:ℝ)+1)+2) := by
        apply Finset.sum_le_sum
        intro b hb
        have hr : b.1 ≤ Nat.sqrt t := by
          have h := Finset.mem_range.mp (Finset.mem_product.mp hb).1
          omega
        exact epoch_bin_bound D hD x y C hC hcount F hF hclose b.1 t hr b.2 j
      _ = _ := by
        rw [Finset.sum_const,hcard,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ (∑ b ∈ S, |labelDeviation (Finset.range t) (fun s => (Nat.sqrt s,x s))
        y b (F b.1 b.2) j|)/(t:ℝ) :=
      calibScore_le_bins S (fun s => (Nat.sqrt s,x s)) (fun b => F b.1 b.2) y j t hS
    _ ≤ (((Nat.sqrt t:ℝ)+1)*(m:ℝ)*(2*C*((n:ℝ)+1)+2))/(t:ℝ) :=
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg t)
    _ = _ := by ring

theorem calibrated_square_forecasts {m n : ℕ} (D : Fin m → Fin n → ℝ)
    (hD : IsJointDist D) (x : ℕ → Fin m) (y : ℕ → Fin n)
    (_hsupp : ∀ t, 0 < D (x t) (y t)) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ t a b, |jointCount (Finset.range t) x y a b-(t:ℝ)*D a b| ≤ C)
    (F : ℕ → Fin m → Fin n → ℝ) (hF : ∀ r a, IsDist (F r a))
    (hclose : ∀ r a, 0 < ∑ b, D a b → ∀ b,
      |F r a b-condForecast₁ D a b| ≤ 1/((r:ℝ)+1)) :
    Shared.Calibrated (fun t => F (Nat.sqrt t) (x t)) y := by
  intro j
  have hlim : Tendsto (fun t : ℕ =>
      ((m:ℝ)*(2*C*((n:ℝ)+1)+2))*((Nat.sqrt t:ℝ)+1)/(t:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc,mul_zero] using
      sqrt_epoch_ratio_tendsto.const_mul ((m:ℝ)*(2*C*((n:ℝ)+1)+2))
  apply squeeze_zero_norm' _ hlim
  filter_upwards with t
  rw [Real.norm_eq_abs,abs_of_nonneg (calibScore_nonneg _ y j t)]
  exact square_forecast_score_bound D hD x y C hC hcount F hF hclose j t


end CalibratedCE.GenericProof
end

/- Complete checked body: GenericConverse -/
section

open Filter Topology
open CalibratedCE.Generic

namespace CalibratedCE.GenericProof

theorem isCE_transpose {m n : ℕ} {u₁ u₂ D : Fin m → Fin n → ℝ}
    (h : IsCE u₁ u₂ D) :
    IsCE (fun b a => u₂ a b) (fun b a => u₁ a b) (fun b a => D a b) := by
  refine ⟨⟨fun b a => h.1.1 a b, ?_⟩, ?_, ?_⟩
  · rw [Finset.sum_comm]
    exact h.1.2
  · intro Φ
    calc
      _ = ∑ a, ∑ b, D a b * u₂ a (Φ b) := Finset.sum_comm
      _ ≤ ∑ a, ∑ b, D a b * u₂ a b := h.2.2 Φ
      _ = _ := Finset.sum_comm
  · intro Φ
    calc
      _ = ∑ a, ∑ b, D a b * u₁ (Φ a) b := Finset.sum_comm
      _ ≤ ∑ a, ∑ b, D a b * u₁ a b := h.2.1 Φ
      _ = _ := Finset.sum_comm

theorem CE_mem_limitSet_of_strictWitnesses {m n : ℕ}
    (u₁ u₂ D : Fin m → Fin n → ℝ) (hCE : IsCE u₁ u₂ D)
    (hgen₁ : StrictWitnesses u₁) (hgen₂ : StrictWitnesses (fun b a => u₂ a b)) :
    D ∈ LimitSet u₁ u₂ := by
  classical
  obtain ⟨x, y, hsupp, hcount, hlim⟩ := exists_bounded_play D hCE.1
  let : Nonempty (Fin m) := ⟨x 0⟩
  let : Nonempty (Fin n) := ⟨y 0⟩
  have hCE' := isCE_transpose hCE
  obtain ⟨F, hFdist, hFstrict, hFclose⟩ := exists_strict_forecasts u₁ D
    (checked_CE_condForecast_best_response u₁ u₂ D hCE).1 hgen₁
  obtain ⟨G, hGdist, hGstrict, hGclose⟩ := exists_strict_forecasts
    (fun b a => u₂ a b) (fun b a => D a b)
    (checked_CE_condForecast_best_response (fun b a => u₂ a b)
      (fun b a => u₁ a b) (fun b a => D a b) hCE').1 hgen₂
  have hxmass (t : ℕ) : 0 < ∑ b, D (x t) b :=
    lt_of_lt_of_le (hsupp t)
      (Finset.single_le_sum (fun b _ => hCE.1.1 (x t) b) (Finset.mem_univ (y t)))
  have hymass (t : ℕ) : 0 < ∑ a, D a (y t) :=
    lt_of_lt_of_le (hsupp t)
      (Finset.single_le_sum (fun a _ => hCE.1.1 a (y t)) (Finset.mem_univ (x t)))
  have hcount' : ∀ t b a,
      |jointCount (Finset.range t) y x b a - (t : ℝ) * D a b| ≤ ((m * n : ℕ) : ℝ) := by
    intro t b a
    have he : jointCount (Finset.range t) y x b a =
        jointCount (Finset.range t) x y a b := by
      unfold jointCount
      congr 2
      ext s
      simp only [Finset.mem_filter, and_comm, and_assoc]
    rw [he]
    exact hcount t a b
  have hc₁ := calibrated_square_forecasts D hCE.1 x y hsupp ((m * n : ℕ) : ℝ)
    (by positivity) hcount F hFdist hFclose
  have hc₂ := calibrated_square_forecasts (fun b a => D a b) hCE'.1 y x hsupp
    ((m * n : ℕ) : ℝ) (by positivity) hcount' G hGdist hGclose
  refine limitSet_of_sequences u₁ u₂ D x y
    (fun t => F (Nat.sqrt t) (x t)) (fun t => G (Nat.sqrt t) (y t))
    (bestReply u₁) (bestReply (fun b a => u₂ a b))
    (bestReply_isBestReply u₁) (bestReply_isBestReply (fun b a => u₂ a b))
    (fun t => hFdist _ _) (fun t => hGdist _ _) ?_ ?_ hc₁ hc₂ hlim
  · intro t
    exact bestReply_eq_of_strict u₁ _ (x t) (hFstrict _ _ (hxmass t))
  · intro t
    exact bestReply_eq_of_strict (fun b a => u₂ a b) _ (y t)
      (hGstrict _ _ (hymass t))

end CalibratedCE.GenericProof

end

/- Complete checked body: GenericRoot -/
section

open MeasureTheory Filter Topology
open CalibratedCE.GenericProof

namespace CalibratedCE.Generic

theorem ae_limitSet_eq_CESet (m n : ℕ) :
    ∀ᵐ G : (Fin m → Fin n → ℝ) × (Fin m → Fin n → ℝ) ∂MeasureTheory.volume,
      LimitSet G.1 G.2 = CESet G.1 G.2 := by
  filter_upwards [ae_game_strictWitnesses m n] with G hG
  refine Set.Subset.antisymm (checked_limitSet_subset_CESet G.1 G.2) ?_
  intro D hD
  exact CE_mem_limitSet_of_strictWitnesses G.1 G.2 D hD hG.1 hG.2

end CalibratedCE.Generic

end

open CalibratedCE CalibratedCE.Generic
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal


theorem solution (m n : ℕ) :
    ∀ᵐ G : (Fin m → Fin n → ℝ) × (Fin m → Fin n → ℝ) ∂MeasureTheory.volume,
      LimitSet G.1 G.2 = CESet G.1 G.2 := by
  exact CalibratedCE.Generic.ae_limitSet_eq_CESet m n

#print axioms CalibratedCE.Generic.ae_limitSet_eq_CESet
#print axioms solution
