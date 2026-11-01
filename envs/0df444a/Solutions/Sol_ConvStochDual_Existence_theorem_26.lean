-- Prove2me | solution 1 for ConvStochDual.Existence.theorem_26
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:37:05.575935+00:00
-- url     : https://prove2.me/submissions/1e8f348f-ff68-49f4-9103-9a27c17ec8ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConvStochDual_Existence_Setting
import Theorems.Thm_ConvStochDual_Existence_theorem_25
import Theorems.Thm_ConvStochDual_Existence_lemma_16_VY

open MeasureTheory Filter

namespace CSDT26

open ConvStochDual.Existence

theorem dot_add_left {k : ℕ} (a a' b : Fin k → ℝ) : dot (a + a') b = dot a b + dot a' b := by
  unfold dot; simp [add_mul, Finset.sum_add_distrib]

theorem dot_smul_left {k : ℕ} (c : ℝ) (a b : Fin k → ℝ) : dot (c • a) b = c * dot a b := by
  unfold dot; simp [Finset.mul_sum, mul_assoc]

theorem dot_zero_right {k : ℕ} (a : Fin k → ℝ) : dot a 0 = 0 := by
  unfold dot; simp

/-- EReal: from `X - r ≤ Z - s` deduce `s - Z ≤ r - X`. -/
theorem ereal_swap (X Z : EReal) (r s : ℝ) (h : X - (r : EReal) ≤ Z - (s : EReal)) :
    (s : EReal) - Z ≤ (r : EReal) - X := by
  induction Z using EReal.rec with
  | bot =>
    rw [EReal.bot_sub, le_bot_iff] at h
    induction X using EReal.rec with
    | bot => rw [EReal.coe_sub_bot]; exact le_top
    | top => simp at h
    | coe x => rw [← EReal.coe_sub] at h; exact absurd h (EReal.coe_ne_bot _)
  | top => rw [EReal.sub_top]; exact bot_le
  | coe z =>
    induction X using EReal.rec with
    | bot => rw [EReal.coe_sub_bot]; exact le_top
    | top => rw [EReal.top_sub_coe, ← EReal.coe_sub, top_le_iff] at h
             exact absurd h (EReal.coe_ne_top _)
    | coe x =>
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]; linarith

variable {Ω X U : Type*} [MeasurableSpace Ω]
  [AddCommGroup X] [Module ℝ X] [UniformSpace X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {T n m : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : Fin n → Fin (T + 1)}
  {𝔽 : Fin (T + 1) → MeasurableSpace Ω}
  {ιX : X →ₗ[ℝ] RV Ω P n} {ιU : U →ₗ[ℝ] RV Ω P m}
  {V : Submodule ℝ (RV Ω P n)} {Y : Submodule ℝ (RV Ω P m)}

/-- The pairing `x ↦ ⟨x, v⟩` as a continuous linear functional. -/
noncomputable def pairCLM {A : Type*} [AddCommGroup A] [Module ℝ A] [TopologicalSpace A] {k : ℕ}
    (ι : A →ₗ[ℝ] RV Ω P k) (v : RV Ω P k)
    (hint : ∀ a : A, Integrable (fun ω => dot (ι a ω) (v ω)) P)
    (hcont : Continuous (fun a : A => pair P (ι a) v)) : A →L[ℝ] ℝ where
  toFun a := pair P (ι a) v
  map_add' a b := by
    unfold pair
    rw [← integral_add (hint a) (hint b)]
    refine integral_congr_ae ?_
    rw [map_add]
    filter_upwards [AEEqFun.coeFn_add (ι a) (ι b)] with ω hω
    rw [hω, Pi.add_apply, dot_add_left]
  map_smul' c a := by
    unfold pair
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    rw [map_smul]
    filter_upwards [AEEqFun.coeFn_smul c (ι a)] with ω hω
    rw [hω, Pi.smul_apply, dot_smul_left]
  cont := hcont

theorem adapted_smul (c : ℝ) (a : RV Ω P n) (ha : Adapted τ 𝔽 P a) :
    Adapted τ 𝔽 P (c • a) := by
  intro i
  obtain ⟨g, hg, hag⟩ := ha i
  refine ⟨fun ω => c * g ω, hg.const_mul c, ?_⟩
  filter_upwards [AEEqFun.coeFn_smul c a, hag] with ω h1 h2
  show (c • a) ω i = c * g ω
  rw [h1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
  exact congrArg (c * ·) h2

theorem zero_mem_perp (s : Setting P τ 𝔽 ιX ιU V Y) : (0 : V) ∈ XaPerp s := by
  intro x _
  unfold pair
  have : (fun ω => dot (ιX x ω) (((0 : V) : RV Ω P n) ω)) =ᵐ[P] fun _ => 0 := by
    filter_upwards [AEEqFun.coeFn_zero (μ := P) (β := Fin n → ℝ)] with ω hω
    simp only [Submodule.coe_zero]
    rw [hω, Pi.zero_apply, dot_zero_right]
  rw [integral_congr_ae this, integral_zero]

theorem phiStar_top (s : Setting P τ 𝔽 ιX ιU V Y)
    (hdom : ∃ q : X × U, Ef s (ιX q.1) (ιU q.2) < ⊤)
    (p : X →L[ℝ] ℝ) (hp : p ∉ XaCirc s) (y : U →L[ℝ] ℝ) : phiStar s p y = ⊤ := by
  simp only [XaCirc, Set.mem_setOf_eq, not_forall] at hp
  obtain ⟨xa, hxa, hpxa⟩ := hp
  obtain ⟨⟨x0, u0⟩, h0⟩ := hdom
  have hadapt : ∀ c : ℝ, Adapted τ 𝔽 P (ιX x0 - ιX (x0 + c • xa)) := by
    intro c
    have e : ιX x0 - ιX (x0 + c • xa) = (-c) • ιX xa := by
      rw [map_add, map_smul, neg_smul]; abel
    rw [e]; exact adapted_smul _ _ hxa
  have hphi_le : ∀ c : ℝ, phi s (x0 + c • xa) u0 ≤ Ef s (ιX x0) (ιU u0) := fun c =>
    iInf₂_le (f := fun x (_ : Adapted τ 𝔽 P (ιX x - ιX (x0 + c • xa))) =>
      Ef s (ιX x) (ιU u0)) x0 (hadapt c)
  have hterm : ∀ c : ℝ, ((p (x0 + c • xa) + y u0 : ℝ) : EReal) - phi s (x0 + c • xa) u0 ≤
      phiStar s p y := fun c =>
    le_iSup₂_of_le (f := fun z u => ((p z + y u : ℝ) : EReal) - phi s z u)
      (x0 + c • xa) u0 le_rfl
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  induction hE : Ef s (ιX x0) (ιU u0) using EReal.rec with
  | bot =>
    have h1 := hphi_le 0
    rw [hE, le_bot_iff] at h1
    have := hterm 0
    rw [h1, EReal.coe_sub_bot, top_le_iff] at this
    rw [this]; exact EReal.coe_lt_top M
  | top => rw [hE] at h0; exact absurd h0 (lt_irrefl _)
  | coe e =>
    set c : ℝ := (M + 1 - p x0 - y u0 + e) / p xa with hc
    have h1 := hphi_le c
    rw [hE] at h1
    have h2 := (hterm c)
    have h3 : ((p (x0 + c • xa) + y u0 : ℝ) : EReal) - (e : EReal) ≤
        ((p (x0 + c • xa) + y u0 : ℝ) : EReal) - phi s (x0 + c • xa) u0 :=
      EReal.sub_le_sub le_rfl h1
    have h4 : p (x0 + c • xa) + y u0 - e = M + 1 := by
      rw [map_add, map_smul, smul_eq_mul, hc]
      field_simp
      ring
    rw [← EReal.coe_sub, h4] at h3
    calc (M : EReal) < ((M + 1 : ℝ) : EReal) := by
          rw [EReal.coe_lt_coe_iff]; linarith
      _ ≤ _ := h3.trans h2

open ConvStochDual.Existence in
theorem main26 (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (hEf : EfProperLsc s) (hEt : CondExpClosed s)
    (hA23 : Assumption23_1 s ∧ Assumption23_2 s) :
    valDs s = valD s ∧
      ((∃ p : X →L[ℝ] ℝ, ∃ y : U →L[ℝ] ℝ,
          ((y s.ubar : ℝ) : EReal) - phiStar s p y = valDs s) ↔
        (∃ p : V, p ∈ XaPerp s ∧
          ∃ y : Y, dualObj s p y = valD s)) := by
  have hdom : ∃ q : X × U, Ef s (ιX q.1) (ιU q.2) < ⊤ := hEf.2.1
  let emb : V → (X →L[ℝ] ℝ) := fun v =>
    pairCLM ιX v.1 (fun a => hS.pair_integrableX a v) (hS.pair_continuousX v)
  let embY : Y → (U →L[ℝ] ℝ) := fun w =>
    pairCLM ιU w.1 (fun a => hS.pair_integrableU a w) (hS.pair_continuousU w)
  have hphi : ∀ v w, phiStar s (emb v) (embY w) = phiStarV s v w := fun v w => rfl
  have hval : ∀ v ∈ XaPerp s, ∀ w : Y,
      ((embY w s.ubar : ℝ) : EReal) - phiStar s (emb v) (embY w) = dualObj s v w := by
    intro v hv w
    rw [hphi, lemma_16_VY s hS hdom v hv w]
    rfl
  have h1 : valD s ≤ valDs s := by
    unfold valD
    refine iSup₂_le fun v hv => iSup_le fun w => ?_
    rw [← hval v hv w]
    unfold valDs
    exact le_iSup₂_of_le (f := fun (p : X →L[ℝ] ℝ) (y : U →L[ℝ] ℝ) =>
      ((y s.ubar : ℝ) : EReal) - phiStar s p y) (emb v) (embY w) le_rfl
  have h2 : ∀ (p : X →L[ℝ] ℝ) (y : U →L[ℝ] ℝ), ∃ v ∈ XaPerp s, ∃ w : Y,
      ((y s.ubar : ℝ) : EReal) - phiStar s p y ≤ dualObj s v w := by
    intro p y
    by_cases hp : p ∈ XaCirc s
    · obtain ⟨v, hv, w, hle⟩ := theorem_25 s hS hEf hEt hA23 p hp y
      refine ⟨v, hv, w, ?_⟩
      rw [← hval v hv w, hphi]
      exact ereal_swap _ _ _ _ hle
    · refine ⟨0, zero_mem_perp s, 0, ?_⟩
      rw [phiStar_top s hdom p hp y, EReal.sub_top]
      exact bot_le
  have hle_valD : ∀ v ∈ XaPerp s, ∀ w : Y, dualObj s v w ≤ valD s := fun v hv w => by
    unfold valD
    exact le_iSup₂_of_le (f := fun (p : V) (_ : p ∈ XaPerp s) => ⨆ y : Y, dualObj s p y) v hv
      (le_iSup_of_le w le_rfl)
  have h3 : valDs s ≤ valD s := by
    unfold valDs
    refine iSup₂_le fun p y => ?_
    obtain ⟨v, hv, w, hle⟩ := h2 p y
    exact hle.trans (hle_valD v hv w)
  have heq : valDs s = valD s := le_antisymm h3 h1
  refine ⟨heq, ⟨?_, ?_⟩⟩
  · rintro ⟨p, y, hpy⟩
    obtain ⟨v, hv, w, hle⟩ := h2 p y
    refine ⟨v, hv, w, le_antisymm (hle_valD v hv w) ?_⟩
    rw [← heq, ← hpy]; exact hle
  · rintro ⟨v, hv, w, hvw⟩
    exact ⟨emb v, embY w, by rw [hval v hv w, hvw, heq]⟩

end CSDT26

open ConvStochDual.Existence in
theorem solution {Ω X U : Type*} [MeasurableSpace Ω]
  [AddCommGroup X] [Module ℝ X] [UniformSpace X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {T n m : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : Fin n → Fin (T + 1)}
  {𝔽 : Fin (T + 1) → MeasurableSpace Ω}
  {ιX : X →ₗ[ℝ] RV Ω P n} {ιU : U →ₗ[ℝ] RV Ω P m}
  {V : Submodule ℝ (RV Ω P n)} {Y : Submodule ℝ (RV Ω P m)}
    (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (hEf : EfProperLsc s) (hEt : CondExpClosed s)
    (hA23 : Assumption23_1 s ∧ Assumption23_2 s) :
    valDs s = valD s ∧
      ((∃ p : X →L[ℝ] ℝ, ∃ y : U →L[ℝ] ℝ,
          ((y s.ubar : ℝ) : EReal) - phiStar s p y = valDs s) ↔
        (∃ p : V, p ∈ XaPerp s ∧
          ∃ y : Y, dualObj s p y = valD s)) :=
  CSDT26.main26 s hS hEf hEt hA23
