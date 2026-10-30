-- Prove2me | solution 1 for BudgetMgmt.Profit.expend_sym
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:10:02.762574+00:00
-- url     : https://prove2.me/submissions/4b24e874-f3b6-435b-aca2-046e0f33dfbd

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

open BudgetMgmt.Profit MeasureTheory

/-- invariance of the law under permuting coordinates -/
theorem solution_aux_perm {n : ℕ} (P : SymInstance n) (σ : Equiv.Perm (Fin n))
    (g : (Fin n → ℝ) → ℝ) : ∫ x, g (x ∘ σ) ∂P.law = ∫ x, g x ∂P.law := by
  let φ := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have hφ : MeasurePreserving φ volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have hφx : ∀ y : Fin n → ℝ, φ y = y ∘ σ := by
    intro y; funext b
    simp [φ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  have hmeas : Measurable (fun x => ENNReal.ofReal (P.f x)) :=
    ENNReal.measurable_ofReal.comp P.f_measurable
  have hlt : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), ENNReal.ofReal (P.f x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold SymInstance.law
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hlt,
    integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  have h1 : ∀ x : Fin n → ℝ, (ENNReal.ofReal (P.f x)).toReal • g (x ∘ σ) =
      (fun y => (ENNReal.ofReal (P.f y)).toReal • g y) (φ x) := by
    intro x
    simp only [hφx]
    rw [P.f_exch]
  simp_rw [h1]
  exact hφ.integral_comp' (f := φ) (fun y => (ENNReal.ofReal (P.f y)).toReal • g y)

theorem solution_aux_noties {n : ℕ} (P : SymInstance n) :
    ∀ᵐ x ∂P.law, Function.Injective x := by
  have hac : P.law ≪ volume := withDensity_absolutelyContinuous _ _
  apply hac.ae_le
  have : ∀ j k : Fin n, j ≠ k → ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), x j ≠ x k := by
    intro j k hjk
    let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k
    have hne : LinearMap.ker L ≠ ⊤ := by
      intro h
      have : Pi.single j (1 : ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
      simp [L, LinearMap.mem_ker, Pi.single_apply, hjk.symm] at this
    have h0 := Measure.addHaar_submodule volume (LinearMap.ker L) hne
    rw [ae_iff]
    refine measure_mono_null ?_ h0
    intro x hx
    simp only [Set.mem_setOf_eq, not_not] at hx
    simp [L, LinearMap.mem_ker, hx]
  have hall : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), ∀ j k : Fin n, j ≠ k → x j ≠ x k := by
    refine ae_all_iff.2 fun j => ae_all_iff.2 fun k => ?_
    by_cases hjk : j = k
    · exact Filter.Eventually.of_forall fun _ h => absurd hjk h
    · filter_upwards [this j k hjk] with x hx _ using hx
  filter_upwards [hall] with x hx
  intro j k hjk
  by_contra h
  exact hx j k h hjk

theorem solution_aux_fold_eq {n : ℕ} {s t : Finset (Fin n)} {f g : Fin n → ℝ}
    (h : ∀ y, (∀ j ∈ s, f j ≤ y) ↔ (∀ j ∈ t, g j ≤ y)) :
    s.fold max 0 f = t.fold max 0 g := by
  have key : ∀ y, s.fold max 0 f ≤ y ↔ t.fold max 0 g ≤ y := by
    intro y
    rw [Finset.fold_max_le, Finset.fold_max_le, h y]
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

theorem solution_aux_compQual {n : ℕ} (a : ℝ) (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : Fin n) : compQual (sym a) (x ∘ σ) j = compQual (sym a) x (σ j) := by
  unfold compQual
  apply solution_aux_fold_eq
  intro y
  constructor
  · intro h k' hk'
    rw [Finset.mem_filter] at hk'
    have := h (σ.symm k') (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      fun e => hk'.2.1 (by rw [← e]; simp), by simpa [sym] using hk'.2.2⟩)
    simpa using this
  · intro h k hk
    rw [Finset.mem_filter] at hk
    exact h (σ k) (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun e => hk.2.1 (σ.injective e),
      hk.2.2⟩)

theorem solution_aux_compShaded {n : ℕ} (a : ℝ) (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : Fin n) : compShaded (sym a) (x ∘ σ) j = compShaded (sym a) x (σ j) := by
  unfold compShaded
  apply solution_aux_fold_eq
  intro y
  constructor
  · intro h k' hk'
    rw [Finset.mem_filter] at hk'
    have := h (σ.symm k') (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      fun e => hk'.2 (by rw [← e]; simp)⟩)
    simpa [sym] using this
  · intro h k hk
    rw [Finset.mem_filter] at hk
    exact h (σ k) (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun e => hk.2 (σ.injective e)⟩)

theorem solution_aux_wins {n : ℕ} (c : ℝ) (m : Mech) (a : ℝ) (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    wins c m (sym a) (x ∘ σ) j ↔ wins c m (sym a) x (σ j) := by
  cases m
  · show max (compQual (sym a) (x ∘ σ) j) a ≤ x (σ j) ↔ max (compQual (sym a) x (σ j)) a ≤ x (σ j)
    rw [solution_aux_compQual]
  · show max (compQual (sym a) (x ∘ σ) j) a ≤ x (σ j) ↔ max (compQual (sym a) x (σ j)) a ≤ x (σ j)
    rw [solution_aux_compQual]
  · show max (compShaded (sym a) (x ∘ σ) j) c ≤ x (σ j) / (1 + a) ↔
      max (compShaded (sym a) x (σ j)) c ≤ x (σ j) / (1 + a)
    rw [solution_aux_compShaded]

theorem solution_aux_price {n : ℕ} (c : ℝ) (m : Mech) (a : ℝ) (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    price c m (sym a) (x ∘ σ) j = price c m (sym a) x (σ j) := by
  cases m
  · show max (compQual (sym a) (x ∘ σ) j) c = max (compQual (sym a) x (σ j)) c
    rw [solution_aux_compQual]
  · show max (compQual (sym a) (x ∘ σ) j) a = max (compQual (sym a) x (σ j)) a
    rw [solution_aux_compQual]
  · show max (compShaded (sym a) (x ∘ σ) j) c = max (compShaded (sym a) x (σ j)) c
    rw [solution_aux_compShaded]

/-- with distinct values, two different buyers cannot both win -/
theorem solution_aux_unique_winner {n : ℕ} (c : ℝ) (hc : 0 < c) (m : Mech) (a : ℝ)
    (x : Fin n → ℝ) (hx : Function.Injective x) (i j : Fin n)
    (hi : wins c m (sym a) x i) (hj : wins c m (sym a) x j) : i = j := by
  by_contra hij
  have hQ : ∀ i j : Fin n, i ≠ j → a ≤ x j → x j ≤ compQual (sym a) x i := by
    intro i j hij hj
    unfold compQual
    rw [Finset.le_fold_max]
    exact Or.inr ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ne.symm hij, hj⟩, le_rfl⟩
  have hS : ∀ i j : Fin n, i ≠ j → x j / (1 + a) ≤ compShaded (sym a) x i := by
    intro i j hij
    unfold compShaded
    rw [Finset.le_fold_max]
    exact Or.inr ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ne.symm hij⟩, by simp [sym]⟩
  cases m
  · have hi' : max (compQual (sym a) x i) a ≤ x i := hi
    have hj' : max (compQual (sym a) x j) a ≤ x j := hj
    rw [max_le_iff] at hi' hj'
    have h1 := hQ i j hij hj'.2
    have h2 := hQ j i (Ne.symm hij) hi'.2
    exact hij (hx (le_antisymm (h2.trans hj'.1) (h1.trans hi'.1)))
  · have hi' : max (compQual (sym a) x i) a ≤ x i := hi
    have hj' : max (compQual (sym a) x j) a ≤ x j := hj
    rw [max_le_iff] at hi' hj'
    have h1 := hQ i j hij hj'.2
    have h2 := hQ j i (Ne.symm hij) hi'.2
    exact hij (hx (le_antisymm (h2.trans hj'.1) (h1.trans hi'.1)))
  · have hi' : max (compShaded (sym a) x i) c ≤ x i / (1 + sym a i) := hi
    have hj' : max (compShaded (sym a) x j) c ≤ x j / (1 + sym a j) := hj
    simp only [sym, max_le_iff] at hi' hj'
    have h1 := hS i j hij
    have h2 := hS j i (Ne.symm hij)
    have he : x i / (1 + a) = x j / (1 + a) :=
      le_antisymm (h2.trans hj'.1) (h1.trans hi'.1)
    by_cases ha : 1 + a = 0
    · rw [ha, div_zero] at hi'
      linarith [hi'.2]
    · exact hij (hx (by field_simp at he; exact he))

open Classical in
theorem solution_aux_alloc_inj {n : ℕ} (c : ℝ) (hc : 0 < c) (m : Mech) (a : ℝ)
    (x : Fin n → ℝ) (hx : Function.Injective x) (i : Fin n) :
    alloc c m (sym a) x i = if wins c m (sym a) x i then 1 else 0 := by
  unfold alloc
  by_cases hw : wins c m (sym a) x i
  · rw [if_pos hw, if_pos ⟨hw, fun j hj hwj =>
      (ne_of_lt hj) (solution_aux_unique_winner c hc m a x hx j i hwj hw)⟩]
  · rw [if_neg hw, if_neg (fun h => hw h.1)]

open Classical in
theorem solution_aux_payment_perm {n : ℕ} (c : ℝ) (hc : 0 < c) (m : Mech) (a : ℝ)
    (x : Fin n → ℝ) (hx : Function.Injective x) (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    payment c m (sym a) (x ∘ σ) j = payment c m (sym a) x (σ j) := by
  unfold payment
  rw [solution_aux_alloc_inj c hc m a (x ∘ σ) (hx.comp σ.injective) j,
    solution_aux_alloc_inj c hc m a x hx (σ j), solution_aux_price]
  congr 1
  exact if_congr (solution_aux_wins c m a x σ j) rfl rfl

theorem solution {n : ℕ} [NeZero n] (P : SymInstance n) (m : Mech) (s₁ : ℝ) (i : Fin n) :
    expend P m (sym s₁) i = G1 P m s₁ := by
  unfold G1 expend
  congr 1
  let σ : Equiv.Perm (Fin n) := Equiv.swap 0 i
  have hσ : σ 0 = i := by simp [σ]
  have h1 : (∫ x, payment P.c m (sym s₁) x i ∂P.law) =
      ∫ x, payment P.c m (sym s₁) (x ∘ σ) 0 ∂P.law := by
    apply integral_congr_ae
    filter_upwards [solution_aux_noties P] with x hx
    rw [solution_aux_payment_perm P.c P.c_pos m s₁ x hx σ 0, hσ]
  rw [h1, solution_aux_perm P σ (fun y => payment P.c m (sym s₁) y 0)]
