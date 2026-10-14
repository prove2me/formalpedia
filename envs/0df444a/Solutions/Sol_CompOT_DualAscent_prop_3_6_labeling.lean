-- Prove2me | solution 1 for CompOT.DualAscent.prop_3_6_labeling
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-13T21:29:18.731384+00:00
-- url     : https://prove2.me/submissions/b1670408-7db5-48be-b7af-ab2a173e702b

import Mathlib
import Definitions.Def_CompOT_DualAscent_Defs
import Theorems.Thm_LinearOptimization_farkas_lemma

section Lab1
open MeasureTheory

namespace CompOT.DualAscent.Lab

/-- ∫_{-M}^{M} 1[t ≤ c] dt = c + M for |c| ≤ M. -/
lemma integral_ind (M c : ℝ) (hc1 : -M ≤ c) (hc2 : c ≤ M) :
    ∫ t in (-M)..M, (if t ≤ c then (1:ℝ) else 0) = c + M := by
  have hM : -M ≤ M := le_trans hc1 hc2
  rw [intervalIntegral.integral_of_le hM]
  have : (fun t : ℝ => if t ≤ c then (1:ℝ) else 0) = (Set.Iic c).indicator (fun _ => (1:ℝ)) := by
    ext t; simp [Set.indicator]
  rw [this, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  simp only [integral_const, smul_eq_mul, mul_one]
  have hset : Set.Iic c ∩ Set.Ioc (-M) M = Set.Ioc (-M) c := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hc2⟩
  rw [hset]
  simp [Measure.real]
  linarith


lemma ind_integrable (M c : ℝ) :
    IntervalIntegrable (fun t : ℝ => if t ≤ c then (1:ℝ) else 0) volume (-M) M := by
  have hanti : Antitone (fun t : ℝ => if t ≤ c then (1:ℝ) else 0) := by
    intro s t hst
    by_cases h1 : t ≤ c
    · have : s ≤ c := hst.trans h1
      simp [h1, this]
    · by_cases h2 : s ≤ c <;> simp [h1, h2]
  exact hanti.intervalIntegrable

/-- Layer-cake: if `∑ a = ∑ b` and `⟨a,u⟩ > ⟨b,v⟩` then some superlevel set has
`a(S_t) > b(S'_t)`. -/
lemma exists_level {ι κ : Type*} [Fintype ι] [Fintype κ] (u : ι → ℝ) (v : κ → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) (hab : ∑ i, a i = ∑ j, b j)
    (h : ∑ j, b j * v j < ∑ i, a i * u i) :
    ∃ t : ℝ, ∑ j ∈ Finset.univ.filter (fun j => t ≤ v j), b j <
      ∑ i ∈ Finset.univ.filter (fun i => t ≤ u i), a i := by
  classical
  by_contra hcon
  push Not at hcon
  set M : ℝ := ∑ i, |u i| + ∑ j, |v j| with hMdef
  have hu : ∀ i, -M ≤ u i ∧ u i ≤ M := by
    intro i
    have h1 : |u i| ≤ ∑ i, |u i| := Finset.single_le_sum (f := fun i => |u i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ j, |v j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    constructor <;> cases abs_cases (u i) <;> linarith
  have hv : ∀ j, -M ≤ v j ∧ v j ≤ M := by
    intro j
    have h1 : |v j| ≤ ∑ j, |v j| := Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    constructor <;> cases abs_cases (v j) <;> linarith
  have hM : -M ≤ M := by
    have : 0 ≤ M := add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.sum_nonneg fun j _ => abs_nonneg _)
    linarith
  -- the integrand
  let F : ℝ → ℝ := fun t => (∑ i, a i * (if t ≤ u i then (1:ℝ) else 0)) -
      ∑ j, b j * (if t ≤ v j then (1:ℝ) else 0)
  have hF : ∀ t, F t ≤ 0 := by
    intro t
    have := hcon t
    simp only [F, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    linarith
  have hInt : ∫ t in (-M)..M, F t = (∑ i, a i * u i - ∑ j, b j * v j) := by
    have e1 : ∀ i ∈ (Finset.univ : Finset ι), IntervalIntegrable
        (fun t : ℝ => a i * (if t ≤ u i then (1:ℝ) else 0)) volume (-M) M :=
      fun i _ => (ind_integrable M (u i)).const_mul (a i)
    have e2 : ∀ j ∈ (Finset.univ : Finset κ), IntervalIntegrable
        (fun t : ℝ => b j * (if t ≤ v j then (1:ℝ) else 0)) volume (-M) M :=
      fun j _ => (ind_integrable M (v j)).const_mul (b j)
    simp only [F]
    have i1 : IntervalIntegrable (fun t : ℝ => ∑ i, a i * (if t ≤ u i then (1:ℝ) else 0)) volume (-M) M := by
      simpa [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ e1
    have i2 : IntervalIntegrable (fun t : ℝ => ∑ j, b j * (if t ≤ v j then (1:ℝ) else 0)) volume (-M) M := by
      simpa [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ e2
    rw [intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_finsetSum e1, intervalIntegral.integral_finsetSum e2]
    have c1 : ∀ i ∈ (Finset.univ : Finset ι), ∫ t in (-M)..M, a i * (if t ≤ u i then (1:ℝ) else 0)
        = a i * (u i + M) := by
      intro i _
      rw [intervalIntegral.integral_const_mul, integral_ind M (u i) (hu i).1 (hu i).2]
    have c2 : ∀ j ∈ (Finset.univ : Finset κ), ∫ t in (-M)..M, b j * (if t ≤ v j then (1:ℝ) else 0)
        = b j * (v j + M) := by
      intro j _
      rw [intervalIntegral.integral_const_mul, integral_ind M (v j) (hv j).1 (hv j).2]
    rw [Finset.sum_congr rfl c1, Finset.sum_congr rfl c2]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hab]
    ring
  have hle : 0 ≤ ∫ t in (-M)..M, -F t :=
    intervalIntegral.integral_nonneg hM (fun t _ => by linarith [hF t])
  rw [intervalIntegral.integral_neg, hInt] at hle
  linarith

end CompOT.DualAscent.Lab
end Lab1

section Lab2
open Matrix

namespace CompOT.DualAscent.Lab

/-- Farkas' lemma for arbitrary finite index types (alternative form). -/
lemma farkas_fintype {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι ℝ) (b : κ → ℝ) (h : ¬ ∃ x : ι → ℝ, 0 ≤ x ∧ A.mulVec x = b) :
    ∃ p : κ → ℝ, 0 ≤ Aᵀ.mulVec p ∧ p ⬝ᵥ b < 0 := by
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let eκ : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let A' : Matrix (Fin (Fintype.card κ)) (Fin (Fintype.card ι)) ℝ := A.submatrix eκ.symm eι.symm
  let b' : Fin (Fintype.card κ) → ℝ := b ∘ eκ.symm
  have hx : ¬ ∃ x : Fin (Fintype.card ι) → ℝ, 0 ≤ x ∧ A'.mulVec x = b' := by
    rintro ⟨x, hx0, hx⟩
    apply h
    refine ⟨x ∘ eι, fun i => hx0 (eι i), ?_⟩
    ext r
    have := congrFun hx (eκ r)
    simp only [A', b', Function.comp, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
      Equiv.symm_apply_apply] at this
    simp only [Function.comp, Matrix.mulVec, dotProduct]
    rw [← this]
    exact Fintype.sum_equiv eι _ _ (fun i => by simp)
  rcases LinearOptimization.farkas_lemma A' b' with ⟨h1, _⟩ | ⟨h2, _⟩
  · exact absurd h1 hx
  · obtain ⟨p', hp1, hp2⟩ := h2
    refine ⟨p' ∘ eκ, fun k => ?_, ?_⟩
    · have := hp1 (eι k)
      simp only [A', Pi.zero_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Matrix.submatrix_apply, Equiv.symm_apply_apply] at this ⊢
      have e : ∑ i, A i k * (p' ∘ eκ) i = ∑ x, A (eκ.symm x) k * p' x :=
        Fintype.sum_equiv eκ _ _ (fun i => by simp)
      rw [e]; exact this
    · simp only [dotProduct, b', Function.comp] at hp2 ⊢
      have e : ∑ i, p' (eκ i) * b i = ∑ x, p' x * b (eκ.symm x) :=
        Fintype.sum_equiv eκ _ _ (fun i => by simp)
      rw [e]; exact hp2

end CompOT.DualAscent.Lab
end Lab2

section Lab3
open Matrix

namespace CompOT.DualAscent.Lab

theorem labeling_core {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (hab : ∑ i, a i = ∑ j, b j) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hno : ¬ ∃ P ∈ CompOT.Assignment.couplings a b, CompOT.Duality.Complementary C P f g) :
    ∃ (S : Finset (Fin n)) (S' : Finset (Fin m)),
      (∀ i ∈ S, ∀ j : Fin m, CompOT.DualAscent.Balanced C f g i j → j ∈ S') ∧
      0 < ∑ i ∈ S, a i - ∑ j ∈ S', b j := by
  classical
  let A : Matrix ((Fin n ⊕ Fin m) ⊕ (Fin n × Fin m)) (Fin n × Fin m) ℝ := Matrix.of fun r p =>
    match r with
    | Sum.inl (Sum.inl i) => if p.1 = i then 1 else 0
    | Sum.inl (Sum.inr j) => if p.2 = j then 1 else 0
    | Sum.inr q => if q = p ∧ C q.1 q.2 ≠ f q.1 + g q.2 then 1 else 0
  let B : (Fin n ⊕ Fin m) ⊕ (Fin n × Fin m) → ℝ := fun r =>
    match r with
    | Sum.inl (Sum.inl i) => a i
    | Sum.inl (Sum.inr j) => b j
    | Sum.inr _ => 0
  have hfar : ¬ ∃ x : Fin n × Fin m → ℝ, 0 ≤ x ∧ A.mulVec x = B := by
    rintro ⟨x, hx0, hx⟩
    apply hno
    refine ⟨fun i j => x (i, j), ⟨fun i j => hx0 (i, j), ?_, ?_⟩, ?_⟩
    · intro i
      have := congrFun hx (Sum.inl (Sum.inl i))
      simp only [A, B, Matrix.of_apply, Matrix.mulVec, dotProduct] at this
      rw [Fintype.sum_prod_type] at this
      simpa [ite_mul, Finset.sum_ite_eq] using this
    · intro j
      have := congrFun hx (Sum.inl (Sum.inr j))
      simp only [A, B, Matrix.of_apply, Matrix.mulVec, dotProduct] at this
      rw [Fintype.sum_prod_type_right] at this
      simpa [ite_mul, Finset.sum_ite_eq] using this
    · intro i j hpos
      by_contra hne
      have := congrFun hx (Sum.inr (i, j))
      simp only [A, B, Matrix.of_apply, Matrix.mulVec, dotProduct] at this
      rw [Finset.sum_eq_single (i, j)] at this
      · simp [hne] at this
        exact absurd this (ne_of_gt hpos)
      · intro p _ hp
        simp [Ne.symm hp]
      · simp
  obtain ⟨p, hp1, hp2⟩ := farkas_fintype A B hfar
  have hbal : ∀ i j, CompOT.DualAscent.Balanced C f g i j →
      0 ≤ p (Sum.inl (Sum.inl i)) + p (Sum.inl (Sum.inr j)) := by
    intro i j hij
    have hne : ¬ (C i j ≠ f i + g j) := not_not.mpr hij.symm
    have := hp1 (i, j)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, A, Matrix.of_apply,
      Matrix.transpose_apply, Pi.zero_apply] at this
    have h3 : ∑ q : Fin n × Fin m, (if q = (i, j) ∧ C q.1 q.2 ≠ f q.1 + g q.2 then (1:ℝ) else 0) *
        p (Sum.inr q) = 0 := by
      refine Finset.sum_eq_zero fun q _ => ?_
      by_cases h : q = (i, j)
      · subst h; simp [hne]
      · simp [h]
    rw [h3] at this
    simpa [ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this
  have hobj : ∑ i, p (Sum.inl (Sum.inl i)) * a i + ∑ j, p (Sum.inl (Sum.inr j)) * b j < 0 := by
    simpa [dotProduct, Fintype.sum_sum_type, B] using hp2
  have hsum : ∑ j, b j * p (Sum.inl (Sum.inr j)) <
      ∑ i, a i * (-p (Sum.inl (Sum.inl i))) := by
    have e : ∑ i, a i * (-p (Sum.inl (Sum.inl i))) = -∑ i, p (Sum.inl (Sum.inl i)) * a i := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    have e2 : ∑ j, b j * p (Sum.inl (Sum.inr j)) = ∑ j, p (Sum.inl (Sum.inr j)) * b j :=
      Finset.sum_congr rfl (fun j _ => by ring)
    rw [e, e2]; linarith
  obtain ⟨t, ht⟩ := exists_level (fun i => -p (Sum.inl (Sum.inl i)))
    (fun j => p (Sum.inl (Sum.inr j))) a b hab hsum
  refine ⟨Finset.univ.filter (fun i => t ≤ -p (Sum.inl (Sum.inl i))),
    Finset.univ.filter (fun j => t ≤ p (Sum.inl (Sum.inr j))), ?_, by linarith⟩
  intro i hi j hij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have := hbal i j hij
  linarith

end CompOT.DualAscent.Lab
end Lab3

theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (f : Fin n → ℝ) (g : Fin m → ℝ) (hfg : CompOT.Duality.dualFeasible C f g)
    (hno : ¬ ∃ P ∈ CompOT.Assignment.couplings a b, CompOT.Duality.Complementary C P f g) :
    ∃ (S : Finset (Fin n)) (S' : Finset (Fin m)),
      (∀ i ∈ S, ∀ j : Fin m, CompOT.DualAscent.Balanced C f g i j → j ∈ S') ∧
      0 < ∑ i ∈ S, a i - ∑ j ∈ S', b j :=
  CompOT.DualAscent.Lab.labeling_core C a b (by rw [ha.2, hb.2]) f g hno
