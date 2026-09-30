-- Prove2me | solution 1 for DurrettProbability.hewitt_savage_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T00:57:48.333986+00:00
-- url     : https://prove2.me/submissions/014ef541-e76a-4c55-9064-234385ebbf18

import Mathlib
import Definitions.Def_DurrettProbability_Series

open MeasureTheory ProbabilityTheory Filter
open scoped symmDiff

namespace DurrettProbability

/-- the involution swapping `i ↔ i + N` for `i < N` -/
def swapBlock (N : ℕ) (i : ℕ) : ℕ := if i < N then i + N else if i < 2 * N then i - N else i

lemma swapBlock_invol (N : ℕ) : Function.Involutive (swapBlock N) := by
  intro i
  unfold swapBlock
  split_ifs <;> omega

theorem hs_main {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] (A : Set (ℕ → S)) (hA : IsPermutable A) :
    (Measure.infinitePi (fun _ : ℕ => μ)) A = 0
      ∨ (Measure.infinitePi (fun _ : ℕ => μ)) A = 1 := by
  set ν := Measure.infinitePi (fun _ : ℕ => μ) with hν
  obtain ⟨hAm, hAp⟩ := hA
  -- key estimate: |p - p^2| < 4ε for every ε > 0
  have key : ∀ ε : ℝ, 0 < ε → |ν.real A - ν.real A ^ 2| ≤ 4 * ε := by
    intro ε hε
    -- approximate A by a cylinder
    have hgen : (MeasurableSpace.pi : MeasurableSpace (ℕ → S)) =
        MeasurableSpace.generateFrom (measurableCylinders fun _ : ℕ => S) :=
      generateFrom_measurableCylinders.symm
    obtain ⟨C, hC, hCA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := ν)
      isSetRing_measurableCylinders
      ⟨{Set.univ}, Set.countable_singleton _, by
        rw [Set.singleton_subset_iff, mem_measurableCylinders]
        exact ⟨∅, Set.univ, MeasurableSet.univ, by simp [cylinder]⟩, by simp⟩
      hgen hAm (ENNReal.ofReal_pos.mpr hε)
    obtain ⟨s, SS, hSS, rfl⟩ := (mem_measurableCylinders C).mp hC
    have hCm := MeasurableSet.of_mem_measurableCylinders hC
    -- the block swap
    set N := s.sup id + 1 with hN
    have hsN : ∀ i ∈ s, i < N := fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
    set σ : Equiv.Perm ℕ := (swapBlock_invol N).toPerm _ with hσ
    have hσapp : ∀ i, σ i = swapBlock N i := fun i => rfl
    have hfin : FinitelySupported σ := by
      unfold FinitelySupported
      rw [Filter.eventually_cofinite]
      refine (Set.finite_lt_nat (2 * N)).subset fun i hi => ?_
      simp only [Set.mem_setOf_eq, hσapp, swapBlock] at hi ⊢
      by_contra h
      apply hi
      split_ifs <;> omega
    set T : (ℕ → S) → (ℕ → S) := fun ω => ω ∘ σ with hT
    have hTm : Measurable T := by
      rw [hT]; exact measurable_pi_lambda _ fun i => measurable_pi_apply (σ i)
    have hTpres : MeasurePreserving T ν ν := by
      refine ⟨hTm, ?_⟩
      have h := Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => μ) σ.symm
      have e : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℕ => S) σ.symm) = T := by
        funext ω i
        simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, hT]
      rw [← e]
      exact h
    have hTA : T ⁻¹' A = A := hAp σ hfin
    -- independence of the cylinder and its shift
    set s' : Finset ℕ := s.map ⟨σ, σ.injective⟩ with hs'
    have hdisj : Disjoint s s' := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      rw [hs', Finset.mem_map] at hi'
      obtain ⟨j, hj, hji⟩ := hi'
      have h1 := hsN i hi
      have h2 := hsN j hj
      simp only [Function.Embedding.coeFn_mk, hσapp, swapBlock] at hji
      split_ifs at hji <;> omega
    have hind : iIndepFun (fun (i : ℕ) (ω : ℕ → S) => ω i) ν :=
      iIndepFun_infinitePi (X := fun _ (x : S) => x) (fun _ => measurable_id)
    have hpair := hind.indepFun_finset s s' hdisj (fun i => measurable_pi_apply i)
    set φ : (s' → S) → (s → S) := fun g i => g ⟨σ i, by
      rw [hs', Finset.mem_map]; exact ⟨i, i.2, rfl⟩⟩ with hφ
    have hφm : Measurable φ := measurable_pi_lambda _ fun i => measurable_pi_apply _
    have hpair2 := hpair.comp (measurable_id) hφm
    have hTC : T ⁻¹' cylinder s SS = (φ ∘ fun (ω : ℕ → S) (i : s') => ω i) ⁻¹' SS := by
      ext ω; simp only [cylinder, Set.mem_preimage, Function.comp_apply, hT, hφ]; rfl
    have hCC : cylinder s SS = (id ∘ fun (ω : ℕ → S) (i : s) => ω i) ⁻¹' SS := by
      ext ω; simp only [cylinder, Set.mem_preimage, Function.comp_apply, id]; rfl
    have hprod : ν (cylinder s SS ∩ T ⁻¹' cylinder s SS) =
        ν (cylinder s SS) * ν (T ⁻¹' cylinder s SS) := by
      rw [hTC]
      conv_lhs => rw [hCC]
      rw [hpair2.measure_inter_preimage_eq_mul SS SS hSS hSS, ← hCC]
    have hTCmeas : ν (T ⁻¹' cylinder s SS) = ν (cylinder s SS) := hTpres.measure_preimage hCm.nullMeasurableSet
    -- real-valued estimates
    set c := ν.real (cylinder s SS) with hc
    set p := ν.real A with hp
    have hd : ν.real (cylinder s SS ∆ A) < ε := by
      have := hCA
      rw [Measure.real]
      exact (ENNReal.toReal_lt_of_lt_ofReal this)
    have hdiff : |c - p| ≤ ν.real (cylinder s SS ∆ A) := by
      have := abs_measureReal_sub_le_measureReal_symmDiff (μ := ν) hCm.nullMeasurableSet hAm.nullMeasurableSet
      exact this
    have hinter : ν.real (cylinder s SS ∩ T ⁻¹' cylinder s SS) = c ^ 2 := by
      rw [Measure.real, hprod, hTCmeas, ENNReal.toReal_mul, ← Measure.real, ← hc, sq]
    have hAA : ν.real (A ∩ T ⁻¹' A) = p := by rw [hTA, Set.inter_self]
    have hsd : ν.real ((cylinder s SS ∩ T ⁻¹' cylinder s SS) ∆ (A ∩ T ⁻¹' A)) ≤
        2 * ν.real (cylinder s SS ∆ A) := by
      have hsub : (cylinder s SS ∩ T ⁻¹' cylinder s SS) ∆ (A ∩ T ⁻¹' A) ⊆
          (cylinder s SS ∆ A) ∪ (T ⁻¹' (cylinder s SS ∆ A)) := by
        intro ω hω
        simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_union] at hω ⊢
        tauto
      have h1 := measureReal_mono (μ := ν) hsub (measure_ne_top _ _)
      have h2 := measureReal_union_le (μ := ν) (cylinder s SS ∆ A) (T ⁻¹' (cylinder s SS ∆ A))
      have h3 : ν.real (T ⁻¹' (cylinder s SS ∆ A)) = ν.real (cylinder s SS ∆ A) := by
        rw [Measure.real, Measure.real,
          hTpres.measure_preimage (hCm.symmDiff hAm).nullMeasurableSet]
      linarith
    have hdiff2 : |c ^ 2 - p| ≤ 2 * ν.real (cylinder s SS ∆ A) := by
      rw [← hinter, ← hAA]
      exact (abs_measureReal_sub_le_measureReal_symmDiff (μ := ν)
        (hCm.inter (hTm hCm)).nullMeasurableSet (hAm.inter (hTm hAm)).nullMeasurableSet).trans hsd
    have hc01 : 0 ≤ c ∧ c ≤ 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
    have hp01 : 0 ≤ p ∧ p ≤ 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
    have hsq : |c ^ 2 - p ^ 2| ≤ 2 * |c - p| := by
      rw [show c ^ 2 - p ^ 2 = (c + p) * (c - p) by ring, abs_mul]
      have : |c + p| ≤ 2 := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have h1 := abs_sub_le (p) (c ^ 2) (p ^ 2)
    rw [abs_sub_comm p (c ^ 2)] at h1
    have e : |c ^ 2 - p ^ 2| = |c ^ 2 - p ^ 2| := rfl
    linarith [abs_nonneg (c - p)]
  -- conclude p = p^2
  have hpp : ν.real A = ν.real A ^ 2 := by
    by_contra hne
    have hpos : 0 < |ν.real A - ν.real A ^ 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have := key (|ν.real A - ν.real A ^ 2| / 8) (by positivity)
    linarith
  have h01 : ν.real A = 0 ∨ ν.real A = 1 := by
    have : ν.real A * (ν.real A - 1) = 0 := by linear_combination -hpp
    rcases mul_eq_zero.mp this with h | h
    · left; exact h
    · right; linarith
  rcases h01 with h | h
  · left
    rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h
  · right
    rw [Measure.real, ENNReal.toReal_eq_one_iff] at h
    exact h

end DurrettProbability

open DurrettProbability

theorem solution {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] (A : Set (ℕ → S)) (hA : IsPermutable A) :
    (Measure.infinitePi (fun _ : ℕ => μ)) A = 0
      ∨ (Measure.infinitePi (fun _ : ℕ => μ)) A = 1 := by
  exact hs_main μ A hA
