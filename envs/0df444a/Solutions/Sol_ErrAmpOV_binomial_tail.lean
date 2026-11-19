-- Prove2me | solution 1 for ErrAmpOV.binomial_tail
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:59:53.566535+00:00
-- url     : https://prove2.me/submissions/7307d818-c623-4cef-850f-0a90ed75c34b

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℓ : ℕ) (E : Fin ℓ → Set Ω) (hE : ∀ i, MeasurableSet (E i)) (hind : iIndepSet E μ)
    (p : ℝ) (hle : ∀ i, μ.real (E i) ≤ p) :
    μ.real {ω | (ℓ : ℝ) / 2 < (({i : Fin ℓ | ω ∈ E i}.ncard : ℕ) : ℝ)} ≤
      (2 * Real.exp 1 * p) ^ ((ℓ : ℝ) / 2) := by
  classical
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0
    simp
  have hp0 : 0 ≤ p := le_trans measureReal_nonneg (hle ⟨0, hpos⟩)
  have he2 : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  by_cases hbig : 1 ≤ 2 * Real.exp 1 * p
  · exact le_trans measureReal_le_one (Real.one_le_rpow hbig (by positivity))
  push_neg at hbig
  have hp1 : p ≤ 1 := by nlinarith
  set m : ℕ := ℓ / 2 + 1 with hm
  -- covering by m-subsets
  have hsub : {ω | (ℓ : ℝ) / 2 < (({i : Fin ℓ | ω ∈ E i}.ncard : ℕ) : ℝ)} ⊆
      ⋃ S ∈ (Finset.univ : Finset (Fin ℓ)).powersetCard m, ⋂ i ∈ S, E i := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    set T : Finset (Fin ℓ) := Finset.univ.filter (fun i => ω ∈ E i) with hT
    have hcard : ({i : Fin ℓ | ω ∈ E i}.ncard) = T.card := by
      rw [← Set.ncard_coe_finset]; congr 1; ext i; simp [hT]
    rw [hcard] at hω
    have hmT : m ≤ T.card := by
      have : ((ℓ / 2 : ℕ) : ℝ) ≤ (ℓ : ℝ) / 2 := by
        rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self ℓ 2
      have : (ℓ / 2 : ℕ) < T.card := by exact_mod_cast (lt_of_le_of_lt this hω)
      omega
    obtain ⟨S, hST, hS⟩ := Finset.exists_subset_card_eq hmT
    simp only [Set.mem_iUnion, Set.mem_iInter]
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, fun i hi => ?_⟩
    have := hST hi
    simpa [hT] using this
  have hmeas_inter : ∀ S ∈ (Finset.univ : Finset (Fin ℓ)).powersetCard m,
      μ.real (⋂ i ∈ S, E i) ≤ p ^ m := by
    intro S hS
    have hcS := (Finset.mem_powersetCard.mp hS).2
    rw [measureReal_def, hind.meas_biInter S, ENNReal.toReal_prod, ← hcS]
    calc ∏ i ∈ S, (μ (E i)).toReal ≤ ∏ _i ∈ S, p :=
          Finset.prod_le_prod (fun i _ => ENNReal.toReal_nonneg) (fun i _ => hle i)
      _ = p ^ S.card := Finset.prod_const p
  calc μ.real {ω | (ℓ : ℝ) / 2 < (({i : Fin ℓ | ω ∈ E i}.ncard : ℕ) : ℝ)}
      ≤ μ.real (⋃ S ∈ (Finset.univ : Finset (Fin ℓ)).powersetCard m, ⋂ i ∈ S, E i) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin ℓ)).powersetCard m, μ.real (⋂ i ∈ S, E i) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin ℓ)).powersetCard m, p ^ m :=
        Finset.sum_le_sum hmeas_inter
    _ = (ℓ.choose m : ℝ) * p ^ m := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ 2 ^ ℓ * p ^ ((ℓ : ℝ) / 2) := by
        apply mul_le_mul
        · exact_mod_cast Nat.choose_le_two_pow ℓ m
        · rw [← Real.rpow_natCast]
          rcases hp0.eq_or_lt with hz | hz
          · subst hz
            rw [Real.zero_rpow (by positivity), Real.zero_rpow (by positivity)]
          · apply Real.rpow_le_rpow_of_exponent_ge hz hp1
            have : (ℓ : ℝ) / 2 ≤ ((ℓ / 2 : ℕ) : ℝ) + 1 := by
              rw [div_le_iff₀ (by norm_num)]
              have := Nat.lt_div_mul_add (a := ℓ) (b := 2) (by norm_num)
              have h2 : (ℓ : ℝ) < ((ℓ / 2 : ℕ) : ℝ) * 2 + 2 := by exact_mod_cast this
              linarith
            simpa [hm] using this
        · positivity
        · positivity
    _ = (4 * p) ^ ((ℓ : ℝ) / 2) := by
        rw [Real.mul_rpow (by norm_num) hp0]
        congr 1
        rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        rw [show (2:ℝ) * ((ℓ:ℝ) / 2) = (ℓ : ℝ) by ring, Real.rpow_natCast]
    _ ≤ (2 * Real.exp 1 * p) ^ ((ℓ : ℝ) / 2) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        nlinarith
