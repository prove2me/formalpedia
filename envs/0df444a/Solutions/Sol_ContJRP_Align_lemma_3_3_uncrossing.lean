-- Prove2me | solution 1 for ContJRP.Align.lemma_3_3_uncrossing
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:20:54.971549+00:00
-- url     : https://prove2.me/submissions/a0502ba7-65cd-4fdb-a8b0-521354c51750

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy
import Theorems.Thm_ContJRP_Align_observation_2_3_first_segment_active
import Theorems.Thm_ContJRP_Align_corollary_2_6_scaling
import Theorems.Thm_ContJRP_Align_claim_3_4_uncrossing_term
import Theorems.Thm_ContJRP_Align_claim_3_5_component_sum

open ContJRP.Align
open Classical

theorem jrp33_mem_inf {ι : Type*} (N : Finset ι) (hN : N.Nonempty) (S : ι → Finset ℝ) (x : ℝ) :
    x ∈ N.inf' hN S ↔ ∀ i ∈ N, x ∈ S i := by
  rw [← Finset.singleton_subset_iff, ← Finset.le_iff_subset, Finset.le_inf'_iff]
  simp

/-- Inclusion–exclusion in terms of `interMultiples`. -/
theorem jrp33_ie (s : Finset ℕ) (R : ℕ → ℝ) (Δ : ℝ) :
    ((numOrders s R Δ : ℕ) : ℤ) = ∑ B ∈ s.powerset.filter (fun B => B.Nonempty),
      (-1 : ℤ) ^ (B.card + 1) * ((interMultiples B R Δ).card : ℤ) := by
  have hie := Finset.inclusion_exclusion_card_biUnion s (fun ℓ => multiplesUpTo (R ℓ) Δ)
  unfold numOrders
  rw [hie, ← Finset.sum_coe_sort (s.powerset.filter (fun B => B.Nonempty))]
  apply Finset.sum_congr rfl
  intro t _
  have ht := Finset.mem_filter.1 t.2
  congr 3
  ext x
  rw [jrp33_mem_inf]
  unfold interMultiples
  rw [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · intro h
    obtain ⟨ℓ, hℓ⟩ := ht.2
    exact ⟨⟨ℓ, hℓ, h ℓ hℓ⟩, h⟩
  · intro h; exact h.2

section comps
variable {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar : ℕ → ℝ)

theorem jrp33_comp_sub {C : Finset ℕ} (hC : C ∈ components ε Tt Tstar Rstar) :
    C ⊆ active ε Tt Tstar := by
  unfold components at hC
  obtain ⟨ℓ0, -, rfl⟩ := Finset.mem_image.mp hC
  exact Finset.filter_subset _ _

theorem jrp33_comp_eq {C : Finset ℕ} (hC : C ∈ components ε Tt Tstar Rstar) {ℓ : ℕ}
    (hℓ : ℓ ∈ C) : C = (active ε Tt Tstar).filter
      (fun ℓ' => (alignGraph ε Tt Tstar Rstar).Reachable ℓ ℓ') := by
  unfold components at hC
  obtain ⟨ℓ0, -, rfl⟩ := Finset.mem_image.mp hC
  rw [Finset.mem_filter] at hℓ
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hr⟩; exact ⟨hx, hℓ.2.symm.trans hr⟩
  · rintro ⟨hx, hr⟩; exact ⟨hx, hℓ.2.trans hr⟩

theorem jrp33_comp_reach {C : Finset ℕ} (hC : C ∈ components ε Tt Tstar Rstar) {ℓ₁ ℓ₂ : ℕ}
    (h1 : ℓ₁ ∈ C) (h2 : ℓ₂ ∈ C) : (alignGraph ε Tt Tstar Rstar).Reachable ℓ₁ ℓ₂ := by
  have := jrp33_comp_eq ε Tt Tstar Rstar hC h1
  rw [this, Finset.mem_filter] at h2
  exact h2.2

theorem jrp33_comp_unique {C C' : Finset ℕ} (hC : C ∈ components ε Tt Tstar Rstar)
    (hC' : C' ∈ components ε Tt Tstar Rstar) {ℓ : ℕ} (h : ℓ ∈ C) (h' : ℓ ∈ C') : C = C' := by
  rw [jrp33_comp_eq ε Tt Tstar Rstar hC h, jrp33_comp_eq ε Tt Tstar Rstar hC' h']

theorem jrp33_comp_of_mem {ℓ : ℕ} (hℓ : ℓ ∈ active ε Tt Tstar) :
    ∃ C ∈ components ε Tt Tstar Rstar, ℓ ∈ C := by
  refine ⟨_, Finset.mem_image_of_mem _ hℓ, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨hℓ, SimpleGraph.Reachable.refl _⟩

theorem jrp33_comp_card : (components ε Tt Tstar Rstar).card ≤ (active ε Tt Tstar).card := by
  unfold components; exact Finset.card_image_le

end comps


set_option maxHeartbeats 1000000 in
theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar)
    (R : ℕ → ℝ) (hfeas : IsLPFeasible ε Tt Tstar Rstar R) :
    ∀ Δ : ℝ, 0 ≤ Δ → ((termI ε Tt Tstar Rstar R Δ : ℤ) : ℝ) ≤
      (1 + 4 * ε) * (numOrders (active ε Tt Tstar) Rstar Δ : ℝ) +
        4 * ((active ε Tt Tstar).card : ℝ) ^ 2 * 2 ^ (active ε Tt Tstar).card := by
  intro Δ hΔ
  set Aa := active ε Tt Tstar with hAa
  set a := Aa.card with ha
  set CC := components ε Tt Tstar Rstar with hCC
  set Nst := (numOrders Aa Rstar Δ : ℝ) with hNst
  have h0 : 0 ∈ Aa := observation_2_3_first_segment_active ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2
  have ha1 : 1 ≤ a := Finset.card_pos.mpr ⟨0, h0⟩
  set f : Finset ℕ → ℝ := fun A => (-1 : ℝ) ^ (A.card + 1) * ((interMultiples A R Δ).card : ℝ)
    with hf
  set Q : Finset ℕ → Finset (Finset ℕ) := fun C => C.powerset.filter (fun A => A.Nonempty)
    with hQ
  -- uncrossing sets are partitioned by components
  have hU : Aa.powerset.filter (fun A => IsUncrossing ε Tt Tstar Rstar A) = CC.biUnion Q := by
    ext A
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion]
    constructor
    · rintro ⟨hsub, hne, hreach⟩
      obtain ⟨ℓ, hℓ⟩ := hne
      obtain ⟨C, hC, hℓC⟩ := jrp33_comp_of_mem ε Tt Tstar Rstar (hsub hℓ)
      refine ⟨C, hC, ?_⟩
      rw [hQ, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun x hx => ?_, ⟨ℓ, hℓ⟩⟩
      rw [jrp33_comp_eq ε Tt Tstar Rstar hC hℓC, Finset.mem_filter]
      exact ⟨hsub hx, hreach ℓ hℓ x hx⟩
    · rintro ⟨C, hC, hA⟩
      rw [hQ, Finset.mem_filter, Finset.mem_powerset] at hA
      exact ⟨hA.1.trans (jrp33_comp_sub ε Tt Tstar Rstar hC), hA.2,
        fun x hx y hy => jrp33_comp_reach ε Tt Tstar Rstar hC (hA.1 hx) (hA.1 hy)⟩
  have hdisj : (CC : Set (Finset ℕ)).PairwiseDisjoint Q := by
    intro C hC C' hC' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro A hA hA'
    rw [hQ, Finset.mem_filter, Finset.mem_powerset] at hA hA'
    obtain ⟨ℓ, hℓ⟩ := hA.2
    exact hne (jrp33_comp_unique ε Tt Tstar Rstar hC hC' (hA.1 hℓ) (hA'.1 hℓ))
  have hI : ((termI ε Tt Tstar Rstar R Δ : ℤ) : ℝ) = ∑ C ∈ CC, ∑ A ∈ Q C, f A := by
    unfold termI
    rw [hU, ← Finset.sum_biUnion hdisj]
    push_cast
    rfl
  -- the per-component bound
  have hcomp : ∀ C ∈ CC, ∑ A ∈ Q C, f A ≤
      (1 + 2 * ε) * (numOrders C Rstar Δ : ℝ) + 2 * 2 ^ a := by
    intro C hC
    obtain ⟨γ, hγ1, hγ2, hγ⟩ :=
      corollary_2_6_scaling ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2 Rstar hR R hfeas C hC
    have hγpos : 0 < γ := by linarith
    have hterm : ∀ A ∈ Q C, f A ≤
        (-1 : ℝ) ^ (A.card + 1) * ((interMultiples A Rstar Δ).card : ℝ) / γ + 2 := by
      intro A hA
      rw [hQ, Finset.mem_filter, Finset.mem_powerset] at hA
      have h := claim_3_4_uncrossing_term ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2 Rstar hR R hfeas
        C hC γ hγ1 hγ2 hγ A hA.1 hA.2 Δ hΔ
      rw [abs_le] at h
      simp only [hf]
      rcases neg_one_pow_eq_or ℝ (A.card + 1) with e | e <;> rw [e]
      · rw [one_mul, one_mul]; linarith [h.2]
      · rw [neg_one_mul, neg_one_mul, neg_div]; linarith [h.1]
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div] at hsum
    have hie := congrArg (Int.cast (R := ℝ)) (jrp33_ie C Rstar Δ)
    push_cast at hie
    rw [← hie] at hsum
    have hNC : (0 : ℝ) ≤ (numOrders C Rstar Δ : ℝ) := Nat.cast_nonneg _
    have hinv : (numOrders C Rstar Δ : ℝ) / γ ≤ (1 + 2 * ε) * (numOrders C Rstar Δ : ℝ) := by
      rw [div_le_iff₀ hγpos]
      have : 1 ≤ (1 + 2 * ε) * γ := by nlinarith
      nlinarith
    have hQc : ((Q C).card : ℝ) ≤ 2 ^ a := by
      have h1 : (Q C).card ≤ C.powerset.card := Finset.card_filter_le _ _
      rw [Finset.card_powerset] at h1
      have h2 : 2 ^ C.card ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num)
        (Finset.card_le_card (jrp33_comp_sub ε Tt Tstar Rstar hC))
      exact_mod_cast le_trans h1 h2
    linarith
  have hsumC := Finset.sum_le_sum hcomp
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsumC
  have h35 := claim_3_5_component_sum ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2 Rstar hR Δ hΔ
  have hIII : (termIII ε Tt Tstar Rstar Δ : ℝ) = ∑ C ∈ CC, (numOrders C Rstar Δ : ℝ) := by
    unfold termIII; push_cast; rfl
  rw [← hIII] at hsumC
  rw [hI]
  have hCCc : (CC.card : ℝ) ≤ a := by exact_mod_cast jrp33_comp_card ε Tt Tstar Rstar
  have hpa : (0 : ℝ) < 2 ^ a := by positivity
  have ha1' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hNn : (0 : ℝ) ≤ Nst := Nat.cast_nonneg _
  have hIIIn : (0 : ℝ) ≤ (termIII ε Tt Tstar Rstar Δ : ℝ) := Nat.cast_nonneg _
  have e1 : (1 + 2 * ε) * (termIII ε Tt Tstar Rstar Δ : ℝ) ≤
      (1 + 2 * ε) * ((1 + ε) * Nst + (a : ℝ) ^ 2 * 2 ^ a) :=
    mul_le_mul_of_nonneg_left h35 (by linarith)
  have e2 : (1 + 2 * ε) * (1 + ε) * Nst ≤ (1 + 4 * ε) * Nst :=
    mul_le_mul_of_nonneg_right (by nlinarith) hNn
  have e3 : (1 + 2 * ε) * ((a : ℝ) ^ 2 * 2 ^ a) ≤ 2 * ((a : ℝ) ^ 2 * 2 ^ a) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e4 : (CC.card : ℝ) * (2 * 2 ^ a) ≤ 2 * ((a : ℝ) ^ 2 * 2 ^ a) := by
    have : (CC.card : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith
    nlinarith
  nlinarith
