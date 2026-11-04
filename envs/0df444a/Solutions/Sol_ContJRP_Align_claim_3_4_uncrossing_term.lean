-- Prove2me | solution 1 for ContJRP.Align.claim_3_4_uncrossing_term
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:16:42.910182+00:00
-- url     : https://prove2.me/submissions/fe93a9c5-2422-444f-8586-059d7531464a

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

open ContJRP.Align
open Classical

/-- Membership in `M_{t,Δ}` for `t > 0`, `Δ ≥ 0`. -/
theorem jrp34_mem_mult (t Δ x : ℝ) (ht : 0 < t) (hΔ : 0 ≤ Δ) :
    x ∈ multiplesUpTo t Δ ↔ ∃ k : ℕ, x = k * t ∧ x ≤ Δ := by
  unfold multiplesUpTo
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k, rfl, ?_⟩
    have h1 : (k : ℝ) ≤ Δ / t :=
      le_trans (by exact_mod_cast (Nat.lt_succ_iff.mp hk)) (Nat.floor_le (div_nonneg hΔ ht.le))
    rwa [le_div_iff₀ ht] at h1
  · rintro ⟨k, rfl, hk⟩
    refine ⟨k, ?_, rfl⟩
    have : (k : ℝ) ≤ Δ / t := by rwa [le_div_iff₀ ht]
    have := Nat.le_floor this
    omega

/-- The common multiples have a least element when nonempty. -/
theorem jrp34_isLeast {ι : Type*} (N : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ N, 0 < T i)
    (hN : N.Nonempty) (hne : (commonMultiples N T).Nonempty) :
    ∃ M, IsLeast (commonMultiples N T) M := by
  obtain ⟨i0, hi0⟩ := hN
  have hex : ∃ k : ℕ, (k : ℝ) * T i0 ∈ commonMultiples N T := by
    obtain ⟨c, hc⟩ := hne
    obtain ⟨k, hk⟩ := hc.2 i0 hi0
    exact ⟨k, hk ▸ hc⟩
  refine ⟨(Nat.find hex : ℝ) * T i0, Nat.find_spec hex, ?_⟩
  intro c hc
  obtain ⟨k, hk⟩ := hc.2 i0 hi0
  have hkm : Nat.find hex ≤ k := Nat.find_min' hex (hk ▸ hc)
  rw [hk]
  have : (Nat.find hex : ℝ) ≤ k := by exact_mod_cast hkm
  exact mul_le_mul_of_nonneg_right this (hT i0 hi0).le

/-- Every common multiple is a natural multiple of the least one. -/
theorem jrp34_dvd {ι : Type*} (N : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ N, 0 < T i)
    (hN : N.Nonempty) (M : ℝ) (hM : IsLeast (commonMultiples N T) M) (x : ℝ)
    (hx : x ∈ commonMultiples N T) : ∃ j : ℕ, x = j * M := by
  have hMpos : 0 < M := hM.1.1
  set j := ⌊x / M⌋₊ with hj
  refine ⟨j, ?_⟩
  by_contra hne
  set r := x - j * M with hr
  have hjle : (j : ℝ) * M ≤ x := by
    have := Nat.floor_le (div_nonneg hx.1.le hMpos.le)
    rw [← hj, le_div_iff₀ hMpos] at this; exact this
  have hrpos : 0 < r := by
    rcases lt_or_eq_of_le hjle with h | h
    · rw [hr]; linarith
    · exact absurd h.symm hne
  have hrlt : r < M := by
    have := Nat.lt_floor_add_one (x / M)
    rw [← hj, div_lt_iff₀ hMpos] at this
    rw [hr]; linarith
  have hrcm : r ∈ commonMultiples N T := by
    refine ⟨hrpos, ?_⟩
    intro i hi
    obtain ⟨a, ha⟩ := hx.2 i hi
    obtain ⟨b, hb⟩ := hM.1.2 i hi
    have hTi := hT i hi
    -- r = (a - j b) T_i with a - j b > 0
    have hreq : r = ((a : ℤ) - (j : ℤ) * b : ℤ) * T i := by
      rw [hr, ha, hb]; push_cast; ring
    have hzpos : (0 : ℤ) < (a : ℤ) - (j : ℤ) * b := by
      have : (0 : ℝ) < (((a : ℤ) - (j : ℤ) * b : ℤ) : ℝ) := by
        rw [hreq] at hrpos
        exact pos_of_mul_pos_left hrpos hTi.le
      exact_mod_cast this
    refine ⟨((a : ℤ) - (j : ℤ) * b).toNat, ?_⟩
    rw [hreq]
    congr 1
    have : (((a : ℤ) - (j : ℤ) * b).toNat : ℤ) = (a : ℤ) - (j : ℤ) * b := Int.toNat_of_nonneg hzpos.le
    exact_mod_cast this.symm
  exact absurd (hM.2 hrcm) (not_le.mpr hrlt)

theorem jrp34_mem_inf {ι : Type*} (N : Finset ι) (hN : N.Nonempty) (S : ι → Finset ℝ) (x : ℝ) :
    x ∈ N.inf' hN S ↔ ∀ i ∈ N, x ∈ S i := by
  rw [← Finset.singleton_subset_iff, ← Finset.le_iff_subset, Finset.le_inf'_iff]
  simp

/-- The count of common multiples in `[0, Δ]` is `Δ / M_N` up to an additive error in `[0, 1]`. -/
theorem jrp34_count {ι : Type*} (N : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ N, 0 < T i)
    (hN : N.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    Δ * invLcm N T ≤ ((N.inf' hN (fun i => multiplesUpTo (T i) Δ)).card : ℝ) ∧
      ((N.inf' hN (fun i => multiplesUpTo (T i) Δ)).card : ℝ) ≤ Δ * invLcm N T + 1 := by
  obtain ⟨i0, hi0⟩ := id hN
  by_cases hne : (commonMultiples N T).Nonempty
  · obtain ⟨M, hM⟩ := jrp34_isLeast N T hT ⟨i0, hi0⟩ hne
    have hMpos : 0 < M := hM.1.1
    have hinv : invLcm N T = M⁻¹ := by
      unfold invLcm; rw [if_pos hne, hM.csInf_eq]
    have hset : N.inf' hN (fun i => multiplesUpTo (T i) Δ) = multiplesUpTo M Δ := by
      ext x
      rw [jrp34_mem_inf, jrp34_mem_mult M Δ x hMpos hΔ]
      constructor
      · intro h
        have h0 := (jrp34_mem_mult _ _ _ (hT i0 hi0) hΔ).mp (h i0 hi0)
        obtain ⟨k0, hk0, hxΔ⟩ := h0
        rcases Nat.eq_zero_or_pos k0 with hk | hk
        · exact ⟨0, by rw [hk0, hk]; simp, hxΔ⟩
        · have hxpos : 0 < x := by
            rw [hk0]; have := hT i0 hi0; positivity
          have hxcm : x ∈ commonMultiples N T := by
            refine ⟨hxpos, fun i hi => ?_⟩
            obtain ⟨k, hk, -⟩ := (jrp34_mem_mult _ _ _ (hT i hi) hΔ).mp (h i hi)
            exact ⟨k, hk⟩
          obtain ⟨j, hj⟩ := jrp34_dvd N T hT ⟨i0, hi0⟩ M hM x hxcm
          exact ⟨j, hj, hxΔ⟩
      · rintro ⟨k, hk, hxΔ⟩ i hi
        rw [jrp34_mem_mult _ _ _ (hT i hi) hΔ]
        obtain ⟨b, hb⟩ := hM.1.2 i hi
        exact ⟨k * b, by rw [hk, hb]; push_cast; ring, hxΔ⟩
    have hcard : (multiplesUpTo M Δ).card = ⌊Δ / M⌋₊ + 1 := by
      unfold multiplesUpTo
      rw [Finset.card_image_of_injective, Finset.card_range]
      intro a b hab
      have := mul_right_cancel₀ (ne_of_gt hMpos) hab
      exact_mod_cast this
    rw [hset, hcard, hinv, ← div_eq_mul_inv]
    push_cast
    have h1 := Nat.floor_le (div_nonneg hΔ hMpos.le)
    have h2 := Nat.lt_floor_add_one (Δ / M)
    constructor <;> linarith
  · have hinv : invLcm N T = 0 := by unfold invLcm; rw [if_neg hne]
    have hset : N.inf' hN (fun i => multiplesUpTo (T i) Δ) = {0} := by
      ext x
      rw [jrp34_mem_inf, Finset.mem_singleton]
      constructor
      · intro h
        by_contra hx0
        apply hne
        obtain ⟨k0, hk0, -⟩ := (jrp34_mem_mult _ _ _ (hT i0 hi0) hΔ).mp (h i0 hi0)
        have hxpos : 0 < x := by
          rcases Nat.eq_zero_or_pos k0 with hk | hk
          · exact absurd (by rw [hk0, hk]; simp) hx0
          · rw [hk0]; have := hT i0 hi0; positivity
        refine ⟨x, hxpos, fun i hi => ?_⟩
        obtain ⟨k, hk, -⟩ := (jrp34_mem_mult _ _ _ (hT i hi) hΔ).mp (h i hi)
        exact ⟨k, hk⟩
      · rintro rfl i hi
        rw [jrp34_mem_mult _ _ _ (hT i hi) hΔ]
        exact ⟨0, by simp, hΔ⟩
    rw [hset, hinv, Finset.card_singleton]
    norm_num


/-- Scaling a family by `γ > 0` scales `1 / M_N` by `1/γ`. -/
theorem jrp34_invLcm_scale {ι : Type*} (N : Finset ι) (T U : ι → ℝ) (hT : ∀ i ∈ N, 0 < T i)
    (hN : N.Nonempty) (γ : ℝ) (hγ : 0 < γ) (hU : ∀ i ∈ N, U i = γ * T i) :
    invLcm N U = invLcm N T / γ := by
  have hmem : ∀ x, x ∈ commonMultiples N U ↔ x / γ ∈ commonMultiples N T := by
    intro x
    unfold commonMultiples
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨div_pos hx hγ, fun i hi => ?_⟩
      obtain ⟨k, hk⟩ := h i hi
      refine ⟨k, ?_⟩
      rw [hk, hU i hi]; field_simp
    · rintro ⟨hx, h⟩
      refine ⟨by have := mul_pos hx hγ; rwa [div_mul_cancel₀ _ hγ.ne'] at this, fun i hi => ?_⟩
      obtain ⟨k, hk⟩ := h i hi
      refine ⟨k, ?_⟩
      rw [hU i hi]
      have : x = γ * (x / γ) := by field_simp
      rw [this, hk]; ring
  by_cases hne : (commonMultiples N T).Nonempty
  · obtain ⟨M, hM⟩ := jrp34_isLeast N T hT hN hne
    have hMU : IsLeast (commonMultiples N U) (γ * M) := by
      constructor
      · rw [hmem]; have : γ * M / γ = M := by field_simp
        rw [this]; exact hM.1
      · intro x hx
        rw [hmem] at hx
        have := hM.2 hx
        rw [le_div_iff₀ hγ] at this
        linarith
    have hneU : (commonMultiples N U).Nonempty := ⟨_, hMU.1⟩
    unfold invLcm
    rw [if_pos hne, if_pos hneU, hM.csInf_eq, hMU.csInf_eq]
    field_simp
  · have hneU : ¬ (commonMultiples N U).Nonempty := by
      rintro ⟨x, hx⟩
      exact hne ⟨_, (hmem x).mp hx⟩
    unfold invLcm
    rw [if_neg hne, if_neg hneU]
    simp

theorem jrp34_inter_eq (A : Finset ℕ) (hA : A.Nonempty) (R : ℕ → ℝ) (Δ : ℝ) :
    interMultiples A R Δ = A.inf' hA (fun ℓ => multiplesUpTo (R ℓ) Δ) := by
  ext x
  rw [jrp34_mem_inf]
  unfold interMultiples
  rw [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · intro h; exact h.2
  · intro h
    obtain ⟨ℓ, hℓ⟩ := hA
    exact ⟨⟨ℓ, hℓ, h ℓ hℓ⟩, h⟩

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar)
    (R : ℕ → ℝ) (hfeas : IsLPFeasible ε Tt Tstar Rstar R)
    (C : Finset ℕ) (hC : C ∈ components ε Tt Tstar Rstar)
    (γ : ℝ) (hγ1 : 1 - ε ≤ γ) (hγ2 : γ ≤ 1 + ε) (hγ : ∀ ℓ ∈ C, R ℓ = γ * Rstar ℓ)
    (A : Finset ℕ) (hA : A ⊆ C) (hAne : A.Nonempty) :
    ∀ Δ : ℝ, 0 ≤ Δ → |((interMultiples A R Δ).card : ℝ) -
      ((interMultiples A Rstar Δ).card : ℝ) / γ| ≤ 2 := by
  intro Δ hΔ
  have hCact : C ⊆ active ε Tt Tstar := by
    unfold components at hC
    obtain ⟨ℓ0, -, rfl⟩ := Finset.mem_image.mp hC
    exact Finset.filter_subset _ _
  have hpos : ∀ ℓ ∈ A, 0 < Rstar ℓ := by
    intro ℓ hℓ
    obtain ⟨i, hi, -⟩ := hR ℓ (hCact (hA hℓ))
    rw [hi]; exact hTstar i
  have hγpos : 0 < γ := by linarith
  have hRpos : ∀ ℓ ∈ A, 0 < R ℓ := by
    intro ℓ hℓ; rw [hγ ℓ (hA hℓ)]; exact mul_pos hγpos (hpos ℓ hℓ)
  have hinv := jrp34_invLcm_scale A Rstar R hpos hAne γ hγpos (fun ℓ hℓ => hγ ℓ (hA hℓ))
  obtain ⟨u1, u2⟩ := jrp34_count A R hRpos hAne Δ hΔ
  obtain ⟨v1, v2⟩ := jrp34_count A Rstar hpos hAne Δ hΔ
  rw [jrp34_inter_eq A hAne R Δ, jrp34_inter_eq A hAne Rstar Δ]
  rw [hinv] at u1 u2
  set x := ((A.inf' hAne (fun ℓ => multiplesUpTo (R ℓ) Δ)).card : ℝ)
  set y := ((A.inf' hAne (fun ℓ => multiplesUpTo (Rstar ℓ) Δ)).card : ℝ)
  set w := Δ * invLcm A Rstar
  have e1 : Δ * (invLcm A Rstar / γ) = w / γ := by rw [mul_div_assoc']
  rw [e1] at u1 u2
  have hy1 : w / γ ≤ y / γ := div_le_div_of_nonneg_right v1 hγpos.le
  have hy2 : y / γ ≤ w / γ + 1 / γ := by
    rw [← add_div]; exact div_le_div_of_nonneg_right v2 hγpos.le
  have hg : 1 / γ ≤ 2 := by
    rw [div_le_iff₀ hγpos]; linarith
  rw [abs_le]; constructor <;> linarith
