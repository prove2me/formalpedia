-- Prove2me | solution 1 for Disjunctive.NormalForms.parsimonious_mip_representation_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:37:38.945812+00:00
-- url     : https://prove2.me/submissions/e2f13d5a-6a75-4a44-8a31-3f4c6cd27bfe

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

open Disjunctive.NormalForms

open Classical

namespace ParsAux

theorem cone_mono {n mk mm : ℕ} (Ak : Matrix (Fin mk) (Fin n) ℝ) (bk : Fin mk → ℝ)
    (Am : Matrix (Fin mm) (Fin n) ℝ) (bm : Fin mm → ℝ)
    (hne : (Poly Ak bk).Nonempty) (hsub : Poly Ak bk ⊆ Poly Am bm)
    (d : Fin n → ℝ) (hd : 0 ≤ Ak.mulVec d) : 0 ≤ Am.mulVec d := by
  obtain ⟨x0, hx0⟩ := hne
  have hray : ∀ t : ℝ, 0 ≤ t → x0 + t • d ∈ Poly Am bm := by
    intro t ht
    apply hsub
    intro k
    have h1 := hx0 k
    have h2 := hd k
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply] at h2 ⊢
    nlinarith
  intro r
  by_contra hc
  push_neg at hc
  set c := (Am.mulVec d) r
  have hK := hray 0 le_rfl r
  simp only [zero_smul, add_zero] at hK
  set K := Am.mulVec x0 r - bm r
  have hcpos : 0 < -c := by simp at hc; linarith
  have ht : 0 ≤ (K + 1) / (-c) := div_nonneg (by simp [K]; linarith) hcpos.le
  have h := hray _ ht r
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at h
  have : (K + 1) / (-c) * c = -(K + 1) := by
    have hc0 : c ≠ 0 := ne_of_lt (by linarith)
    rw [div_mul_eq_mul_div, mul_div_assoc, div_neg, div_self hc0]; ring
  change bm r ≤ Am.mulVec x0 r + (K + 1) / (-c) * c at h
  rw [this] at h
  simp [K] at h
  linarith

end ParsAux

theorem solution {n : ℕ} {T0 : Type*} [Fintype T0] (Qr : T0 → Type*)
    [∀ r, Fintype (Qr r)] (a : (r : T0) → Qr r → Fin n → ℝ) (a0 : (r : T0) → Qr r → ℝ)
    {T : Type*} [Fintype T] (T0j : T → Finset T0)
    (hpart : ∀ r : T0, ∃! j : T, r ∈ T0j j) (Qj : T → Type*) [∀ j, Fintype (Qj j)]
    (mA : (j : T) → Qj j → ℕ) (A : (j : T) → (i : Qj j) → Matrix (Fin (mA j i)) (Fin n) ℝ)
    (b : (j : T) → (i : Qj j) → Fin (mA j i) → ℝ)
    (Mi : (j : T) → Qj j → (ρ : { r : T0 // r ∈ T0j j }) → Qr ρ.1)
    (hPoly : ∀ j i, Poly (A j i) (b j i) = ⋂ ρ : { r : T0 // r ∈ T0j j },
      HalfspaceGE (a ρ.1 (Mi j i ρ)) (a0 ρ.1 (Mi j i ρ)))
    (hChoices : ∀ j, Function.Bijective (Mi j))
    (h25 : ∀ (j : T) (i i' : Qj j), IsMaximalDisjunct Qj mA A b j i →
      IsMaximalDisjunct Qj mA A b j i' →
        {y : Fin n → ℝ | 0 ≤ (A j i).mulVec y} = {y : Fin n → ℝ | 0 ≤ (A j i').mulVec y})
    (h26 : ∀ (j : T) (k i : Qj j), ¬ (Poly (A j k) (b j k)).Nonempty →
      IsMaximalDisjunct Qj mA A b j i →
        {y : Fin n → ℝ | 0 ≤ (A j k).mulVec y} ⊆ {y : Fin n → ℝ | 0 ≤ (A j i).mulVec y}) :
    (⋂ j : T, ⋃ i : Qj j, Poly (A j i) (b j i)) =
      {x : Fin n → ℝ | ∃ (y : (j : T) → Qj j → Fin n → ℝ) (y0 : (j : T) → Qj j → ℝ)
        (δ : (r : T0) → Qr r → ℝ),
        (∀ j, x = ∑ i, y j i) ∧
        (∀ j i, 0 ≤ (A j i).mulVec (y j i) - y0 j i • (b j i) ∧ 0 ≤ y0 j i) ∧
        (∀ j, ∑ i, y0 j i = 1) ∧
        (∀ r s, δ r s = ∑ j : T, ∑ i : Qj j,
          if h : r ∈ T0j j then (if Mi j i ⟨r, h⟩ = s then y0 j i else 0) else 0) ∧
        (∀ r, ∑ s, δ r s = 1) ∧
        (∀ r s, δ r s = 0 ∨ δ r s = 1)} := by
  -- formula for the δ-sum
  have hform : ∀ (y0 : (j : T) → Qj j → ℝ) (r : T0) (s : Qr r) (j : T) (h : r ∈ T0j j),
      (∑ j' : T, ∑ i : Qj j',
        if h : r ∈ T0j j' then (if Mi j' i ⟨r, h⟩ = s then y0 j' i else 0) else 0) =
      ∑ i : Qj j, (if Mi j i ⟨r, h⟩ = s then y0 j i else 0) := by
    intro y0 r s j h
    rw [Finset.sum_eq_single j]
    · apply Finset.sum_congr rfl; intro i _; rw [dif_pos h]
    · intro j' _ hj'
      apply Finset.sum_eq_zero; intro i _
      have : r ∉ T0j j' := by
        intro h'
        obtain ⟨j0, _, hu⟩ := hpart r
        exact hj' ((hu j' h').trans (hu j h).symm)
      rw [dif_neg this]
    · intro h'; exact absurd (Finset.mem_univ j) h'
  -- maximal disjunct above a feasible one
  have hmax : ∀ (j : T) (i : Qj j), (Poly (A j i) (b j i)).Nonempty →
      ∃ m, IsMaximalDisjunct Qj mA A b j m ∧ Poly (A j i) (b j i) ⊆ Poly (A j m) (b j m) := by
    intro j i hne
    obtain ⟨m, hm, hmx⟩ := Finset.exists_maximalFor (fun k => Poly (A j k) (b j k))
      (Finset.univ.filter (fun k => (Poly (A j k) (b j k)).Nonempty ∧
        Poly (A j i) (b j i) ⊆ Poly (A j k) (b j k))) ⟨i, by simp [hne]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm hmx
    refine ⟨m, ⟨hm.1, fun k hk hsub => ?_⟩, hm.2⟩
    exact hmx ⟨hk, hm.2.trans hsub⟩ hsub
  ext x
  simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · intro hx
    choose ix hix using hx
    refine ⟨fun j i => if i = ix j then x else 0, fun j i => if i = ix j then 1 else 0, _,
      ?_, ?_, ?_, fun r s => rfl, ?_, ?_⟩
    · intro j; simp
    · intro j i
      by_cases hi : i = ix j
      · subst hi
        refine ⟨?_, by simp⟩
        intro k
        have := hix j k
        simp only [if_true, one_smul, Pi.sub_apply, Pi.zero_apply]
        linarith
      · simp [hi]
    · intro j; simp
    · intro r
      obtain ⟨jr, hjr, _⟩ := hpart r
      rw [Finset.sum_congr rfl (fun s _ => hform _ r s jr hjr)]
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single (ix jr)]
      · simp
      · intro i _ hi; simp [hi]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro r s
      obtain ⟨jr, hjr, _⟩ := hpart r
      rw [hform _ r s jr hjr, Finset.sum_eq_single (ix jr)]
      · simp only [if_true]; split_ifs <;> simp
      · intro i _ hi; simp [hi]
      · intro h; exact absurd (Finset.mem_univ _) h
  · rintro ⟨y, y0, δ, hxy, hA, hy0, hδ, hδ1, hδb⟩ j
    -- choose s_ρ with δ = 1
    have hsel : ∀ ρ : { r : T0 // r ∈ T0j j }, ∃ s, δ ρ.1 s = 1 := by
      intro ρ
      by_contra hc
      push_neg at hc
      have : ∑ s, δ ρ.1 s = 0 := Finset.sum_eq_zero (fun s _ => (hδb _ s).resolve_right (hc s))
      rw [hδ1] at this; exact one_ne_zero this
    choose σ hσ using hsel
    obtain ⟨istar, histar⟩ := (hChoices j).2 σ
    have hy0nn : ∀ i, 0 ≤ y0 j i := fun i => (hA j i).2
    have hzero : ∀ i, i ≠ istar → y0 j i = 0 := by
      intro i hi
      have hne : Mi j i ≠ σ := by
        intro h; apply hi; apply (hChoices j).1; rw [h, histar]
      obtain ⟨ρ, hρ⟩ : ∃ ρ, Mi j i ρ ≠ σ ρ := by
        by_contra hc; push_neg at hc; exact hne (funext hc)
      have h1 : ∑ i', (if Mi j i' ρ = σ ρ then y0 j i' else 0) = 1 := by
        rw [← hform y0 ρ.1 (σ ρ) j ρ.2, ← hδ]; exact hσ ρ
      have hsplit : ∑ i', y0 j i' = ∑ i', (if Mi j i' ρ = σ ρ then y0 j i' else 0) +
          ∑ i', (if Mi j i' ρ = σ ρ then 0 else y0 j i') := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i' _; split_ifs <;> simp
      rw [hy0, h1] at hsplit
      have h2 : ∑ i', (if Mi j i' ρ = σ ρ then 0 else y0 j i') = 0 := by linarith
      have h3 : (if Mi j i ρ = σ ρ then 0 else y0 j i) ≤
          ∑ i', (if Mi j i' ρ = σ ρ then 0 else y0 j i') :=
        Finset.single_le_sum (f := fun i' => if Mi j i' ρ = σ ρ then 0 else y0 j i')
          (fun i' _ => by split_ifs <;> simp [hy0nn]) (Finset.mem_univ i)
      rw [if_neg hρ] at h3
      linarith [hy0nn i]
    have hone : y0 j istar = 1 := by
      rw [← hy0 j, Finset.sum_eq_single istar (fun i _ hi => hzero i hi)
        (fun h => absurd (Finset.mem_univ _) h)]
    have hstar : y j istar ∈ Poly (A j istar) (b j istar) := by
      intro k
      have := (hA j istar).1 k
      simp only [hone, one_smul, Pi.sub_apply, Pi.zero_apply] at this
      linarith
    have hcone : ∀ i, i ≠ istar → 0 ≤ (A j i).mulVec (y j i) := by
      intro i hi
      have := (hA j i).1
      rwa [hzero i hi, zero_smul, sub_zero] at this
    obtain ⟨m, hm, hsubm⟩ := hmax j istar ⟨_, hstar⟩
    have hconem : ∀ i, i ≠ istar → 0 ≤ (A j m).mulVec (y j i) := by
      intro i hi
      by_cases hfe : (Poly (A j i) (b j i)).Nonempty
      · obtain ⟨m', hm', hsub'⟩ := hmax j i hfe
        have h1 := ParsAux.cone_mono _ _ _ _ hfe hsub' _ (hcone i hi)
        have h2 := h25 j m' m hm' hm
        have : y j i ∈ {y : Fin n → ℝ | 0 ≤ (A j m').mulVec y} := h1
        rw [h2] at this; exact this
      · exact h26 j i m hfe hm (hcone i hi)
    refine ⟨m, ?_⟩
    intro k
    rw [hxy j, Matrix.mulVec_sum, Finset.sum_apply,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ istar)]
    have h1 := hsubm hstar k
    have h2 : 0 ≤ ∑ i ∈ Finset.univ.erase istar, (A j m).mulVec (y j i) k :=
      Finset.sum_nonneg (fun i hi => hconem i (Finset.ne_of_mem_erase hi) k)
    linarith
