-- Prove2me | solution 1 for Disjunctive.HigherDim.sherali_adams_reaches_hull_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:29:26.860753+00:00
-- url     : https://prove2.me/submissions/ebf705e9-08c9-4d3f-a762-eb4a50485633

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts
import Definitions.Def_Disjunctive_HigherDim_BoundRows

set_option autoImplicit false

namespace SAHull52

open Disjunctive.HigherDim

theorem mob {α : Type*} [DecidableEq α] (P : Finset α) (f : Finset α → ℝ) :
    ∑ J ∈ P.powerset, ∑ S ∈ (P \ J).powerset, (-1 : ℝ) ^ S.card * f (J ∪ S) = f ∅ := by
  have h1 : ∑ J ∈ P.powerset, ∑ S ∈ (P \ J).powerset, (-1 : ℝ) ^ S.card * f (J ∪ S)
      = ∑ T ∈ P.powerset, ∑ S ∈ T.powerset, (-1 : ℝ) ^ S.card * f T := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij' (fun p _ => (⟨p.1 ∪ p.2, p.2⟩ : (_ : Finset α) × Finset α))
      (fun p _ => (⟨p.1 \ p.2, p.2⟩ : (_ : Finset α) × Finset α)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨J, S⟩ h
      simp only [Finset.mem_sigma, Finset.mem_powerset] at h ⊢
      exact ⟨Finset.union_subset h.1 (h.2.trans Finset.sdiff_subset), Finset.subset_union_right⟩
    · rintro ⟨T, S⟩ h
      simp only [Finset.mem_sigma, Finset.mem_powerset] at h ⊢
      refine ⟨Finset.sdiff_subset.trans h.1, ?_⟩
      intro s hs
      rw [Finset.mem_sdiff]
      refine ⟨h.1 (h.2 hs), ?_⟩
      intro h'
      exact (Finset.mem_sdiff.1 h').2 hs
    · rintro ⟨J, S⟩ h
      simp only [Finset.mem_sigma, Finset.mem_powerset] at h
      have hd : Disjoint J S := Finset.disjoint_of_subset_right h.2 Finset.disjoint_sdiff
      simp only [Finset.union_sdiff_cancel_right hd]
    · rintro ⟨T, S⟩ h
      simp only [Finset.mem_sigma, Finset.mem_powerset] at h
      simp only [Finset.sdiff_union_of_subset h.2]
    · rintro ⟨J, S⟩ _
      rfl
  rw [h1, Finset.sum_eq_single ∅]
  · simp
  · intro T _ hT
    rw [← Finset.sum_mul]
    have h2 := Finset.sum_powerset_neg_one_pow_card (x := T)
    rw [if_neg hT] at h2
    have h3 : ∑ m ∈ T.powerset, (-1 : ℝ) ^ m.card = 0 := by exact_mod_cast h2
    rw [h3, zero_mul]
  · intro h
    exact absurd (Finset.empty_mem_powerset P) h

variable {m n : ℕ}

/-- Möbius mass of the partition `(J, P \ J)`. -/
def lamF (P : Finset (Fin n)) (w : Finset (Fin n) → ℝ) (J : Finset (Fin n)) : ℝ :=
  ∑ S ∈ (P \ J).powerset, (-1 : ℝ) ^ S.card * w (J ∪ S)

/-- Möbius vector of the partition `(J, P \ J)`. -/
def zF (P : Finset (Fin n)) (w : Finset (Fin n) → ℝ) (v : Finset (Fin n) → Fin n → ℝ)
    (J : Finset (Fin n)) (k : Fin n) : ℝ :=
  ∑ S ∈ (P \ J).powerset, (-1 : ℝ) ^ S.card * MomentEval P w v (J ∪ S) k

theorem rowEq (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (P : Finset (Fin n))
    (w : Finset (Fin n) → ℝ) (v : Finset (Fin n) → Fin n → ℝ) (i : Fin m) (J : Finset (Fin n)) :
    RowNLt A b P w v i J (P \ J) = ∑ k, A i k * zF P w v J k - b i * lamF P w J := by
  simp only [RowNLt, zF, lamF, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun S _ => by ring
  · exact Finset.sum_congr rfl fun S _ => by ring

theorem zMem (P : Finset (Fin n)) (w : Finset (Fin n) → ℝ) (v : Finset (Fin n) → Fin n → ℝ)
    (J : Finset (Fin n)) (j : Fin n) (hjP : j ∈ P) :
    zF P w v J j = if j ∈ J then lamF P w J else 0 := by
  split_ifs with hj
  · unfold zF lamF
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [MomentEval, if_pos hjP, Finset.insert_eq_of_mem (Finset.mem_union_left S hj)]
  · have hjD : j ∈ P \ J := Finset.mem_sdiff.2 ⟨hjP, hj⟩
    unfold zF
    rw [← Finset.insert_erase hjD, Finset.sum_powerset_insert (Finset.notMem_erase j _),
      ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro S hS
    have hjS : j ∉ S := fun h => Finset.notMem_erase j _ (Finset.mem_powerset.1 hS h)
    rw [Finset.card_insert_of_notMem hjS]
    simp only [MomentEval, if_pos hjP, Finset.union_insert, Finset.insert_idem]
    ring

theorem kt_sub (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (P : Finset (Fin n))
    (hK : HasBoundRows A b P) (x : Fin n → ℝ) (hx : x ∈ KtSet A b P P.card) :
    x ∈ convexHull ℝ (K0Set A b P) := by
  obtain ⟨w, v, hw0, hw1, hv0, hrow⟩ := hx
  have hrowJ : ∀ i, ∀ J ⊆ P, b i * lamF P w J ≤ ∑ k, A i k * zF P w v J k := by
    intro i J hJ
    have := hrow i J (P \ J) Finset.disjoint_sdiff hJ Finset.sdiff_subset
      (by rw [Finset.union_sdiff_of_subset hJ])
    rw [rowEq] at this
    linarith
  have hlam : ∀ J ⊆ P, 0 ≤ lamF P w J := by
    intro J hJ
    by_cases hJn : J.Nonempty
    · obtain ⟨j, hj⟩ := hJn
      obtain ⟨i, hAi, hbi⟩ := hK.1 j
      have := hrowJ i J hJ
      rw [hbi] at this
      simp only [hAi, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, zero_mul] at this
      rw [zMem P w v J j (hJ hj), if_pos hj] at this
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hJn
      subst hJn
      by_cases hP : P.Nonempty
      · obtain ⟨j, hj⟩ := hP
        obtain ⟨i, hAi, hbi⟩ := hK.2 j hj
        have := hrowJ i ∅ (Finset.empty_subset _)
        rw [hbi] at this
        simp only [hAi, Pi.neg_apply, Pi.single_apply, neg_mul, ite_mul, one_mul, zero_mul,
          Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        rw [zMem P w v ∅ j hj, if_neg (Finset.notMem_empty j)] at this
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty] at hP
        subst hP
        simp [lamF, hw0]
  have hsum1 : ∑ J ∈ P.powerset, lamF P w J = 1 := by
    rw [← hw0]
    exact mob P w
  have hsumz : ∀ k, ∑ J ∈ P.powerset, zF P w v J k = x k := by
    intro k
    have := mob P (fun U => MomentEval P w v U k)
    simp only [zF]
    rw [this]
    unfold MomentEval
    split_ifs with hk
    · simpa using hw1 k hk
    · exact hv0 k hk
  -- choose J0 with positive mass
  obtain ⟨J0, hJ0mem, hJ0ne⟩ : ∃ J0 ∈ P.powerset, lamF P w J0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at hsum1
    exact zero_ne_one hsum1
  have hJ0P : J0 ⊆ P := Finset.mem_powerset.1 hJ0mem
  have hJ0pos : 0 < lamF P w J0 := lt_of_le_of_ne (hlam J0 hJ0P) (Ne.symm hJ0ne)
  set lam := lamF P w with hlamdef
  set z := zF P w v with hzdef
  let r : Fin n → ℝ := fun k => ∑ J ∈ P.powerset, if lam J = 0 then z J k else 0
  let Y : Finset (Fin n) → Fin n → ℝ := fun J k =>
    (lam J)⁻¹ * z J k + (if J = J0 then (lam J0)⁻¹ * r k else 0)
  have hr_row : ∀ i, 0 ≤ ∑ k, A i k * r k := by
    intro i
    have : ∑ k, A i k * r k = ∑ J ∈ P.powerset, if lam J = 0 then ∑ k, A i k * z J k else 0 := by
      simp only [r, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun J _ => ?_
      split_ifs <;> simp
    rw [this]
    refine Finset.sum_nonneg fun J hJ => ?_
    split_ifs with h0
    · have := hrowJ i J (Finset.mem_powerset.1 hJ)
      rw [h0, mul_zero] at this
      exact this
    · exact le_refl _
  have hr_P : ∀ j ∈ P, r j = 0 := by
    intro j hj
    refine Finset.sum_eq_zero fun J hJ => ?_
    split_ifs with h0
    · rw [hzdef, zMem P w v J j hj]
      split_ifs
      · exact h0
      · rfl
    · rfl
  have hY : ∀ J ∈ P.powerset, lam J ≠ 0 → Y J ∈ K0Set A b P := by
    intro J hJ hne
    have hJP := Finset.mem_powerset.1 hJ
    have hpos : 0 < lam J := lt_of_le_of_ne (hlam J hJP) (Ne.symm hne)
    refine ⟨?_, ?_⟩
    · intro i
      have hrow' := hrowJ i J hJP
      have hrr := hr_row i
      show b i ≤ ∑ k, A i k * Y J k
      have hexp : ∑ k, A i k * Y J k = (lam J)⁻¹ * ∑ k, A i k * z J k +
          (if J = J0 then (lam J0)⁻¹ * ∑ k, A i k * r k else 0) := by
        simp only [Y, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun k _ => by ring
        · split_ifs
          · exact Finset.sum_congr rfl fun k _ => by ring
          · simp
      rw [hexp]
      have h1 : b i ≤ (lam J)⁻¹ * ∑ k, A i k * z J k := by
        rw [← div_eq_inv_mul, le_div_iff₀ hpos]
        linarith
      have h2 : 0 ≤ (if J = J0 then (lam J0)⁻¹ * ∑ k, A i k * r k else 0) := by
        split_ifs
        · exact mul_nonneg (inv_nonneg.2 hJ0pos.le) hrr
        · exact le_refl _
      linarith
    · simp only [Set.mem_iInter]
      intro j hj
      show Y J j = 0 ∨ Y J j = 1
      simp only [Y, hr_P j hj, mul_zero, ite_self, add_zero]
      rw [hzdef, zMem P w v J j hj]
      split_ifs
      · right; exact inv_mul_cancel₀ hne
      · left; simp
  let q : Finset (Fin n) → Fin n → ℝ := fun J => if lam J = 0 then Y J0 else Y J
  have hxq : x = ∑ J ∈ P.powerset, lam J • q J := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hterm : ∀ J ∈ P.powerset, lam J * q J k =
        (if lam J = 0 then 0 else z J k) + (if J = J0 then r k else 0) := by
      intro J _
      by_cases h0 : lam J = 0
      · have hne : J ≠ J0 := fun h => hJ0ne (h ▸ h0)
        simp [q, h0, hne]
      · have hq : q J = Y J := by simp only [q, if_neg h0]
        rw [hq]
        simp only [Y, if_neg h0]
        split_ifs with hJ
        · subst hJ
          field_simp
        · simp only [add_zero]
          rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' P.powerset J0,
      if_pos hJ0mem]
    simp only [r]
    rw [← Finset.sum_add_distrib, ← hsumz k]
    refine Finset.sum_congr rfl fun J _ => ?_
    split_ifs <;> simp_all
  rw [hxq]
  refine (convex_convexHull ℝ _).sum_mem (fun J hJ => hlam J (Finset.mem_powerset.1 hJ)) hsum1 ?_
  intro J hJ
  apply subset_convexHull
  by_cases h0 : lam J = 0
  · simp only [q, if_pos h0]
    exact hY J0 hJ0mem hJ0ne
  · simp only [q, if_neg h0]
    exact hY J hJ h0

theorem rowLin (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (P : Finset (Fin n))
    (w1 w2 : Finset (Fin n) → ℝ) (v1 v2 : Finset (Fin n) → Fin n → ℝ) (a c : ℝ) (i : Fin m)
    (J1 J2 : Finset (Fin n)) :
    RowNLt A b P (fun J => a * w1 J + c * w2 J) (fun J k => a * v1 J k + c * v2 J k) i J1 J2 =
      a * RowNLt A b P w1 v1 i J1 J2 + c * RowNLt A b P w2 v2 i J1 J2 := by
  have hME : ∀ U k, MomentEval P (fun J => a * w1 J + c * w2 J)
      (fun J k => a * v1 J k + c * v2 J k) U k =
      a * MomentEval P w1 v1 U k + c * MomentEval P w2 v2 U k := by
    intro U k
    unfold MomentEval
    split_ifs <;> rfl
  simp only [RowNLt, hME, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hs : ∑ k, A i k * (a * MomentEval P w1 v1 (J1 ∪ S) k + c * MomentEval P w2 v2 (J1 ∪ S) k)
      = a * ∑ k, A i k * MomentEval P w1 v1 (J1 ∪ S) k
        + c * ∑ k, A i k * MomentEval P w2 v2 (J1 ∪ S) k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hs]
  ring

theorem kt_convex (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (P : Finset (Fin n)) (t : ℕ) :
    Convex ℝ (KtSet A b P t) := by
  rintro x ⟨w1, v1, h1a, h1b, h1c, h1d⟩ y ⟨w2, v2, h2a, h2b, h2c, h2d⟩ a c ha hc hac
  refine ⟨fun J => a * w1 J + c * w2 J, fun J k => a * v1 J k + c * v2 J k, ?_, ?_, ?_, ?_⟩
  · simp only [h1a, h2a, mul_one, hac]
  · intro j hj
    simp only [h1b j hj, h2b j hj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro k hk
    simp only [h1c k hk, h2c k hk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro i J1 J2 hd hJ1 hJ2 hcard
    rw [rowLin]
    exact add_nonneg (mul_nonneg ha (h1d i J1 J2 hd hJ1 hJ2 hcard))
      (mul_nonneg hc (h2d i J1 J2 hd hJ1 hJ2 hcard))

theorem k0_sub (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (P : Finset (Fin n)) :
    K0Set A b P ⊆ KtSet A b P P.card := by
  rintro x ⟨hP, hZ⟩
  simp only [Set.mem_iInter] at hZ
  have hZ' : ∀ j ∈ P, x j = 0 ∨ x j = 1 := fun j hj => hZ j hj
  have hid : ∀ j ∈ P, x j * x j = x j := by
    intro j hj
    rcases hZ' j hj with h | h <;> simp [h]
  refine ⟨fun J => ∏ j ∈ J, x j, fun J k => x k * ∏ j ∈ J, x j, by simp, fun j _ => by simp,
    fun k _ => by simp, ?_⟩
  intro i J1 J2 hd h1 h2 _
  have hME : ∀ U k, MomentEval P (fun J => ∏ j ∈ J, x j) (fun J k => x k * ∏ j ∈ J, x j) U k
      = x k * ∏ j ∈ U, x j := by
    intro U k
    unfold MomentEval
    split_ifs with hk
    · show ∏ j ∈ insert k U, x j = x k * ∏ j ∈ U, x j
      by_cases hkU : k ∈ U
      · rw [Finset.insert_eq_of_mem hkU, ← Finset.mul_prod_erase U x hkU, ← mul_assoc, hid k hk]
      · rw [Finset.prod_insert hkU]
    · rfl
  have hval : RowNLt A b P (fun J => ∏ j ∈ J, x j) (fun J k => x k * ∏ j ∈ J, x j) i J1 J2 =
      (∏ j ∈ J1, x j) * (∏ j ∈ J2, (1 - x j)) * (∑ k, A i k * x k - b i) := by
    unfold RowNLt
    simp only [hME]
    have hfac : ∀ S ∈ J2.powerset, (-1 : ℝ) ^ S.card *
        ((∑ k, A i k * (x k * ∏ j ∈ J1 ∪ S, x j)) - b i * ∏ j ∈ J1 ∪ S, x j) =
        (∏ j ∈ J1, x j) * ((∏ j ∈ S, -x j) * (∑ k, A i k * x k - b i)) := by
      intro S hS
      rw [Finset.prod_union (Finset.disjoint_of_subset_right (Finset.mem_powerset.1 hS) hd),
        Finset.prod_neg]
      have : ∑ k, A i k * (x k * ((∏ j ∈ J1, x j) * ∏ j ∈ S, x j)) =
          ((∏ j ∈ J1, x j) * ∏ j ∈ S, x j) * ∑ k, A i k * x k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this]
      ring
    rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, ← Finset.sum_mul]
    have hpa := Finset.prod_add (fun j => -x j) (fun _ => (1 : ℝ)) J2
    simp only [Finset.prod_const_one, mul_one] at hpa
    rw [← hpa]
    have : ∏ j ∈ J2, (-x j + 1) = ∏ j ∈ J2, (1 - x j) :=
      Finset.prod_congr rfl fun j _ => by ring
    rw [this]
    ring
  rw [hval]
  have hA : b i ≤ ∑ k, A i k * x k := hP i
  refine mul_nonneg (mul_nonneg ?_ ?_) (by linarith)
  · refine Finset.prod_nonneg fun j hj => ?_
    rcases hZ' j (h1 hj) with h | h <;> simp [h]
  · refine Finset.prod_nonneg fun j hj => ?_
    rcases hZ' j (h2 hj) with h | h <;> simp [h]

end SAHull52

open Disjunctive.HigherDim in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) :
    KtSet A b Nprime Nprime.card = convexHull ℝ (K0Set A b Nprime) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact SAHull52.kt_sub A b Nprime hK x hx
  · exact convexHull_min (SAHull52.k0_sub A b Nprime) (SAHull52.kt_convex A b Nprime _)
