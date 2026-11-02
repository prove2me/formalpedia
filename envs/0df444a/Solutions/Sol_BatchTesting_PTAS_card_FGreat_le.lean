-- Prove2me | solution 1 for BatchTesting.PTAS.card_FGreat_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:25:16.017149+00:00
-- url     : https://prove2.me/submissions/6f39f3cc-94a1-401b-9655-bf6ed38a69a8

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

open BatchTesting.PTAS

namespace BTCommon

variable {n : ℕ} (I : Instance n) (eps : ℝ)

theorem mem_cls {r : ℕ} {i : Fin n} : i ∈ cls I eps r ↔ classOf I eps i = r := by
  simp [cls]

theorem rank_lt_rank {i j : Fin n} (hij : classOf I eps i = classOf I eps j)
    (h : toLex (I.p i, i) < toLex (I.p j, j)) : rank I eps i < rank I eps j := by
  unfold rank
  rw [hij]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, ?_, ?_⟩
    · simp [mem_cls, hij, h]
    · simp
  · intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_trans hk.2 h⟩

theorem rank_injOn (r : ℕ) : Set.InjOn (rank I eps) (cls I eps r) := by
  intro i hi j hj hr
  simp only [Finset.mem_coe, mem_cls] at hi hj
  by_contra hne
  have hlex : toLex (I.p i, i) ≠ toLex (I.p j, j) := by
    intro h
    exact hne (congrArg Prod.snd (toLex.injective h))
  rcases lt_or_gt_of_ne hlex with h | h
  · exact (rank_lt_rank I eps (hi.trans hj.symm) h).ne hr
  · exact (rank_lt_rank I eps (hj.trans hi.symm) h).ne hr.symm

theorem rank_lt_card (i : Fin n) : rank I eps i < (cls I eps (classOf I eps i)).card := by
  unfold rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨i, by simp [mem_cls], by simp⟩

theorem image_rank (r : ℕ) : (cls I eps r).image (rank I eps) = Finset.range (cls I eps r).card := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have := rank_lt_card I eps i
    rw [(mem_cls I eps).mp hi] at this
    simpa using this
  · rw [Finset.card_image_of_injOn (rank_injOn I eps r)]
    simp

theorem card_filter_rank (r k : ℕ) :
    ((cls I eps r).filter (fun i => rank I eps i < k)).card = min k (cls I eps r).card := by
  have h1 : ((cls I eps r).filter (fun i => rank I eps i < k)).card =
      (((cls I eps r).filter (fun i => rank I eps i < k)).image (rank I eps)).card := by
    rw [Finset.card_image_of_injOn]
    exact (rank_injOn I eps r).mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have h2 : ((cls I eps r).filter (fun i => rank I eps i < k)).image (rank I eps) =
      ((cls I eps r).image (rank I eps)).filter (fun x => x < k) := by
    ext x; simp only [Finset.mem_image, Finset.mem_filter]; constructor
    · rintro ⟨i, ⟨hi, hk⟩, rfl⟩; exact ⟨⟨i, hi, rfl⟩, hk⟩
    · rintro ⟨⟨i, hi, rfl⟩, hk⟩; exact ⟨i, ⟨hi, hk⟩, rfl⟩
  rw [h1, h2, image_rank]
  have : (Finset.range (cls I eps r).card).filter (fun x => x < k) =
      Finset.range (min k (cls I eps r).card) := by
    ext x; simp; omega
  rw [this, Finset.card_range]

theorem mem_tested {N : State I eps} {i : Fin n} :
    i ∈ tested I eps N ↔ rank I eps i < N (classIdx I eps i) := by
  simp [tested]

theorem classIdx_eq_iff (i : Fin n) (r : Fin (R I eps + 1)) :
    classIdx I eps i = r ↔ classOf I eps i = (r : ℕ) := by
  simp [classIdx, Fin.ext_iff]

/-- The class-`r` part of `tested N`. -/
theorem tested_filter (N : State I eps) (r : Fin (R I eps + 1)) :
    (tested I eps N).filter (fun i => classIdx I eps i = r) =
      (cls I eps r).filter (fun i => rank I eps i < N r) := by
  ext i
  simp only [Finset.mem_filter, mem_tested, mem_cls, classIdx_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    have : classIdx I eps i = r := (classIdx_eq_iff I eps i r).mpr h2
    rwa [this] at h1
  · rintro ⟨h2, h1⟩
    have : classIdx I eps i = r := (classIdx_eq_iff I eps i r).mpr h2
    exact ⟨by rwa [this], h2⟩

theorem card_tested_filter (N : State I eps) (r : Fin (R I eps + 1)) :
    ((tested I eps N).filter (fun i => classIdx I eps i = r)).card =
      min (N r) (cls I eps r).card := by
  rw [tested_filter, card_filter_rank]

theorem mem_F {N : State I eps} : N ∈ F I eps ↔ ∀ r, N r ≤ (cls I eps r).card := by
  simp [F, Fintype.mem_piFinset]

theorem tested_mono {N M : State I eps} (h : N ≤ M) : tested I eps N ⊆ tested I eps M := by
  intro i hi
  rw [mem_tested] at hi ⊢
  exact lt_of_lt_of_le hi (h _)

theorem tested_zero : tested I eps 0 = ∅ := by
  ext i; simp [mem_tested]

theorem tested_Nall : tested I eps (Nall I eps) = Finset.univ := by
  ext i
  simp only [mem_tested, Finset.mem_univ, iff_true, Nall, classIdx]
  exact rank_lt_card I eps i

theorem card_sdiff_filter {N M : State I eps} (hNM : N ≤ M) (hM : M ∈ F I eps)
    (r : Fin (R I eps + 1)) :
    ((tested I eps M \ tested I eps N).filter (fun i => classIdx I eps i = r)).card = M r - N r := by
  have hfs : (tested I eps M \ tested I eps N).filter (fun i => classIdx I eps i = r) =
      (tested I eps M).filter (fun i => classIdx I eps i = r) \
        (tested I eps N).filter (fun i => classIdx I eps i = r) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [hfs, Finset.card_sdiff_of_subset, card_tested_filter, card_tested_filter]
  · have h1 := (mem_F I eps).mp hM r
    have h2 := hNM r
    rw [min_eq_left h1, min_eq_left (h2.trans h1)]
  · exact Finset.monotone_filter_left _ (tested_mono I eps hNM)

/-- Sum of a class-dependent weight over a finset, grouped by class. -/
theorem sum_by_class (s : Finset (Fin n)) (f : Fin (R I eps + 1) → ℝ) :
    ∑ i ∈ s, f (classIdx I eps i) =
      ∑ r, ((s.filter (fun i => classIdx I eps i = r)).card : ℝ) * f r := by
  rw [← Finset.sum_fiberwise s (classIdx I eps) (fun i => f (classIdx I eps i))]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_congr rfl (g := fun _ => f r)]
  · simp
  · intro i hi
    rw [(Finset.mem_filter.mp hi).2]

theorem P0_nonneg (hI : I.Standing) (N : State I eps) : 0 ≤ P0 I eps N :=
  Finset.prod_nonneg fun i _ => (hI.2.1 i).1

theorem P0_le_one (hI : I.Standing) (N : State I eps) : P0 I eps N ≤ 1 :=
  Finset.prod_le_one (fun i _ => (hI.2.1 i).1) (fun i _ => (hI.2.1 i).2)

theorem P0_anti (hI : I.Standing) {N M : State I eps} (h : N ≤ M) : P0 I eps M ≤ P0 I eps N := by
  unfold P0
  rw [← Finset.prod_sdiff (tested_mono I eps h)]
  calc (∏ i ∈ tested I eps M \ tested I eps N, I.p i) * ∏ i ∈ tested I eps N, I.p i
      ≤ 1 * ∏ i ∈ tested I eps N, I.p i := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun i _ => (hI.2.1 i).1)
        exact Finset.prod_le_one (fun i _ => (hI.2.1 i).1) (fun i _ => (hI.2.1 i).2)
    _ = _ := one_mul _

theorem P0_zero : P0 I eps 0 = 1 := by
  simp [P0, tested_zero]

theorem cmin_pos (hI : I.Standing) : 0 < cmin I := by
  obtain ⟨hn, -, hc, -⟩ := hI
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := I.c)
  unfold cmin; rw [← hj]; exact hc j

theorem stepCost_nonneg (hI : I.Standing) (h0 : 0 < eps) (Δ : State I eps) :
    0 ≤ stepCost I eps Δ := by
  unfold stepCost
  have := cmin_pos I hI
  have := hI.2.2.2
  apply add_nonneg (div_nonneg this (le_of_lt ‹_›))
  exact Finset.sum_nonneg fun r _ => by positivity

theorem pathCost_cons_cons (a b : State I eps) (l : List (State I eps)) :
    pathCost I eps (a :: b :: l) = P0 I eps a * stepCost I eps (b - a) + pathCost I eps (b :: l) := by
  simp [pathCost]

theorem pathCost_single (a : State I eps) : pathCost I eps [a] = 0 := by
  simp [pathCost]

theorem pathCost_nil : pathCost I eps [] = 0 := by
  simp [pathCost]

theorem schemeOf_cons_cons (a b : State I eps) (l : List (State I eps)) :
    schemeOf I eps (a :: b :: l) = (tested I eps b \ tested I eps a) :: schemeOf I eps (b :: l) := by
  simp [schemeOf]

theorem schemeOf_single (a : State I eps) : schemeOf I eps [a] = [] := by
  simp [schemeOf]

theorem phi_cons_succ (B : Finset (Fin n)) (S : List (Finset (Fin n))) (t : ℕ) :
    phi I (B :: S) (t + 1) = (∏ i ∈ B, I.p i) * phi I S t := by
  unfold phi
  rw [Finset.prod_range_succ']
  simp [mul_comm]

theorem expectedCostWith_cons (c : Fin n → ℝ) (B : Finset (Fin n)) (S : List (Finset (Fin n))) :
    expectedCostWith I c (B :: S) =
      batchCost I c B + (∏ i ∈ B, I.p i) * expectedCostWith I c S := by
  unfold expectedCostWith
  rw [List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
  simp only [phi_cons_succ, List.getD_cons_succ, List.getD_cons_zero]
  have : phi I (B :: S) 0 = 1 := by simp [phi]
  rw [this, one_mul, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem batchCost_step (hI : I.Standing) {a b : State I eps} (hab : a ≤ b) (hb : b ∈ F I eps) :
    batchCost I (roundedCost I eps) (tested I eps b \ tested I eps a) =
      cmin I * stepCost I eps (b - a) := by
  have hm := cmin_pos I hI
  unfold batchCost stepCost
  have hsum : ∑ i ∈ tested I eps b \ tested I eps a, roundedCost I eps i =
      ∑ i ∈ tested I eps b \ tested I eps a,
        (fun r : Fin (R I eps + 1) => cmin I * (1 + eps) ^ (r : ℕ)) (classIdx I eps i) := rfl
  rw [hsum, sum_by_class I eps _ (fun r : Fin (R I eps + 1) => cmin I * (1 + eps) ^ (r : ℕ))]
  simp only [card_sdiff_filter I eps hab hb, Pi.sub_apply]
  rw [mul_add, Finset.mul_sum, mul_div_cancel₀ _ hm.ne']
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  ring

end BTCommon

open BatchTesting.PTAS

namespace BTCard
open BTCommon

theorem le_psi {m : ℕ} (N : Fin m → ℕ) (r : Fin m) (h : N r ≠ 0) : (r : ℤ) ≤ psi N := by
  unfold psi
  have : (r : ℕ) + 1 ≤ (Finset.univ.filter (fun r => N r ≠ 0)).sup (fun r => (r : ℕ) + 1) :=
    Finset.le_sup (f := fun r : Fin m => (r : ℕ) + 1) (by simp [h])
  omega

theorem psi_cases {m : ℕ} (N : Fin m → ℕ) :
    psi N = -1 ∨ ∃ r : Fin m, N r ≠ 0 ∧ psi N = r := by
  unfold psi
  by_cases hs : (Finset.univ.filter (fun r => N r ≠ 0)).Nonempty
  · obtain ⟨r, hr, heq⟩ := Finset.exists_mem_eq_sup _ hs (fun r : Fin m => (r : ℕ) + 1)
    right
    refine ⟨r, (Finset.mem_filter.mp hr).2, ?_⟩
    rw [heq]; push_cast; ring
  · left
    rw [Finset.not_nonempty_iff_eq_empty] at hs
    rw [hs]; simp

/-- Tuples of length `k` with sum at most `s` number at most `C(s+k, k)`. -/
theorem card_tuples_le (k s : ℕ) :
    ((Fintype.piFinset (fun _ : Fin k => Finset.range (s + 1))).filter
      (fun f => ∑ j, f j ≤ s)).card ≤ Nat.choose (s + k) k := by
  classical
  let toMS : (Fin k → ℕ) → Multiset (Fin (k + 1)) := fun f =>
    (∑ j, Multiset.replicate (f j) (Fin.castSucc j)) +
      Multiset.replicate (s - ∑ j, f j) (Fin.last k)
  have hcount : ∀ f (j : Fin k), (toMS f).count (Fin.castSucc j) = f j := by
    intro f j
    simp only [toMS, Multiset.count_add, Multiset.count_sum', Multiset.count_replicate]
    rw [Finset.sum_eq_single j]
    · simp only [if_true]
      rw [if_neg (fun h => (Fin.castSucc_lt_last j).ne h.symm)]
      simp
    · intro b _ hb
      simp [Fin.castSucc_inj, hb]
    · simp
  have hcard : ∀ f, ∑ j, f j ≤ s → Multiset.card (toMS f) = s := by
    intro f hf
    simp only [toMS, Multiset.card_add, Multiset.card_sum, Multiset.card_replicate]
    omega
  let T : Finset (Multiset (Fin (k + 1))) :=
    Finset.image (Sym.toMultiset (α := Fin (k + 1)) (n := s)) Finset.univ
  have hT : T.card ≤ Nat.choose (s + k) k := by
    calc T.card ≤ (Finset.univ : Finset (Sym (Fin (k + 1)) s)).card := Finset.card_image_le
      _ = Nat.choose (s + k) k := by
        rw [Finset.card_univ, Sym.card_sym_eq_choose, Fintype.card_fin]
        rw [show k + 1 + s - 1 = s + k by omega, Nat.choose_symm_add]
  refine le_trans (Finset.card_le_card_of_injOn toMS ?_ ?_) hT
  · intro f hf
    have hf' := (Finset.mem_filter.mp hf).2
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨(⟨toMS f, hcard f hf'⟩ : Sym (Fin (k + 1)) s), Finset.mem_univ _, rfl⟩)
  · intro f _ g _ hfg
    funext j
    rw [← hcount f j, ← hcount g j, hfg]

variable {n : ℕ} (I : Instance n) (eps : ℝ)

/-- The state determined by `ψ`, `ρ` and the middle-class multipliers `µ'`. -/
noncomputable def recon (x : ℤ × ℕ × (Fin (kappa n eps).toNat → ℕ)) : State I eps := fun r =>
  if (r : ℤ) ≤ x.1 - kappa n eps then (cls I eps r).card
  else if (r : ℤ) ≤ x.1 then
    (if h : ((r : ℤ) - (x.1 - kappa n eps + 1)).toNat < (kappa n eps).toNat then
      min ⌊(x.2.2 ⟨_, h⟩ : ℝ) * (eps ^ 2 / (kappa n eps : ℝ)) * P2 ((1 + eps) ^ x.2.1) /
        (1 + eps) ^ (r : ℕ)⌋₊ (cls I eps r).card
    else 0)
  else 0

end BTCard

open BTCommon BTCard in
theorem solution {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1) :
    (FGreat I eps).card ≤ (n + 1) * (R I eps + ⌈Real.logb (1 + eps) (n : ℝ)⌉₊ + 1) *
      Nat.choose (⌊3 * (kappa n eps : ℝ) / eps ^ 2⌋₊ + (kappa n eps).toNat) (kappa n eps).toNat := by
  classical
  set κ := kappa n eps with hκ
  set k := κ.toNat with hk
  set s := ⌊3 * (κ : ℝ) / eps ^ 2⌋₊ with hs
  let A : Finset ℤ := insert (-1) (Finset.univ.image (fun i : Fin n => (classOf I eps i : ℤ)))
  let B : Finset ℕ := Finset.range (R I eps + ⌈Real.logb (1 + eps) (n : ℝ)⌉₊ + 1)
  let C : Finset (Fin k → ℕ) :=
    (Fintype.piFinset (fun _ : Fin k => Finset.range (s + 1))).filter (fun f => ∑ j, f j ≤ s)
  have hA : A.card ≤ n + 1 := by
    calc A.card ≤ (Finset.univ.image (fun i : Fin n => (classOf I eps i : ℤ))).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ n + 1 := by
        have := Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => (classOf I eps i : ℤ))
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega
  have hC : C.card ≤ Nat.choose (s + k) k := card_tuples_le k s
  have hsub : FGreat I eps ⊆ (A ×ˢ B ×ˢ C).image (recon I eps) := by
    intro N hN
    have hN' : N ∈ F I eps ∧ IsGreat I eps N := by
      unfold FGreat at hN; exact Finset.mem_filter.mp hN
    obtain ⟨hNF, hnice, ρ, hρ, μ, hμsum, hμ⟩ := hN'
    -- the middle multipliers, re-indexed by `j = r - (ψ - κ + 1)`
    let valid : Fin k → Prop := fun j =>
      0 ≤ psi N - κ + 1 + (j : ℕ) ∧ (psi N - κ + 1 + (j : ℕ)).toNat ≤ R I eps
    let g : Fin k → Fin (R I eps + 1) := fun j =>
      ⟨min (psi N - κ + 1 + (j : ℕ)).toNat (R I eps), Nat.lt_succ_of_le (min_le_right _ _)⟩
    let μ' : Fin k → ℕ := fun j => if valid j then μ (g j) else 0
    rw [Finset.mem_image]
    refine ⟨(psi N, ρ, μ'), ?_, ?_⟩
    · simp only [Finset.mem_product]
      refine ⟨?_, ?_, ?_⟩
      · rcases psi_cases N with h | ⟨r, hr, h⟩
        · rw [h]; exact Finset.mem_insert_self _ _
        · rw [h]
          apply Finset.mem_insert_of_mem
          have hcpos : 0 < (cls I eps r).card := by
            have := (mem_F I eps).mp hNF r; omega
          obtain ⟨i, hi⟩ := Finset.card_pos.mp hcpos
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [(mem_cls I eps).mp hi]⟩
      · simp only [B, Finset.mem_range]; omega
      · simp only [C, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        -- the sum of µ' is bounded by the middle sum of µ
        have hle : ∑ j, μ' j ≤ ∑ r ∈ Finset.univ.filter (fun r : Fin (R I eps + 1) =>
            IsMiddle (psi N) κ r), μ r := by
          have e1 : ∑ j, μ' j = ∑ j ∈ Finset.univ.filter valid, μ (g j) := by
            rw [Finset.sum_filter]
          rw [e1, ← Finset.sum_image (g := g) (f := μ)]
          · apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro r hr
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
              have hv := (Finset.mem_filter.mp hj).2
              have hjk := j.isLt
              simp only [valid] at hv
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              simp only [IsMiddle, g]
              omega
            · intros; exact Nat.zero_le _
          · intro a ha b hb hab
            have ha' := (Finset.mem_filter.mp ha).2
            have hb' := (Finset.mem_filter.mp hb).2
            simp only [g, valid, Fin.ext_iff] at ha' hb' hab
            apply Fin.ext
            omega
        have hsum : ∑ j, μ' j ≤ s := by
          rw [hs]
          apply Nat.le_floor
          calc ((∑ j, μ' j : ℕ) : ℝ) ≤ ((∑ r ∈ Finset.univ.filter (fun r : Fin (R I eps + 1) =>
              IsMiddle (psi N) κ r), μ r : ℕ) : ℝ) := by exact_mod_cast hle
            _ ≤ _ := by push_cast; exact hμsum
        refine ⟨fun j => ?_, hsum⟩
        have := Finset.single_le_sum (f := μ') (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        omega
    · funext r
      unfold recon
      simp only
      have hrR := r.isLt
      split_ifs with h1 h2 h3
      · exact (hnice r h1).symm
      · have hmid : IsMiddle (psi N) κ r := ⟨by omega, h2⟩
        rw [hμ r hmid]
        have hv : valid ⟨_, h3⟩ := by
          simp only [valid]; constructor <;> omega
        have hg : g ⟨_, h3⟩ = r := by
          apply Fin.ext; simp only [g]; omega
        simp only [μ', if_pos hv, hg]
      · exfalso; apply h3; omega
      · by_contra hne
        exact h2 (le_psi N r (Ne.symm hne))
  calc (FGreat I eps).card ≤ ((A ×ˢ B ×ˢ C).image (recon I eps)).card := Finset.card_le_card hsub
    _ ≤ (A ×ˢ B ×ˢ C).card := Finset.card_image_le
    _ = A.card * (B.card * C.card) := by rw [Finset.card_product, Finset.card_product]
    _ ≤ (n + 1) * ((R I eps + ⌈Real.logb (1 + eps) (n : ℝ)⌉₊ + 1) * Nat.choose (s + k) k) := by
        apply Nat.mul_le_mul hA
        apply Nat.mul_le_mul (by simp [B]) hC
    _ = _ := by ring
