-- Prove2me | solution 1 for CountingLLL.DetCount.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T03:53:03.084657+00:00
-- url     : https://prove2.me/submissions/981819b6-a699-4b6d-9a50-3c8d3987a43d

import Mathlib
set_option autoImplicit false

-- The rooted generating-set count below is adapted from dbenbenn’s Apache-2.0 proof
-- of RobustShattering.Supermartingale.lemma_4_2 on Prove2Me.
namespace ConnectedCounting
open Finset
open scoped Classical

variable {V : Type*}

/-- `S ⊆ A`, `R ⊆ S`, and every vertex of `S` is joined to some root in `R` by a path inside `S`. -/
def Gen (H : SimpleGraph V) (A R S : Finset V) : Prop :=
  S ⊆ A ∧ R ⊆ S ∧ ∀ u ∈ S, ∃ r ∈ R,
    Relation.ReflTransGen (fun a b => H.Adj a b ∧ b ∈ S) r u

lemma rtg_mem {H : SimpleGraph V} {S : Finset V} {r u : V}
    (h : Relation.ReflTransGen (fun a b => H.Adj a b ∧ b ∈ S) r u) (hr : r ∈ S) : u ∈ S := by
  induction h with
  | refl => exact hr
  | tail _ hbc _ => exact hbc.2

lemma vand (M s n : ℕ) :
    ∑ k ∈ range (M+1), M.choose k * (if k ≤ n then (M*s).choose (n-k) else 0)
      = (M*(s+1)).choose n := by
  have e : M*(s+1) = M + M*s := by ring
  rw [e, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h1 : ∑ k ∈ range (M+1), M.choose k * (if k ≤ n then (M*s).choose (n-k) else 0)
      = ∑ k ∈ range (M+n+1), M.choose k * (if k ≤ n then (M*s).choose (n-k) else 0) := by
    apply sum_subset (range_subset_range.2 (by omega))
    intro k _ hk
    simp only [mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have h2 : ∑ k ∈ range (n+1), M.choose k * (M*s).choose (n-k)
      = ∑ k ∈ range (M+n+1), M.choose k * (if k ≤ n then (M*s).choose (n-k) else 0) := by
    rw [← sum_subset (range_subset_range.2 (show n+1 ≤ M+n+1 by omega))]
    · apply sum_congr rfl
      intro k hk
      simp only [mem_range] at hk
      rw [if_pos (by omega)]
    · intro k _ hk
      simp only [mem_range] at hk
      rw [if_neg (by omega)]; simp
  rw [h1, h2]

theorem gen_count (H : SimpleGraph V) [H.LocallyFinite] (M : ℕ)
    (hM : ∀ u, (H.neighborFinset u).card ≤ M) :
    ∀ (s : ℕ) (A R : Finset V),
      ((A.powerset).filter (fun S => S.card = s ∧ Gen H A R S)).card
        ≤ if R.card ≤ s then (M*s).choose (s - R.card) else 0 := by
  intro s
  induction s with
  | zero =>
    intro A R
    by_cases hR : R.card ≤ 0
    · rw [if_pos hR]
      have : (A.powerset.filter (fun S => S.card = 0 ∧ Gen H A R S)) ⊆ {∅} := by
        intro S hS
        simp only [mem_filter, mem_powerset] at hS
        simp [card_eq_zero.1 hS.2.1]
      calc _ ≤ ({∅} : Finset (Finset V)).card := card_le_card this
        _ ≤ _ := by simp
    · rw [if_neg hR]
      have : (A.powerset.filter (fun S => S.card = 0 ∧ Gen H A R S)) = ∅ := by
        apply eq_empty_of_forall_notMem
        intro S hS
        simp only [mem_filter] at hS
        have := card_le_card hS.2.2.2.1
        omega
      rw [this, card_empty]
  | succ s ih =>
    intro A R
    by_cases hR : R.card ≤ s+1
    swap
    · rw [if_neg hR]
      have : (A.powerset.filter (fun S => S.card = s+1 ∧ Gen H A R S)) = ∅ := by
        apply eq_empty_of_forall_notMem
        intro S hS
        simp only [mem_filter] at hS
        have := card_le_card hS.2.2.2.1
        omega
      simp [this]
    rw [if_pos hR]
    rcases R.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
    · have : (A.powerset.filter (fun S => S.card = s+1 ∧ Gen H A ∅ S)) = ∅ := by
        apply eq_empty_of_forall_notMem
        intro S hS
        simp only [mem_filter] at hS
        obtain ⟨u, hu⟩ : S.Nonempty := card_pos.1 (by omega)
        obtain ⟨r, hr, _⟩ := hS.2.2.2.2 u hu
        simp at hr
      simp [this]
    · have hr1 : 1 ≤ R.card := card_pos.2 ⟨w, hw⟩
      set P : Finset V := ((A.erase w).filter (H.Adj w)) \ R with hP
      have hPM : P.card ≤ M := by
        refine le_trans (card_le_card ?_) (hM w)
        intro x hx
        simp only [hP, mem_sdiff, mem_filter] at hx
        exact (H.mem_neighborFinset w x).2 hx.1.2
      set n := s + 1 - R.card with hn
      set g : ℕ → ℕ := fun k => if k ≤ n then (M*s).choose (n-k) else 0 with hg
      have hB : ∀ W : Finset V, W ∈ P.powerset →
          (((A.erase w).powerset.filter
              (fun S' => S'.card = s ∧ Gen H (A.erase w) ((R.erase w) ∪ W) S')).image
              (insert w)).card ≤ g W.card := by
        intro W hW
        have hWP : W ⊆ P := mem_powerset.1 hW
        have hdisj : Disjoint (R.erase w) W := by
          rw [disjoint_left]
          intro x hx hxW
          have := hWP hxW
          simp only [hP, mem_sdiff] at this
          exact this.2 (mem_of_mem_erase hx)
        have hcardR : ((R.erase w) ∪ W).card = R.card - 1 + W.card := by
          rw [card_union_of_disjoint hdisj, card_erase_of_mem hw]
        refine le_trans card_image_le (le_trans (ih (A.erase w) ((R.erase w) ∪ W)) ?_)
        rw [hcardR]
        simp only [hg, hn]
        split_ifs with h1 h2 h2
        · apply le_of_eq; congr 1; omega
        · omega
        · omega
        · exact le_rfl
      have hcover : (A.powerset.filter (fun S => S.card = s+1 ∧ Gen H A R S)) ⊆
          P.powerset.biUnion (fun W => ((A.erase w).powerset.filter
              (fun S' => S'.card = s ∧ Gen H (A.erase w) ((R.erase w) ∪ W) S')).image
              (insert w)) := by
        intro S hS
        simp only [mem_filter, mem_powerset] at hS
        obtain ⟨hSA, hcard, _, hRS, hconn⟩ := hS
        have hwS : w ∈ S := hRS hw
        set W : Finset V := ((S.erase w).filter (H.Adj w)) \ R with hW
        have hWP : W ⊆ P := by
          intro x hx
          simp only [hW, hP, mem_sdiff, mem_filter] at hx ⊢
          refine ⟨⟨?_, hx.1.2⟩, hx.2⟩
          exact mem_erase.2 ⟨(mem_erase.1 hx.1.1).1, hSA (mem_erase.1 hx.1.1).2⟩
        rw [mem_biUnion]
        refine ⟨W, mem_powerset.2 hWP, ?_⟩
        rw [mem_image]
        refine ⟨S.erase w, ?_, insert_erase hwS⟩
        rw [mem_filter, mem_powerset]
        have hWS : W ⊆ S.erase w := by
          intro x hx
          simp only [hW, mem_sdiff, mem_filter] at hx
          exact hx.1.1
        refine ⟨erase_subset_erase w hSA, by rw [card_erase_of_mem hwS]; omega,
          erase_subset_erase w hSA, ?_, ?_⟩
        · intro x hx
          rw [mem_union] at hx
          rcases hx with hx | hx
          · exact erase_subset_erase w hRS hx
          · exact hWS hx
        · intro u hu
          obtain ⟨r, hrR, hch⟩ := hconn u (mem_of_mem_erase hu)
          have huw : u ≠ w := ne_of_mem_erase hu
          -- generalised induction on the chain
          have key : ∀ u', Relation.ReflTransGen (fun a b => H.Adj a b ∧ b ∈ S) r u' →
              u' ∈ S.erase w → ∃ r' ∈ (R.erase w) ∪ W,
                Relation.ReflTransGen (fun a b => H.Adj a b ∧ b ∈ S.erase w) r' u' := by
            intro u' h
            induction h with
            | refl =>
              intro hu'
              refine ⟨r, ?_, Relation.ReflTransGen.refl⟩
              exact mem_union_left _ (mem_erase.2 ⟨ne_of_mem_erase hu', hrR⟩)
            | @tail b c hrb hbc ihb =>
              intro hc
              by_cases hbw : b = w
              · subst hbw
                refine ⟨c, ?_, Relation.ReflTransGen.refl⟩
                by_cases hcR : c ∈ R
                · exact mem_union_left _ (mem_erase.2 ⟨ne_of_mem_erase hc, hcR⟩)
                · apply mem_union_right
                  simp only [hW, mem_sdiff, mem_filter]
                  exact ⟨⟨hc, hbc.1⟩, hcR⟩
              · have hbS : b ∈ S := rtg_mem hrb (hRS hrR)
                obtain ⟨r', hr', hch'⟩ := ihb (mem_erase.2 ⟨hbw, hbS⟩)
                exact ⟨r', hr', hch'.tail ⟨hbc.1, hc⟩⟩
          exact key u hch hu
      calc _ ≤ _ := card_le_card hcover
        _ ≤ ∑ W ∈ P.powerset, (((A.erase w).powerset.filter
              (fun S' => S'.card = s ∧ Gen H (A.erase w) ((R.erase w) ∪ W) S')).image
              (insert w)).card := card_biUnion_le
        _ ≤ ∑ W ∈ P.powerset, g W.card := sum_le_sum hB
        _ = ∑ m ∈ range (P.card+1), P.card.choose m • g m := sum_powerset_apply_card g
        _ ≤ ∑ m ∈ range (P.card+1), M.choose m * g m := by
            apply sum_le_sum
            intro m _
            rw [smul_eq_mul]
            exact Nat.mul_le_mul_right _ (Nat.choose_le_choose _ hPM)
        _ ≤ ∑ m ∈ range (M+1), M.choose m * g m :=
            sum_le_sum_of_subset (range_subset_range.2 (by omega))
        _ = (M*(s+1)).choose n := vand M s n


lemma connected_gen (H : SimpleGraph V) (S : Finset V) (v : V) (hv : v ∈ S)
    (hc : (H.induce (S : Set V)).Connected) (A : Finset V) (hSA : S ⊆ A) : Gen H A {v} S := by
  refine ⟨hSA, by simpa using hv, ?_⟩
  intro u hu
  refine ⟨v, mem_singleton_self _, ?_⟩
  have hr : (H.induce (S : Set V)).Reachable ⟨v, hv⟩ ⟨u, hu⟩ := hc.preconnected _ _
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  have := Relation.ReflTransGen.lift (fun x : ↥(S : Set V) => (x : V))
    (r := fun a b => (H.induce (S : Set V)).Adj a b)
    (p := fun a b => H.Adj a b ∧ b ∈ S) (fun a b hab => ⟨by simpa using hab, b.2⟩) _ _ hr
  exact this

end ConnectedCounting

private theorem pow_succ_le_exp_fact (k : ℕ) :
    ((k : ℝ) + 1)^k ≤ Real.exp 1 ^ k * (k.factorial : ℝ) := by
  by_cases hk0 : k = 0
  · subst k; simp
  by_cases hk1 : k = 1
  · subst k
    norm_num
    linarith [Real.exp_one_gt_two]
  have hk2 : 2 ≤ k := by omega
  have hk : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hp : (1 + 1 / (k : ℝ)) ^ k ≤ Real.exp 1 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + 1 / (k : ℝ) by positivity)
      (show 1 + 1 / (k : ℝ) ≤ Real.exp (1 / (k : ℝ)) by linarith [Real.add_one_le_exp (1 / (k : ℝ))]) k
    rw [← Real.exp_nat_mul] at h
    have heq : (k : ℝ) * (k : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hk)
    simpa only [one_div, heq] using h
  have hsqrt : Real.exp 1 ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    apply (Real.le_sqrt he.le (by positivity)).2
    have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hpigt := Real.pi_gt_three
    have he3 := Real.exp_one_lt_three
    nlinarith [sq_nonneg (Real.exp 1 - 3), sq_nonneg (Real.exp 1)]
  have hratio : (1 + 1 / (k : ℝ)) ^ k ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := le_trans hp hsqrt
  have hst := Stirling.le_factorial_stirling k
  have hmul := mul_le_mul_of_nonneg_right hst (pow_nonneg he.le k)
  have hs : Real.sqrt (2 * Real.pi * (k : ℝ)) * (k : ℝ)^k ≤
      (k.factorial : ℝ) * Real.exp 1 ^ k := by
    have hpow : ((k : ℝ) / Real.exp 1)^k * Real.exp 1 ^ k = (k : ℝ)^k := by
      rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt he)]
    rw [← hpow]
    nlinarith [hmul]
  calc
    ((k : ℝ) + 1)^k = (k : ℝ)^k * (1 + 1 / (k : ℝ))^k := by
      rw [← mul_pow]
      congr 1
      field_simp
    _ ≤ (k : ℝ)^k * Real.sqrt (2 * Real.pi * (k : ℝ)) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ _ := by nlinarith

private theorem choose_real_sharp (M t : ℕ) (ht : 1 ≤ t) :
    (((M*t).choose (t-1) : ℕ) : ℝ) ≤ (Real.exp 1 * (M : ℝ))^(t-1) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k+1 := ⟨t-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h := Nat.choose_le_pow_div (α := ℝ) k (M*(k+1))
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hh := pow_succ_le_exp_fact k
  calc
    (((M*(k+1)).choose k : ℕ) : ℝ) ≤ ((M*(k+1) : ℕ) : ℝ)^k / (k.factorial : ℝ) := h
    _ = (M : ℝ)^k * (((k : ℝ)+1)^k / (k.factorial : ℝ)) := by push_cast; rw [mul_pow]; ring
    _ ≤ (M : ℝ)^k * (Real.exp 1)^k := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_iff₀ hf).2 (by nlinarith [hh])
    _ = _ := by rw [mul_pow]; ring

open ConnectedCounting

theorem solution {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (Δ : ℕ)
    (hΔ : ∀ u, G.degree u ≤ Δ) (v : V) (ℓ : ℕ) :
    {S : Finset V | v ∈ S ∧ S.card = ℓ ∧ (G.induce (S : Set V)).Connected}.Finite ∧
    (({S : Finset V | v ∈ S ∧ S.card = ℓ ∧ (G.induce (S : Set V)).Connected}.ncard : ℕ) : ℝ) ≤
      (Real.exp 1 * Δ) ^ (ℓ - 1) := by
  classical
  let T : Set (Finset V) := {S : Finset V | v ∈ S ∧ S.card = ℓ ∧ (G.induce (S : Set V)).Connected}
  let B : ℕ := if 1 ≤ ℓ then (Δ*ℓ).choose (ℓ-1) else 0
  have hF : ∀ F : Finset (Finset V), (↑F : Set (Finset V)) ⊆ T → F.card ≤ B := by
    intro F hFT
    by_cases ht : 1 ≤ ℓ
    · let A : Finset V := F.biUnion id
      have hsub : F ⊆ A.powerset.filter (fun S => S.card = ℓ ∧ Gen G A {v} S) := by
        intro S hS
        have hTS : v ∈ S ∧ S.card = ℓ ∧ (G.induce (S : Set V)).Connected := hFT hS
        have hSA : S ⊆ A := Finset.subset_biUnion_of_mem id hS
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hSA, hTS.2.1, connected_gen G S v hTS.1 hTS.2.2 A hSA⟩
      have hh := gen_count G Δ (fun u => by simpa using hΔ u) ℓ A {v}
      have : F.card ≤ (Δ*ℓ).choose (ℓ-1) := by
        calc
          _ ≤ (A.powerset.filter (fun S => S.card = ℓ ∧ Gen G A {v} S)).card := Finset.card_le_card hsub
          _ ≤ _ := by simpa [ht] using hh
      simpa [B, ht] using this
    · have hzero : ℓ = 0 := by omega
      have hEmpty : F = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro S hS
        have hTS : v ∈ S ∧ S.card = ℓ ∧ (G.induce (S : Set V)).Connected := hFT hS
        have : S = ∅ := Finset.card_eq_zero.mp (by simpa [hzero] using hTS.2.1)
        simpa [this] using hTS.1
      simp [hEmpty, B, ht]
  have hfinite : T.Finite := by
    by_contra hnot
    obtain ⟨F, hFT, hcard⟩ := (Set.not_finite.mp hnot).exists_subset_card_eq (B+1)
    have hb := hF F hFT
    omega
  have hcard : T.ncard ≤ B := by
    have hh := hF hfinite.toFinset (by simp)
    simpa only [← Set.ncard_coe_finset, hfinite.coe_toFinset] using hh
  refine ⟨hfinite, ?_⟩
  change (T.ncard : ℝ) ≤ _
  by_cases ht : 1 ≤ ℓ
  · calc
      _ ≤ (B : ℝ) := by exact_mod_cast hcard
      _ = (((Δ*ℓ).choose (ℓ-1) : ℕ) : ℝ) := by simp [B, ht]
      _ ≤ (Real.exp 1 * (Δ : ℝ)) ^ (ℓ-1) := choose_real_sharp Δ ℓ ht
  · have hz : ℓ = 0 := by omega
    have : T.ncard = 0 := by
      have : B = 0 := by simp [B, ht]
      omega
    simp [this, hz]
